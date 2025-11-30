/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps

module gshare_bp
  import ceres_param::*;
(
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic                     spec_hit_i,     // Speculation doğru mu? (1=doğru, 0=misprediction)
    input  logic                     stall_i,        // Pipeline stall sinyali
    input  inst_t                    inst_i,         // Fetch edilen instruction
    input  logic          [XLEN-1:0] pc_target_i,    // EX aşamasından gelen gerçek branch hedefi
    input  logic          [XLEN-1:0] pc_i,           // Mevcut program counter
    input  logic          [XLEN-1:0] pc_incr_i,      // PC + 4 (sequential adres)
    input  logic                     fetch_valid_i,  // Fetch geçerli mi?
    output predict_info_t            spec_o,         // Prediction çıktısı (pc, taken)
    input  pipe_info_t               de_info_i,
    input  pipe_info_t               ex_info_i
);

  // ============================================================================
  // GSHARE YAPISAL BİLEŞENLERİ
  // ============================================================================

  // Global History Register: Son N branch'in sonuçlarını tutar
  logic [             GHR_SIZE-1:0] ghr;

  // Pattern History Table: 2-bit saturating counter'lar
  logic [                      1:0] pht       [PHT_SIZE];

  // Branch Target Buffer
  logic                             btb_valid [BTB_SIZE];
  logic [XLEN-1:$clog2(BTB_SIZE)+2] btb_tag   [BTB_SIZE];
  logic [                 XLEN-1:0] btb_target[BTB_SIZE];

  // Indirect Branch Target Cache (JALR için)
  // PC ile indekslenen basit bir hedef adresi tablosu
  localparam IBTC_SIZE = 32;  // 32 entry indirect branch target cache
  logic                              ibtc_valid                          [IBTC_SIZE];
  logic [XLEN-1:$clog2(IBTC_SIZE)+2] ibtc_tag                            [IBTC_SIZE];
  logic [                  XLEN-1:0] ibtc_target                         [IBTC_SIZE];

  // ============================================================================
  // İÇ SİNYALLER
  // ============================================================================

  // Immediate değer (B/J type için)
  logic [                  XLEN-1:0] imm;

  // Instruction type decode sinyalleri
  logic                              j_type;  // JAL (unconditional jump)
  logic                              jr_type;  // JALR (indirect jump)
  logic                              b_type;  // Conditional branch

  // RAS sinyalleri
  logic                              req_valid;
  logic [                  XLEN-1:0] return_addr;
  ras_t                              restore;
  ras_t                              popped;

  // Index hesaplama
  logic [      $clog2(PHT_SIZE)-1:0] pht_rd_idx;
  logic [      $clog2(PHT_SIZE)-1:0] pht_wr_idx;
  logic [      $clog2(BTB_SIZE)-1:0] btb_rd_idx;
  logic [      $clog2(BTB_SIZE)-1:0] btb_wr_idx;
  logic [     $clog2(IBTC_SIZE)-1:0] ibtc_rd_idx;
  logic [     $clog2(IBTC_SIZE)-1:0] ibtc_wr_idx;

  // BTB lookup sonuçları
  logic                              btb_hit;
  logic [                  XLEN-1:0] btb_predicted_target;

  // IBTC lookup sonuçları
  logic                              ibtc_hit;
  logic [                  XLEN-1:0] ibtc_predicted_target;

  // PHT prediction
  logic                              pht_taken;

  // Misprediction sinyali
  logic                              spec_miss;

  // EX stage'den gelen branch bilgisi
  logic                              ex_is_branch;
  logic                              ex_was_taken;

  // ============================================================================
  // INSTRUCTION DECODE
  // ============================================================================
  always_comb begin
    // Instruction type detection
    b_type  = (inst_i[6:0] == op_b_type);
    j_type  = (inst_i[6:0] == op_u_type_jump);
    jr_type = (inst_i[6:0] == op_i_type_jump);

    // Immediate extraction
    case (1'b1)
      b_type:  imm = {{20{inst_i[31]}}, inst_i[7], inst_i[30:25], inst_i[11:8], 1'b0};
      j_type:  imm = {{12{inst_i[31]}}, inst_i[19:12], inst_i[20], inst_i[30:21], 1'b0};
      jr_type: imm = {{20{inst_i[31]}}, inst_i[31:20]};
      default: imm = '0;
    endcase

    return_addr = pc_incr_i;
  end

  // ============================================================================
  // INDEX HESAPLAMA
  // ============================================================================
  always_comb begin
    // GSHARE: PC XOR GHR
    pht_rd_idx  = pc_i[$clog2(PHT_SIZE):1] ^ ghr[$clog2(PHT_SIZE)-1:0];
    btb_rd_idx  = pc_i[$clog2(BTB_SIZE):1];
    ibtc_rd_idx = pc_i[$clog2(IBTC_SIZE):1];

    // Write index'leri (EX stage PC ile)
    pht_wr_idx  = ex_info_i.pc[$clog2(PHT_SIZE):1] ^ ghr[$clog2(PHT_SIZE)-1:0];
    btb_wr_idx  = ex_info_i.pc[$clog2(BTB_SIZE):1];
    ibtc_wr_idx = ex_info_i.pc[$clog2(IBTC_SIZE):1];
  end

  // ============================================================================
  // BTB & IBTC LOOKUP
  // ============================================================================
  always_comb begin
    btb_hit = btb_valid[btb_rd_idx] && (btb_tag[btb_rd_idx] == pc_i[XLEN-1:$clog2(BTB_SIZE)+2]);
    btb_predicted_target = btb_target[btb_rd_idx];

    ibtc_hit = ibtc_valid[ibtc_rd_idx] && (ibtc_tag[ibtc_rd_idx] == pc_i[XLEN-1:$clog2(IBTC_SIZE)+2]);
    ibtc_predicted_target = ibtc_target[ibtc_rd_idx];

    pht_taken = pht[pht_rd_idx][1];  // MSB = taken prediction
  end

  // ============================================================================
  // PREDICTION LOGIC
  // ============================================================================
  always_comb begin
    spec_miss       = !spec_hit_i && (ex_info_i.bjtype != NO_BJ);

    // RAS restore kontrolü
    restore.data    = de_info_i.pc;
    restore.valid   = !stall_i && !spec_hit_i && (de_info_i.spec.spectype == RAS);

    // RAS request
    req_valid       = !spec_miss && !stall_i && fetch_valid_i && (j_type || jr_type);

    // Prediction öncelik sırası:
    // 1. RAS (return prediction)
    // 2. JAL (unconditional direct jump)
    // 3. JALR (unconditional indirect jump) - IBTC kullan
    // 4. Branch (conditional) - PHT + BTB
    // 5. Sequential (PC + 4)

    spec_o.pc       = pc_incr_i;
    spec_o.taken    = 1'b0;
    spec_o.spectype = NO_SPEC;

    if (fetch_valid_i && !stall_i) begin
      if (popped.valid) begin
        // RAS hit - return prediction
        spec_o.pc       = popped.data;
        spec_o.taken    = 1'b1;
        spec_o.spectype = RAS;
      end else if (j_type) begin
        // JAL - always taken, PC-relative
        spec_o.pc       = pc_i + imm;
        spec_o.taken    = 1'b1;
        spec_o.spectype = JUMP;
      end else if (jr_type && ibtc_hit) begin
        // JALR - IBTC hit, use cached target
        spec_o.pc       = ibtc_predicted_target;
        spec_o.taken    = 1'b1;
        spec_o.spectype = JUMP;
      end else if (b_type && pht_taken && btb_hit) begin
        // Branch predicted taken ve BTB hit
        spec_o.pc       = btb_predicted_target;
        spec_o.taken    = 1'b1;
        spec_o.spectype = BRANCH;
      end
      // else: sequential (default)
    end
  end

  // ============================================================================
  // EX STAGE FEEDBACK
  // ============================================================================
  always_comb begin
    ex_is_branch = (ex_info_i.bjtype != NO_BJ) && (ex_info_i.spec.spectype == BRANCH);

    // Branch gerçekten alındı mı?
    // spec_hit && taken -> doğru tahmin, taken
    // !spec_hit && !taken -> yanlış tahmin ama aslında taken (branch taken, biz not-taken dedik)
    ex_was_taken = ex_is_branch && ((spec_hit_i && ex_info_i.spec.taken) || (!spec_hit_i && !ex_info_i.spec.taken));
  end

  // ============================================================================
  // RETURN ADDRESS STACK (RAS)
  // ============================================================================
  ras #(
      .RAS_SIZE(RAS_SIZE)
  ) i_ras (
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),
      .restore_i    (restore),
      .req_valid_i  (req_valid),
      .rd_addr_i    (inst_i.rd_addr),
      .r1_addr_i    (inst_i.r1_addr),
      .j_type_i     (j_type),
      .jr_type_i    (jr_type),
      .return_addr_i(return_addr),
      .popped_o     (popped)
  );

  // ============================================================================
  // PHT, BTB, IBTC ve GHR UPDATE
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      ghr <= '0;
      for (int i = 0; i < PHT_SIZE; i++) pht[i] <= 2'b01;  // Weakly Not-Taken
      for (int i = 0; i < BTB_SIZE; i++) begin
        btb_valid[i]  <= 1'b0;
        btb_tag[i]    <= '0;
        btb_target[i] <= '0;
      end
      for (int i = 0; i < IBTC_SIZE; i++) begin
        ibtc_valid[i]  <= 1'b0;
        ibtc_tag[i]    <= '0;
        ibtc_target[i] <= '0;
      end
    end else if (!stall_i) begin
      // Branch çözüldüğünde güncelle
      if (ex_is_branch) begin
        // PHT Update: 2-bit saturating counter
        if (ex_was_taken) begin
          if (pht[pht_wr_idx] < 2'b11) pht[pht_wr_idx] <= pht[pht_wr_idx] + 1;
        end else begin
          if (pht[pht_wr_idx] > 2'b00) pht[pht_wr_idx] <= pht[pht_wr_idx] - 1;
        end

        // BTB Update: Taken branch'leri cache'le
        if (ex_was_taken) begin
          btb_valid[btb_wr_idx]  <= 1'b1;
          btb_tag[btb_wr_idx]    <= ex_info_i.pc[XLEN-1:$clog2(BTB_SIZE)+2];
          btb_target[btb_wr_idx] <= pc_target_i;
        end

        // GHR Update: Shift left, yeni sonucu ekle
        ghr <= {ghr[GHR_SIZE-2:0], ex_was_taken};
      end

      // IBTC Update: JALR instruction'ları için hedef adresi cache'le
      // RAS tarafından handle edilmeyenler (non-return JALR'lar)
      if (ex_info_i.bjtype == JALR && ex_info_i.spec.spectype != RAS) begin
        ibtc_valid[ibtc_wr_idx]  <= 1'b1;
        ibtc_tag[ibtc_wr_idx]    <= ex_info_i.pc[XLEN-1:$clog2(IBTC_SIZE)+2];
        ibtc_target[ibtc_wr_idx] <= pc_target_i;
      end
    end
  end

  // ============================================================================
  // BRANCH PREDICTION LOGGER
  // Enable with: +define+LOG_BP
  // ============================================================================
`ifdef LOG_BP
  // İstatistik sayaçları (reset'ten bağımsız - kümülatif)
  // ressette verilator sorun çıkarıyor
  logic [63:0] total_branches = '0;
  logic [63:0] correct_predictions = '0;
  logic [63:0] mispredictions = '0;
  logic [63:0] ras_predictions = '0;
  logic [63:0] ras_correct = '0;
  logic [63:0] btb_hits = '0;
  logic [63:0] btb_misses = '0;
  // JAL/JALR için ek sayaçlar
  logic [63:0] jal_count = '0;
  logic [63:0] jal_correct = '0;
  logic [63:0] jalr_count = '0;
  logic [63:0] jalr_correct = '0;
  // IBTC sayaçları
  logic [63:0] ibtc_predictions = '0;
  logic [63:0] ibtc_correct = '0;

  // İstatistik güncelleme (reset'ten bağımsız)
  always_ff @(posedge clk_i) begin
    if (rst_ni && !stall_i) begin
      // Tüm control transfer istatistikleri
      if (ex_info_i.bjtype != NO_BJ) begin
        total_branches <= total_branches + 1;
        if (spec_hit_i) begin
          correct_predictions <= correct_predictions + 1;
        end else begin
          mispredictions <= mispredictions + 1;
        end
      end

      // JAL istatistikleri
      if (ex_info_i.bjtype == JAL) begin
        jal_count <= jal_count + 1;
        if (spec_hit_i) jal_correct <= jal_correct + 1;
      end

      // JALR istatistikleri
      if (ex_info_i.bjtype == JALR) begin
        jalr_count <= jalr_count + 1;
        if (spec_hit_i) jalr_correct <= jalr_correct + 1;
      end

      // RAS istatistikleri
      if (ex_info_i.spec.spectype == RAS) begin
        ras_predictions <= ras_predictions + 1;
        if (spec_hit_i) begin
          ras_correct <= ras_correct + 1;
        end
      end

      // IBTC istatistikleri (JALR, RAS değil, JUMP spectype ile)
      if (ex_info_i.bjtype == JALR && ex_info_i.spec.spectype == JUMP) begin
        ibtc_predictions <= ibtc_predictions + 1;
        if (spec_hit_i) ibtc_correct <= ibtc_correct + 1;
      end

      // Conditional Branch istatistikleri (BEQ, BNE, BLT, BGE, BLTU, BGEU)
      if (ex_info_i.bjtype inside {BEQ, BNE, BLT, BGE, BLTU, BGEU}) begin
        if (spec_hit_i) begin
          btb_hits <= btb_hits + 1;
        end else begin
          btb_misses <= btb_misses + 1;
        end
      end
    end
  end

  // Log dosyasına yazma - VERILATOR_LOG_DIR environment variable kullanır
  integer bp_log_file;
  string  log_dir;
  string  bp_log_path;

  initial begin
    // Environment variable'dan log dizinini al
    if (!$value$plusargs("BP_LOG_DIR=%s", log_dir)) begin
      // Plusarg yoksa environment variable'ı dene
      if ($test$plusargs("VERILATOR_LOG_DIR")) begin
        void'($value$plusargs("VERILATOR_LOG_DIR=%s", log_dir));
      end else begin
        log_dir = ".";  // Varsayılan: çalışma dizini
      end
    end

    bp_log_path = {log_dir, "/bp_stats.log"};
    bp_log_file = $fopen(bp_log_path, "w");

    if (bp_log_file == 0) begin
      $display("ERROR: Cannot open %s", bp_log_path);
    end else begin
      $display("[BP_LOGGER] Writing to: %s", bp_log_path);
      $fwrite(bp_log_file, "=== GSHARE Branch Predictor Statistics ===\n");
      $fwrite(bp_log_file, "Time,TotalBranches,Correct,Mispred,JAL,JAL_Correct,JALR,JALR_Correct,RAS_Total,RAS_Correct,BTB_Hits,BTB_Misses\n");
    end
  end

  // Her N cycle'da log yaz
  localparam LOG_INTERVAL = 10000;
  logic [31:0] log_counter;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      log_counter <= '0;
    end else begin
      log_counter <= log_counter + 1;
      if (log_counter == LOG_INTERVAL) begin
        log_counter <= '0;
        if (bp_log_file != 0) begin
          $fwrite(bp_log_file, "%0t,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d\n", $time, total_branches, correct_predictions, mispredictions, jal_count, jal_correct, jalr_count, jalr_correct,
                  ras_predictions, ras_correct, btb_hits, btb_misses);
          $fflush(bp_log_file);
        end
      end
    end
  end

  // Simülasyon sonunda özet yazdır
  final begin
    automatic real    total_accuracy = total_branches > 0 ? (real'(correct_predictions) * 100.0 / real'(total_branches)) : 0.0;
    automatic real    mispred_rate = total_branches > 0 ? (real'(mispredictions) * 100.0 / real'(total_branches)) : 0.0;
    automatic real    jal_accuracy = jal_count > 0 ? (real'(jal_correct) * 100.0 / real'(jal_count)) : 0.0;
    automatic real    jalr_accuracy = jalr_count > 0 ? (real'(jalr_correct) * 100.0 / real'(jalr_count)) : 0.0;
    automatic real    ras_accuracy = ras_predictions > 0 ? (real'(ras_correct) * 100.0 / real'(ras_predictions)) : 0.0;
    automatic real    ibtc_accuracy = ibtc_predictions > 0 ? (real'(ibtc_correct) * 100.0 / real'(ibtc_predictions)) : 0.0;
    automatic longint cond_total = btb_hits + btb_misses;
    automatic real    cond_accuracy = cond_total > 0 ? (real'(btb_hits) * 100.0 / real'(cond_total)) : 0.0;
    automatic real    cond_mispred = cond_total > 0 ? (real'(btb_misses) * 100.0 / real'(cond_total)) : 0.0;

    if (bp_log_file != 0) begin
      $fwrite(bp_log_file, "\n");
      $fwrite(
          bp_log_file,
          "╔══════════════════════════════════════════════════════════════╗\n");
      $fwrite(bp_log_file, "║          GSHARE Branch Predictor - Final Statistics          ║\n");
      $fwrite(
          bp_log_file,
          "╠══════════════════════════════════════════════════════════════╣\n");
      $fwrite(bp_log_file, "║  Total Control Transfers : %10d                         ║\n", total_branches);
      $fwrite(bp_log_file, "║  Correct Predictions     : %10d  (%6.2f%%)              ║\n", correct_predictions, total_accuracy);
      $fwrite(bp_log_file, "║  Mispredictions          : %10d  (%6.2f%%)              ║\n", mispredictions, mispred_rate);
      $fwrite(
          bp_log_file,
          "╠══════════════════════════════════════════════════════════════╣\n");
      $fwrite(bp_log_file, "║  JAL (Direct Jump)                                           ║\n");
      $fwrite(bp_log_file, "║    Total                 : %10d                         ║\n", jal_count);
      $fwrite(bp_log_file, "║    Correct               : %10d  (%6.2f%%)              ║\n", jal_correct, jal_accuracy);
      $fwrite(
          bp_log_file,
          "╠══════════════════════════════════════════════════════════════╣\n");
      $fwrite(bp_log_file, "║  JALR (Indirect Jump)                                        ║\n");
      $fwrite(bp_log_file, "║    Total                 : %10d                         ║\n", jalr_count);
      $fwrite(bp_log_file, "║    Correct               : %10d  (%6.2f%%)              ║\n", jalr_correct, jalr_accuracy);
      $fwrite(bp_log_file, "║    - RAS Predictions     : %10d  (%6.2f%% accurate)     ║\n", ras_predictions, ras_accuracy);
      $fwrite(bp_log_file, "║    - IBTC Predictions    : %10d  (%6.2f%% accurate)     ║\n", ibtc_predictions, ibtc_accuracy);
      $fwrite(
          bp_log_file,
          "╠══════════════════════════════════════════════════════════════╣\n");
      $fwrite(bp_log_file, "║  Conditional Branch (BEQ/BNE/BLT/BGE/BLTU/BGEU)               ║\n");
      $fwrite(bp_log_file, "║    Total                 : %10d                         ║\n", cond_total);
      $fwrite(bp_log_file, "║    Correct               : %10d  (%6.2f%%)              ║\n", btb_hits, cond_accuracy);
      $fwrite(bp_log_file, "║    Mispredicted          : %10d  (%6.2f%%)              ║\n", btb_misses, cond_mispred);
      $fwrite(
          bp_log_file,
          "╚══════════════════════════════════════════════════════════════╝\n");
      $fclose(bp_log_file);
    end

    $display("");
    $display(
        "╔══════════════════════════════════════════════════════════════╗");
    $display("║          GSHARE Branch Predictor - Final Statistics          ║");
    $display(
        "╠══════════════════════════════════════════════════════════════╣");
    $display("║  Total Control Transfers : %10d                         ║", total_branches);
    $display("║  Correct Predictions     : %10d  (%6.2f%%)              ║", correct_predictions, total_accuracy);
    $display("║  Mispredictions          : %10d  (%6.2f%%)              ║", mispredictions, mispred_rate);
    $display(
        "╠══════════════════════════════════════════════════════════════╣");
    $display("║  JAL (Direct Jump)                                           ║");
    $display("║    Total                 : %10d                         ║", jal_count);
    $display("║    Correct               : %10d  (%6.2f%%)              ║", jal_correct, jal_accuracy);
    $display(
        "╠══════════════════════════════════════════════════════════════╣");
    $display("║  JALR (Indirect Jump)                                        ║");
    $display("║    Total                 : %10d                         ║", jalr_count);
    $display("║    Correct               : %10d  (%6.2f%%)              ║", jalr_correct, jalr_accuracy);
    $display("║    - RAS Predictions     : %10d  (%6.2f%% accurate)     ║", ras_predictions, ras_accuracy);
    $display("║    - IBTC Predictions    : %10d  (%6.2f%% accurate)     ║", ibtc_predictions, ibtc_accuracy);
    $display(
        "╠══════════════════════════════════════════════════════════════╣");
    $display("║  Conditional Branch (BEQ/BNE/BLT/BGE/BLTU/BGEU)               ║");
    $display("║    Total                 : %10d                         ║", cond_total);
    $display("║    Correct               : %10d  (%6.2f%%)              ║", btb_hits, cond_accuracy);
    $display("║    Mispredicted          : %10d  (%6.2f%%)              ║", btb_misses, cond_mispred);
    $display(
        "╚══════════════════════════════════════════════════════════════╝");
    $display("");
  end

  // Real-time misprediction log (opsiyonel, çok verbose)
  // Enable with: +define+LOG_BP_VERBOSE
`ifdef LOG_BP_VERBOSE
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      // nothing
    end else if (!stall_i && !spec_hit_i && (ex_info_i.bjtype != NO_BJ)) begin
      $display("[BP MISS] Time=%0t PC=0x%08h Type=%s Predicted=%s Actual=%s Target=0x%08h", $time, ex_info_i.pc, ex_info_i.spec.spectype.name(), ex_info_i.spec.taken ? "TAKEN" : "NOT_TAKEN",
               ex_info_i.spec.taken ? "NOT_TAKEN" : "TAKEN", pc_target_i);
    end
  end
`endif  // LOG_BP_VERBOSE
`endif  // LOG_BP

endmodule
