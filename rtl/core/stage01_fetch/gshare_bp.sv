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
  // PARAMETRELER VE SABITLER
  // ============================================================================
  localparam PROGRAM_LIMIT = 32'h8000_3D40;  // Program bellek sınırı (muhtemelen gereksiz)

  // ============================================================================
  // İÇ SİNYALLER
  // ============================================================================

  // Immediate değer (B/J/I type için farklı formatlar)
  logic          [                 XLEN-1:0] imm;

  // Instruction type decode sinyalleri
  logic                                      j_type;  // JAL (unconditional jump)
  logic                                      jr_type;  // JALR (indirect jump - register based)
  logic                                      b_type;  // BEQ, BNE, BLT, vb. (conditional branch)

  // RAS (Return Address Stack) sinyalleri
  logic                                      req_valid;  // RAS'a push/pop isteği
  logic          [                 XLEN-1:0] pushed_addr;  // RAS'a push edilecek return adresi

  // ============================================================================
  // GSHARE YAPISAL BİLEŞENLERİ
  // ============================================================================

  // Global History Register: Son N branch'in sonuçlarını tutar
  logic          [             GHR_SIZE-1:0] ghr;

  // Pattern History Table: 2-bit saturating counter'lar
  // Her entry bir branch pattern için tahmin gücünü tutar (00=Strong NT, 11=Strong T)
  logic          [                      1:0] pht                                                           [PHT_SIZE];

  // Branch Target Buffer: Branch hedef adreslerini cache'ler
  logic          [XLEN-1:$clog2(PHT_SIZE)+1] btb_pc                                                        [BTB_SIZE];  // Tag (PC'nin üst bitleri)
  logic          [                 XLEN-1:0] btb_target                                                    [BTB_SIZE];  // Hedef adres

  // SORUN: BTB'de valid bit yok! Initialization'dan sonra garbage match olabilir

  // Pipeline register'ları (2 aşamalık - YETERSİZ!)

  // Prediction bilgisi
  predict_info_t                             branch;  // BTB'den gelen tahmin

  // Index hesaplama sinyalleri
  logic          [     $clog2(PHT_SIZE)-1:0] pht_rd_idx;  // PHT okuma index'i (PC ⊕ GHR)
  logic          [     $clog2(PHT_SIZE)-1:0] pht_wr_idx;  // PHT yazma index'i
  logic          [     $clog2(BTB_SIZE)-1:0] btb_rd_idx;  // BTB okuma index'i
  logic          [     $clog2(BTB_SIZE)-1:0] btb_wr_idx;  // BTB yazma index'i

  // Durum takip değişkenleri
  logic          [                      1:0] pht_ptr;  // SORUN: Amacı belirsiz, tutarlı kullanılmamış
  logic          [                      1:0] pht_bit1;  // PHT'nin MSB'sini tutar (taken/not taken)
  logic                                      ex_taken;  // EX aşamasında branch gerçekten alındı mı?

  // RAS restore sinyalleri
  ras_t                                      restore;
  ras_t                                      popped;
  logic                                      spec_miss;
  // ============================================================================
  // INSTRUCTION DECODE VE PREDICTION LOGIC
  // ============================================================================
  always_comb begin
    spec_miss = (!spec_hit_i && |ex_info_i.bjtype);
    // Instruction type detection
    b_type = inst_i[6:0] == op_b_type;  // Conditional branch
    j_type = inst_i[6:0] == op_u_type_jump;  // JAL
    jr_type = inst_i[6:0] == op_i_type_jump;  // JALR

    // Immediate extraction (RISC-V encoding)
    case (1'b1)
      b_type:  imm = {{20{inst_i[31]}}, inst_i[7], inst_i[30:25], inst_i[11:8], 1'b0};
      j_type:  imm = {{12{inst_i[31]}}, inst_i[19:12], inst_i[20], inst_i[30:21], 1'b0};
      jr_type: imm = {{20{inst_i[31]}}, inst_i[31:20]};
      default: imm = '0;
    endcase

    // Return address (PC+4 / PC+2) - call instruction'lar için
    pushed_addr = pc_incr_i;

    // PREDICTION LOGIC (öncelik sırası ile):
    // 1. RAS hit ise -> RAS'tan gelen adres
    // 2. JAL ise -> PC + immediate
    // 3. Branch ve PHT[1]=1 ise -> BTB'den gelen hedef
    // 4. Hiçbiri değilse -> Sequential (PC+4)
    if (popped.valid) begin
      spec_o.pc = popped.data;
    end else if (j_type) begin
      spec_o.pc = pc_i + imm;
    end else if ((pht[pht_rd_idx][1] && b_type)) begin
      spec_o.pc = branch.pc;
    end else begin
      spec_o.pc = pushed_addr;
    end

    // Taken sinyali: jump, predicted branch veya RAS hit
    // PROGRAM_LIMIT kontrolü gereksiz enerji tüketir
    // Sanırım sadece branch tipi için speculation üretiyoruz, ama ras overflow falan oldu ise oda yanlış olabiliyor o yüzden spec demek mantıklı gibi

    spec_o.taken = (j_type || branch.taken || (popped.valid && popped.data != 0)) && (spec_o.pc < PROGRAM_LIMIT);
    spec_o.spectype = NO_SPEC;

    if (spec_o.taken) begin
      if (popped.valid) begin
        spec_o.spectype = RAS;
      end else if (j_type) begin
        spec_o.spectype = JUMP;
      end else if ((pht[pht_rd_idx][1] && b_type)) begin
        spec_o.spectype = BRANCH;
      end else begin
        spec_o.spectype = NO_SPEC;
      end
    end
    // RAS'a istek gönder (JAL/JALR için)
    req_valid = spec_miss ? 1'b0 : !stall_i && fetch_valid_i && (j_type || jr_type);
  end

  // ============================================================================
  // RETURN ADDRESS STACK (RAS) MODÜLÜ
  // ============================================================================
  // Function call/return tracking için stack yapısı
  // rd=x1/x5 ise push, rs1=x1/x5 ise pop mantığı
  ras #(
      .RAS_SIZE(RAS_SIZE)
  ) ras (
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),
      .restore_i    (restore),         // Misprediction'da RAS'ı restore et
      .req_valid_i  (req_valid),
      .rd_addr_i    (inst_i.rd_addr),  // Destination register
      .r1_addr_i    (inst_i.r1_addr),  // Source register
      .j_type_i     (j_type),
      .jr_type_i    (jr_type),
      .return_addr_i(pushed_addr),
      .popped_o     (popped)
  );
  // ============================================================================
  // INDEX HESAPLAMA VE LOOKUP LOGIC
  // ============================================================================
  always_comb begin
    // RAS restore: Stage 0'daki PC'ye geri dön
    restore.data = de_info_i.pc;
    restore.valid = !stall_i && !spec_hit_i && de_info_i.spec.spectype == RAS;


    // GSHARE INDEX: PC ⊕ GHR (global history ile correlation)
    pht_rd_idx = pc_i[$clog2(PHT_SIZE):1] ^ ghr[$clog2(PHT_SIZE)-1:0];
    btb_rd_idx = pc_i[$clog2(BTB_SIZE):1];  // BTB: sadece PC indexing

    // Update için index'ler (1 cycle gecikmiş PC ile)
    pht_wr_idx = ex_info_i.pc[$clog2(PHT_SIZE):1] ^ ghr[$clog2(PHT_SIZE)-1:0];
    btb_wr_idx = ex_info_i.pc[$clog2(BTB_SIZE):1];

    // EX aşamasında branch gerçekten alındı mı?
    // spec_hit_i=1 && ex_info_i.spec.taken=1 -> Doğru tahmin, taken
    // spec_hit_i=0 && ex_info_i.spec.taken=0 -> Misprediction vardı, ama aslında taken
    ex_taken = ex_info_i.spec.spectype == BRANCH && ((spec_hit_i && ex_info_i.spec.taken && ex_info_i.spec.spectype != RAS) || (!spec_hit_i && !(ex_info_i.spec.taken && ex_info_i.spec.spectype != RAS)));

    // BTB lookup: Tag match ve PHT MSB kontrolü
    // SORUN: Valid bit yok, initialization sonrası false positive olabilir
    branch.pc = btb_target[btb_rd_idx];
    branch.taken = (btb_pc[btb_rd_idx] == pc_i[31:$clog2(PHT_SIZE)+1]) && (pht[pht_rd_idx][1]);
  end

  // ============================================================================
  // PIPELINE REGISTER UPDATE
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      pht_bit1 <= '{default: 0};
    end else if (!stall_i) begin
      if (!spec_hit_i) begin
        // MİSPREDICTION: Pipeline flush
        pht_bit1 <= '{default: 0};
      end else begin
        // Normal pipeline advance



        pht_bit1[1] <= pht_bit1[0];
        pht_bit1[0] <= popped.valid ? pht_bit1[0] : pht[pht_wr_idx][1];

      end
    end
  end

  // ============================================================================
  // PHT, BTB ve GHR UPDATE LOGİC
  // ============================================================================
  always @(posedge clk_i) begin
    if (!rst_ni) begin
      ghr        <= '0;
      btb_target <= '{default: 0};
      btb_pc     <= '{default: 0};
      pht        <= '{default: 2'b01};  // Weakly Not Taken (alternatif: 2'b10)
      pht_ptr    <= '0;
    end else begin
      // Branch EX aşamasında çözüldüğünde update
      if (spec_o.spectype == BRANCH && !stall_i) begin

        // PHT UPDATE: 2-bit saturating counter
        if (ex_taken) begin
          if (pht[pht_wr_idx] < 2'b11) pht[pht_wr_idx] <= pht[pht_wr_idx] + 1;  // Increment (max 11)
        end else begin
          if (pht[pht_wr_idx] > 2'b00) pht[pht_wr_idx] <= pht[pht_wr_idx] + 1;  // Decrement (min 00)
        end

        // BTB UPDATE: Sadece taken branch'leri cache'le
        btb_target[btb_wr_idx] <= ex_taken ? pc_target_i : '0;
        btb_pc[btb_wr_idx]     <= ex_taken ? ex_info_i.pc[31:$clog2(PHT_SIZE)+1] : '0;

        pht_ptr                <= ex_taken ? pht_ptr + 1 : 0;

        // GHR UPDATE:
        // Taken ise: Sol shift ve yeni bit ekle
        // `pht_ptr >>> ghr` işlemi mantıksız - eski GHR değerini nasıl restore eder?
        // Çözüm: Checkpoint buffer kullanarak eski GHR'leri saklamalısınız
        ghr                    <= ex_taken ? {ghr[GHR_SIZE-2:0], pht_bit1[1] & spec_hit_i} : pht_ptr >>> ghr;
      end
    end
  end

endmodule

// ============================================================================
// ÖNERİLEN İYİLEŞTİRMELER:
// ============================================================================
// 1. Pipeline depth'i 5'e çıkarın (stage_pc[4:0], branch_q[4:0], vb.)
// 2. BTB'ye valid bit ekleyin
// 3. GHR için checkpoint buffer implementasyonu yapın (her branch için eski GHR'yi sakla)
// 4. BTB'yi 2-way set-associative yapın (LRU replacement ile)
// 5. PHT initialization'ı 2'b10 olarak değiştirmeyi deneyin
// 6. pht_ptr değişkenini kaldırın veya amacını netleştirin
// 7. PROGRAM_LIMIT kontrolünü kaldırın (gereksiz güç tüketimi)
// 8. BTB tag boyutunu artırın (alias problemini azaltır)
//
// ÖRNEK GHR CHECKPOINT YAPISI:
// logic [GHR_SIZE-1:0] ghr_checkpoint [PIPELINE_DEPTH];
// logic [$clog2(PIPELINE_DEPTH)-1:0] ghr_head;
// 
// // Branch fetch olduğunda checkpoint al:
// ghr_checkpoint[ghr_head] <= ghr;
// ghr_head <= ghr_head + 1;
//
// // Misprediction'da restore et:
// ghr <= ghr_checkpoint[correct_checkpoint_index];
// ============================================================================
