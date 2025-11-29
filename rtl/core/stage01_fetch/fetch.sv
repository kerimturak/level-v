/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"
/* verilator lint_off VARHIDDEN */
module fetch
  import ceres_param::*;
#(
    parameter RESET_VECTOR = 32'h8000_0000
) (
`ifdef TRACER_EN
    output fe_tracer_info_t            fe_tracer_o,
`endif
    input  logic                       clk_i,
    input  logic                       rst_ni,
    input  stall_e                     stall_i,
    input  logic                       flush_i,
    input  logic            [XLEN-1:0] flush_pc_i,
    input  ilowX_res_t                 lx_ires_i,
    input  logic            [XLEN-1:0] pc_target_i,
    input  logic            [XLEN-1:0] ex_mtvec_i,
    input  logic                       trap_active_i,
    input  logic                       spec_hit_i,
    output predict_info_t              spec_o,
    output ilowX_req_t                 lx_ireq_o,
    output logic            [XLEN-1:0] pc_o,
    output logic            [XLEN-1:0] pc_incr_o,
    output logic            [XLEN-1:0] inst_o,
    output logic                       imiss_stall_o,
    output exc_type_e                  exc_type_o,
    input  pipe_info_t                 de_info_i,
    input  pipe_info_t                 ex_info_i,
    output instr_type_e                instr_type_o
);

  // Internal signals
  logic        [XLEN-1:0] pc;
  logic        [XLEN-1:0] pc_next;
  logic                   pc_en;
  logic                   fetch_valid;
  logic                   uncached;
  /* verilator lint_off UNUSEDSIGNAL */
  logic                   memregion;
  /* verilator lint_on UNUSEDSIGNAL */
  logic                   grand;
  logic                   illegal_instr;
  logic                   is_comp;
  abuff_res_t             buff_res;
  abuff_req_t             buff_req;
  icache_res_t            icache_res;
  icache_req_t            abuff_icache_req;  // Raw request from align_buffer
  icache_req_t            icache_req;  // Gated request to cache
  blowX_res_t             buff_lowX_res;
  logic                   buf_lookup_ack;

  // ============================================================================
  // PC Register: Program Counter yönetimi
  // Reset'te RESET_VECTOR'e atanır, aksi halde pc_en aktifken güncellenir
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      pc <= RESET_VECTOR;
    end else if (pc_en) begin
      pc <= pc_next;
    end
  end

  // ============================================================================
  // PC Enable Logic: Stall durumunda PC güncellenmez
  // ============================================================================
  always_comb begin
    pc_en = trap_active_i || (stall_i == NO_STALL) || flush_i;

    // ============================================================================
    // Current PC Selection: Exception durumunda writeback PC'si, normal durumda
    // pipeline PC'si kullanılır
    // ============================================================================
    pc_o = pc;

    // ============================================================================
    // PC Increment Calculation: Compressed instruction ise +2, değilse +4
    // ============================================================================
    pc_incr_o = (buff_res.valid && is_comp) ? (pc_o + 32'd2) : (pc_o + 32'd4);

    // ============================================================================
    // Next PC Logic: Dallanma tahminleri ve exception durumlarına göre
    // bir sonraki PC değerinin belirlenmesi
    // Öncelik sırası:
    // 1. Misprediction/Exception recovery -> pc_target_i
    // 2. Branch taken -> spec_o.pc
    // 3. Sequential fetch -> pc_incr_o
    // ============================================================================
    if (flush_i) begin
      pc_next = flush_pc_i;
    end else if (trap_active_i) begin
      pc_next = ex_mtvec_i;
    end else if (!spec_hit_i) begin
      // Misprediction veya exception recovery durumu
      pc_next = pc_target_i;
    end else if (spec_o.taken) begin
      // Branch prediction taken durumu
      pc_next = spec_o.pc;
    end else begin
      // Sequential instruction fetch
      pc_next = pc_incr_o;
    end

    // ============================================================================
    // Fetch Valid Logic: Instruction fetch'in geçerli olup olmadığını belirler
    // Flush durumunda veya exception varsa fetch geçersiz kabul edilir
    // speculation hit ise normal exp kontrolü yapılır değilse zaten fetch ve decode
    // exptionları anlamsız olur ve flsuhlanacaklardır. Fakat yaşlı exceptionlar uygulanmalı
    // ============================================================================
    if (flush_i) begin
      fetch_valid = 1'b0;
    end else if (spec_hit_i) begin
      // Speculation hit durumunda hiç exception olmamalı
      fetch_valid = !trap_active_i;  //!has_any_exc;
    end else begin
      // Speculation miss durumunda sadece execute exception kontrolü
      // Exception WB de is trap handler için fetch yapılır
      fetch_valid = !trap_active_i  /*!(has_exe_exc || has_mem_exc)*/;
    end

    // ============================================================================
    // Instruction Type Detection: Gelen instruction'ın tipini belirler
    // ============================================================================
    instr_type_o  = resolved_instr_type(inst_o);

    // ============================================================================
    // Buffer Request Formation: Align buffer'a gönderilecek istek oluşturulur
    // ============================================================================
    buff_req      = '{valid    : fetch_valid, ready    : !flush_i && rst_ni,  // Sadece PC güncellenebiliyorsa ready
 addr     : pc_o, uncached : uncached};

    // ============================================================================
    // Instruction Cache Miss Stall: Fetch geçerli ama buffer hazır değilse stall
    // Klasik ready valid handshake'i kurulamadı. Buffer isteği registerlamıyor
    // Valid cevabı valid istekle aynı cycle da üretildiği için.
    // TODO: Belki handshake kurulabilir, olası çoğu comp loop sebebi burası
    // ============================================================================
    imiss_stall_o = (buff_req.valid && !buff_res.valid);

    // ============================================================================
    // Exception Type Detection: Öncelik sırasına göre exception tipini belirler
    // Öncelik: ACCESS_FAULT > ILLEGAL_INSTR > EBREAK > ECALL
    // ============================================================================
    exc_type_o    = NO_EXCEPTION;

    if (!fetch_valid) begin
      exc_type_o = NO_EXCEPTION;

    end else if (pc_o[0]) begin
      // 1) Highest priority: instruction address misaligned
      exc_type_o = INSTR_MISALIGNED;

    end else if (!grand) begin
      // 2) Access fault (PMA)
      exc_type_o = INSTR_ACCESS_FAULT;

    end else if (illegal_instr && buff_res.valid) begin
      // 3) Illegal instruction
      exc_type_o = ILLEGAL_INSTRUCTION;

    end else begin
      // 4) Other synchronous exceptions
      case (instr_type_o)
        ebreak:  exc_type_o = EBREAK;
        ecall:   exc_type_o = ECALL;
        default: exc_type_o = NO_EXCEPTION;
      endcase
    end

    // ============================================================================
    // Cache Response to Buffer Response Mapping: Cache cevabını buffer formatına
    // dönüştürür
    // ============================================================================
    buff_lowX_res.valid = icache_res.valid;
    buff_lowX_res.ready = icache_res.ready;
    buff_lowX_res.blk   = icache_res.blk;

    // ============================================================================
    // Buffer to Cache Request Gating
    // ============================================================================
    // align_buffer outputs a continuous valid signal during miss.
    // We gate it with buf_lookup_ack to create a one-cycle handshake:
    //   - buf_lookup_ack=0: Allow request through
    //   - buf_lookup_ack=1: Request already sent, suppress until response
    icache_req.valid    = abuff_icache_req.valid && !buf_lookup_ack;
    icache_req.ready    = abuff_icache_req.ready;
    icache_req.addr     = abuff_icache_req.addr;
    icache_req.uncached = abuff_icache_req.uncached;
  end

  // Track pending request to icache - reset on response or new request from buffer
  /* verilator lint_off UNUSEDSIGNAL */
  logic prev_icache_req_valid;
  /* verilator lint_on UNUSEDSIGNAL */

  always_ff @(posedge clk_i) begin
    if (!rst_ni || flush_i) begin
      buf_lookup_ack <= 1'b0;
      prev_icache_req_valid <= 1'b0;
    end else begin
      prev_icache_req_valid <= icache_req.valid;

      if (buff_lowX_res.valid) begin
        // Response received - clear ack to allow next request
        buf_lookup_ack <= 1'b0;
      end else if (buff_res.waiting_second && buf_lookup_ack) begin
        // Double miss: align_buffer needs second request, clear ack
        buf_lookup_ack <= 1'b0;
      end else if (icache_req.valid && buff_lowX_res.ready && !buf_lookup_ack) begin
        // Request accepted by cache - set ack
        buf_lookup_ack <= 1'b1;
      end
    end
  end

  // ============================================================================
  // Physical Memory Attributes (PMA) Module: Bellek bölgesinin özelliklerini
  // belirler (cached/uncached, erişim izni vb.)
  // ============================================================================
  pma ipma (
      .addr_i     (pc_o),
      .uncached_o (uncached),
      .memregion_o(memregion),  // TODO:Şu an kullanılmıyor
      .grand_o    (grand)
  );

  // ============================================================================
  // Branch Prediction Unit: Dallanma tahminlerini yapar (GShare algoritması)
  // ============================================================================
  gshare_bp branch_prediction (
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),
      .spec_hit_i   (spec_hit_i),
      .pc_target_i  (pc_target_i),
      .inst_i       (inst_o),
      .stall_i      (!pc_en),
      .pc_i         (pc_o),
      .pc_incr_i    (pc_incr_o),
      .fetch_valid_i(buff_res.valid),
      .spec_o       (spec_o),
      .de_info_i    (de_info_i),
      .ex_info_i    (ex_info_i)
  );

  // ============================================================================
  // Align Buffer: Misaligned instruction'ları hizalar ve compressed
  // instruction desteği sağlar
  // ============================================================================
  align_buffer align_buffer (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .flush_i   (flush_i),
      .buff_req_i(buff_req),
      .buff_res_o(buff_res),
      .lowX_res_i(buff_lowX_res),
      .lowX_req_o(abuff_icache_req)  // Raw request, gated in always_comb
  );

  // ============================================================================
  // Instruction Cache: Instruction'ları cache'ler, cache miss durumunda
  // lower level memory'ye istek gönderir
  // ============================================================================
  cache #(
      .IS_ICACHE  (1),
      .cache_req_t(icache_req_t),
      .cache_res_t(icache_res_t),
      .lowX_req_t (ilowX_req_t),
      .lowX_res_t (ilowX_res_t),
      .CACHE_SIZE (IC_CAPACITY),
      .BLK_SIZE   (BLK_SIZE),
      .XLEN       (XLEN),
      .NUM_WAY    (IC_WAY)
  ) icache (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .flush_i    (flush_i),
      .cache_req_i(icache_req),
      .cache_res_o(icache_res),
      .lowX_res_i (lx_ires_i),
      .lowX_req_o (lx_ireq_o)
  );

  // ============================================================================
  // RISC-V Compressed Decoder: 16-bit compressed instruction'ları 32-bit
  // formata çevirir ve illegal instruction tespiti yapar
  // ============================================================================
  compressed_decoder compressed_decoder (
      .instr_i        (buff_res.blk),
      .instr_o        (inst_o),
      .is_compressed_o(is_comp),
      .illegal_instr_o(illegal_instr)
  );

`ifdef FETCH_LOGGER
  // Simple fetch-stage logger to aid cross-simulator comparison (ModelSim vs Verilator)
  // Enable with +define+FETCH_LOGGER and optionally set path with +fetch_log=/path/to/log
  string  fetch_trace_path;
  integer fetch_fd;
  string  simulator;
  string  test_name;

  initial begin
    // Try to get an explicit path from plusargs
    if (!$value$plusargs("fetch_log=%s", fetch_trace_path)) begin
      // Fallback to results/logs/<sim>/<test>/fetch_trace.log using plusargs if provided
      if (!$value$plusargs("simulator=%s", simulator)) simulator = "sim";
      if (!$value$plusargs("test_name=%s", test_name)) test_name = "unknown_test";
      fetch_trace_path = $sformatf("results/logs/%0s/%0s/fetch_trace.log", simulator, test_name);
    end

    // Ensure directory exists (system call) and open file
    void'($system($sformatf("mkdir -p %s", $sformatf("results/logs/%0s/%0s", simulator, test_name))));
    fetch_fd = $fopen(fetch_trace_path, "w");
    if (fetch_fd == 0) begin
      $display("[FETCH_LOGGER] Failed to open fetch log: %s", fetch_trace_path);
    end else begin
      $display("[FETCH_LOGGER] Logging fetches to %s", fetch_trace_path);
      $fwrite(fetch_fd, "#time,pc,raw_inst,is_compressed\n");
    end
  end

  // Log when buffer response is valid (an instruction is delivered to pipeline)
  always_ff @(posedge clk_i) begin
    if (fetch_fd != 0 && buff_res.valid) begin
      $fwrite(fetch_fd, "%0t,0x%08h,0x%08h,%0d\n", $time, pc_o, buff_res.blk, is_comp);
    end
  end

  final begin
    if (fetch_fd != 0) $fclose(fetch_fd);
  end
`endif

`ifdef TRACER_EN
  always_comb begin
    fe_tracer_o.inst = '0;
    if ((stall_i == NO_STALL) && buff_res.valid) begin
      if ((buff_res.valid && is_comp)) begin
        fe_tracer_o.inst = {16'b0, buff_res.blk[15:0]};
      end else begin
        fe_tracer_o.inst = buff_res.blk;
      end
    end
  end
`endif

endmodule
