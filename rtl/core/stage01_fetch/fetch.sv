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
    parameter RESET_VECTOR = ceres_param::RESET_VECTOR
) (
`ifdef COMMIT_TRACER
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
    input  logic                       misa_c_i,       // C extension enabled
    input  logic            [XLEN-1:0] tdata1_i,       // Trigger data 1 (config)
    input  logic            [XLEN-1:0] tdata2_i,       // Trigger data 2 (breakpoint addr)
    input  logic            [XLEN-1:0] tcontrol_i,     // Trigger control (mte bit[3] enables triggers)
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
  logic                   fetch_valid_reg;  // Registered fetch_valid for gshare_bp
  logic                   uncached;
  logic                   uncached_next;
  /* verilator lint_off UNUSEDSIGNAL */
  logic                   memregion;
  logic                   memregion_next;
  /* verilator lint_on UNUSEDSIGNAL */
  logic                   grand;
  logic                   grand_next;
  logic                   illegal_instr;
  logic                   is_comp;
  abuff_res_t             buff_res;
  abuff_req_t             buff_req;
  icache_res_t            icache_res;
  icache_req_t            abuff_icache_req;  // Raw request from align_buffer
  icache_req_t            icache_req;  // Gated request to cache
  blowX_res_t             buff_lowX_res;
  logic                   buf_lookup_ack;

  // Exception priority detection signals
  logic                   has_debug_breakpoint;
  logic                   has_instr_misaligned;
  logic                   has_instr_access_fault;
  logic                   has_illegal_instr;
  logic                   has_ebreak;
  logic                   has_ecall;

  // ============================================================================
  // PC Register: Program Counter yönetimi
  // Reset'te RESET_VECTOR'e atanır, aksi halde pc_en aktifken güncellenir
  // PMA attributes are registered together with PC to break combinational loop
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      pc              <= RESET_VECTOR;
      uncached        <= 1'b0;        // Reset vector is cached
      grand           <= 1'b1;        // Reset vector is executable
      memregion       <= 1'b1;        // Reset vector is valid memory
      fetch_valid_reg <= 1'b0;        // No valid fetch at reset
    end else if (pc_en) begin
      pc              <= pc_next;
      uncached        <= uncached_next;
      grand           <= grand_next;
      memregion       <= memregion_next;
      fetch_valid_reg <= fetch_valid;  // Register fetch_valid to break comb loop
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
    instr_type_o           = resolved_instr_type(inst_o);

    // ============================================================================
    // Buffer Request Formation: Align buffer'a gönderilecek istek oluşturulur
    // ============================================================================
    buff_req               = '{valid    : fetch_valid, ready    : !flush_i && rst_ni,  // Sadece PC güncellenebiliyorsa ready
 addr     : pc_o, uncached : uncached};

    // ============================================================================
    // Instruction Cache Miss Stall: Fetch geçerli ama buffer hazır değilse stall
    // Klasik ready valid handshake'i kurulamadı. Buffer isteği registerlamıyor
    // Valid cevabı valid istekle aynı cycle da üretildiği için.
    // TODO: Belki handshake kurulabilir, olası çoğu comp loop sebebi burası
    // ============================================================================
    imiss_stall_o          = (buff_req.valid && !buff_res.valid);

    // ============================================================================
    // Exception Type Detection: Parametric priority-based exception selection
    // Follows RISC-V Privileged Specification Section 3.1.15
    // Priority can be configured via parameters in ceres_param.sv
    // 
    // Exception detection with parametric priority:
    // 1. Hardware breakpoint (debug trigger) - highest priority
    // 2. Instruction address misaligned
    // 3. Instruction access fault
    // 4. Illegal instruction
    // 5. EBREAK/C.EBREAK instruction
    // 6. ECALL instruction - lowest priority
    // ============================================================================

    // Detect all exceptions present
    // Breakpoint trigger requires: mte bit enabled (tcontrol[3]) + execute bit (tdata1[2]) + address match
    has_debug_breakpoint   = fetch_valid && tcontrol_i[3] && tdata1_i[2] && (pc_o == tdata2_i);
    has_instr_misaligned   = fetch_valid && (misa_c_i ? pc_o[0] : (pc_o[1:0] != 2'b00));
    has_instr_access_fault = fetch_valid && !grand;
    has_illegal_instr      = fetch_valid && illegal_instr && buff_res.valid;
    has_ebreak             = fetch_valid && (instr_type_o == ebreak);
    has_ecall              = fetch_valid && (instr_type_o == ecall);

    // Parametric priority-based selection
    // Check in order of priority and take first one that's enabled and present
    exc_type_o             = NO_EXCEPTION;

    if (has_debug_breakpoint && check_exc_priority(EXC_PRIORITY_DEBUG_BREAKPOINT, PRIORITY_7)) begin
      exc_type_o = BREAKPOINT;
    end else if (has_instr_misaligned && check_exc_priority(EXC_PRIORITY_INSTR_MISALIGNED, PRIORITY_7)) begin
      exc_type_o = INSTR_MISALIGNED;
    end else if (has_instr_access_fault && check_exc_priority(EXC_PRIORITY_INSTR_ACCESS_FAULT, PRIORITY_7)) begin
      exc_type_o = INSTR_ACCESS_FAULT;
    end else if (has_illegal_instr && check_exc_priority(EXC_PRIORITY_ILLEGAL, PRIORITY_7)) begin
      exc_type_o = ILLEGAL_INSTRUCTION;
    end else if (has_ebreak && check_exc_priority(EXC_PRIORITY_EBREAK, PRIORITY_7)) begin
      exc_type_o = EBREAK;
    end else if (has_ecall && check_exc_priority(EXC_PRIORITY_ECALL, PRIORITY_7)) begin
      exc_type_o = ECALL;
    end else begin
      exc_type_o = NO_EXCEPTION;
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
  // PMA lookup is done for pc_next (combinational), but result is registered
  // together with PC to break combinational loop while maintaining zero-cycle latency
  // ============================================================================
  pma i_pma (
      .addr_i     (pc_next),
      .uncached_o (uncached_next),
      .memregion_o(memregion_next),
      .grand_o    (grand_next)
  );

  // ============================================================================
  // Branch Prediction Unit: Dallanma tahminlerini yapar (GShare algoritması)
  // ============================================================================
  gshare_bp i_gshare_bp (
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),
      .spec_hit_i   (spec_hit_i),
      .pc_target_i  (pc_target_i),
      .inst_i       (inst_o),
      .stall_i      (!pc_en),
      .pc_i         (pc_o),
      .pc_incr_i    (pc_incr_o),
      .fetch_valid_i(fetch_valid_reg),  // Use registered fetch_valid to break comb loop
      .spec_o       (spec_o),
      .de_info_i    (de_info_i),
      .ex_info_i    (ex_info_i)
  );

  // ============================================================================
  // Align Buffer: Misaligned instruction'ları hizalar ve compressed
  // instruction desteği sağlar
  // ============================================================================
  align_buffer i_align_buffer (
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
  logic icache_fencei_stall;  // Not used for icache, always 0

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
  ) i_icache (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .flush_i       (flush_i),
      .cache_req_i   (icache_req),
      .cache_res_o   (icache_res),
      .lowX_res_i    (lx_ires_i),
      .lowX_req_o    (lx_ireq_o),
      .fencei_stall_o(icache_fencei_stall)  // Always 0 for icache
  );

  // ============================================================================
  // RISC-V Compressed Decoder: 16-bit compressed instruction'ları 32-bit
  // formata çevirir ve illegal instruction tespiti yapar
  // ============================================================================
  compressed_decoder i_compressed_decoder (
      .instr_i        (buff_res.blk),
      .instr_o        (inst_o),
      .is_compressed_o(is_comp),
      .illegal_instr_o(illegal_instr)
  );

`ifdef COMMIT_TRACER
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
