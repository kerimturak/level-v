/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "level_defines.svh"
module cpu
  import level_param::*;
(
    input  logic       clk_i,
    input  logic       rst_ni,
    // Hardware interrupt inputs
    input  logic       timer_irq_i,    // CLINT timer interrupt (MTIP)
    input  logic       sw_irq_i,       // CLINT software interrupt (MSIP)
    input  logic       ext_irq_i,      // PLIC external interrupt (MEIP)
    output iomem_req_t iomem_req_o,
    input  iomem_res_t iomem_res_i
);

  stall_e                   stall_cause;
  ilowX_req_t               lx_ireq;
  dlowX_res_t               lx_dres;
  dlowX_req_t               lx_dreq;

  // ============================================================================
  // fetch logic:
  // ============================================================================
  logic                     fe_stall;
  ilowX_res_t               fe_lx_ires;
  logic                     fe_imiss_stall;
  logic          [XLEN-1:0] fe_pc /*verilator split_var*/;
  logic          [XLEN-1:0] fe_pc_incr;
  logic          [XLEN-1:0] fe_inst /*verilator split_var*/;
  predict_info_t            fe_spec;
  exc_type_e                fe_exc_type;
  exc_type_e                fe_active_exc_type;
  instr_type_e              fe_instr_type;
  logic                     fencei_flush;
  logic                     fencei_was_stalled_q;  // one-shot: tracks D-cache stall seen
  logic         [XLEN-1:0]  flush_pc;
`ifdef COMMIT_TRACER
  fe_tracer_info_t fe_tracer;
`endif
  logic                  fe_trap_active;

  // ============================================================================
  // decode logic:
  // ============================================================================
  pipe1_t                pipe1;
  ctrl_t                 de_ctrl;
  logic                  de_enable;
  logic                  de_stall;
  logic                  de_flush;
  logic                  de_flush_en;
  logic       [XLEN-1:0] de_r1_data;
  logic       [XLEN-1:0] de_r2_data;
  logic                  de_fwd_a;
  logic                  de_fwd_b;
  logic       [XLEN-1:0] de_imm;
  exc_type_e             de_exc_type;
  pipe_info_t            de_info;
  exc_type_e             de_active_exc_type;

  // Decode-stage early branch resolution
  logic                  de_branch_taken;
  logic       [XLEN-1:0] de_branch_target;
  logic       [XLEN-1:0] de_redirect_target;
  logic                  de_can_resolve;
  logic                  de_early_spec_hit;
  logic                  de_early_miss;
  logic                  de_early_flush;

  // ============================================================================
  // execute logic:
  // ============================================================================
  pipe2_t                pipe2;
  logic                  ex_flush;
  logic                  ex_flush_en;
  logic       [     1:0] ex_fwd_a;
  logic       [     1:0] ex_fwd_b;
  logic       [XLEN-1:0] ex_alu_result;
  logic       [XLEN-1:0] ex_pc_target;
  logic       [XLEN-1:0] ex_pc_target_last;
  // Correct redirect target: taken→branch target, not-taken→fall-through
  assign ex_pc_target_last = ex_pc_sel ? ex_pc_target : pipe2.pc_incr;
  logic       [XLEN-1:0] ex_wdata;
  logic                  ex_pc_sel;
  logic                  ex_alu_stall;
  logic                  ex_spec_hit;       // Effective: suppresses EX flush for DE-resolved branches
  logic                  ex_actual_spec_hit; // Actual prediction accuracy (for GShare)
  exc_type_e             ex_exc_type;
  exc_type_e             ex_alu_exc_type;
  logic                  ex_rd_csr;
  logic                  ex_wr_csr;
  logic       [XLEN-1:0] ex_mtvec;
  logic                  ex_misa_c;
  logic       [XLEN-1:0] ex_tdata1[0:1];
  logic       [XLEN-1:0] ex_tdata2[0:1];
  logic       [XLEN-1:0] ex_tcontrol;
  //logic       [XLEN-1:0] ex_mepc;
  pipe_info_t            ex_info;
  logic                  ex_valid_csr;
  logic       [XLEN-1:0] ex_trap_cause;
  logic       [XLEN-1:0] ex_trap_mepc;
    `ifdef COMMIT_TRACER
  logic                  ex_csr_write_valid;  // CSR write was accepted (not rejected)
  logic       [XLEN-1:0] ex_csr_wr_data;
    `endif
  data_req_t ex_data_req;
  logic                  de_trap_active;

  // ============================================================================
  // memory logic:
  // ============================================================================
  pipe3_t                pipe3;
  logic                  me_dmiss_stall;
  logic                  me_fencei_stall;  // Dcache dirty writeback stall for fence.i
  logic       [XLEN-1:0] me_rdata;
  data_req_t me_data_req;

  // ============================================================================
  // writeback logic:
  // ============================================================================
  pipe4_t                pipe4;
  logic                  wb_rf_rw;
  //logic       [XLEN-1:0] wb_pc;
  logic       [XLEN-1:0] wb_data;


  // ============================================================================
  // general logic:
  // ============================================================================
  logic       [     3:0] excp_mask;
  logic       [1:0]      priority_flush;
  logic                  trap_active;
  logic       [XLEN-1:0] trap_tval;
  logic                  pipe_downstream_stall;
  logic                  pipe2_frozen;
  // MEM→EX bypass data must match writeback mux (not raw alu_result for loads/JAL)
  logic       [XLEN-1:0] ex_mem_bypass_data;

  always_comb begin
    unique case (pipe3.result_src)
      2'b01: ex_mem_bypass_data = pipe3.read_data;   // load → use mem read, not EA in alu_result
      2'b10: ex_mem_bypass_data = pipe3.pc_incr;     // JAL/JALR rd
      default: ex_mem_bypass_data = pipe3.alu_result;
    endcase
  end

  // ============================================================================
  // FETCH
  // ============================================================================

  // ============================================================================
  // FETCH Exception List
  // ----------------------------------------------------------------------------
  // INSTR_ACCESS_FAULT - if PMA does not grant access
  // ILLEGAL_INSTRUCTION - if the instruction is not supported
  // EBREAK - 
  // ECALL - 
  // ============================================================================

  fetch #(
      .RESET_VECTOR(RESET_VECTOR)
  ) i_fetch (
`ifdef COMMIT_TRACER
      .fe_tracer_o  (fe_tracer),
`endif
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),
      .flush_i      (fencei_flush),
      .flush_pc_i   (flush_pc),
      .stall_i      (stall_cause),
      .lx_ires_i    (fe_lx_ires),
      .pc_target_i  (ex_pc_target_last),
      .spec_hit_i   (ex_spec_hit),
      .actual_spec_hit_i(ex_actual_spec_hit),
      .de_redirect_i(de_early_flush),
      .de_redirect_target_i(de_redirect_target),
      .ex_mtvec_i   (ex_mtvec),
      .trap_active_i(fe_trap_active),
      .misa_c_i     (ex_misa_c),
      .tdata1_i     (ex_tdata1),
      .tdata2_i     (ex_tdata2),
      .tcontrol_i   (ex_tcontrol),
      .spec_o       (fe_spec),
      .lx_ireq_o    (lx_ireq),
      .pc_o         (fe_pc),
      .pc_incr_o    (fe_pc_incr),
      .inst_o       (fe_inst),
      .imiss_stall_o(fe_imiss_stall),
      .exc_type_o   (fe_exc_type),
      .instr_type_o (fe_instr_type),
      .de_info_i    (de_info),
      .ex_info_i    (ex_info)
  );

  // ============================================================================
  // DECODE
  // ============================================================================

  // ============================================================================
  // FETCH → DECODE Pipeline Register (pipe1)
  // ----------------------------------------------------------------------------
  // This always_ff block moves information from fetch to decode.
  // - pipe1 updates on each clock edge.
  // - On reset or flush, pipe1 is cleared (nop-like).
  // - When de_enable is asserted, new fetch data is loaded.
  // - When the tracer is enabled, trace info (fe_tracer) is carried as well.
  // - If ex_exc_type is set, decode and fetch must flush; the wrong path was fetched before the exception
  // ============================================================================
  //  Decode Exception List
  //  - ILLEGAL_INSTRUCTION
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni || de_flush_en || de_early_flush || |priority_flush || fencei_flush) begin
      pipe1 <= '{exc_type: NO_EXCEPTION, instr_type: instr_invalid, default: '0};
    end else if (de_enable) begin
      pipe1 <= '{
      `ifdef COMMIT_TRACER
        fe_tracer: fe_tracer,
        flushed: 1'b0,  // Normal instruction, not flushed
      `endif
        pc      : fe_pc, pc_incr : fe_pc_incr, inst : fe_inst, exc_type: fe_active_exc_type, instr_type : fe_instr_type, spec: fe_spec, misa_c: ex_misa_c};
    end
  end

  // ============================================================================
  //  DECODE control logic
  // ----------------------------------------------------------------------------
  // This always_comb block computes decode-stage control signals.
  // - fe_active_exc_type: fetch exception applies only on speculative hit; cleared on mispredict
  // - fencei_flush: I-cache flush when a fence.i is detected
  // - de_enable: decode enable (no stall and no flush required)
  // - de_flush_en: when flush is active, pipe1 is reset
  // - de_info: carries information to later stages (fetch–execute feedback)
  // If speculative prediction (branch prediction) fails,
  // this instruction does not raise an exception (NO_EXCEPTION).
  // On a speculative hit, the exception from fetch is preserved.
  // ============================================================================

  // One-shot fence.i flush: once D-cache writeback stall has risen and fallen,
  // the fence.i processing is complete.  Drop fencei_flush so the I-cache
  // flush can finish without being perpetually re-triggered.
  always_ff @(posedge clk_i) begin
    if (!rst_ni || pipe2.instr_type != fence_i)
      fencei_was_stalled_q <= 1'b0;
    else if (me_fencei_stall)
      fencei_was_stalled_q <= 1'b1;
  end

  always_comb begin
    fe_active_exc_type  = ex_spec_hit ? fe_exc_type : NO_EXCEPTION;
    de_active_exc_type  = ex_spec_hit ? pipe1.exc_type != NO_EXCEPTION ? pipe1.exc_type : de_exc_type : NO_EXCEPTION;
    // Flush on fence.i OR misa write (misa.C change affects instruction decoding)
    // One-shot: suppress when D-cache stall was seen and has now dropped
    fencei_flush        = ((pipe2.instr_type == fence_i) && !(fencei_was_stalled_q && !me_fencei_stall)) || 
                          (ex_wr_csr && pipe2.csr_idx == 12'h301);  // misa write
    flush_pc            = pipe2.pc_incr;
    de_enable           = (stall_cause == NO_STALL); // to synch spike and core log stall on fetch flush
    de_flush_en         = (stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL}) ? 1'b0 : de_flush; //(stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL}) && de_flush;
    de_info.spec        = pipe1.spec;
    de_info.bjtype      = is_branch(pipe1.instr_type);
    de_info.pc          = pipe1.pc;
    de_info.misa_c      = pipe1.misa_c;
  end

  decode i_decode (
      .clk_i       (clk_i),
      .rst_ni      (rst_ni),
      .fwd_a_i     (de_fwd_a),
      .fwd_b_i     (de_fwd_b),
      .wb_data_i   (wb_data),
      .inst_i      (pipe1.inst),
      .instr_type_i(pipe1.instr_type),
      .rd_addr_i   (pipe4.rd_addr),
      .rf_rw_en_i  (wb_rf_rw),
      .r1_data_o   (de_r1_data),
      .r2_data_o   (de_r2_data),
      .ctrl_o      (de_ctrl),
      .imm_o       (de_imm),
      .exc_type_o  (de_exc_type)
  );

  // ============================================================================
  // DECODE-STAGE EARLY BRANCH RESOLUTION
  // ----------------------------------------------------------------------------
  // Resolves branches 1 cycle earlier than EX to reduce misprediction penalty
  // from 2 cycles to 1 cycle.  When the branch has no data hazard with the
  // instruction in EX (pipe2), we can compare the prediction against the actual
  // outcome here in DE.  If a misprediction is detected, only the IF stage
  // (pipe1) is flushed — saving 1 bubble cycle.
  //
  // Data forwarding for the comparator:
  //   MEM→DE: from pipe3 (ex_mem_bypass_data)  — 1 stage ahead, result available
  //   WB→DE:  already handled by decode module (de_r1_data / de_r2_data)
  //   EX→DE:  NOT possible (ALU result not computed yet) — skip DE resolution
  // ============================================================================

  // --- MEM→DE forwarding for branch operands ---
  logic [XLEN-1:0] de_cmp_a, de_cmp_b;

  always_comb begin
    // MEM→DE forwarding takes priority over WB→DE (more recent)
    if (pipe3.rf_rw_en && pipe1.inst.r1_addr == pipe3.rd_addr && pipe1.inst.r1_addr != 0)
      de_cmp_a = ex_mem_bypass_data;
    else
      de_cmp_a = de_r1_data;  // includes WB→DE forwarding from decode module

    if (pipe3.rf_rw_en && pipe1.inst.r2_addr == pipe3.rd_addr && pipe1.inst.r2_addr != 0)
      de_cmp_b = ex_mem_bypass_data;
    else
      de_cmp_b = de_r2_data;
  end

  // --- EX→DE hazard detection (can't forward, skip DE resolution) ---
  wire de_is_cond_branch = de_ctrl.pc_sel inside {BEQ, BNE, BLT, BGE, BLTU, BGEU};
  wire de_is_jalr        = (de_ctrl.pc_sel == JALR);
  wire de_is_jal         = (de_ctrl.pc_sel == JAL);
  wire de_is_any_branch  = (de_ctrl.pc_sel != NO_BJ);

  // rs1 needed for: conditional branches and JALR (not JAL)
  wire de_needs_rs1 = de_is_any_branch && !de_is_jal;
  // rs2 needed for: conditional branches only
  wire de_needs_rs2 = de_is_cond_branch;

  wire de_rs1_ex_haz = de_needs_rs1 && pipe2.rf_rw_en &&
                       (pipe1.inst.r1_addr == pipe2.rd_addr) && (pipe1.inst.r1_addr != 0);
  wire de_rs2_ex_haz = de_needs_rs2 && pipe2.rf_rw_en &&
                       (pipe1.inst.r2_addr == pipe2.rd_addr) && (pipe1.inst.r2_addr != 0);
  wire de_branch_hazard = de_rs1_ex_haz || de_rs2_ex_haz;

  // --- Branch comparator ---
  always_comb begin
    de_branch_taken  = 1'b0;
    de_branch_target = pipe1.pc + de_imm;  // default: PC-relative (B-type, JAL)

    case (de_ctrl.pc_sel)
      BEQ:  de_branch_taken = (de_cmp_a == de_cmp_b);
      BNE:  de_branch_taken = (de_cmp_a != de_cmp_b);
      BLT:  de_branch_taken = ($signed(de_cmp_a) < $signed(de_cmp_b));
      BGE:  de_branch_taken = ($signed(de_cmp_a) >= $signed(de_cmp_b));
      BLTU: de_branch_taken = (de_cmp_a < de_cmp_b);
      BGEU: de_branch_taken = (de_cmp_a >= de_cmp_b);
      JAL:  de_branch_taken = 1'b1;
      JALR: begin
        de_branch_taken  = 1'b1;
        de_branch_target = (de_cmp_a + de_imm) & ~32'h1;
      end
      default: de_branch_taken = 1'b0;
    endcase
  end

  // --- Resolution gate: only resolve when no hazard and instruction is valid ---
  assign de_can_resolve = de_is_any_branch && !de_branch_hazard &&
                          (pipe1.instr_type != mret) &&
                          (pipe1.instr_type != instr_invalid) &&
                          (pipe1.exc_type == NO_EXCEPTION) &&
                          (de_exc_type == NO_EXCEPTION);

  // --- Compare with prediction ---
  always_comb begin
    if (de_branch_taken)
      de_early_spec_hit = pipe1.spec.taken && (de_branch_target == pipe1.spec.pc);
    else
      de_early_spec_hit = !pipe1.spec.taken;
  end

  // DE redirect target
  always_comb begin
    if (de_branch_taken)
      de_redirect_target = de_branch_target;
    else
      de_redirect_target = pipe1.pc_incr;
  end

  // Fire early miss only when: resolved, mispredicted, no stall, no higher-priority flush
  assign de_early_miss = de_can_resolve && !de_early_spec_hit && ex_spec_hit &&
                         !(|priority_flush) && !fencei_flush;
  assign de_early_flush = (stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL})
                          ? 1'b0 : de_early_miss;

  // ============================================================================
  // EXECUTE
  // ============================================================================

  // ============================================================================
  // DECODE → EXECUTE Pipeline Register (pipe2)
  // ----------------------------------------------------------------------------
  // This block moves the instruction decoded in decode into execute.
  // - pipe2 is cleared on reset or flush.
  // - It does not update if there is a fetch flush (e.g. fence.i) or a pipeline stall.
  // - Otherwise, control signals and operands from decode are passed to execute.
  // Exception handling:
  // If speculative branch prediction is wrong this instruction will be flushed,
  // so clear the exception. Otherwise carry the decode exception.
  // - If ex_exc_type is set, decode and fetch must flush; wrong path was fetched before the exception
  // - On fencei_flush we flush pipe1 (decode) but the fence.i in pipe2 must
  //   proceed to execute/memory/writeback and must not flush itself
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni || ex_flush_en || priority_flush == 3 || priority_flush == 2) begin
      pipe2 <= '{rw_size: NO_SIZE, instr_type: instr_invalid, alu_ctrl: OP_ADD, pc_sel: NO_BJ, default: '0};
    end else if (!(stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL})) begin
      pipe2 <= '{
        `ifdef COMMIT_TRACER
            fe_tracer   : pipe1.fe_tracer,
            // Propagate flushed flag from previous stage
            flushed     : pipe1.flushed,
        `endif
          pc           : pipe1.pc,
          pc_incr      : pipe1.pc_incr,
          rf_rw_en     : de_ctrl.rf_rw_en,
          wr_en        : de_ctrl.wr_en,
          rw_size      : de_ctrl.rw_size,
          result_src   : de_ctrl.result_src,
          alu_ctrl     : de_ctrl.alu_ctrl,
          pc_sel       : de_ctrl.pc_sel,
          alu_in1_sel  : de_ctrl.alu_in1_sel,
          alu_in2_sel  : de_ctrl.alu_in2_sel,
          ld_op_sign   : de_ctrl.ld_op_sign,
          rd_csr       : de_ctrl.rd_csr,
          wr_csr       : de_ctrl.wr_csr,
          csr_idx      : de_ctrl.csr_idx,
          csr_or_data  : de_ctrl.csr_or_data,
          dcache_valid : de_ctrl.dcache_valid,
          de_resolved  : de_can_resolve,
          de_taken     : de_branch_taken,
          de_target    : de_branch_target,
          r1_data      : de_r1_data,
          r2_data      : de_r2_data,
          r1_addr      : pipe1.inst.r1_addr,
          r2_addr      : pipe1.inst.r2_addr,
          rd_addr      : pipe1.inst.rd_addr,
          imm          : de_imm,
          instr_type   : pipe1.instr_type,
          spec         : pipe1.spec,
          misa_c       : pipe1.misa_c
      };
    end
  end

  // ============================================================================
  // EXECUTE control logic
  // ----------------------------------------------------------------------------
  // This section defines execute-stage exception and CSR behavior.
  // - ex_flush_en: when the execute flush signal is effective
  // - ex_exc_type: detects faults from ALU and memory accesses
  // - ex_rd_csr / ex_wr_csr: avoid CSR access colliding with stall
  // ============================================================================
  //  Execute Exception List
  //  - ALU- INSTR_MISALIGNED
  //  - STORE_MISALIGNED
  //  - LOAD_MISALIGNED
  // ============================================================================

  always_comb begin
    ex_flush_en = (stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL}) ? 1'b0 : ex_flush; // !(stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL}) &&  ex_flush;
    if (ex_alu_exc_type != NO_EXCEPTION) begin
      ex_exc_type = ex_alu_exc_type;
    end else if (pipe2.rw_size != NO_SIZE) begin
      if (pipe2.wr_en) begin
        unique case (pipe2.rw_size)
          HALF:   ex_exc_type = ex_alu_result[0] ? STORE_MISALIGNED : NO_EXCEPTION;
          WORD:   ex_exc_type = (ex_alu_result[1] | ex_alu_result[0]) ? STORE_MISALIGNED : NO_EXCEPTION;
          default: ex_exc_type = NO_EXCEPTION;
        endcase
      end else begin
        unique case (pipe2.rw_size)
          HALF:   ex_exc_type = ex_alu_result[0] ? LOAD_MISALIGNED : NO_EXCEPTION;
          WORD:   ex_exc_type = (ex_alu_result[1] | ex_alu_result[0]) ? LOAD_MISALIGNED : NO_EXCEPTION;
          default: ex_exc_type = NO_EXCEPTION;
        endcase
      end
    end else begin
      ex_exc_type = NO_EXCEPTION;
    end
    // NOTE: Removed stall_cause dependency from ex_rd_csr/ex_wr_csr to break
    // combinational loop: stall_cause → ex_rd_csr → csr_rdata → alu_result → 
    // ex_data_req.data → memory → dmiss_stall → stall_cause
    // The stall control is already handled inside cs_reg_file via stall_i input.
    ex_rd_csr = pipe2.rd_csr;
    ex_wr_csr = pipe2.wr_csr;
  end

  execution i_execution (
    `ifdef COMMIT_TRACER
      .csr_wr_data_o(ex_csr_wr_data),
      .csr_write_valid_o(ex_csr_write_valid),
    `endif
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),
      .stall_i      (stall_cause),
      .fwd_a_i      (ex_fwd_a),
      .fwd_b_i      (ex_fwd_b),
      .alu_result_i (ex_mem_bypass_data),
      .wb_data_i    (wb_data),
      .r1_data_i    (pipe2.r1_data),
      .r2_data_i    (pipe2.r2_data),
      .alu_in1_sel_i(pipe2.alu_in1_sel),
      .alu_in2_sel_i(pipe2.alu_in2_sel),
      .instr_type_i (pipe2.instr_type),
      .trap_active_i(trap_active), // mux: PC of the stage where the exception occurred must be selected
      .de_trap_active_i(de_trap_active), // mux: PC of the stage where the exception occurred must be selected
      .trap_tval_i  (trap_tval), // mux: PC of the stage where the exception occurred must be selected
      .trap_cause_i (ex_trap_cause ),
      .trap_mepc_i  (ex_trap_mepc  ),  // mux: PC of the stage where the exception occurred must be selected
      // Hardware interrupt inputs
      .timer_irq_i  (timer_irq_i),
      .sw_irq_i     (sw_irq_i),
      .ext_irq_i    (ext_irq_i),
      .rd_csr_i     (ex_rd_csr),
      .wr_csr_i     (ex_wr_csr),
      .csr_idx_i    (pipe2.csr_idx),
      .csr_or_data_i(pipe2.csr_or_data),
      .pc_i         (pipe2.pc),
      .pc_incr_i    (pipe2.pc_incr),
      .imm_i        (pipe2.imm),
      .pc_sel_i     (pipe2.pc_sel),
      .alu_ctrl_i   (pipe2.alu_ctrl),
      .misa_c_i     (pipe2.misa_c),
      .write_data_o (ex_wdata),
      .pc_target_o  (ex_pc_target),
      .alu_result_o (ex_alu_result),
      .pc_sel_o     (ex_pc_sel),
      .alu_stall_o  (ex_alu_stall),
      .exc_type_o   (ex_alu_exc_type),
      .mtvec_o      (ex_mtvec),
      .misa_c_o     (ex_misa_c),
      .tdata1_o     (ex_tdata1),
      .tdata2_o     (ex_tdata2),
      .tcontrol_o   (ex_tcontrol)
  );

  // ============================================================================
  // BRANCH PREDICTION VERIFICATION & PIPELINE FEEDBACK
  // ----------------------------------------------------------------------------
  // This block checks whether branch prediction (speculative execution) in execute
  // was correct and provides feedback to fetch.
  // It also fills ex_info so later stages can track exception / spec state.
  // ============================================================================

  always_comb begin
    // Actual prediction accuracy (always computed, used for GShare update)
    if (ex_pc_sel) ex_actual_spec_hit = pipe2.spec.taken && (ex_pc_target == pipe2.spec.pc);
    else ex_actual_spec_hit = !pipe2.spec.taken;

    // Effective spec_hit: when DE resolved, verify direction with EX.
    // DE and EX must agree on taken/not-taken. For conditional branches,
    // the target is always pc+imm so no target check needed.
    // For JALR, DE only resolves when no EX hazard, so forwarding matches.
    if (pipe2.de_resolved) begin
      ex_spec_hit = (ex_pc_sel == pipe2.de_taken);
    end else begin
      ex_spec_hit = ex_actual_spec_hit;
    end
    ex_info.spec     = pipe2.spec;
    ex_info.bjtype   = is_branch(pipe2.instr_type);
    ex_info.pc       = pipe2.pc;
    ex_info.misa_c   = pipe2.misa_c;

    ex_trap_cause   = ex_exc_type != NO_EXCEPTION ? trap_cause_decode(ex_exc_type) :
                      de_active_exc_type != NO_EXCEPTION ?  trap_cause_decode(de_active_exc_type) :
                      fe_active_exc_type != NO_EXCEPTION ? trap_cause_decode(fe_active_exc_type) : trap_cause_decode(ex_exc_type);
 
    ex_trap_mepc    = ex_exc_type != NO_EXCEPTION ? pipe2.pc :
                      de_active_exc_type != NO_EXCEPTION ?  pipe1.pc :
                      fe_active_exc_type != NO_EXCEPTION ? fe_pc : pipe2.pc;
  end

  // ============================================================================
  // MEMORY
  // ============================================================================

  // ============================================================================
  // CSR (Control and Status Register) Validation
  // ----------------------------------------------------------------------------
  // This block checks whether the CSR index (csr_idx) requested in execute
  // is supported by the core.
  // If it is a valid CSR address, ex_valid_csr = 1.
  // Writeback uses this to permit CSR writes.
  // ============================================================================
  always_comb begin // supported csrs
    ex_valid_csr = is_supported_csr(pipe2.csr_idx); 
  end

  
  always_ff @(posedge clk_i) begin
    if (!rst_ni || priority_flush == 3) begin
      `ifdef COMMIT_TRACER
      pipe3 <= '{instr_type:instr_invalid, rw_size: NO_SIZE, default: '0};
      `else
      pipe3 <= '0;
      `endif
    end else if (pipe_downstream_stall && !trap_active) begin
      // ME-stage stall (DMISS / ALU / FENCEI): freeze pipe3
    end else if (pipe2_frozen) begin
      // pipe2 is stalled but no downstream stall: drain pipe3→pipe4 with bubble
      `ifdef COMMIT_TRACER
      pipe3 <= '{instr_type:instr_invalid, rw_size: NO_SIZE, default: '0};
      `else
      pipe3 <= '0;
      `endif
    end else begin
      pipe3 <= '{
        `ifdef COMMIT_TRACER
          fe_tracer    : pipe2.fe_tracer,
          rd_en_csr    : ex_rd_csr,
          wr_en_csr    : ex_valid_csr & ex_wr_csr,
          csr_idx      : pipe2.csr_idx,
          instr_type   : pipe2.instr_type,
          csr_wr_data  : ex_csr_wr_data,
          csr_write_valid : ex_csr_write_valid,
          flushed      : (priority_flush == 3) ? 1'b1 : pipe2.flushed,
        `endif
          pc_incr      : pipe2.pc_incr,
          pc           : pipe2.pc,
          rf_rw_en     : pipe2.rf_rw_en,
          wr_en        : pipe2.wr_en,
          rw_size      : pipe2.rw_size,
          result_src   : pipe2.result_src,
          ld_op_sign   : pipe2.ld_op_sign,
          rd_addr      : pipe2.rd_addr,
          alu_result   : ex_alu_result,
          write_data   : ex_wdata,
          dcache_valid : pipe2.dcache_valid,
          read_data   : me_rdata
      };
    end
  end

  always_comb begin
    // Disable memory request on exception to prevent spurious memory access
    ex_data_req.valid      = pipe2.dcache_valid && (ex_exc_type == NO_EXCEPTION);
    ex_data_req.addr       = ex_alu_result;
    ex_data_req.rw         = pipe2.wr_en;
    ex_data_req.rw_size    = pipe2.rw_size;
    ex_data_req.data       = ex_wdata;
    ex_data_req.ld_op_sign = pipe2.ld_op_sign;
    me_data_req.valid      = pipe3.dcache_valid;
    me_data_req.addr       = pipe3.alu_result;
    me_data_req.rw         = pipe3.wr_en;
    me_data_req.rw_size    = pipe3.rw_size;
    me_data_req.data       = pipe3.write_data;
    me_data_req.ld_op_sign = pipe3.ld_op_sign;
  end

  memory i_memory (
      // data req starts from execute and continue in mem for correct stall beignning
      .clk_i            (clk_i),
      .rst_ni           (rst_ni),
      .stall_i          (stall_cause),
      .fe_flush_cache_i (fencei_flush),
      .me_data_req_i    (me_data_req),
      .ex_data_req_i    (ex_data_req),
      .lx_dres_i        (lx_dres),
      .lx_dreq_o        (lx_dreq),
      .me_data_o        (me_rdata),
      .dmiss_stall_o    (me_dmiss_stall),
      .fencei_stall_o   (me_fencei_stall)
  );

  // ============================================================================
  // WRITEBACK
  // ============================================================================

  // ============================================================================
  // EXECUTE → MEMORY Pipeline Register (pipe3)
  // ----------------------------------------------------------------------------
  // This register moves results computed in execute into the memory stage.
  // - ALU result, memory address, or CSR access state is held here.
  // - When not in reset and not frozen by downstream stall, new values load from pipe3.
  // - When the tracer is enabled, CSR access info is recorded as well.
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      `ifdef COMMIT_TRACER
      pipe4 <= '{instr_type:instr_invalid, rw_size: NO_SIZE, default: '0};
      `else
      pipe4 <= '0;
      `endif
    end else if (pipe_downstream_stall && !trap_active) begin
      // ME-stage stall (DMISS / ALU / FENCEI): freeze pipe4
    end else begin
      pipe4 <= '{
        `ifdef COMMIT_TRACER
          fe_tracer   : pipe3.fe_tracer,
          wr_en       : pipe3.wr_en,
          rw_size     : pipe3.rw_size,
          write_data  : pipe3.write_data,
          rd_en_csr   : pipe3.rd_en_csr,
          wr_en_csr   : pipe3.wr_en_csr,
          csr_idx     : pipe3.csr_idx,
          instr_type  : pipe3.instr_type,
          csr_wr_data : pipe3.csr_wr_data,
          csr_write_valid : pipe3.csr_write_valid,
          pc          : pipe3.pc,
          flushed     : pipe3.flushed,
        `endif
          dcache_valid : pipe3.dcache_valid,
          pc_incr     : pipe3.pc_incr,
          rf_rw_en    : pipe3.rf_rw_en,
          result_src  : pipe3.result_src,
          rd_addr     : pipe3.rd_addr,
          alu_result  : pipe3.alu_result,
          read_data   : pipe3.read_data
      };
    end
  end

  writeback i_writeback (
`ifdef COMMIT_TRACER
      .fe_tracer_i     (pipe4.fe_tracer),
      .wr_en_i         (pipe4.wr_en),
      .rw_size_i       (pipe4.rw_size),
      .write_data_i    (pipe4.write_data),
      .rd_addr_i       (pipe4.rd_addr),
      .rd_en_csr_i     (pipe4.rd_en_csr),
      .wr_en_csr_i     (pipe4.wr_en_csr),
      .csr_idx_i       (pipe4.csr_idx),
      .instr_type_i    (pipe4.instr_type),
      .csr_wr_data_i   (pipe4.csr_wr_data),
      .csr_write_valid_i(pipe4.csr_write_valid),
      .trap_active_i   (trap_active),
      .tcontrol_i      (ex_tcontrol),
      .pc_i            (pipe4.pc),
      .flushed_i       (pipe4.flushed),
`endif
      .fe_flush_cache_i(fencei_flush),
      .clk_i           (clk_i),
      .rst_ni          (rst_ni),
      .data_sel_i      (pipe4.result_src),
      .pc_incr_i       (pipe4.pc_incr),
      .alu_result_i    (pipe4.alu_result),
      .read_data_i     (pipe4.read_data),
      .stall_i         (stall_cause),
      .downstream_stall_i(pipe_downstream_stall),
      .rf_rw_en_i      (pipe4.rf_rw_en),
      .rf_rw_en_o      (wb_rf_rw),
      .wb_data_o       (wb_data)
  );

  // ============================================================================
  // MULTIPLE STAGE
  // ============================================================================

  hazard_unit i_hazard_unit (
      .r1_addr_de_i (pipe1.inst.r1_addr),
      .r2_addr_de_i (pipe1.inst.r2_addr),
      .r1_addr_ex_i (pipe2.r1_addr),
      .r2_addr_ex_i (pipe2.r2_addr),
      .pc_sel_ex_i  (!ex_spec_hit),
      .rd_addr_me_i (pipe3.rd_addr),
      .rf_rw_me_i   (pipe3.rf_rw_en),
      .rf_rw_wb_i   (pipe4.rf_rw_en),
      .rd_addr_wb_i (pipe4.rd_addr),
      .stall_fe_o   (fe_stall),
      .stall_de_o   (de_stall),
      .flush_de_o   (de_flush),
      .flush_ex_o   (ex_flush),
      .fwd_a_ex_o   (ex_fwd_a),
      .fwd_b_ex_o   (ex_fwd_b),
      .fwd_a_de_o   (de_fwd_a),
      .fwd_b_de_o   (de_fwd_b)
  );

  logic l2_miss_busy;
`ifdef USE_L2_CACHE
  nbmbmp_l2_cache i_l2_cache (
      .clk_i           (clk_i),
      .rst_ni          (rst_ni),
      .flush_i         (1'b0),
      .icache_req_i    (lx_ireq),
      .icache_res_o    (fe_lx_ires),
      .dcache_req_i    (lx_dreq),
      .dcache_res_o    (lx_dres),
      .mem_req_o       (iomem_req_o),
      .mem_res_i       (iomem_res_i),
      .l2_miss_busy_o  (l2_miss_busy)
  );
`else
  assign l2_miss_busy = 1'b0;
  memory_arbiter i_memory_arbiter (
      .clk_i       (clk_i),
      .rst_ni      (rst_ni),
      .icache_req_i(lx_ireq),
      .dcache_req_i(lx_dreq),
      .icache_res_o(fe_lx_ires),
      .dcache_res_o(lx_dres),
      .iomem_res_i (iomem_res_i),
      .iomem_req_o (iomem_req_o)
  );
`endif

  // ============================================================================
  //  PIPELINE CONTROL & EXCEPTION MANAGEMENT
  // ----------------------------------------------------------------------------
  // This always_comb block sets the pipeline control state for the current cycle.
  // - Computes which stage is the cause of stall.
  // - Masks which stage raised an exception (excp_mask).
  // - Chooses flush by exception priority (priority_flush).
  // ============================================================================
  // Downstream stall: freezes ME/WB stages (DMISS, ALU, FENCEI — but NOT IMISS).
  // Checked directly from raw stall sources so IMISS masking in stall_cause
  // does not hide an active DMISS.
  assign pipe_downstream_stall = me_dmiss_stall || ex_alu_stall || me_fencei_stall;

  always_comb begin
    stall_cause = NO_STALL;
    if (me_fencei_stall) begin
      stall_cause = FENCEI_STALL;
    end else if (fe_imiss_stall) begin
      stall_cause = IMISS_STALL;
    end else if (me_dmiss_stall) begin
      stall_cause = DMISS_STALL;
    end else if (fe_stall || de_stall) begin
      stall_cause = LOAD_RAW_STALL;
    end else if (ex_alu_stall) begin
      stall_cause = ALU_STALL;
    end
    excp_mask = '0;
    excp_mask = {1'b0, ex_exc_type != NO_EXCEPTION, de_active_exc_type != NO_EXCEPTION, fe_active_exc_type != NO_EXCEPTION};
    fe_trap_active = |{excp_mask[3:1], de_active_exc_type != NO_EXCEPTION};
    trap_active = |excp_mask[3:1];
    de_trap_active = de_active_exc_type != NO_EXCEPTION;
    priority_flush = ex_exc_type != NO_EXCEPTION ? 3:
                      de_active_exc_type != NO_EXCEPTION ?  2 : 0;


 // EX stage: misaligned LOAD/STORE, illegal vs.
  if (ex_exc_type != NO_EXCEPTION) begin
    unique case (ex_exc_type)
      ILLEGAL_INSTRUCTION: begin
        // RISC-V spec: mtval can be 0 for illegal (impl-defined, Spike uses 0)
        trap_tval = '0;
      end
      LOAD_MISALIGNED,
      STORE_MISALIGNED: begin
        // IMPORTANT: mtval must be the faulting address
        // ex_fault_addr = rs1 + imm (ALU effective address)
        trap_tval = ex_alu_result; // memory stage would use pipe2.pc; replace with your address signal if needed
      end
      default: begin
        trap_tval = '0;
      end
    endcase
  // DE stage: illegal at decode, misaligned fetch propagated from fetch, etc.
  end else if (de_active_exc_type != NO_EXCEPTION) begin
    unique case (de_active_exc_type)
      ILLEGAL_INSTRUCTION: begin
        // RISC-V spec: mtval can be 0 for illegal (impl-defined, Spike uses 0)
        trap_tval = '0;
      end
      INSTR_MISALIGNED: begin
        // mtval = faulting PC
        trap_tval = pipe1.pc;
      end
      default: begin
        trap_tval = '0;
      end
    endcase

  // Exception still active from FE (if you move it to decode but keep an FE-originated type, handle it last)
  end else if (fe_active_exc_type != NO_EXCEPTION) begin
    unique case (fe_active_exc_type)
      INSTR_MISALIGNED: begin
        // Optionally use pipe1.pc from decode here instead of fe_pc
        trap_tval = fe_pc;
      end
      ILLEGAL_INSTRUCTION: begin
        // RISC-V spec: mtval can be 0 for illegal (impl-defined, Spike uses 0)
        trap_tval = '0;
      end
      default: begin
        trap_tval = '0;
      end
    endcase
  end else begin
    trap_tval = '0;
  end

  end

  // pipe2 is frozen during any heavy stall — pipe3 must not re-accept
  // stale pipe2 output.  Declared early; assigned after stall_cause for vlog.
  assign pipe2_frozen = (stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL});

  // Fence.i debug logger — Enable with: +define+LOG_FENCEI_DEBUG or make LOG_FENCEI_DEBUG=1
  // synthesis translate_off
`ifdef LOG_FENCEI_DEBUG
  logic fencei_dbg_prev;
  always_ff @(posedge clk_i) begin
    if (!rst_ni) fencei_dbg_prev <= 1'b0;
    else         fencei_dbg_prev <= fencei_flush;
  end
  logic [15:0] post_fencei_cnt;
  always_ff @(posedge clk_i) begin
    if (!rst_ni) post_fencei_cnt <= '0;
    else if (fencei_dbg_prev && !fencei_flush) post_fencei_cnt <= 16'd1;
    else if (post_fencei_cnt > 0 && post_fencei_cnt < 16'd50) post_fencei_cnt <= post_fencei_cnt + 16'd1;
    else if (post_fencei_cnt >= 16'd50) post_fencei_cnt <= '0;
  end
  always_ff @(posedge clk_i) begin
    if (rst_ni) begin
      // Log rising edge of fencei_flush
      if (fencei_flush && !fencei_dbg_prev)
        $display("[FENCEI-DBG][CPU] %0t FENCE.I DETECTED pc=%08x flush_pc=%08x", $time, pipe2.pc, flush_pc);
      // Log stall state every 100 cycles during fence.i stall
      if (stall_cause == FENCEI_STALL && ($time % 100 == 0))
        $display("[FENCEI-DBG][CPU] %0t STALL stall=%0d fencei_flush=%b me_fencei_stall=%b pipe2.instr_type=%0d",
                 $time, stall_cause, fencei_flush, me_fencei_stall, pipe2.instr_type);
      // Log when stall deasserts
      if (fencei_dbg_prev && !fencei_flush)
        $display("[FENCEI-DBG][CPU] %0t FENCE.I COMPLETE — stall released", $time);
      // Log 50 cycles after fence.i to diagnose post-fence.i deadlock
      if (post_fencei_cnt > 0 && post_fencei_cnt <= 16'd50)
        $display("[FENCEI-DBG][CPU] %0t POST-FENCEI +%0d stall=%0d imiss=%b dmiss=%b fencei=%b pipe2.pc=%08x pipe2.type=%0d",
                 $time, post_fencei_cnt, stall_cause, fe_imiss_stall, me_dmiss_stall, me_fencei_stall, pipe2.pc, pipe2.instr_type);
    end
  end
`endif
  // synthesis translate_on

  // Pipeline visualizer (KONATA format)
  // Enable with: +define+KONATA_TRACER
`ifdef KONATA_TRACER
  konata_logger i_konata_logger ();
`endif

  // Stall cycle histogram + end-of-sim summary
  // Enable with: +define+LOG_PERF_STALL or make verilate/run LOG_PERF_STALL=1
`ifdef LOG_PERF_STALL
  perf_stall_counters i_perf_stall_counters (
      .clk_i              (clk_i),
      .rst_ni             (rst_ni),
      .stall_cause        (stall_cause),
      .fencei_flush_i     (fencei_flush),
      .priority_flush_i   (priority_flush),
      .de_flush_en_i      (de_flush_en),
      .ex_flush_en_i      (ex_flush_en),
      .l2_miss_busy_i     (l2_miss_busy),
      .raw_fencei_i       (me_fencei_stall),
      .raw_imiss_i        (fe_imiss_stall),
      .raw_dmiss_i        (me_dmiss_stall),
      .raw_load_hazard_i  (fe_stall || de_stall),
      .raw_alu_i          (ex_alu_stall)
  );
`endif

endmodule
