/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"
module cpu
  import ceres_param::*;
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
  logic       [XLEN-1:0] ex_wdata;
  logic                  ex_pc_sel;
  logic                  ex_alu_stall;
  logic                  ex_spec_hit /*verilator split_var*/;
  exc_type_e             ex_exc_type;
  exc_type_e             ex_alu_exc_type;
  logic                  ex_rd_csr;
  logic                  ex_wr_csr;
  logic       [XLEN-1:0] ex_mtvec;
  logic                  ex_misa_c;
  logic       [XLEN-1:0] ex_tdata1;
  logic       [XLEN-1:0] ex_tdata2;
  logic       [XLEN-1:0] ex_tcontrol;
  //logic       [XLEN-1:0] ex_mepc;
  pipe_info_t            ex_info;
  logic                  ex_valid_csr;
  logic       [XLEN-1:0] ex_trap_cause;
  logic       [XLEN-1:0] ex_trap_mepc;
    `ifdef COMMIT_TRACER
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

  // ============================================================================
  // FETCH
  // ============================================================================

  // ============================================================================
  // FETCH Exception List
  // ----------------------------------------------------------------------------
  // INSTR_ACCESS_FAULT - pma grand yoksa
  // ILLEGAL_INSTRUCTION - desteklenen instruction değilse
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
  // Bu always_ff bloğu, fetch aşamasından gelen bilgileri decode aşamasına taşır.
  // - Her clock kenarında pipe1 güncellenir.
  // - Reset veya flush durumunda pipe1 temizlenir (nop benzeri).
  // - de_enable sinyali aktifse yeni fetch verileri yüklenir.
  // - Tracer açıkken, trace bilgisi (fe_tracer) de taşınır.
  // - ex_exc_type varsa decode ve fetch flush edilmeli, exception öncesi yanlış çekilmiştir
  // ============================================================================
  //  Decode Exception List
  //  - ILLEGAL_INSTRUCTION
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni || de_flush_en || |priority_flush || fencei_flush) begin
      pipe1 <= '{exc_type: NO_EXCEPTION, instr_type: instr_invalid, default: 0};
    end else if (de_enable) begin
      pipe1 <= '{
      `ifdef COMMIT_TRACER
        fe_tracer: fe_tracer,
      `endif
        pc      : fe_pc, pc_incr : fe_pc_incr, inst : fe_inst, exc_type: fe_active_exc_type, instr_type : fe_instr_type, spec: fe_spec};
    end
  end

  // ============================================================================
  //  DECODE kontrol mantığı
  // ----------------------------------------------------------------------------
  // Bu always_comb bloğu, decode aşamasının kontrol sinyallerini hesaplar.
  // - fe_active_exc_type : exc misprediction sonucu üretildi ise geçersizdir
  // - fencei_flush : fence.i komutu tespit edildiğinde I-cache flush sinyali
  // - de_enable      : decode enable durumu (stall yoksa ve flush gerekmezse)
  // - de_flush_en    : flush sinyali aktifse pipe1 sıfırlanır
  // - de_info        : sonraki aşamalara (fetch-execute feedback) bilgi taşır
  // Eğer speculative tahmin (branch prediction) başarısızsa,
  // bu instruction exception oluşturmaz (NO_EXCEPTION).
  // Ancak speculative hit ise, fetch’ten gelen exception korunur.
  // ============================================================================
  always_comb begin
    fe_active_exc_type  = ex_spec_hit ? fe_exc_type : NO_EXCEPTION;
    de_active_exc_type  = ex_spec_hit ? pipe1.exc_type != NO_EXCEPTION ? pipe1.exc_type : de_exc_type : NO_EXCEPTION;
    // Flush on fence.i OR misa write (misa.C change affects instruction decoding)
    fencei_flush        = (pipe2.instr_type == fence_i) || 
                          (ex_wr_csr && pipe2.csr_idx == 12'h301);  // misa write
    flush_pc            = pipe2.pc_incr;
    de_enable           = (stall_cause == NO_STALL); // to synch spike and core log stall on fetch flush
    de_flush_en         = (stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL}) ? 1'b0 : de_flush; //(stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL}) && de_flush;
    de_info.spec        = pipe1.spec;
    de_info.bjtype      = is_branch(pipe1.instr_type);
    de_info.pc          = pipe1.pc;
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
  // EXECUTE
  // ============================================================================

  // ============================================================================
  // DECODE → EXECUTE Pipeline Register (pipe2)
  // ----------------------------------------------------------------------------
  // Bu blok, decode aşamasında çözümlenen instruction’ı execute aşamasına taşır.
  // - Reset veya flush durumunda pipe2 sıfırlanır.
  // - Eğer fetch flush (örneğin fence.i) veya pipeline stall varsa güncellenmez.
  // - Aksi durumda, decode aşamasında üretilen kontrol sinyalleri ve operandlar
  //   execute aşamasına aktarılır.
  // Exception bilgisi:
  // Eğer speculative branch tahmini hatalıysa bu instruction flushlanacak,
  // bu yüzden exception'ı sıfırla. Aksi durumda decode exception'ı taşı.
  // - ex_exc_type varsa decode ve fetch flush edilmeli, exception öncesi yanlış çekilmiştir
  // - fencei_flush durumunda pipe1'i (decode) flush ediyoruz ama pipe2'deki fence.i instruction'ı
  //   execute/memory/writeback'e ilerlemeli, kendisini flush etmemeli
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni || ex_flush_en || priority_flush == 3 || priority_flush == 2) begin
      pipe2 <= '{instr_type: instr_invalid, alu_ctrl: OP_ADD, pc_sel: NO_BJ, default: 0};
    end else if (!(stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL})) begin
      pipe2 <= '{
        `ifdef COMMIT_TRACER
            fe_tracer   : pipe1.fe_tracer,
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
          r1_data      : de_r1_data,
          r2_data      : de_r2_data,
          r1_addr      : pipe1.inst.r1_addr,
          r2_addr      : pipe1.inst.r2_addr,
          rd_addr      : pipe1.inst.rd_addr,
          imm          : de_imm,
          instr_type   : pipe1.instr_type,
          spec         : pipe1.spec
      };
    end
  end

  // ============================================================================
  // EXECUTE kontrol mantığı
  // ----------------------------------------------------------------------------
  // Bu kısım, execute aşamasındaki exception ve CSR davranışlarını belirler.
  // - ex_flush_en: execute flush sinyalinin ne zaman etkin olacağını belirler
  // - ex_exc_type: ALU ve bellek erişimlerinden kaynaklanan hataları tespit eder
  // - ex_rd_csr / ex_wr_csr: CSR erişimlerinin stall ile çakışmasını önler
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
    end else if (pipe2.rw_size != 0) begin
      if (pipe2.wr_en) begin
        unique case (pipe2.rw_size)
          2'b10:   ex_exc_type = ex_alu_result[0] ? STORE_MISALIGNED : NO_EXCEPTION;
          2'b11:   ex_exc_type = (ex_alu_result[1] | ex_alu_result[0]) ? STORE_MISALIGNED : NO_EXCEPTION;
          default: ex_exc_type = NO_EXCEPTION;
        endcase
      end else begin
        unique case (pipe2.rw_size)
          2'b10:   ex_exc_type = ex_alu_result[0] ? LOAD_MISALIGNED : NO_EXCEPTION;
          2'b11:   ex_exc_type = (ex_alu_result[1] | ex_alu_result[0]) ? LOAD_MISALIGNED : NO_EXCEPTION;
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
    `endif
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),
      .stall_i      (stall_cause),
      .fwd_a_i      (ex_fwd_a),
      .fwd_b_i      (ex_fwd_b),
      .alu_result_i (pipe3.alu_result),
      .wb_data_i    (wb_data),
      .r1_data_i    (pipe2.r1_data),
      .r2_data_i    (pipe2.r2_data),
      .alu_in1_sel_i(pipe2.alu_in1_sel),
      .alu_in2_sel_i(pipe2.alu_in2_sel),
      .instr_type_i (pipe2.instr_type),
      .trap_active_i(trap_active), // muxlanarak exc çıkan aşamanın pcsi atanmalı
      .de_trap_active_i(de_trap_active), // muxlanarak exc çıkan aşamanın pcsi atanmalı
      .trap_tval_i  (trap_tval), // muxlanarak exc çıkan aşamanın pcsi atanmalı
      .trap_cause_i (ex_trap_cause ),
      .trap_mepc_i  (ex_trap_mepc  ),  // muxlanarak exc çıkan aşamanın pcsi atanmalı
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
  // Bu blok, execute aşamasında branch prediction’ın (speculative execution)
  // doğru olup olmadığını kontrol eder ve fetch aşamasına geri bildirim sağlar.
  // Ayrıca ex_info yapısını doldurarak sonraki aşamalarda exception / spec
  // takibi yapılmasına olanak tanır.
  // ============================================================================

  always_comb begin
    if (ex_pc_sel) ex_spec_hit = pipe2.spec.taken && (ex_pc_target == pipe2.spec.pc);
    else ex_spec_hit = !pipe2.spec.taken;

    if (!ex_spec_hit) begin
      if (ex_pc_sel) ex_pc_target_last = ex_pc_target;
      else ex_pc_target_last = pipe2.pc_incr;
    end else begin
      ex_pc_target_last = ex_pc_target;
    end

    ex_info.spec     = pipe2.spec;
    ex_info.bjtype   = is_branch(pipe2.instr_type);
    ex_info.pc       = pipe2.pc;

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
  // Bu blok, execute aşamasında erişilmek istenen CSR adresinin (csr_idx)
  // işlemci tarafından desteklenip desteklenmediğini kontrol eder.
  // Eğer geçerli bir CSR adresiyse ex_valid_csr = 1 olur.
  // Bu bilgi, writeback aşamasında CSR yazma izni için kullanılır.
  // ============================================================================
  always_comb begin // supported csrs
    ex_valid_csr = is_supported_csr(pipe2.csr_idx); 
  end

  
  always_ff @(posedge clk_i) begin
    if (!rst_ni || priority_flush == 3) begin
      `ifdef COMMIT_TRACER
      pipe3 <= '{instr_type:instr_invalid, default: 0};
      `else
      pipe3 <= '0;
      `endif
    end else if (!(stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL} && !trap_active)) begin
      pipe3 <= '{
        `ifdef COMMIT_TRACER
          fe_tracer    : pipe2.fe_tracer,
          rd_en_csr    : ex_rd_csr,
          wr_en_csr    : ex_valid_csr & ex_wr_csr,
          csr_idx      : pipe2.csr_idx,
          instr_type   : pipe2.instr_type,
          csr_wr_data  : ex_csr_wr_data,
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
  // Bu register, execute aşamasında hesaplanan sonuçları memory aşamasına taşır.
  // - ALU sonucu, memory adresi veya CSR erişimleri burada saklanır.
  // - Eğer reset varsa veya pipeline stall değilse yeni değerler yüklenir.
  // - Tracer açıksa, CSR erişim bilgileri de kaydedilir.
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      `ifdef COMMIT_TRACER
      pipe4 <= '{instr_type:instr_invalid, default: 0};
      `else
      pipe4 <= '0;
      `endif
    end else if (!(stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL} && !trap_active)) begin
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
          dcache_valid : pipe3.dcache_valid,
        `endif
          pc_incr     : pipe3.pc_incr,
          pc          : pipe3.pc,
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
      .trap_active_i   (trap_active),
      .tcontrol_i      (ex_tcontrol),
`endif
      .fe_flush_cache_i(fencei_flush),
      .clk_i           (clk_i),
      .rst_ni          (rst_ni),
      .data_sel_i      (pipe4.result_src),
      .pc_incr_i       (pipe4.pc_incr),
      .pc_i            (pipe4.pc),
      .alu_result_i    (pipe4.alu_result),
      .read_data_i     (pipe4.read_data),
      .stall_i         (stall_cause),
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
      .rd_addr_ex_i (pipe2.rd_addr),
      .pc_sel_ex_i  (!ex_spec_hit),
      .rslt_sel_ex_0(pipe2.result_src[0]),
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

  // ============================================================================
  //  PIPELINE CONTROL & EXCEPTION MANAGEMENT
  // ----------------------------------------------------------------------------
  // Bu always_comb bloğu, işlemcinin o cycle’daki pipeline kontrol durumunu belirler.
  // - Hangi aşamanın stall (durma) sebebi olduğunu hesaplar.
  // - Hangi aşamada exception oluştuğunu maskeler (excp_mask).
  // - Exception önceliğine göre flush kararı verir (priority_flush).
  // ============================================================================
  always_comb begin
    stall_cause = NO_STALL;
    if (me_fencei_stall) begin
      // Fence.i: dcache dirty writeback in progress, stall everything
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
        // ÖNEMLİ: mtval = faulting address olmalı
        // ex_fault_addr = rs1 + imm (ALU effective address)
        trap_tval = ex_alu_result; //because mempry stage address is this pipe2.pc;  // <- BUNU kendi adres sinyalinle değiştir
      end
      default: begin
        trap_tval = '0;
      end
    endcase
  // DE stage: decode’de illegal, fetch’ten taşınan misaligned_fetch vs.
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

  // FE tarafında aktif kalmış exception (sen decode’a taşıyorum diyorsun,
  // ama yine de FE kaynaklı bir tip tutuyorsan, son sıraya koyuyoruz)
  end else if (fe_active_exc_type != NO_EXCEPTION) begin
    unique case (fe_active_exc_type)
      INSTR_MISALIGNED: begin
        // İstersen burada fe_pc yerine decode’taki pipe1.pc kullan
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
  end

  end

  // Pipeline visualizer (KONATA format)
  // Enable with: +define+KONATA_TRACER
`ifdef KONATA_TRACER
  konata_logger i_konata_logger ();
`endif
endmodule
