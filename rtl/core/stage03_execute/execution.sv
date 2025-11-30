/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"
module execution
  import ceres_param::*;
(
`ifdef COMMIT_TRACER
    output logic        [XLEN-1:0] csr_wr_data_o,
`endif
    input  logic                   clk_i,
    input  logic                   rst_ni,
    input  stall_e                 stall_i,
    input  logic        [     1:0] fwd_a_i,
    input  logic        [     1:0] fwd_b_i,
    input  logic        [XLEN-1:0] alu_result_i,
    input  logic        [XLEN-1:0] wb_data_i,
    input  logic        [XLEN-1:0] r1_data_i,
    input  logic        [XLEN-1:0] r2_data_i,
    input  logic        [     1:0] alu_in1_sel_i,
    input  logic                   alu_in2_sel_i,
    input  logic                   rd_csr_i,
    input  logic                   wr_csr_i,
    input  logic        [    11:0] csr_idx_i,
    input  logic                   csr_or_data_i,
    input  logic                   trap_active_i,
    input  logic                   de_trap_active_i,
    input  logic        [XLEN-1:0] trap_cause_i,
    input  logic        [XLEN-1:0] trap_tval_i,       // faulting instruction / adres
    input  logic        [XLEN-1:0] trap_mepc_i,
    input  logic        [XLEN-1:0] pc_i,
    input  logic        [XLEN-1:0] pc_incr_i,
    input  logic        [XLEN-1:0] imm_i,
    input  pc_sel_e                pc_sel_i,
    input  alu_op_e                alu_ctrl_i,
    input  instr_type_e            instr_type_i,
    output logic        [XLEN-1:0] write_data_o,
    output logic        [XLEN-1:0] pc_target_o,
    output logic        [XLEN-1:0] alu_result_o,
    output logic                   pc_sel_o,
    output logic                   alu_stall_o,
    output exc_type_e              exc_type_o,
    output logic        [XLEN-1:0] mtvec_o,
    output logic                   misa_c_o

);

  logic        [XLEN-1:0] data_a;
  logic        [XLEN-1:0] operant_a;
  logic        [XLEN-1:0] operant_b;
  logic signed [XLEN-1:0] signed_imm;
  logic                   ex_zero;
  logic                   ex_slt;
  logic                   ex_sltu;
  logic        [XLEN-1:0] alu_result;
  logic        [XLEN-1:0] csr_rdata;
  logic        [XLEN-1:0] mepc;
  logic                   misa_c;

  assign misa_c_o = misa_c;

  always_comb begin
    data_a = fwd_a_i[1] ? alu_result_i : (fwd_a_i[0] ? wb_data_i : r1_data_i);
    case (alu_in1_sel_i)
      2'b00: operant_a = data_a;
      2'b01: operant_a = pc_incr_i;
      2'b10: operant_a = pc_i;
      2'b11: operant_a = data_a;
    endcase

    write_data_o = fwd_b_i[1] ? alu_result_i : (fwd_b_i[0] ? wb_data_i : r2_data_i);
    operant_b = alu_in2_sel_i ? imm_i : write_data_o;
    signed_imm = imm_i;
    /*
    Eğer exception desteği yoksa burası
    pc_target_o = pc_sel_i == JALR ? (data_a + imm_i) & ~1 : pc_i + signed_imm;
    */
    pc_target_o = instr_type_i == mret ? mepc : pc_sel_i == JALR ? (data_a + imm_i) & ~1 : pc_i + signed_imm;

    pc_sel_o = (pc_sel_i == BEQ) && ex_zero;
    pc_sel_o |= (pc_sel_i == BNE) && !ex_zero;
    pc_sel_o |= (pc_sel_i == BLT) && ex_slt;
    pc_sel_o |= (pc_sel_i == BGE) && (!ex_slt || ex_zero);
    pc_sel_o |= (pc_sel_i == BLTU) && ex_sltu;
    pc_sel_o |= (pc_sel_i == BGEU) && (!ex_sltu || ex_zero);
    pc_sel_o |= (pc_sel_i == JALR);
    pc_sel_o |= (pc_sel_i == JAL);
    pc_sel_o |= (instr_type_i == mret);

    exc_type_o = pc_sel_o && pc_target_o[0] ? INSTR_MISALIGNED : NO_EXCEPTION;
  end

  alu i_alu (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .alu_a_i    (operant_a),
      .csr_rdata_i(csr_rdata),
      .alu_b_i    (operant_b),
      .op_sel_i   (alu_ctrl_i),
      .alu_stall_o(alu_stall_o),
      .zero_o     (ex_zero),
      .slt_o      (ex_slt),
      .sltu_o     (ex_sltu),
      .alu_o      (alu_result)
  );

  logic [XLEN-1:0] rd_data;

  always_comb begin
    unique case (instr_type_i)
      u_jal, i_jalr: rd_data = pc_incr_i;  // rd = PC+4
      default:       rd_data = alu_result;
    endcase

    if (rd_csr_i && csr_or_data_i) rd_data = csr_rdata;
  end

  assign alu_result_o = rd_data;

`ifdef COMMIT_TRACER
  always_comb begin
    if (instr_type_i == mret) begin
      // cs_reg_file içindeki pack_mstatus sonucu loglanmalı
      csr_wr_data_o        = 0;
      csr_wr_data_o[3]     = csr_rdata[3];
      csr_wr_data_o[7]     = csr_rdata[7];
      csr_wr_data_o[12:11] = csr_rdata[12:11];
    end else begin
      csr_wr_data_o = csr_wmask(csr_idx_i, alu_result);
    end
  end
`endif

  cs_reg_file i_cs_reg_file (
      .clk_i           (clk_i),
      .rst_ni          (rst_ni),
      .stall_i         (stall_i),
      .rd_en_i         (rd_csr_i),
      .wr_en_i         (wr_csr_i),
      .csr_idx_i       (csr_idx_i),
      .csr_wdata_i     (alu_result),
      .csr_rdata_o     (csr_rdata),
      .trap_active_i   (trap_active_i),
      .de_trap_active_i(de_trap_active_i),
      .trap_cause_i    (trap_cause_i),
      .trap_mepc_i     (trap_mepc_i),
      .trap_tval_i     (trap_tval_i),
      .instr_type_i    (instr_type_i),
      .mtvec_o         (mtvec_o),
      .mepc_o          (mepc),
      .misa_c_o        (misa_c),
      .tdata1_o        (),  // Trigger outputs - not used yet
      .tdata2_o        ()   // Breakpoint address - not used yet
  );
endmodule
