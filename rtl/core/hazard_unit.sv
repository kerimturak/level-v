/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "level_defines.svh"
module hazard_unit (
    input  logic [4:0] r1_addr_de_i,
    input  logic [4:0] r2_addr_de_i,
    input  logic [4:0] r1_addr_ex_i,
    input  logic [4:0] r2_addr_ex_i,
    input  logic       pc_sel_ex_i,
    input  logic [4:0] rd_addr_me_i,
    input  logic       rf_rw_me_i,
    input  logic       rf_rw_wb_i,
    input  logic [4:0] rd_addr_wb_i,
    output logic       stall_fe_o,
    output logic       stall_de_o,
    output logic       flush_de_o,
    output logic       flush_ex_o,
    output logic [1:0] fwd_a_ex_o,
    output logic [1:0] fwd_b_ex_o,
    output logic       fwd_a_de_o,
    output logic       fwd_b_de_o
);

  always_comb begin
    if (rf_rw_me_i && (r1_addr_ex_i == rd_addr_me_i) && (r1_addr_ex_i != 0)) begin  // memory to execution
      fwd_a_ex_o = 2'b10;
    end else if (rf_rw_wb_i && (r1_addr_ex_i == rd_addr_wb_i) && (r1_addr_ex_i != 0)) begin  // writeback to execution
      fwd_a_ex_o = 2'b01;
    end else begin
      fwd_a_ex_o = 2'b00;
    end

    if (rf_rw_me_i && (r2_addr_ex_i == rd_addr_me_i) && (r2_addr_ex_i != 0)) begin
      fwd_b_ex_o = 2'b10;
    end else if (rf_rw_wb_i && (r2_addr_ex_i == rd_addr_wb_i) && (r2_addr_ex_i != 0)) begin
      fwd_b_ex_o = 2'b01;
    end else begin
      fwd_b_ex_o = 2'b00;
    end

    fwd_a_de_o = rf_rw_wb_i && (r1_addr_de_i == rd_addr_wb_i) && (r1_addr_de_i != 0);  // writeback to decode
    fwd_b_de_o = rf_rw_wb_i && (r2_addr_de_i == rd_addr_wb_i) && (r2_addr_de_i != 0);

    // Load-use (SSR, arXiv:1912.10663): do not stall FE/DE or flush EX. When the
    // dependent reaches EX, the producer load is in MEM (pipe3); MEM→EX bypass
    // (fwd_* = 2'b10, ex_mem_bypass_data) supplies read_data / ALU result.
    stall_fe_o = 1'b0;
    stall_de_o = 1'b0;

    flush_de_o = pc_sel_ex_i;
    flush_ex_o = pc_sel_ex_i;

  end

endmodule
