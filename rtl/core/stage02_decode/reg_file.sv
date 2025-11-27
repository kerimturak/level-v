/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"
module reg_file
  import ceres_param::*;
(
    input  logic            clk_i,
    input  logic            rst_ni,
    input  logic            rw_en_i,
    input  logic [     4:0] r1_addr_i,
    input  logic [     4:0] r2_addr_i,
    input  logic [     4:0] waddr_i,
    input  logic [XLEN-1:0] wdata_i,
    output logic [XLEN-1:0] r1_data_o,
    output logic [XLEN-1:0] r2_data_o
);

  logic [XLEN-1:0] registers[31:0];

  always_comb begin : register_read
    r1_data_o = registers[r1_addr_i];
    r2_data_o = registers[r2_addr_i];
  end

  always_ff @(posedge clk_i) begin : register_write
    if (!rst_ni) begin
      registers <= '{default: 0};
    end else if (rw_en_i == 1'b1 && waddr_i != 5'b0) begin
      registers[waddr_i] <= wdata_i;
    end
  end

endmodule
