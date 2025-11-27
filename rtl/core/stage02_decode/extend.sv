/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"
module extend
  import ceres_param::*;
(
    input logic [XLEN-1:7] imm_i,
    input imm_e sel_i,
    output logic [XLEN-1:0] imm_o
);

  always_comb begin : immediate_generator
    case (sel_i)
      I_IMM:   imm_o = {{20{imm_i[31]}}, imm_i[31:20]};  // i 12-bit signed immediate
      I_USIMM: imm_o = {{20{1'b0}}, imm_i[31:20]};  // i 12-bit unsigned immediate
      S_IMM:   imm_o = {{20{imm_i[31]}}, imm_i[31:25], imm_i[11:7]};  // s 12-bit signed immediate
      B_IMM:   imm_o = {{20{imm_i[31]}}, imm_i[7], imm_i[30:25], imm_i[11:8], 1'b0};  // b 13-bit signed immediate
      U_IMM:   imm_o = {{imm_i[31:12]}, 12'b0};  // u 20-bit signed immediate
      J_IMM:   imm_o = {{12{imm_i[31]}}, imm_i[19:12], imm_i[20], imm_i[30:21], 1'b0};  // j 20-bit signed immediate
      CSR_IMM: imm_o = {27'b0, imm_i[19:15]};
      default: imm_o = '0;
    endcase
  end

endmodule
