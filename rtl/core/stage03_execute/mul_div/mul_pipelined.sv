// Pipelined Multiplier for improved timing
// Implements a 2-stage pipelined multiplier to reduce combinational logic depth
// while maintaining high performance
//
// Stage 1: Partial product generation (split into 4 groups of 8 bits each)
// Stage 2: Tree reduction and final addition
//
// This approach breaks the deep combinational path of single-cycle multiplier
// Expected timing improvement: 10-15ns on critical path
//
// ceres RISC-V Processor
// Copyright (c) 2024 Kerim TURAK
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software
// and associated documentation files (the "Software"), to deal in the Software without restriction,
// including without limitation the rights to use, copy, modify, merge, publish, distribute,
// sublicense, and/or sell copies of the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.

`timescale 1ns / 1ps
`include "ceres_defines.svh"

module mul_pipelined #(
    parameter XLEN = 32,
    parameter YLEN = 32
) (
    input logic clk_i,
    input logic rst_ni,

    input  logic             start_i,      // Start multiplication
    input  logic [XLEN-1:0]  a_i,          // Multiplicand
    input  logic [YLEN-1:0]  b_i,          // Multiplier
    output logic [XLEN+YLEN-1:0] product_o, // Product output
    output logic             busy_o,       // Calculation in progress
    output logic             done_o,       // Calculation complete (one tick)
    output logic             valid_o       // Result is valid
);

  // Stage 1: Intermediate products (4 quarters of 8x32 bits each)
  logic [XLEN-1:0]      a_stage1;
  logic [YLEN-1:0]      b_stage1;
  logic [XLEN+7:0]      prod_q0;  // b[7:0] * a
  logic [XLEN+7:0]      prod_q1;  // b[15:8] * a
  logic [XLEN+7:0]      prod_q2;  // b[23:16] * a
  logic [XLEN+7:0]      prod_q3;  // b[31:24] * a
  logic                 stage1_valid;

  // Stage 2: Final accumulation
  logic [XLEN+YLEN-1:0] result;
  logic                 stage2_valid;

  // Pipeline control
  logic pipe_active;

  // ------------------------------------------------------------
  // Stage 1: Compute 4 partial products (8-bit slices)
  // This breaks the 32x32 multiplication into 4 smaller 8x32 multiplications
  // Synthesis will infer smaller, faster multipliers
  // ------------------------------------------------------------
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      a_stage1      <= '0;
      b_stage1      <= '0;
      prod_q0       <= '0;
      prod_q1       <= '0;
      prod_q2       <= '0;
      prod_q3       <= '0;
      stage1_valid  <= 1'b0;
    end else begin
      if (start_i) begin
        a_stage1 <= a_i;
        b_stage1 <= b_i;

        // Break into 4 quarters - smaller multipliers have better timing
        prod_q0 <= a_i * b_i[7:0];   // Lower 8 bits
        prod_q1 <= a_i * b_i[15:8];  // Second 8 bits
        prod_q2 <= a_i * b_i[23:16]; // Third 8 bits
        prod_q3 <= a_i * b_i[31:24]; // Upper 8 bits

        stage1_valid <= 1'b1;
      end else begin
        stage1_valid <= 1'b0;
      end
    end
  end

  // ------------------------------------------------------------
  // Stage 2: Combine partial products with proper shifting
  // Each quarter is shifted by 8, 16, or 24 bits
  // ------------------------------------------------------------
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      result       <= '0;
      product_o    <= '0;
      stage2_valid <= 1'b0;
      valid_o      <= 1'b0;
      done_o       <= 1'b0;
    end else begin
      if (stage1_valid) begin
        // Accumulate with proper shifts
        result <= ({56'b0, prod_q0})       +    // No shift
                   ({48'b0, prod_q1} << 8)  +    // Shift by 8
                   ({40'b0, prod_q2} << 16) +    // Shift by 16
                   ({32'b0, prod_q3} << 24);     // Shift by 24

        stage2_valid <= 1'b1;
      end else begin
        stage2_valid <= 1'b0;
      end

      // Output control
      if (stage2_valid) begin
        product_o <= result;
        valid_o   <= 1'b1;
        done_o    <= 1'b1;
      end else begin
        done_o    <= 1'b0;
        if (!start_i && !stage1_valid) begin
          valid_o <= 1'b0;
        end
      end
    end
  end

  // ------------------------------------------------------------
  // Pipeline Control
  // Multiplication takes 2 cycles in pipelined mode
  // ------------------------------------------------------------
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      pipe_active <= 1'b0;
      busy_o      <= 1'b0;
    end else begin
      if (start_i) begin
        pipe_active <= 1'b1;
        busy_o      <= 1'b1;
      end else if (pipe_active) begin
        if (stage1_valid) begin
          // Still in pipeline, one more cycle to go
          busy_o <= 1'b1;
        end else begin
          pipe_active <= 1'b0;
          busy_o      <= 1'b0;
        end
      end else begin
        busy_o <= 1'b0;
      end
    end
  end

endmodule
