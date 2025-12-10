// Pipelined Division Unit for improved timing
// Implements iterative restoring division with reduced combinational logic depth
// Uses 2 bits per cycle to balance performance and timing
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

module divu_pipelined #(
    parameter WIDTH = 32,
    parameter BITS_PER_CYCLE = 2  // Process 2 bits per cycle for better timing
) (
    input logic clk_i,
    input logic rst_ni,

    input logic             start_i,     // start calculation
    input logic [WIDTH-1:0] dividend_i,  // dividend (numerator)
    input logic [WIDTH-1:0] divisor_i,   // divisor (denominator)

    output logic busy_o,   // calculation in progress
    output logic done_o,   // calculation is complete (one tick)
    output logic valid_o,  // result is valid
    output logic dbz_o,    // divide by zero

    output logic [WIDTH-1:0] quotient_o,  // result: quotient
    output logic [WIDTH-1:0] reminder_o   // result: remainder
);

  localparam int ITERATIONS = WIDTH / BITS_PER_CYCLE;  // 32/2 = 16 iterations

  // Internal registers
  logic [          WIDTH-1:0] divisor_q;
  logic [          WIDTH-1:0] quotient_q;
  logic [            WIDTH:0] remainder_q;  // 1 bit wider
  logic [$clog2(ITERATIONS+1)-1:0] count_q;

  // Intermediate computation signals - broken into stages for better timing
  // Stage 1: First bit shift and compare
  logic [WIDTH:0] rem_stage1;
  logic [WIDTH-1:0] quo_stage1;
  logic sub1_valid;

  // Stage 2: Second bit shift and compare
  logic [WIDTH:0] rem_stage2;
  logic [WIDTH-1:0] quo_stage2;

  // ------------------------------------------------------------
  // Division step - Process 2 bits per cycle
  // Break the combinational logic into stages to reduce depth
  // ------------------------------------------------------------

  // First bit processing
  always_comb begin
    // Shift left: {remainder, quotient} << 1
    rem_stage1 = {remainder_q[WIDTH-1:0], quotient_q[WIDTH-1]};
    quo_stage1 = {quotient_q[WIDTH-2:0], 1'b0};

    // Compare and subtract if possible
    sub1_valid = (rem_stage1 >= {1'b0, divisor_q});
    if (sub1_valid) begin
      rem_stage1 = rem_stage1 - {1'b0, divisor_q};
      quo_stage1[0] = 1'b1;
    end
  end

  // Second bit processing (uses stage1 results)
  always_comb begin
    // Shift left again: {rem_stage1, quo_stage1} << 1
    rem_stage2 = {rem_stage1[WIDTH-1:0], quo_stage1[WIDTH-1]};
    quo_stage2 = {quo_stage1[WIDTH-2:0], 1'b0};

    // Compare and subtract if possible
    if (rem_stage2 >= {1'b0, divisor_q}) begin
      rem_stage2 = rem_stage2 - {1'b0, divisor_q};
      quo_stage2[0] = 1'b1;
    end
  end

  // ------------------------------------------------------------
  // Main state machine
  // ------------------------------------------------------------
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      busy_o      <= 1'b0;
      done_o      <= 1'b0;
      valid_o     <= 1'b0;
      dbz_o       <= 1'b0;
      quotient_o  <= '0;
      reminder_o  <= '0;

      divisor_q   <= '0;
      quotient_q  <= '0;
      remainder_q <= '0;
      count_q     <= '0;
    end else begin
      // Defaults
      done_o <= 1'b0;
      dbz_o  <= 1'b0;

      if (start_i) begin
        // New division request
        valid_o <= 1'b0;

        if (divisor_i == '0) begin
          // Divide by zero
          busy_o     <= 1'b0;
          done_o     <= 1'b1;
          valid_o    <= 1'b1;
          dbz_o      <= 1'b1;

          quotient_o <= '0;
          reminder_o <= dividend_i;
        end else begin
          // Start normal division
          busy_o      <= 1'b1;
          done_o      <= 1'b0;
          valid_o     <= 1'b0;
          dbz_o       <= 1'b0;

          divisor_q   <= divisor_i;
          quotient_q  <= dividend_i;
          remainder_q <= '0;
          count_q     <= ITERATIONS[$clog2(ITERATIONS+1)-1:0];
        end
      end else if (busy_o) begin
        // Processing division iterations (2 bits per cycle)
        remainder_q <= rem_stage2;
        quotient_q  <= quo_stage2;

        if (count_q == 1) begin
          // Final iteration complete
          busy_o     <= 1'b0;
          done_o     <= 1'b1;
          valid_o    <= 1'b1;

          quotient_o <= quo_stage2;
          reminder_o <= rem_stage2[WIDTH-1:0];

          count_q    <= '0;
        end else begin
          // Continue iterations
          count_q <= count_q - 1'b1;
          done_o  <= 1'b0;
          valid_o <= 1'b0;
        end
      end else begin
        // Idle state
        done_o <= 1'b0;
      end
    end
  end

endmodule
