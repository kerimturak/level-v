// This file includes code snippets inspired by https://projectf.io/posts/division-in-verilog/
// Modified for the Level project.
//
// Level RISC-V Processor
// Copyright (c) 2024 Kerim TURAK
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software
// and associated documentation files (the "Software"), to deal in the Software without restriction,
// including without limitation the rights to use, copy, modify, merge, publish, distribute,
// sublicense, and/or sell copies of the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.

`timescale 1ns / 1ps
`include "level_defines.svh"

module divu_int #(
    parameter WIDTH = 32
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

  // Internal registers
  logic [          WIDTH-1:0] divisor_q;
  logic [          WIDTH-1:0] quotient_q;
  logic [            WIDTH:0] remainder_q;  // one extra bit
  logic [$clog2(WIDTH+1)-1:0] count_q;

  // Next-state signals
  logic [          WIDTH-1:0] quotient_next;
  logic [            WIDTH:0] remainder_next;

  // ------------------------------------------------------------
  // Restoring division step (unsigned)
  // ------------------------------------------------------------
  always_comb begin
    // Default: shift {remainder, quotient} left first
    // Similar to {remainder_q, quotient_q} << 1
    remainder_next = {remainder_q[WIDTH-1:0], quotient_q[WIDTH-1]};
    quotient_next  = {quotient_q[WIDTH-2:0], 1'b0};

    // If remainder_next >= divisor_q:
    // subtract divisor from remainder and set quotient LSB to 1
    if (remainder_next >= {1'b0, divisor_q}) begin
      remainder_next   = remainder_next - {1'b0, divisor_q};
      quotient_next[0] = 1'b1;
    end
  end

  // ------------------------------------------------------------
  // State machine
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
      done_o <= 1'b0;  // pulsed high only on completion cycle
      dbz_o  <= 1'b0;  // set only on start

      if (start_i) begin
        // New divide request
        valid_o <= 1'b0;

        if (divisor_i == '0) begin
          // Divide by zero: handled in RISC-V wrapper; set flag here
          busy_o     <= 1'b0;
          done_o     <= 1'b1;
          valid_o    <= 1'b1;
          dbz_o      <= 1'b1;

          quotient_o <= '0;  // not used at core level
          reminder_o <= dividend_i;  // overridden in wrapper for RISC-V
        end else begin
          // Start normal division
          busy_o      <= 1'b1;
          done_o      <= 1'b0;
          valid_o     <= 1'b0;
          dbz_o       <= 1'b0;

          divisor_q   <= divisor_i;
          quotient_q  <= dividend_i;
          remainder_q <= '0;
          count_q     <= WIDTH[$clog2(WIDTH+1)-1:0];
        end
      end else if (busy_o) begin
        // One division step per cycle
        remainder_q <= remainder_next;
        quotient_q  <= quotient_next;

        if (count_q == 1) begin
          // After final step
          busy_o     <= 1'b0;
          done_o     <= 1'b1;
          valid_o    <= 1'b1;

          quotient_o <= quotient_next;
          // remainder is WIDTH+1 bits; true remainder is WIDTH bits (MSB 0)
          reminder_o <= remainder_next[WIDTH-1:0];

          count_q    <= '0;
        end else begin
          // Continue stepping
          count_q <= count_q - 1'b1;
          done_o  <= 1'b0;
          valid_o <= 1'b0;
        end
      end else begin
        // Idle: hold outputs steady
        done_o <= 1'b0;
      end
    end
  end

endmodule
