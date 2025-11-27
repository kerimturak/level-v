// This file includes code snippets inspired by https://projectf.io/posts/division-in-verilog/
// Modified for the ceres project.
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

  // Dahili registerlar
  logic [          WIDTH-1:0] divisor_q;
  logic [          WIDTH-1:0] quotient_q;
  logic [            WIDTH:0] remainder_q;  // 1 bit geniş
  logic [$clog2(WIDTH+1)-1:0] count_q;

  // Next-state sinyalleri
  logic [          WIDTH-1:0] quotient_next;
  logic [            WIDTH:0] remainder_next;

  // ------------------------------------------------------------
  // Restoring division step (unsigned)
  // ------------------------------------------------------------
  always_comb begin
    // Varsayılan: önce remainder:quotient sol kaydır
    // {remainder_q, quotient_q} << 1 benzeri
    remainder_next = {remainder_q[WIDTH-1:0], quotient_q[WIDTH-1]};
    quotient_next  = {quotient_q[WIDTH-2:0], 1'b0};

    // Eğer remainder_next >= divisor_q ise:
    // remainder'dan divisor'u çıkar ve quotient'in LSB'sini 1 yap
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
      // Varsayılanlar
      done_o <= 1'b0;  // sadece tamamlandığı cycle 1 olacak
      dbz_o  <= 1'b0;  // sadece start'ta set edilir

      if (start_i) begin
        // Yeni bölme isteği
        valid_o <= 1'b0;

        if (divisor_i == '0) begin
          // Divide by zero: RISC-V wrapper'da halledeceksin ama burada flag'i set edelim
          busy_o     <= 1'b0;
          done_o     <= 1'b1;
          valid_o    <= 1'b1;
          dbz_o      <= 1'b1;

          quotient_o <= '0;  // core seviyesinde kullanmayacaksın zaten
          reminder_o <= dividend_i;  // RISC-V için wrapper’da override ediyorsun
        end else begin
          // Normal bölme başlat
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
        // Her cycle bir division step
        remainder_q <= remainder_next;
        quotient_q  <= quotient_next;

        if (count_q == 1) begin
          // Son adım sonrası
          busy_o     <= 1'b0;
          done_o     <= 1'b1;
          valid_o    <= 1'b1;

          quotient_o <= quotient_next;
          // remainder WIDTH+1 bit, asıl remainder WIDTH bitlik (MSB 0)
          reminder_o <= remainder_next[WIDTH-1:0];

          count_q    <= '0;
        end else begin
          // Devam ediyoruz
          count_q <= count_q - 1'b1;
          done_o  <= 1'b0;
          valid_o <= 1'b0;
        end
      end else begin
        // idle durumu, outputlar sabit kalsın
        done_o <= 1'b0;
      end
    end
  end

endmodule
