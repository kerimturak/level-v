// ceres RISC-V Processor
// Copyright (c) 2024 Kerim TURAK
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software
// and associated documentation files (the "Software"), to deal in the Software without restriction,
// including without limitation the rights to use, copy, modify, merge, publish, distribute,
// sublicense, and/or sell copies of the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Kerim TURAK - kerimturak@hotmail.com                       //
//                                                                            //
// Additional contributions by:                                               //
//                 --                                                         //
//                                                                            //
// Design Name:    seq_multiplier                                             //
// Project Name:   ceres                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Slow multiplication                                        //
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns / 1ps
`include "ceres_defines.svh"
module mul_int #(
    parameter SIZE = 32
) (
    input  logic              clk_i,
    input  logic              rst_ni,
    input  logic              start_i,         // start_i calculation
    input  logic [  SIZE-1:0] multiplicand_i,  // unsigned multiplicand
    input  logic [  SIZE-1:0] multiplier_i,    // unsigned multiplier
    output logic [2*SIZE-1:0] product_o,       // unsigned product
    output logic              busy_o,          // calculation in progress
    output logic              done_o,          // calculation is complete (high for one tick)
    output logic              valid_o          // result is valid_o
);

  logic [        SIZE-1:0] mult;  // multiplier
  logic [$clog2(SIZE)-1:0] counter;
  logic                    shift;

  assign shift = |(counter ^ 31);  //1: counter<31; 0: counter==31

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      mult    <= '0;
      product_o    <= '0;
      counter <= '0;
      done_o    <= 1'b0;
      busy_o    <= 1'b0;
      valid_o   <= 1'b0;
    end else begin
      if (start_i) begin
        mult    <= multiplier_i;
        product_o    <= '0;
        counter <= '0;
        done_o    <= 1'b0;
        busy_o    <= 1'b1;
        valid_o   <= 1'b0;
      end else if (busy_o) begin
        mult      <= mult << 1;
        product_o <= (product_o + (multiplicand_i & {SIZE{mult[SIZE-1]}})) << shift;
        counter   <= counter + shift;
        done_o    <= counter + 1'b1 == 32'd32 ? 1'b1 : 1'b0;
        busy_o    <= counter + 1'b1 == 32'd32 ? 1'b0 : 1'b1;
        valid_o   <= counter + 1'b1 == 32'd32 ? 1'b1 : 1'b0;
      end
    end
  end

endmodule
