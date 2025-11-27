/************************************************
  The Verilog HDL code example is from the book
  Computer Principles and Design in Verilog HDL
  by Yamin Li, published by A JOHN WILEY & SONS
************************************************/
`timescale 1ns / 1ps
module wallace_8x8_product (a,b,z);                       // 8*8 wt product
    input  [07:00] a;                                     // 8 bits
    input  [07:00] b;                                     // 8 bits
    output [15:00] z;                                     // product
    wire   [15:05] x;                                     // sum high
    wire   [15:05] y;                                     // carry high
    wire   [15:05] z_high;                                // product high
    wire   [04:00] z_low;                                 // product low
    wallace_8x8 wt_partial (a, b, x, y, z_low);           // partial product
    assign z_high = x + y;
    assign z = {z_high,z_low};                            // product
endmodule
