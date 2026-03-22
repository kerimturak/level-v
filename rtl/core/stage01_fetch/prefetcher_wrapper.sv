/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
Parametric Prefetcher Wrapper
================================================================================
PREFETCH_TYPE: 0=None, 1=NextLine, 2-4=NextLine placeholder until stride/stream exist.
================================================================================
*/
`timescale 1ns / 1ps

module prefetcher_wrapper
  import level_param::*;
#(
    parameter int XLEN          = level_param::XLEN,
    parameter int BLK_SIZE      = level_param::BLK_SIZE,
    parameter int PREFETCH_TYPE = level_param::PREFETCH_TYPE
) (
    input  logic            clk_i,
    input  logic            rst_ni,
    input  logic            flush_i,
    input  logic            cache_miss_i,
    input  logic            miss_uncached_i,
    input  logic [XLEN-1:0] miss_addr_i,
    input  logic            prefetch_ack_i,
    output logic            prefetch_valid_o,
    output logic [XLEN-1:0] prefetch_addr_o
);

  generate
    if (PREFETCH_TYPE == 0) begin : gen_no_prefetch

      assign prefetch_valid_o = 1'b0;
      assign prefetch_addr_o  = '0;

    end else begin : gen_next_line_any

      next_line_prefetcher #(
          .XLEN    (XLEN),
          .BLK_SIZE(BLK_SIZE)
      ) u_next_line_prefetcher (
          .clk_i            (clk_i),
          .rst_ni           (rst_ni),
          .flush_i          (flush_i),
          .cache_miss_i     (cache_miss_i),
          .miss_uncached_i  (miss_uncached_i),
          .miss_addr_i      (miss_addr_i),
          .prefetch_ack_i   (prefetch_ack_i),
          .prefetch_valid_o (prefetch_valid_o),
          .prefetch_addr_o  (prefetch_addr_o)
      );

    end
  endgenerate

endmodule
