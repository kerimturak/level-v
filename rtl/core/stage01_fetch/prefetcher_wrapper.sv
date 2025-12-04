/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
Parametric Prefetcher Wrapper
================================================================================
PREFETCH_TYPE parametresine göre uygun prefetcher'ı instantiate eder.

Desteklenen Prefetcher Türleri:
  0 - None      : Prefetching devre dışı
  1 - NextLine  : Basit next-line prefetcher
  2 - Stride    : PC-indexed stride prefetcher (TODO)
  3 - Stream    : Multi-stream prefetcher (TODO)
  4 - Hybrid    : Stride + Stream kombinasyonu (TODO)

Kullanım:
  ceres_param::PREFETCH_TYPE parametresi ile kontrol edilir.
================================================================================
*/
`timescale 1ns / 1ps

module prefetcher_wrapper
  import ceres_param::*;
#(
    parameter int XLEN          = ceres_param::XLEN,
    parameter int BLK_SIZE      = ceres_param::BLK_SIZE,
    parameter int PREFETCH_TYPE = ceres_param::PREFETCH_TYPE
) (
    input  logic            clk_i,
    input  logic            rst_ni,
    input  logic            flush_i,
    // Cache interface
    input  logic            cache_miss_i,
    input  logic            cache_hit_i,
    input  logic [XLEN-1:0] access_addr_i,
    input  logic [XLEN-1:0] access_pc_i,
    input  logic            access_valid_i,
    input  logic            cache_busy_i,
    // Prefetch interface
    input  logic            prefetch_ack_i,
    output logic            prefetch_valid_o,
    output logic [XLEN-1:0] prefetch_addr_o
);

  generate
    // ========================================================================
    // Type 0: No Prefetching
    // ========================================================================
    if (PREFETCH_TYPE == 0) begin : gen_no_prefetch

      assign prefetch_valid_o = 1'b0;
      assign prefetch_addr_o  = '0;

      // ========================================================================
      // Type 1: Next-Line Prefetcher
      // ========================================================================
    end else if (PREFETCH_TYPE == 1) begin : gen_next_line

      next_line_prefetcher #(
          .XLEN    (XLEN),
          .BLK_SIZE(BLK_SIZE)
      ) u_next_line_prefetcher (
          .clk_i           (clk_i),
          .rst_ni          (rst_ni),
          .flush_i         (flush_i),
          .cache_miss_i    (cache_miss_i),
          .miss_addr_i     (access_addr_i),
          .prefetch_ack_i  (prefetch_ack_i),
          .cache_busy_i    (cache_busy_i),
          .prefetch_valid_o(prefetch_valid_o),
          .prefetch_addr_o (prefetch_addr_o)
      );

      // ========================================================================
      // Type 2: Stride Prefetcher (TODO)
      // ========================================================================
    end else if (PREFETCH_TYPE == 2) begin : gen_stride

      // TODO: Implement stride_prefetcher
      // stride_prefetcher #(
      //     .XLEN       (XLEN),
      //     .TABLE_SIZE (ceres_param::STRIDE_TABLE_SIZE),
      //     .STRIDE_BITS(ceres_param::STRIDE_BITS),
      //     .BLK_SIZE   (BLK_SIZE)
      // ) u_stride_prefetcher (
      //     .clk_i              (clk_i),
      //     .rst_ni             (rst_ni),
      //     .access_valid_i     (access_valid_i),
      //     .access_pc_i        (access_pc_i),
      //     .access_addr_i      (access_addr_i),
      //     .cache_hit_i        (cache_hit_i),
      //     .prefetch_ack_i     (prefetch_ack_i),
      //     .prefetch_valid_o   (prefetch_valid_o),
      //     .prefetch_addr_o    (prefetch_addr_o),
      //     .prefetch_confidence_o()
      // );

      // Placeholder - fall back to next-line until stride is implemented
      next_line_prefetcher #(
          .XLEN    (XLEN),
          .BLK_SIZE(BLK_SIZE)
      ) u_next_line_prefetcher (
          .clk_i           (clk_i),
          .rst_ni          (rst_ni),
          .flush_i         (flush_i),
          .cache_miss_i    (cache_miss_i),
          .miss_addr_i     (access_addr_i),
          .prefetch_ack_i  (prefetch_ack_i),
          .cache_busy_i    (cache_busy_i),
          .prefetch_valid_o(prefetch_valid_o),
          .prefetch_addr_o (prefetch_addr_o)
      );

      // ========================================================================
      // Type 3: Stream Prefetcher (TODO)
      // ========================================================================
    end else if (PREFETCH_TYPE == 3) begin : gen_stream

      // TODO: Implement stream_prefetcher
      // stream_prefetcher #(
      //     .XLEN           (XLEN),
      //     .NUM_STREAMS    (ceres_param::NUM_STREAMS),
      //     .PREFETCH_DEGREE(ceres_param::PREFETCH_DEGREE),
      //     .BLK_SIZE       (BLK_SIZE)
      // ) u_stream_prefetcher (
      //     .clk_i          (clk_i),
      //     .rst_ni         (rst_ni),
      //     .cache_miss_i   (cache_miss_i),
      //     .miss_addr_i    (access_addr_i),
      //     .prefetch_ack_i (prefetch_ack_i),
      //     .prefetch_valid_o(prefetch_valid_o),
      //     .prefetch_addr_o (prefetch_addr_o)
      // );

      // Placeholder
      next_line_prefetcher #(
          .XLEN    (XLEN),
          .BLK_SIZE(BLK_SIZE)
      ) u_next_line_prefetcher (
          .clk_i           (clk_i),
          .rst_ni          (rst_ni),
          .flush_i         (flush_i),
          .cache_miss_i    (cache_miss_i),
          .miss_addr_i     (access_addr_i),
          .prefetch_ack_i  (prefetch_ack_i),
          .cache_busy_i    (cache_busy_i),
          .prefetch_valid_o(prefetch_valid_o),
          .prefetch_addr_o (prefetch_addr_o)
      );

      // ========================================================================
      // Type 4: Hybrid Prefetcher (TODO)
      // ========================================================================
    end else if (PREFETCH_TYPE == 4) begin : gen_hybrid

      // TODO: Implement hybrid prefetcher (Stride + Stream with arbiter)
      // Placeholder
      next_line_prefetcher #(
          .XLEN    (XLEN),
          .BLK_SIZE(BLK_SIZE)
      ) u_next_line_prefetcher (
          .clk_i           (clk_i),
          .rst_ni          (rst_ni),
          .flush_i         (flush_i),
          .cache_miss_i    (cache_miss_i),
          .miss_addr_i     (access_addr_i),
          .prefetch_ack_i  (prefetch_ack_i),
          .cache_busy_i    (cache_busy_i),
          .prefetch_valid_o(prefetch_valid_o),
          .prefetch_addr_o (prefetch_addr_o)
      );

      // ========================================================================
      // Default: No Prefetching
      // ========================================================================
    end else begin : gen_default

      assign prefetch_valid_o = 1'b0;
      assign prefetch_addr_o  = '0;

    end
  endgenerate

endmodule
