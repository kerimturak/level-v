/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
Next-Line Prefetcher
================================================================================
Basit ve etkili bir prefetcher implementasyonu.
Cache miss olduğunda, bir sonraki cache line'ı proaktif olarak prefetch eder.

Özellikler:
  - Minimum alan kullanımı (~50 FF)
  - Sıralı erişim pattern'leri için optimize
  - %5-10 cache hit artışı beklenir
  - Tek cycle latency

Kullanım:
  - I-Cache veya D-Cache ile entegre edilebilir
  - Miss sinyali ile tetiklenir
  - Prefetch queue veya doğrudan memory arbiter'a bağlanır
================================================================================
*/
`timescale 1ns / 1ps

module next_line_prefetcher
  import ceres_param::*;
#(
    parameter int XLEN     = ceres_param::XLEN,
    parameter int BLK_SIZE = ceres_param::BLK_SIZE  // Cache line size in bits
) (
    input  logic            clk_i,
    input  logic            rst_ni,
    input  logic            flush_i,           // Pipeline flush
    input  logic            cache_miss_i,      // Cache miss occurred
    input  logic [XLEN-1:0] miss_addr_i,       // Address that missed
    input  logic            prefetch_ack_i,    // Prefetch request accepted
    input  logic            cache_busy_i,      // Cache is busy (don't prefetch)
    output logic            prefetch_valid_o,  // Prefetch request valid
    output logic [XLEN-1:0] prefetch_addr_o    // Prefetch address
);

  // ============================================================================
  // Local Parameters
  // ============================================================================
  localparam int LINE_BYTES = BLK_SIZE / 8;  // 16 bytes for 128-bit line
  localparam int OFFSET_BITS = $clog2(LINE_BYTES);

  // ============================================================================
  // State Machine
  // ============================================================================
  typedef enum logic [1:0] {
    IDLE,     // Waiting for miss
    PENDING,  // Prefetch request pending
    WAIT_ACK  // Waiting for acknowledgment
  } state_e;

  state_e state_q, state_d;

  // ============================================================================
  // Registers
  // ============================================================================
  logic [XLEN-1:0] prefetch_addr_q;
  logic [XLEN-1:0] last_miss_addr_q;  // Track last miss to avoid duplicate prefetch

  // ============================================================================
  // Next Line Address Calculation
  // ============================================================================
  // Cache line aligned, then add one line size
  logic [XLEN-1:0] next_line_addr;
  assign next_line_addr = {miss_addr_i[XLEN-1:OFFSET_BITS], {OFFSET_BITS{1'b0}}} + LINE_BYTES;

  // Check if this is a new miss (not same as last one)
  logic is_new_miss;
  assign is_new_miss = (miss_addr_i[XLEN-1:OFFSET_BITS] != last_miss_addr_q[XLEN-1:OFFSET_BITS]);

  // ============================================================================
  // Output Assignments
  // ============================================================================
  assign prefetch_valid_o = (state_q == PENDING) || (state_q == WAIT_ACK);
  assign prefetch_addr_o = prefetch_addr_q;

  // ============================================================================
  // Next State Logic
  // ============================================================================
  always_comb begin
    state_d = state_q;

    case (state_q)
      IDLE: begin
        // Wait for a cache miss
        if (cache_miss_i && is_new_miss && !cache_busy_i) begin
          state_d = PENDING;
        end
      end

      PENDING: begin
        // Request is out, waiting for accept or busy signal
        if (flush_i) begin
          state_d = IDLE;
        end else if (prefetch_ack_i) begin
          state_d = IDLE;  // Done, go back to idle
        end else if (cache_busy_i) begin
          state_d = WAIT_ACK;  // Cache became busy, wait
        end
      end

      WAIT_ACK: begin
        // Waiting for cache to become available
        if (flush_i) begin
          state_d = IDLE;
        end else if (!cache_busy_i) begin
          state_d = PENDING;  // Try again
        end
      end

      default: state_d = IDLE;
    endcase
  end

  // ============================================================================
  // Sequential Logic
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      state_q <= IDLE;
      prefetch_addr_q <= '0;
      last_miss_addr_q <= '0;
    end else if (flush_i) begin
      state_q <= IDLE;
      // Keep addresses for potential reuse
    end else begin
      state_q <= state_d;

      // Capture prefetch address on new miss
      if (cache_miss_i && is_new_miss && (state_q == IDLE) && !cache_busy_i) begin
        prefetch_addr_q  <= next_line_addr;
        last_miss_addr_q <= miss_addr_i;
      end
    end
  end

  // ============================================================================
  // Assertions
  // ============================================================================
`ifndef SYNTHESIS
  // Prefetch address should always be cache-line aligned
  assert property (@(posedge clk_i) disable iff (!rst_ni) prefetch_valid_o |-> (prefetch_addr_o[OFFSET_BITS-1:0] == '0))
  else $error("Prefetch address not cache-line aligned!");

  // No prefetch during flush
  assert property (@(posedge clk_i) disable iff (!rst_ni) flush_i |=> !prefetch_valid_o)
  else $error("Prefetch should be cancelled on flush!");

  // State should not be unknown
  assert property (@(posedge clk_i) disable iff (!rst_ni) !$isunknown(state_q))
  else $error("State is unknown!");
`endif

endmodule
