`timescale 1ns / 1ps
`include "level_defines.svh"

// ============================================================================
// Cache Request/Response Logger — table-formatted debug output
// ============================================================================
// This module logs requests into the unified cache and returning responses
// in a readable table format.
//
// Usage:
//   make run LOG_CACHE=1  or  make verilate LOG_CACHE=1
// ============================================================================

module cache_logger
  import level_param::*;
(
    input logic        clk_i,
    input logic        rst_ni,
    input dcache_req_t cache_req_i,
    input dcache_res_t cache_res_i
);

  // Header-printed flag
  logic header_printed;

  // Check cache activity each clock cycle
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      header_printed <= 1'b0;
    end else begin
      // Print header on first activity
      if (!header_printed && (cache_req_i.valid || cache_res_i.valid)) begin
        $display(
            "\n╔════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╗");
        $display("║                                         CACHE TRANSACTION LOG                                                      ║");
        $display(
            "╠═════════╦═══════════╦════════════╦═════════╦═════════╦═══════════════╦═════════════════════════════════════════════╣");
        $display("║  Time   ║    REQ    ║  Address   ║  Op     ║  Size   ║  Write Data   ║                RESPONSE                     ║");
        $display("║   (ns)  ║  Valid    ║   (hex)    ║ (R/W)   ║ (bytes) ║     (hex)     ║  Valid  │  Miss  │  Ready  │   Read Data    ║");
        $display(
            "╠═════════╬═══════════╬════════════╬═════════╬═════════╬═══════════════╬═════════╪════════╪═════════╪════════════════╣");
        header_printed <= 1'b1;
      end

      // Request monitoring
      if (cache_req_i.valid) begin
        string op_str;
        string size_str;
        string uncached_str;
        int    size_bytes;

        // Operation type
        op_str = cache_req_i.rw ? "WRITE " : "READ  ";

        // Size decoding
        case (cache_req_i.rw_size)
          BYTE: begin
            size_str   = "1B  ";
            size_bytes = 1;
          end
          HALF: begin
            size_str   = "2B  ";
            size_bytes = 2;
          end
          WORD: begin
            size_str   = "4B  ";
            size_bytes = 4;
          end
          default: begin
            size_str   = "???";
            size_bytes = 0;
          end
        endcase

        // Uncached flag
        uncached_str = cache_req_i.uncached ? "[UC]" : "    ";

        // Print request info
        if (cache_req_i.rw) begin
          // Write operation - show write data
          $display("║ %7t ║     1     ║ 0x%08h ║ %s  ║  %s   ║  0x%08h   ║    -    │   -    │    -    │        -       ║", $time, cache_req_i.addr, op_str, size_str,
                   cache_req_i.data);
        end else begin
          // Read operation - no write data
          $display("║ %7t ║     1     ║ 0x%08h ║ %s  ║  %s   ║       -       ║    -    │   -    │    -    │        -       ║", $time, cache_req_i.addr, op_str, size_str);
        end

        if (cache_req_i.uncached) begin
          $display("║         ║           ║            ║ [UNCACHED ACCESS]                                                                ║");
        end
      end

      // Response monitoring
      if (cache_res_i.valid) begin
        string miss_str;
        string ready_str;

        miss_str  = cache_res_i.miss ? " MISS " : " HIT  ";
        ready_str = cache_res_i.ready ? "  YES  " : "  NO   ";

        // Print response info
        $display("║ %7t ║     -     ║     -      ║    -    ║    -    ║       -       ║    1    │ %s │ %s │  0x%08h    ║", $time, miss_str, ready_str, cache_res_i.data);
      end

      // Separator every 10 transactions for readability
      // (optional — remove this block if undesired)
    end
  end

  // Print footer at end of simulation
  final begin
    if (header_printed) begin
      $display(
          "╚═════════╩═══════════╩════════════╩═════════╩═════════╩═══════════════╩═════════╧════════╧═════════╧══════════════════╝");
      $display("");
    end
  end


endmodule
