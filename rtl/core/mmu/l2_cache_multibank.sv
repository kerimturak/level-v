/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/

`timescale 1ns / 1ps

// ============================================================================
// Multi-Bank L2 Cache with Non-Blocking Support
// ============================================================================
// This module implements a banked L2 cache that can handle multiple
// outstanding requests in parallel. Each bank operates independently
// and can serve hits while other banks handle misses.
//
// Architecture:
//   - 2 banks (interleaved by address bit)
//   - Each bank: 8KB, 8-way set associative
//   - Bank selection: addr[BOFFSET] - interleaved at cache line granularity
//   - Independent MSHR per bank (4 entries each)
//   - Response arbitration for fairness
//
// Features:
//   - Hit-under-miss: can serve hits while miss is outstanding
//   - Miss-under-miss: can handle multiple misses to different banks
//   - Request merging: multiple requests to same line merged
// ============================================================================

module l2_cache_multibank
  import ceres_param::*;
#(
    parameter CACHE_SIZE = 16384,                  // Total 16KB L2 cache
    parameter BLK_SIZE   = ceres_param::BLK_SIZE,
    parameter XLEN       = ceres_param::XLEN,
    parameter NUM_WAY    = 8,                      // 8-way per bank
    parameter NUM_BANKS  = 2                       // 2 banks
) (
    input  logic      clk_i,
    input  logic      rst_ni,
    input  logic      flush_i,
    input  lowX_req_t l1_req_i,   // Request from L1 (via arbiter)
    output lowX_res_t l1_res_o,   // Response to L1 (via arbiter)
    input  lowX_res_t mem_res_i,  // Response from memory
    output lowX_req_t mem_req_o   // Request to memory
);

  // ============================================================================
  // Parameters and Constants
  // ============================================================================
  localparam BANK_SIZE = CACHE_SIZE / NUM_BANKS;  // 8KB per bank
  localparam BOFFSET = $clog2(BLK_SIZE / 8);
  localparam BANK_SEL_BIT = BOFFSET;  // Use addr[BOFFSET] for bank selection

  // MSHR parameters
  localparam NUM_MSHR = 4;  // 4 MSHR entries per bank
  localparam MSHR_IDX_WIDTH = $clog2(NUM_MSHR);

  // ============================================================================
  // Bank Interfaces
  // ============================================================================
  lowX_req_t [NUM_BANKS-1:0] bank_req;
  lowX_res_t [NUM_BANKS-1:0] bank_res;

  // Memory interface from each bank
  lowX_req_t [NUM_BANKS-1:0] bank_mem_req;
  lowX_res_t [NUM_BANKS-1:0] bank_mem_res;

  // ============================================================================
  // Bank Selection Logic
  // ============================================================================
  logic [NUM_BANKS-1:0] bank_select;
  logic bank_id;

  assign bank_id = l1_req_i.addr[BANK_SEL_BIT];

  always_comb begin
    bank_select = '0;
    bank_select[bank_id] = l1_req_i.valid;
  end

  // Route request to selected bank
  always_comb begin
    for (int i = 0; i < NUM_BANKS; i++) begin
      bank_req[i] = l1_req_i;
      bank_req[i].valid = bank_select[i];
    end
  end

  // ============================================================================
  // Response Arbitration
  // ============================================================================
  // Round-robin arbiter for responses from banks
  logic [$clog2(NUM_BANKS):0] resp_bank_ptr;  // Extra bit to handle NUM_BANKS=2
  logic [NUM_BANKS-1:0] bank_has_response;

  always_comb begin
    for (int i = 0; i < NUM_BANKS; i++) begin
      bank_has_response[i] = bank_res[i].valid;
    end
  end

  // Priority encoder starting from resp_bank_ptr
  logic [NUM_BANKS-1:0] grant;
  logic any_grant;

  /* verilator lint_off WIDTHEXPAND */
  always_comb begin
    grant = '0;
    any_grant = 1'b0;

    // Try from current pointer to end
    for (int i = 0; i < NUM_BANKS; i++) begin
      automatic int idx = int'((resp_bank_ptr + i) % NUM_BANKS);
      if (bank_has_response[idx] && !any_grant) begin
        grant[idx] = 1'b1;
        any_grant = 1'b1;
      end
    end
  end
  /* verilator lint_on WIDTHEXPAND */

  // Update pointer on grant
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      resp_bank_ptr <= '0;
    end else if (any_grant) begin
      // Move to next bank after current grant
      for (int i = 0; i < NUM_BANKS; i++) begin
        if (grant[i]) begin
          resp_bank_ptr <= ($clog2(NUM_BANKS)+1)'((i + 1) % NUM_BANKS);
        end
      end
    end
  end

  // Mux response based on grant
  always_comb begin
    l1_res_o = '0;
    for (int i = 0; i < NUM_BANKS; i++) begin
      if (grant[i]) begin
        l1_res_o = bank_res[i];
      end
    end
  end

  // ============================================================================
  // Memory Request Arbitration
  // ============================================================================
  // Round-robin arbiter for memory requests from banks
  logic [$clog2(NUM_BANKS):0] mem_req_bank_ptr;  // Extra bit to handle NUM_BANKS=2
  logic [NUM_BANKS-1:0] bank_has_mem_req;

  always_comb begin
    for (int i = 0; i < NUM_BANKS; i++) begin
      bank_has_mem_req[i] = bank_mem_req[i].valid;
    end
  end

  logic [NUM_BANKS-1:0] mem_grant;
  logic any_mem_grant;

  /* verilator lint_off WIDTHEXPAND */
  always_comb begin
    mem_grant = '0;
    any_mem_grant = 1'b0;

    // Try from current pointer to end
    for (int i = 0; i < NUM_BANKS; i++) begin
      automatic int idx = int'((mem_req_bank_ptr + i) % NUM_BANKS);
      if (bank_has_mem_req[idx] && !any_mem_grant && mem_res_i.ready) begin
        mem_grant[idx] = 1'b1;
        any_mem_grant = 1'b1;
      end
    end
  end
  /* verilator lint_on WIDTHEXPAND */

  // Update pointer on grant
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      mem_req_bank_ptr <= '0;
    end else if (any_mem_grant) begin
      for (int i = 0; i < NUM_BANKS; i++) begin
        if (mem_grant[i]) begin
          mem_req_bank_ptr <= ($clog2(NUM_BANKS)+1)'((i + 1) % NUM_BANKS);
        end
      end
    end
  end

  // Mux memory request based on grant
  always_comb begin
    mem_req_o = '0;
    for (int i = 0; i < NUM_BANKS; i++) begin
      if (mem_grant[i]) begin
        mem_req_o = bank_mem_req[i];
      end
    end
  end

  // Route memory response to requesting bank based on ID or tracked state
  // For now, broadcast to all banks - each bank checks ID
  always_comb begin
    for (int i = 0; i < NUM_BANKS; i++) begin
      bank_mem_res[i] = mem_res_i;
    end
  end

  // ============================================================================
  // Bank Instances
  // ============================================================================
  generate
    for (genvar b = 0; b < NUM_BANKS; b++) begin : gen_banks
      l2_cache #(
          .CACHE_SIZE(BANK_SIZE),
          .BLK_SIZE  (BLK_SIZE),
          .XLEN      (XLEN),
          .NUM_WAY   (NUM_WAY)
      ) i_l2_bank (
          .clk_i     (clk_i),
          .rst_ni    (rst_ni),
          .flush_i   (flush_i),
          .l1_req_i  (bank_req[b]),
          .l1_res_o  (bank_res[b]),
          .mem_res_i (bank_mem_res[b]),
          .mem_req_o (bank_mem_req[b])
      );
    end
  endgenerate

endmodule
