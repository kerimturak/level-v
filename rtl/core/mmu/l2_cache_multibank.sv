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
    parameter NUM_BANKS  = 2,                      // 2 banks
    parameter NUM_L1_PORTS = 2                     // 2 L1 ports (icache + dcache)
) (
    input  logic      clk_i,
    input  logic      rst_ni,
    input  logic      flush_i,
    // Multiple L1 request ports (from icache and dcache)
    input  lowX_req_t [NUM_L1_PORTS-1:0] l1_req_i,
    output lowX_res_t [NUM_L1_PORTS-1:0] l1_res_o,
    // Single memory interface
    input  lowX_res_t mem_res_i,
    output lowX_req_t mem_req_o
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
  localparam NUM_PORTS_PER_BANK = 2;  // Each bank has 2 request ports

  lowX_req_t [NUM_BANKS-1:0][NUM_PORTS_PER_BANK-1:0] bank_req;
  lowX_res_t [NUM_BANKS-1:0][NUM_PORTS_PER_BANK-1:0] bank_res;

  // Memory interface from each bank
  lowX_req_t [NUM_BANKS-1:0] bank_mem_req;
  lowX_res_t [NUM_BANKS-1:0] bank_mem_res;

  // ============================================================================
  // Bank Selection and Request Routing
  // ============================================================================
  // Route each L1 request to appropriate bank based on address
  // Each bank can receive requests from multiple L1 ports simultaneously

  always_comb begin
    // Initialize all bank ports
    for (int b = 0; b < NUM_BANKS; b++) begin
      for (int p = 0; p < NUM_PORTS_PER_BANK; p++) begin
        bank_req[b][p] = '0;
      end
    end

    // Simple routing: L1 port N goes to bank port N
    // Bank selection is based on address bit
    for (int l1_port = 0; l1_port < NUM_L1_PORTS; l1_port++) begin
      automatic int target_bank = l1_req_i[l1_port].valid ?
                                  int'(l1_req_i[l1_port].addr[BANK_SEL_BIT]) : 0;
      if (target_bank < NUM_BANKS && l1_port < NUM_PORTS_PER_BANK) begin
        bank_req[target_bank][l1_port] = l1_req_i[l1_port];
      end
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
      bank_has_response[i] = bank_res[i][0].valid || bank_res[i][1].valid;
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

  // Mux responses back to L1 ports
  // Simple routing: bank port N goes back to L1 port N
  // Responses from both banks for the same L1 port need arbitration
  always_comb begin
    // Initialize L1 responses - ready=1 means L2 can accept requests
    for (int l1_port = 0; l1_port < NUM_L1_PORTS; l1_port++) begin
      l1_res_o[l1_port] = '0;
      l1_res_o[l1_port].ready = 1'b1;  // L2 is always ready to accept requests (has internal buffering)
    end

    // Collect responses from all banks
    // Priority: bank 0 has priority over bank 1 for each L1 port
    for (int l1_port = 0; l1_port < NUM_L1_PORTS; l1_port++) begin
      if (l1_port < NUM_PORTS_PER_BANK) begin
        // Check bank 0 first
        if (bank_res[0][l1_port].valid) begin
          l1_res_o[l1_port] = bank_res[0][l1_port];
        end
        // Then bank 1 (if bank 0 doesn't have response)
        else if (bank_res[1][l1_port].valid) begin
          l1_res_o[l1_port] = bank_res[1][l1_port];
        end
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
  // Bank Instances (Multi-Ported)
  // ============================================================================
  generate
    for (genvar b = 0; b < NUM_BANKS; b++) begin : gen_banks
      l2_bank_multiport #(
          .CACHE_SIZE(BANK_SIZE),
          .BLK_SIZE  (BLK_SIZE),
          .XLEN      (XLEN),
          .NUM_WAY   (NUM_WAY),
          .NUM_PORTS (NUM_PORTS_PER_BANK)
      ) i_l2_bank (
          .clk_i     (clk_i),
          .rst_ni    (rst_ni),
          .flush_i   (flush_i),
          .req_i     (bank_req[b]),
          .res_o     (bank_res[b]),
          .mem_res_i (bank_mem_res[b]),
          .mem_req_o (bank_mem_req[b])
      );
    end
  endgenerate

endmodule
