/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/

`timescale 1ns / 1ps
`include "ceres_defines.svh"
import ceres_param::*;

// ============================================================================
// Memory Arbiter - Pass-Through for Multi-Port L2
// ============================================================================
// Since L2 now has multiple ports (one for icache, one for dcache),
// the arbiter simply forwards requests and responses without arbitration.
//
// Port mapping:
//   - L2 Port 0: ICache requests/responses
//   - L2 Port 1: DCache requests/responses
// ============================================================================

module memory_arbiter (
    input logic clk_i,
    input logic rst_ni,
    input ilowX_req_t icache_req_i,
    input dlowX_req_t dcache_req_i,
    output ilowX_res_t icache_res_o,
    output dlowX_res_t dcache_res_o,
    // Multi-port L2 interface (2 ports)
    input lowX_res_t [1:0] l2_res_i,  // Responses from L2 cache (port 0: icache, port 1: dcache)
    output lowX_req_t [1:0] l2_req_o  // Requests to L2 cache (port 0: icache, port 1: dcache)
);

  // ============================================================================
  // Request Forwarding
  // ============================================================================
  // Forward requests to L2, but respect L2's ready signal
  // IMPORTANT: The 'ready' field in l2_req_o is NOT used by L2 as input!
  // L2 uses l1_res_o.ready as output to indicate it can accept requests.
  // The l1_req_i.ready from caches is used by them to indicate their buffer status.

  // Forward icache request to L2 port 0
  always_comb begin
    l2_req_o[0].valid    = icache_req_i.valid;
    l2_req_o[0].ready    = l2_res_i[0].ready;  // Feedback from L2 (not used, but keep consistent)
    l2_req_o[0].addr     = icache_req_i.addr;
    l2_req_o[0].uncached = icache_req_i.uncached;
    l2_req_o[0].id       = icache_req_i.id;
    l2_req_o[0].rw       = 1'b0;  // ICache always reads
    l2_req_o[0].rw_size  = NO_SIZE;
    l2_req_o[0].data     = '0;
  end

  // Forward dcache request to L2 port 1
  always_comb begin
    l2_req_o[1].valid    = dcache_req_i.valid;
    l2_req_o[1].ready    = l2_res_i[1].ready;  // Feedback from L2 (not used, but keep consistent)
    l2_req_o[1].addr     = dcache_req_i.addr;
    l2_req_o[1].uncached = dcache_req_i.uncached;
    l2_req_o[1].id       = dcache_req_i.id;
    l2_req_o[1].rw       = dcache_req_i.rw;
    l2_req_o[1].rw_size  = dcache_req_i.rw_size;
    l2_req_o[1].data     = dcache_req_i.data;
  end

  // ============================================================================
  // Response Forwarding
  // ============================================================================
  // Forward L2 responses back to L1 caches
  // CRITICAL: The 'ready' signal from L2 tells L1 caches whether they can send new requests

  // Forward L2 port 0 response to icache
  always_comb begin
    icache_res_o.valid = l2_res_i[0].valid;
    icache_res_o.ready = l2_res_i[0].ready;  // From L2: can L1 send new requests?
    icache_res_o.blk   = l2_res_i[0].blk;
    icache_res_o.id    = l2_res_i[0].id;
  end

  // Forward L2 port 1 response to dcache
  always_comb begin
    dcache_res_o.valid = l2_res_i[1].valid;
    dcache_res_o.ready = l2_res_i[1].ready;  // From L2: can L1 send new requests?
    dcache_res_o.data  = l2_res_i[1].blk;
    dcache_res_o.id    = l2_res_i[1].id;
  end

endmodule
