/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/

`timescale 1ns / 1ps

// ============================================================================
// Multi-Port L2 Cache Bank
// ============================================================================
// Wraps a single-ported L2 cache with request buffering to accept multiple
// requests per cycle and manage them through a single-ported cache core.
//
// Features:
//   - 2 request input ports (can accept 2 requests per cycle)
//   - Request queue with arbitration
//   - Single cache core (time-multiplexed)
//   - Response buffering for out-of-order completion
//   - 4 MSHR entries for tracking outstanding misses
// ============================================================================

module l2_bank_multiport
  import ceres_param::*;
#(
    parameter CACHE_SIZE = 8192,                   // 8KB per bank
    parameter BLK_SIZE   = ceres_param::BLK_SIZE,
    parameter XLEN       = ceres_param::XLEN,
    parameter NUM_WAY    = 8,
    parameter NUM_PORTS  = 2                       // Number of request ports
) (
    input  logic                      clk_i,
    input  logic                      rst_ni,
    input  logic                      flush_i,
    // Multiple request ports
    input  lowX_req_t [NUM_PORTS-1:0] req_i,
    output lowX_res_t [NUM_PORTS-1:0] res_o,
    // Single memory interface
    input  lowX_res_t                 mem_res_i,
    output lowX_req_t                 mem_req_o
);

  // ============================================================================
  // Request Queue
  // ============================================================================
  localparam QUEUE_DEPTH = 4;
  localparam QUEUE_PTR_WIDTH = $clog2(QUEUE_DEPTH);

  typedef struct packed {
    lowX_req_t req;
    logic [$clog2(NUM_PORTS)-1:0] port_id;  // Which port this came from
  } queue_entry_t;

  queue_entry_t [  QUEUE_DEPTH-1:0] req_queue;
  logic         [QUEUE_PTR_WIDTH:0] queue_head;  // Read pointer
  logic         [QUEUE_PTR_WIDTH:0] queue_tail;  // Write pointer
  logic         [QUEUE_PTR_WIDTH:0] queue_count;
  logic                             queue_full;
  logic                             queue_empty;
  logic                             req_pending;  // Request register has valid request

  assign queue_full  = (queue_count == QUEUE_DEPTH);
  assign queue_empty = (queue_count == 0);

  // ============================================================================
  // Request Arbitration and Queuing
  // ============================================================================
  logic [        NUM_PORTS-1:0] req_valid;
  logic [        NUM_PORTS-1:0] req_grant;
  logic [$clog2(NUM_PORTS)-1:0] grant_port;

  always_comb begin
    for (int i = 0; i < NUM_PORTS; i++) begin
      // IMPORTANT: Only check valid, NOT req_i[i].ready!
      // req_i.ready is L1's response buffer status (not relevant for request acceptance)
      // L2's readiness is indicated via res_o[i].ready output
      req_valid[i] = req_i[i].valid;
    end
  end

  // Priority encoder for request arbitration (port 0 has priority)
  always_comb begin
    req_grant  = '0;
    grant_port = '0;
    for (int i = 0; i < NUM_PORTS; i++) begin
      if (req_valid[i] && req_grant == '0) begin
        req_grant[i] = 1'b1;
        grant_port   = ($clog2(NUM_PORTS))'(i);
      end
    end
  end

  // Can accept up to 2 requests per cycle if queue has space
  // Queue acts as a buffer - we don't need to wait for cache core readiness
  logic [      NUM_PORTS-1:0] can_enqueue;
  logic [$clog2(NUM_PORTS):0] enqueue_count;

  // Cache ready comes from cache core's l1_res_o.ready signal (declare early for use below)
  logic                       cache_req_ready;

  always_comb begin
    can_enqueue   = '0;
    enqueue_count = 0;

    // Accept new requests if queue has space (cache readiness not required - queue buffers)
    // Try to enqueue up to NUM_PORTS requests
    for (int i = 0; i < NUM_PORTS; i++) begin
      if (req_valid[i] && !queue_full && (queue_count + enqueue_count < QUEUE_DEPTH)) begin
        can_enqueue[i] = 1'b1;
        enqueue_count  = enqueue_count + 1;
      end
    end
  end

  // Queue management
  always_ff @(posedge clk_i) begin
    if (!rst_ni || flush_i) begin
      queue_head  <= '0;
      queue_tail  <= '0;
      queue_count <= '0;
    end else begin
      logic [$clog2(NUM_PORTS):0] enq_cnt;
      logic                       deq;

      enq_cnt = 0;

      // Enqueue requests
      for (int i = 0; i < NUM_PORTS; i++) begin
        if (can_enqueue[i]) begin
          automatic logic [QUEUE_PTR_WIDTH:0] write_ptr = (queue_tail + enq_cnt) % QUEUE_DEPTH;
          req_queue[write_ptr].req <= req_i[i];
          req_queue[write_ptr].port_id <= ($clog2(NUM_PORTS))'(i);
          enq_cnt = enq_cnt + 1;
        end
      end

      // Dequeue from queue when we load a new request into the request register
      // This happens when: no pending request AND queue not empty
      deq = !req_pending && !queue_empty;

      // Update pointers
      if (enq_cnt > 0) begin
        queue_tail <= (queue_tail + enq_cnt) % QUEUE_DEPTH;
      end

      if (deq) begin
        queue_head <= (queue_head + 1) % QUEUE_DEPTH;
      end

      // Update count
      if (enq_cnt > 0 && deq) begin
        queue_count <= queue_count + enq_cnt - 1;
      end else if (enq_cnt > 0) begin
        queue_count <= queue_count + enq_cnt;
      end else if (deq) begin
        queue_count <= queue_count - 1;
      end
    end
  end

  // ============================================================================
  // Cache Core Interface
  // ============================================================================
  lowX_req_t                         cache_req;
  lowX_req_t                         cache_req_reg;  // Registered request to prevent resubmission
  lowX_res_t                         cache_res;
  logic      [$clog2(NUM_PORTS)-1:0] active_port_id;
  logic      [$clog2(NUM_PORTS)-1:0] active_port_id_reg;
  logic                              req_sent;  // Request was sent, waiting for response

  // Cache request handshake:
  // - When queue not empty and no pending request, load new request and send
  // - When response arrives (cache_res.valid), allow next request
  always_ff @(posedge clk_i) begin
    if (!rst_ni || flush_i) begin
      cache_req_reg <= '0;
      active_port_id_reg <= '0;
      req_pending <= 1'b0;
      req_sent <= 1'b0;
    end else begin
      // Clear req_sent when response arrives for our request
      // (Response routing happens in combinational block below)
      if (cache_res.valid) begin
        req_sent <= 1'b0;
      end

      // Load new request when previous one completed
      if (!req_pending && !queue_empty) begin
        // No pending request and queue has data - load new request
        cache_req_reg <= req_queue[queue_head].req;
        cache_req_reg.valid <= 1'b1;
        active_port_id_reg <= req_queue[queue_head].port_id;
        req_pending <= 1'b1;
      end else if (req_pending && !req_sent && cache_res.ready) begin
        // Request is pending and cache is ready - mark as sent
        req_sent <= 1'b1;
      end else if (req_pending && req_sent && cache_res.valid) begin
        // Response received - clear pending for next request
        req_pending <= 1'b0;
      end
    end
  end

  // Output to cache: only send valid when pending and not yet sent
  always_comb begin
    if (req_pending && !req_sent) begin
      cache_req = cache_req_reg;
      active_port_id = active_port_id_reg;
    end else begin
      cache_req = '0;
      active_port_id = '0;
    end
  end

  // Cache ready comes from cache core's l1_res_o.ready signal
  assign cache_req_ready = cache_res.ready;

  // ============================================================================
  // Single-Ported Cache Core
  // ============================================================================
  l2_cache #(
      .CACHE_SIZE(CACHE_SIZE),
      .BLK_SIZE  (BLK_SIZE),
      .XLEN      (XLEN),
      .NUM_WAY   (NUM_WAY)
  ) i_cache_core (
      .clk_i    (clk_i),
      .rst_ni   (rst_ni),
      .flush_i  (flush_i),
      .l1_req_i (cache_req),
      .l1_res_o (cache_res),
      .mem_res_i(mem_res_i),
      .mem_req_o(mem_req_o)
  );

  // ============================================================================
  // Response Routing
  // ============================================================================
  // Route response back to the port that made the request (tracked by ID)
  // Also propagate ready signal to indicate which ports can accept new requests

  always_comb begin
    // Initialize all port responses with proper ready signals
    for (int i = 0; i < NUM_PORTS; i++) begin
      res_o[i].valid = 1'b0;
      res_o[i].blk   = '0;
      res_o[i].id    = '0;
      // Ready signal: can this port accept new requests?
      // Queue acts as a buffer - if queue has space, we can accept
      // The cache core's busy state doesn't prevent queue entry
      res_o[i].ready = !queue_full;
    end

    // Route cache response to appropriate port based on request ID tracking
    // Simple routing: use MSB of ID to determine port
    // IDs 0x8-0xF go to port 0 (icache), 0x0-0x7 go to port 1 (dcache)
    if (cache_res.valid) begin
      automatic int target_port = cache_res.id[3] ? 0 : 1;
      if (target_port < NUM_PORTS) begin
        res_o[target_port].valid = cache_res.valid;
        res_o[target_port].blk   = cache_res.blk;
        res_o[target_port].id    = cache_res.id;
        // Keep ready signal as computed above
      end
    end
  end

endmodule
