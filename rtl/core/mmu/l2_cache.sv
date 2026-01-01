/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps

/* verilator lint_off VARHIDDEN */
module l2_cache
  import ceres_param::*;
#(
    parameter CACHE_SIZE = 16384,                  // 16KB L2 cache
    parameter BLK_SIZE   = ceres_param::BLK_SIZE,
    parameter XLEN       = ceres_param::XLEN,
    parameter NUM_WAY    = 8                       // 8-way for L2
) (
    input  logic      clk_i,
    input  logic      rst_ni,
    input  logic      flush_i,
    input  lowX_req_t l1_req_i,   // Request from L1 (via arbiter)
    output lowX_res_t l1_res_o,   // Response to L1 (via arbiter)
    input  lowX_res_t mem_res_i,  // Response from memory (mem_res_i.ready = can accept request)
    output lowX_req_t mem_req_o   // Request to memory
);

  // COMMON SIGNALS & Parameters
  localparam NUM_SET = (CACHE_SIZE / BLK_SIZE) / NUM_WAY;
  localparam IDX_WIDTH = $clog2(NUM_SET) == 0 ? 1 : $clog2(NUM_SET);
  localparam BOFFSET = $clog2(BLK_SIZE / 8);
  localparam WOFFSET = $clog2(BLK_SIZE / 32);
  localparam TAG_SIZE = XLEN - IDX_WIDTH - BOFFSET;

  // Common registers and wires
  logic                      flush;
  logic      [IDX_WIDTH-1:0] flush_index;
  lowX_req_t                 cache_req_q;
  logic      [          3:0] cache_req_id_q;  // Latched request ID
  logic      [IDX_WIDTH-1:0] rd_idx;
  logic      [IDX_WIDTH-1:0] wr_idx;
  logic      [IDX_WIDTH-1:0] cache_idx;
  logic                      cache_miss;
  logic                      cache_hit;
  logic      [  NUM_WAY-2:0] updated_node;
  logic      [  NUM_WAY-1:0] cache_valid_vec;
  logic      [  NUM_WAY-1:0] cache_hit_vec;
  logic      [  NUM_WAY-1:0] evict_way;
  logic      [ BLK_SIZE-1:0] cache_select_data;
  logic      [  NUM_WAY-1:0] cache_wr_way;
  logic                      cache_wr_en;
  logic                      lookup_ack;

  // Shared memory structures
  typedef struct packed {
    logic [IDX_WIDTH-1:0]             idx;
    logic [NUM_WAY-1:0]               way;
    logic [BLK_SIZE-1:0]              wdata;
    logic [NUM_WAY-1:0][BLK_SIZE-1:0] rdata;
  } dsram_t;

  typedef struct packed {
    logic [IDX_WIDTH-1:0]           idx;
    logic [NUM_WAY-1:0]             way;
    logic [TAG_SIZE:0]              wtag;
    logic [NUM_WAY-1:0][TAG_SIZE:0] rtag;
  } tsram_t;

  typedef struct packed {
    logic [IDX_WIDTH-1:0] idx;
    logic                 rw_en;
    logic [NUM_WAY-2:0]   wnode;
    logic [NUM_WAY-2:0]   rnode;
  } nsram_t;

  dsram_t                    dsram;
  tsram_t                    tsram;
  nsram_t                    nsram;

  // Dirty bit array signals
  logic      [IDX_WIDTH-1:0] dirty_wr_idx;
  logic      [  NUM_WAY-1:0] dirty_wr_way;
  logic                      dirty_wr_en;
  logic                      dirty_wr_val;
  logic      [  NUM_WAY-1:0] dirty_read_vec;

  // Internal low-level request latch to hold writeback requests
  lowX_req_t                 lowx_req_q;
  logic                      lowx_req_valid_q;

  // Temporary variables to break combinatorial loops
  logic      [IDX_WIDTH-1:0] dirty_idx_temp;
  logic                      dirty_rw_en_temp;
  logic      [  NUM_WAY-1:0] dirty_way_temp;
  logic                      dirty_wdirty_temp;

  // L2 cache specific wires
  logic      [ BLK_SIZE-1:0] mask_data;
  logic                      data_array_wr_en;
  logic      [ BLK_SIZE-1:0] data_wr_pre;
  logic                      tag_array_wr_en;
  logic      [  WOFFSET-1:0] word_idx;
  logic                      write_back;
  logic      [ TAG_SIZE-1:0] evict_tag;
  logic      [ BLK_SIZE-1:0] evict_data;
  logic                      mem_res_id_match;  // Memory response ID matches expected ID
  logic                      mem_req_fire;
  logic                      mshr_alloc_fire;
  logic                      mshr_merge_fire;
  logic                      mshr_free_fire;
  logic                      fill_from_mshr;

  // ============================================================================
  // MSHR (Miss Status Holding Registers) for Non-Blocking Cache
  // ============================================================================
  // MSHR tracks outstanding cache misses and enables hit-under-miss operation
  localparam NUM_MSHR = 4;  // 4 outstanding misses per bank
  localparam MAX_REQ_PER_MSHR = 4;  // Max requests per MSHR entry (merged requests)
  localparam MSHR_IDX_WIDTH = $clog2(NUM_MSHR);

  // Response fanout state
  logic resp_active_q, resp_active_d;
  logic [MAX_REQ_PER_MSHR-1:0] resp_valid_q, resp_valid_d;
  logic [MAX_REQ_PER_MSHR-1:0][3:0] resp_ids_q, resp_ids_d;
  logic [                BLK_SIZE-1:0] resp_blk_q;
  logic [          MSHR_IDX_WIDTH-1:0] resp_entry_idx_q;
  logic [$clog2(MAX_REQ_PER_MSHR)-1:0] resp_pick_idx;
  logic                                resp_has_entry;
  logic                                resp_fire;
  logic                                resp_done_pulse;
  logic [               IDX_WIDTH-1:0] fill_idx_sel;
  logic [                TAG_SIZE-1:0] fill_tag_sel;
  logic [                 NUM_WAY-1:0] fill_way_sel;

  typedef struct packed {
    logic                             valid;          // Entry is valid
    logic [TAG_SIZE-1:0]              tag;            // Cache line tag
    logic [IDX_WIDTH-1:0]             index;          // Cache line index
    logic [NUM_WAY-1:0]               way;            // Selected way for fill
    logic [MAX_REQ_PER_MSHR-1:0][3:0] request_ids;    // All request IDs for this cache line
    logic [MAX_REQ_PER_MSHR-1:0]      request_valid;  // Which request IDs are valid
    logic                             is_write;       // Has write request
    logic                             mem_req_sent;   // Memory request sent
  } mshr_entry_t;

  mshr_entry_t [      NUM_MSHR-1:0] mshr;
  logic        [      NUM_MSHR-1:0] mshr_valid_vec;
  logic        [      NUM_MSHR-1:0] mshr_match_vec;
  logic        [      NUM_MSHR-1:0] mshr_alloc_vec;
  logic        [MSHR_IDX_WIDTH-1:0] mshr_alloc_idx;
  logic        [MSHR_IDX_WIDTH-1:0] mshr_match_idx;
  logic                             mshr_full;
  logic                             mshr_hit;
  logic                             mshr_can_accept;
  logic        [      NUM_MSHR-1:0] mshr_resp_vec;
  logic        [MSHR_IDX_WIDTH-1:0] mshr_resp_idx;
  logic                             mshr_has_resp;

  // ============================================================================
  // Cache Logger for MSHR Debugging
  // ============================================================================
`ifndef SYNTHESIS
  always_ff @(posedge clk_i) begin
    if (rst_ni) begin
      // Log L1 requests
      if (l1_req_i.ready && l1_req_i.valid) begin
        $display("[L2_CACHE] @%0t L1_REQ: id=%0d addr=0x%08x valid=%0b ready=%0b rw=%0b", $time, l1_req_i.id, l1_req_i.addr, l1_req_i.valid, l1_req_i.ready, l1_req_i.rw);
      end

      // Log cache hits/misses
      if (cache_req_q.valid) begin
        if (cache_hit) begin
          $display("[L2_CACHE] @%0t CACHE_HIT: id=%0d addr=0x%08x tag=0x%05x idx=%0d", $time, cache_req_id_q, cache_req_q.addr, cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET],
                   cache_req_q.addr[BOFFSET+:IDX_WIDTH]);
        end else if (cache_miss) begin
          $display("[L2_CACHE] @%0t CACHE_MISS: id=%0d addr=0x%08x tag=0x%05x idx=%0d", $time, cache_req_id_q, cache_req_q.addr, cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET],
                   cache_req_q.addr[BOFFSET+:IDX_WIDTH]);
        end
      end

      // MSHR debug logging
      if (mshr_alloc_fire) begin
        $display("[L2_CACHE][MSHR] @%0t ALLOC idx=%0d tag=0x%05x set=%0d id=%0d", $time, mshr_alloc_idx, cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET], cache_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET],
                 cache_req_id_q);
      end

      if (mshr_merge_fire) begin
        $display("[L2_CACHE][MSHR] @%0t MERGE idx=%0d tag=0x%05x set=%0d id=%0d", $time, mshr_match_idx, cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET], cache_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET],
                 cache_req_id_q);
      end

      if (mshr_free_fire) begin
        $display("[L2_CACHE][MSHR] @%0t FREE idx=%0d tag=0x%05x set=%0d resp_id=%0d", $time, mshr_resp_idx, mshr[mshr_resp_idx].tag, mshr[mshr_resp_idx].index, mem_res_i.id);
      end

      // Log memory requests
      if (mem_req_o.valid && mem_req_o.ready) begin
        $display("[L2_CACHE] @%0t MEM_REQ: id=%0d addr=0x%08x rw=%0b", $time, mem_req_o.id, mem_req_o.addr, mem_req_o.rw);
      end

      // Log memory responses
      if (mem_res_i.valid) begin
        $display("[L2_CACHE] @%0t MEM_RES: id=%0d blk=0x%064x id_match=%0b", $time, mem_res_i.id, mem_res_i.blk, mem_res_id_match);
      end

      // Log L1 responses
      if (l1_res_o.valid) begin
        $display("[L2_CACHE] @%0t L1_RES: blk=0x%064x", $time, l1_res_o.blk);
      end

      // Log writeback operations
      if (write_back) begin
        $display("[L2_CACHE] @%0t WRITEBACK: addr=0x%08x blk=0x%064x", $time, {evict_tag, cache_idx, {BOFFSET{1'b0}}}, evict_data);
      end
    end
  end
`endif

  // Request pipeline register with ID tracking
  // Non-blocking mode: once request is added to MSHR (alloc or merge), clear pipeline
  // IMPORTANT: Only accept new request when l1_res_o.ready is high (computed in comb block)
  logic can_accept_new_req;
  logic req_handled;  // Request was added to MSHR this cycle

  assign can_accept_new_req = !flush && !write_back && !resp_active_q && (!cache_req_q.valid || cache_hit || req_handled || (cache_miss && mem_res_i.valid && mem_res_id_match)) && mshr_can_accept;

  // Request is handled when it's added to MSHR (either alloc or merge)
  assign req_handled = mshr_alloc_fire || mshr_merge_fire;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      cache_req_q    <= '0;
      cache_req_id_q <= '0;
    end else begin
      if (cache_hit && cache_req_q.valid) begin
        // Cache hit - clear pipeline, ready for next request
        if (l1_req_i.valid && can_accept_new_req) begin
          cache_req_q    <= l1_req_i;
          cache_req_id_q <= l1_req_i.id;
        end else begin
          cache_req_q    <= '0;
          cache_req_id_q <= '0;
        end
      end else if (req_handled) begin
        // Request added to MSHR (alloc or merge) - clear pipeline
        if (l1_req_i.valid && can_accept_new_req) begin
          cache_req_q    <= l1_req_i;
          cache_req_id_q <= l1_req_i.id;
        end else begin
          cache_req_q    <= '0;
          cache_req_id_q <= '0;
        end
      end else if (cache_miss && cache_req_q.valid && !(mem_res_i.valid && mem_res_id_match)) begin
        // Cache miss pending and not yet added to MSHR - hold request
        cache_req_q    <= cache_req_q;
        cache_req_id_q <= cache_req_id_q;
      end else if (can_accept_new_req) begin
        // Ready to accept new request
        if (l1_req_i.valid) begin
          cache_req_q    <= l1_req_i;
          cache_req_id_q <= l1_req_i.id;
        end else begin
          // No new request, clear pipeline register
          cache_req_q    <= '0;
          cache_req_id_q <= '0;
        end
      end else begin
        // Not ready (flush, writeback, or response fanout active)
        // Hold current state
        cache_req_q    <= cache_req_q;
        cache_req_id_q <= cache_req_id_q;
      end
    end
  end

  // Flush logic
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      flush_index <= '0;
      flush       <= 1'b1;
    end else begin
      if (flush && flush_index != IDX_WIDTH'(NUM_SET - 1)) flush_index <= flush_index + 1'b1;
      else begin
        flush_index <= '0;
        flush       <= flush_i;
      end
    end
  end

  // Memory instantiation: Data and tag arrays
  for (genvar i = 0; i < NUM_WAY; i++) begin : data_array
    sp_bram #(
        .DATA_WIDTH(BLK_SIZE),
        .NUM_SETS  (NUM_SET)
    ) i_data_array (
        .clk    (clk_i),
        .chip_en(1'b1),
        .addr   (dsram.idx),
        .wr_en  (dsram.way[i]),
        .wr_data(dsram.wdata),
        .rd_data(dsram.rdata[i])
    );
  end

  for (genvar i = 0; i < NUM_WAY; i++) begin : tag_array
    sp_bram #(
        .DATA_WIDTH(TAG_SIZE + 1),
        .NUM_SETS  (NUM_SET)
    ) i_tag_array (
        .clk    (clk_i),
        .chip_en(1'b1),
        .addr   (tsram.idx),
        .wr_en  (tsram.way[i]),
        .wr_data(tsram.wtag),
        .rd_data(tsram.rtag[i])
    );
  end

  /* verilator lint_off UNOPTFLAT */
  sp_bram #(
      .DATA_WIDTH(NUM_WAY - 1),
      .NUM_SETS  (NUM_SET)
  ) i_node_array (
      .clk    (clk_i),
      .chip_en(1'b1),
      .addr   (nsram.idx),
      .wr_en  (nsram.rw_en),
      .wr_data(nsram.wnode),
      .rd_data(nsram.rnode)
  );
  /* verilator lint_on UNOPTFLAT */

  // ============================================================================
  // Dirty Array as Register Array (not SRAM)
  // ============================================================================
  logic [NUM_WAY-1:0] dirty_reg[NUM_SET];

  // Register-based dirty array write
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      for (int i = 0; i < NUM_SET; i++) dirty_reg[i] <= '0;
    end else begin
      for (int w = 0; w < NUM_WAY; w++) begin
        if (dirty_wr_way[w]) begin
          dirty_reg[dirty_wr_idx][w] <= dirty_wr_val;
        end
      end
    end
  end

  // PLRU logic
  always_comb begin
    updated_node = update_node(nsram.rnode, cache_wr_way);
    evict_way = compute_evict_way(nsram.rnode);
  end

  // Common tag and data selection logic
  always_comb begin
    for (int i = 0; i < NUM_WAY; i++) begin
      cache_valid_vec[i] = tsram.rtag[i][TAG_SIZE];
      cache_hit_vec[i]   = tsram.rtag[i][TAG_SIZE-1:0] == cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET];
    end

    cache_select_data = '0;
    for (int i = 0; i < NUM_WAY; i++) begin
      if (cache_hit_vec[i]) cache_select_data = dsram.rdata[i];
    end

    cache_miss = cache_req_q.valid && !flush && !(|(cache_valid_vec & cache_hit_vec));
    cache_hit = cache_req_q.valid && !flush && (|(cache_valid_vec & cache_hit_vec));

    rd_idx = cache_req_q.valid ? cache_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET] : l1_req_i.addr[IDX_WIDTH+BOFFSET-1:BOFFSET];
    wr_idx = flush ? flush_index : (cache_miss ? cache_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET] : rd_idx);

    // Check ID match for memory responses
    // Match against current request ID OR any MSHR entry request ID
    mem_res_id_match = (mem_res_i.id == cache_req_id_q) || mshr_has_resp;

    fill_from_mshr = mem_res_i.valid && mshr_has_resp;
    fill_idx_sel = fill_from_mshr ? mshr[mshr_resp_idx].index : rd_idx;
    fill_way_sel = fill_from_mshr ? mshr[mshr_resp_idx].way : (cache_hit ? cache_hit_vec : evict_way);
    fill_tag_sel = fill_from_mshr ? mshr[mshr_resp_idx].tag : cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET];

    cache_wr_en = (fill_from_mshr && !cache_req_q.uncached) || (cache_miss && mem_res_i.valid && mem_res_id_match && !cache_req_q.uncached) || flush;
    
    // During flush, use flush_index to iterate through all sets
    // Otherwise use fill_idx_sel for cache line fill or rd_idx for read
    cache_idx = flush ? flush_index : (cache_wr_en ? fill_idx_sel : rd_idx);

    cache_wr_way = fill_way_sel;
  end

  // L2 cache data masking and control signals
  always_comb begin
    mask_data   = cache_hit ? cache_select_data : mem_res_i.blk;
    data_wr_pre = mask_data;

    // L2 handles full cache line writes from L1
    if (cache_req_q.rw) begin
      data_wr_pre = cache_req_q.data;
    end

    word_idx = cache_req_q.addr[(WOFFSET+2)-1:2];

    dirty_idx_temp = cache_idx;
  end

  // Read dirty bits using the computed index
  always_comb begin
    dirty_read_vec = '0;

    for (int w = 0; w < NUM_WAY; w++) begin
      dirty_read_vec[w] = dirty_reg[dirty_idx_temp][w];
    end
  end

  // Compute write_back
  always_comb begin
    write_back = 1'b0;
    if (cache_miss) begin
      write_back = |(dirty_read_vec & evict_way & cache_valid_vec);
    end
    if (lowx_req_valid_q) write_back = 1'b1;
  end

  // Block data/tag array writes during writeback
  always_comb begin
    data_array_wr_en = ((cache_hit && cache_req_q.rw) || (cache_miss && mem_res_i.valid && mem_res_id_match && !cache_req_q.uncached)) && !write_back;
    tag_array_wr_en  = ((cache_hit && cache_req_q.rw) || (cache_miss && mem_res_i.valid && mem_res_id_match && !cache_req_q.uncached)) && !write_back;
  end

  // Dirty control signals
  always_comb begin
    dirty_wdirty_temp = (flush) ? '0 : (write_back ? '0 : (fill_from_mshr ? '0 : (cache_req_q.rw ? '1 : '0)));
    dirty_wr_val = dirty_wdirty_temp;

    dirty_rw_en_temp = ((cache_req_q.rw && (cache_hit || (cache_miss && mem_res_i.valid && mem_res_id_match))) ||
                      (write_back && mem_res_i.valid && mem_res_id_match) || (flush));
    dirty_wr_en  = dirty_rw_en_temp;

    dirty_wr_idx    = dirty_idx_temp;

    for (int i = 0; i < NUM_WAY; i++) begin
      dirty_way_temp[i] = (flush && !write_back) ? '1 : (cache_wr_way[i] && dirty_rw_en_temp);
      dirty_wr_way[i]   = dirty_way_temp[i];
    end
  end

  // Response fanout control from MSHR entries
  always_comb begin
    resp_pick_idx = '0;
    for (int i = 0; i < MAX_REQ_PER_MSHR; i++) begin
      if (resp_valid_q[i]) resp_pick_idx = i[$clog2(MAX_REQ_PER_MSHR)-1:0];
    end

    resp_has_entry  = |resp_valid_q;
    resp_valid_d    = resp_valid_q;
    resp_ids_d      = resp_ids_q;
    resp_active_d   = resp_active_q;
    resp_fire       = resp_active_q && resp_has_entry;  // ready is hardwired to 1 in resp path
    resp_done_pulse = 1'b0;

    if (resp_fire) begin
      resp_valid_d[resp_pick_idx] = 1'b0;
      if (resp_valid_d == '0) begin
        resp_active_d   = 1'b0;
        resp_done_pulse = 1'b1;
      end
    end
  end

  // nsram/tsram/dsram updates and evict selection
  always_comb begin
    nsram.rw_en = (flush) || data_array_wr_en;
    nsram.wnode = (flush) ? '0 : updated_node;
    nsram.idx   = cache_idx;

    tsram.way   = '0;
    tsram.idx   = cache_idx;
    tsram.wtag  = (flush) ? '0 : {1'b1, fill_tag_sel};
    for (int i = 0; i < NUM_WAY; i++) tsram.way[i] = (flush) ? '1 : (cache_wr_way[i] && tag_array_wr_en);

    dsram.way   = '0;
    dsram.idx   = cache_idx;
    dsram.wdata = cache_req_q.rw ? data_wr_pre : mem_res_i.blk;
    for (int i = 0; i < NUM_WAY; i++) dsram.way[i] = cache_wr_way[i] && data_array_wr_en;

    evict_tag  = '0;
    evict_data = '0;
    for (int i = 0; i < NUM_WAY; i++) begin
      if (evict_way[i]) begin
        evict_tag  = tsram.rtag[i][TAG_SIZE-1:0];
        evict_data = dsram.rdata[i];
      end
    end
  end

  // L2 cache response and request logic
  always_comb begin
    if (lowx_req_valid_q) begin
      // Hold previously latched writeback request
      mem_req_o = lowx_req_q;
    end else begin
      // Normal cache miss handling (includes writeback)
      // Only send memory request if:
      // - Cache miss AND
      // - NOT already in MSHR (no request merging case) AND
      // - Memory is ready
      mem_req_o.valid = cache_miss && !mshr_hit && mshr_can_accept && cache_req_q.valid;
      mem_req_o.ready = 1'b1;  // L2 always ready to receive memory response
      mem_req_o.uncached = write_back ? 1'b0 : cache_req_q.uncached;
      mem_req_o.addr = write_back ? {evict_tag, rd_idx, {BOFFSET{1'b0}}} : (cache_req_q.uncached ? cache_req_q.addr : {cache_req_q.addr[31:BOFFSET], {BOFFSET{1'b0}}});
      mem_req_o.rw = write_back ? 1'b1 : (cache_req_q.uncached ? cache_req_q.rw : 1'b0);
      mem_req_o.rw_size = write_back ? WORD : cache_req_q.rw_size;
      mem_req_o.data = write_back ? evict_data : (cache_req_q.uncached ? cache_req_q.data : '0);
      mem_req_o.id = cache_req_id_q;  // Pass through request ID
    end

    // Cache response priority: drain MSHR responses first, else normal path
    if (resp_active_q && resp_has_entry) begin
      l1_res_o.valid = 1'b1;
      l1_res_o.blk   = resp_blk_q;
      l1_res_o.id    = resp_ids_q[resp_pick_idx];
    end else begin
      l1_res_o.valid = !write_back && cache_req_q.valid && (cache_hit || (cache_miss && mem_res_i.valid && mem_res_id_match));
      l1_res_o.blk = (cache_miss && mem_res_i.valid && mem_res_id_match) ? mem_res_i.blk : cache_select_data;
      l1_res_o.id = mem_res_id_match ? mem_res_i.id : cache_req_id_q;  // Return the matched request ID
    end

    // l1_res_o.ready: Can L2 accept a NEW request from L1?
    // Must be 0 when:
    //   - Cache miss is pending (blocking mode)
    //   - MSHR is full (non-blocking mode but no space)
    //   - Writeback is in progress
    //   - Flush is in progress
    //   - Response fanout is draining MSHR entries
    l1_res_o.ready = !flush && !write_back && !resp_active_q && (!cache_req_q.valid || cache_hit || (cache_miss && mem_res_i.valid && mem_res_id_match)) && mshr_can_accept;
  end

  // Memory request handshake helper
  assign mem_req_fire = mem_req_o.valid && mem_res_i.ready;

  // MSHR event helpers
  assign mshr_alloc_fire = cache_miss && cache_req_q.valid && !mshr_hit && mshr_can_accept && mem_req_fire;
  assign mshr_merge_fire = cache_miss && cache_req_q.valid && mshr_hit;
  assign mshr_free_fire = resp_done_pulse;

  // Lookup acknowledgment logic
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      lookup_ack <= '0;
    end else begin
      lookup_ack <= (mem_res_i.valid && mem_res_id_match) ? !mem_req_o.ready : (!lookup_ack ? mem_req_o.valid && mem_res_i.ready : lookup_ack);
    end
  end

  // Response fanout state
  always_ff @(posedge clk_i) begin
    if (!rst_ni || flush_i) begin
      resp_active_q    <= 1'b0;
      resp_valid_q     <= '0;
      resp_ids_q       <= '0;
      resp_blk_q       <= '0;
      resp_entry_idx_q <= '0;
    end else if (mem_res_i.valid && mshr_has_resp) begin
      // Latch incoming memory response for the matching MSHR entry
      resp_active_q    <= 1'b1;
      resp_valid_q     <= mshr[mshr_resp_idx].request_valid;
      resp_ids_q       <= mshr[mshr_resp_idx].request_ids;
      resp_blk_q       <= mem_res_i.blk;
      resp_entry_idx_q <= mshr_resp_idx;
    end else begin
      resp_active_q    <= resp_active_d;
      resp_valid_q     <= resp_valid_d;
      resp_ids_q       <= resp_ids_d;
      resp_blk_q       <= resp_blk_q;
      resp_entry_idx_q <= resp_entry_idx_q;
    end
  end

  // Latch writeback requests
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      lowx_req_q <= '0;
      lowx_req_valid_q <= 1'b0;
    end else begin
      if (lowx_req_valid_q) begin
        if (mem_res_i.valid && mem_res_id_match) begin
          lowx_req_q <= '0;
          lowx_req_valid_q <= 1'b0;
        end else begin
          lowx_req_q <= lowx_req_q;
          lowx_req_valid_q <= 1'b1;
        end
      end else begin
        if (write_back && cache_miss && mem_res_i.ready) begin
          lowx_req_valid_q    <= 1'b1;
          lowx_req_q.valid    <= 1'b1;
          lowx_req_q.ready    <= 1'b1;
          lowx_req_q.addr     <= {evict_tag, rd_idx, {BOFFSET{1'b0}}};
          lowx_req_q.rw       <= 1'b1;
          lowx_req_q.rw_size  <= WORD;
          lowx_req_q.data     <= evict_data;
          lowx_req_q.uncached <= 1'b0;
        end else begin
          lowx_req_q <= '0;
          lowx_req_valid_q <= 1'b0;
        end
      end
    end
  end

  // ============================================================================
  // MSHR Management Logic
  // ============================================================================

  // MSHR valid vector
  always_comb begin
    for (int i = 0; i < NUM_MSHR; i++) begin
      mshr_valid_vec[i] = mshr[i].valid;
    end
  end

  // MSHR full check
  assign mshr_full = &mshr_valid_vec;
  assign mshr_can_accept = !mshr_full;

  // MSHR match check - does incoming request match existing MSHR entry?
  always_comb begin
    mshr_match_vec = '0;
    mshr_hit = 1'b0;
    mshr_match_idx = '0;

    for (int i = 0; i < NUM_MSHR; i++) begin
      if (mshr[i].valid && (mshr[i].tag == cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET]) && (mshr[i].index == cache_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET])) begin
        mshr_match_vec[i] = 1'b1;
        mshr_hit = 1'b1;
        mshr_match_idx = MSHR_IDX_WIDTH'(i);
      end
    end
  end

  // MSHR allocation - find first free entry
  always_comb begin
    mshr_alloc_vec = '0;
    mshr_alloc_idx = '0;

    for (int i = 0; i < NUM_MSHR; i++) begin
      if (!mshr[i].valid && mshr_alloc_vec == '0) begin
        mshr_alloc_vec[i] = 1'b1;
        mshr_alloc_idx = MSHR_IDX_WIDTH'(i);
      end
    end
  end

  // MSHR response detection - which entry matches incoming memory response ID?
  always_comb begin
    mshr_resp_vec = '0;
    mshr_resp_idx = '0;
    mshr_has_resp = 1'b0;

    for (int i = 0; i < NUM_MSHR; i++) begin
      if (mshr[i].valid) begin
        for (int j = 0; j < MAX_REQ_PER_MSHR; j++) begin
          if (mshr[i].request_valid[j] && (mshr[i].request_ids[j] == mem_res_i.id)) begin
            mshr_resp_vec[i] = 1'b1;
            mshr_resp_idx = MSHR_IDX_WIDTH'(i);
            mshr_has_resp = 1'b1;
          end
        end
      end
    end
  end

  // MSHR sequential logic - allocation and deallocation
  // NOTE: MSHR is currently disabled for blocking mode operation
  // In blocking mode, we wait for each miss to complete before accepting new requests
  always_ff @(posedge clk_i) begin
    if (!rst_ni || flush_i) begin
      for (int i = 0; i < NUM_MSHR; i++) begin
        mshr[i] <= '0;
      end
    end else begin
      // Default: hold state
      for (int i = 0; i < NUM_MSHR; i++) begin
        mshr[i] <= mshr[i];
      end

      // Free entry on matching memory response
      if (mshr_free_fire) begin
        mshr[resp_entry_idx_q] <= '0;
      end

      // Merge new request into existing MSHR entry
      if (mshr_merge_fire) begin
        logic merged;
        logic dup_id;
        merged = 1'b0;
        dup_id = 1'b0;

        mshr[mshr_match_idx].is_write <= mshr[mshr_match_idx].is_write | cache_req_q.rw;

        for (int j = 0; j < MAX_REQ_PER_MSHR; j++) begin
          if (mshr[mshr_match_idx].request_valid[j] && (mshr[mshr_match_idx].request_ids[j] == cache_req_id_q)) begin
            dup_id = 1'b1;
          end
        end

        for (int j = 0; j < MAX_REQ_PER_MSHR; j++) begin
          if (!merged && !dup_id && !mshr[mshr_match_idx].request_valid[j]) begin
            mshr[mshr_match_idx].request_ids[j]   <= cache_req_id_q;
            mshr[mshr_match_idx].request_valid[j] <= 1'b1;
            merged = 1'b1;
          end
        end
      end

      // Allocate new MSHR entry on miss
      if (mshr_alloc_fire) begin
        mshr[mshr_alloc_idx].valid            <= 1'b1;
        mshr[mshr_alloc_idx].tag              <= cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET];
        mshr[mshr_alloc_idx].index            <= cache_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET];
        mshr[mshr_alloc_idx].request_ids      <= '0;
        mshr[mshr_alloc_idx].request_valid    <= '0;
        mshr[mshr_alloc_idx].request_ids[0]   <= cache_req_id_q;
        mshr[mshr_alloc_idx].request_valid[0] <= 1'b1;
        mshr[mshr_alloc_idx].is_write         <= cache_req_q.rw;
        mshr[mshr_alloc_idx].mem_req_sent     <= 1'b1;
        mshr[mshr_alloc_idx].way              <= cache_wr_way;
      end
    end
  end

  // PLRU update function
  function automatic [NUM_WAY-2:0] update_node(input logic [NUM_WAY-2:0] node_in, input logic [NUM_WAY-1:0] hit_vec);
    logic [NUM_WAY-2:0] node_tmp;
    int unsigned idx_base, shift;
    node_tmp = node_in;
    for (int unsigned i = 0; i < NUM_WAY; i++) begin
      if (hit_vec[i]) begin
        for (int unsigned lvl = 0; lvl < $clog2(NUM_WAY); lvl++) begin
          idx_base = (2 ** lvl) - 1;
          shift = $clog2(NUM_WAY) - lvl;
          node_tmp[idx_base+(i>>shift)] = ((i >> (shift - 1)) & 1) == 0;
        end
      end
    end
    return node_tmp;
  endfunction

  // PLRU evict_way function
  function automatic [NUM_WAY-1:0] compute_evict_way(input logic [NUM_WAY-2:0] node_in);
    logic [NUM_WAY-1:0] way;
    int unsigned idx_base, shift;
    for (int unsigned i = 0; i < NUM_WAY; i++) begin
      logic en;
      en = 1'b1;
      for (int unsigned lvl = 0; lvl < $clog2(NUM_WAY); lvl++) begin
        idx_base = (2 ** lvl) - 1;
        shift = $clog2(NUM_WAY) - lvl;
        if (((i >> (shift - 1)) & 32'b1) == 32'b1) en &= node_in[idx_base+(i>>shift)];
        else en &= ~node_in[idx_base+(i>>shift)];
      end
      way[i] = en;
    end
    return way;
  endfunction

endmodule
