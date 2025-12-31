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
    input  lowX_res_t mem_res_i,  // Response from memory
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

  // Request pipeline register with ID tracking
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      cache_req_q    <= '0;
      cache_req_id_q <= '0;
    end else begin
      if (cache_miss) begin
        if (!(mem_res_i.valid && !write_back) || !l1_req_i.ready) begin
          cache_req_q    <= cache_req_q;
          cache_req_id_q <= cache_req_id_q;
        end else begin
          cache_req_q    <= l1_req_i;
          cache_req_id_q <= l1_req_i.id;
        end
      end else begin
        // Cache HIT: update request register
        if (!l1_req_i.ready) begin
          // No new request: clear old request to prevent stale response
          cache_req_q    <= flush && flush_index != IDX_WIDTH'(NUM_SET - 1) ? '0 : '0;
          cache_req_id_q <= '0;
        end else begin
          // New request available
          cache_req_q    <= flush && flush_index != IDX_WIDTH'(NUM_SET - 1) ? '0 : l1_req_i;
          cache_req_id_q <= flush && flush_index != IDX_WIDTH'(NUM_SET - 1) ? '0 : l1_req_i.id;
        end
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

    cache_wr_en = (cache_miss && mem_res_i.valid && !cache_req_q.uncached) || flush;
    cache_idx = cache_wr_en ? wr_idx : rd_idx;

    cache_wr_way = cache_hit ? cache_hit_vec : evict_way;
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
    data_array_wr_en = ((cache_hit && cache_req_q.rw) || (cache_miss && mem_res_i.valid && !cache_req_q.uncached)) && !write_back;
    tag_array_wr_en  = ((cache_hit && cache_req_q.rw) || (cache_miss && mem_res_i.valid && !cache_req_q.uncached)) && !write_back;
  end

  // Dirty control signals
  always_comb begin
    dirty_wdirty_temp = (flush) ? '0 : (write_back ? '0 : (cache_req_q.rw ? '1 : '0));
    dirty_wr_val = dirty_wdirty_temp;

    dirty_rw_en_temp = ((cache_req_q.rw && (cache_hit || (cache_miss && mem_res_i.valid))) ||
                      (write_back && mem_res_i.valid) || (flush));
    dirty_wr_en  = dirty_rw_en_temp;

    dirty_wr_idx    = dirty_idx_temp;

    for (int i = 0; i < NUM_WAY; i++) begin
      dirty_way_temp[i] = (flush && !write_back) ? '1 : (cache_wr_way[i] && dirty_rw_en_temp);
      dirty_wr_way[i]   = dirty_way_temp[i];
    end
  end

  // nsram/tsram/dsram updates and evict selection
  always_comb begin
    nsram.rw_en = (flush) || data_array_wr_en;
    nsram.wnode = (flush) ? '0 : updated_node;
    nsram.idx   = cache_idx;

    tsram.way   = '0;
    tsram.idx   = cache_idx;
    tsram.wtag  = (flush) ? '0 : {1'b1, cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET]};
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
      mem_req_o.valid = cache_miss && mem_res_i.ready;
      mem_req_o.ready = 1'b1;
      mem_req_o.uncached = write_back ? 1'b0 : cache_req_q.uncached;
      mem_req_o.addr = write_back ? {evict_tag, rd_idx, {BOFFSET{1'b0}}} : (cache_req_q.uncached ? cache_req_q.addr : {cache_req_q.addr[31:BOFFSET], {BOFFSET{1'b0}}});
      mem_req_o.rw = write_back ? 1'b1 : (cache_req_q.uncached ? cache_req_q.rw : 1'b0);
      mem_req_o.rw_size = write_back ? WORD : cache_req_q.rw_size;
      mem_req_o.data = write_back ? evict_data : (cache_req_q.uncached ? cache_req_q.data : '0);
      mem_req_o.id = cache_req_id_q;  // Pass through request ID
    end

    // Cache response with ID matching to prevent stale responses
    // Only respond if current L1 request ID matches the latched request ID
    l1_res_o.valid   = !write_back && (l1_req_i.id == cache_req_id_q) &&
                          (!cache_req_q.rw ? (cache_req_q.valid && (cache_hit || (cache_miss && mem_req_o.ready && mem_res_i.valid))) :
                                             (cache_req_q.valid && l1_req_i.ready && (cache_hit || (cache_miss && mem_req_o.ready && mem_res_i.valid))));
    l1_res_o.ready = !write_back && (l1_req_i.id == cache_req_id_q) && (!cache_req_q.rw ? ((!cache_miss || mem_res_i.valid) && !flush && !tag_array_wr_en) : (!tag_array_wr_en && mem_req_o.ready && mem_res_i.valid && !flush));
    l1_res_o.blk = (cache_miss && mem_res_i.valid) ? mem_res_i.blk : cache_select_data;
    l1_res_o.id  = cache_req_id_q;  // Return the request ID
  end

  // Lookup acknowledgment logic
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      lookup_ack <= '0;
    end else begin
      lookup_ack <= mem_res_i.valid ? !mem_req_o.ready : (!lookup_ack ? mem_req_o.valid && mem_res_i.ready : lookup_ack);
    end
  end

  // Latch writeback requests
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      lowx_req_q <= '0;
      lowx_req_valid_q <= 1'b0;
    end else begin
      if (lowx_req_valid_q) begin
        if (mem_res_i.valid) begin
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
