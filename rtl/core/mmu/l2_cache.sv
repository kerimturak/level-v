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
    parameter type lowX_res_t = logic,
    parameter type lowX_req_t = logic,
    parameter      CACHE_SIZE = 16384,                  // 16KB L2 cache
    parameter      BLK_SIZE   = ceres_param::BLK_SIZE,
    parameter      XLEN       = ceres_param::XLEN,
    parameter      NUM_WAY    = 8                       // 8-way for L2
) (
    input  logic      clk_i,
    input  logic      rst_ni,
    input  logic      flush_i,
    // Lower level interface (from memory arbiter)
    input  lowX_req_t l1_req_i,
    output lowX_res_t l1_res_o,
    // Memory interface (to main memory)
    input  lowX_res_t mem_res_i,
    output lowX_req_t mem_req_o
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

  // L2-specific wires
  logic      [ BLK_SIZE-1:0] data_wr_pre;
  logic                      data_array_wr_en;
  logic                      tag_array_wr_en;
  logic                      write_back;
  logic      [ TAG_SIZE-1:0] evict_tag;
  logic      [ BLK_SIZE-1:0] evict_data;

  // Request pipeline register
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      cache_req_q <= '0;
    end else begin
      if (cache_miss) begin
        // Only advance pipeline on valid response from memory
        if (!(mem_res_i.valid && !write_back) || !l1_req_i.ready) cache_req_q <= cache_req_q;
        else cache_req_q <= l1_req_i;
      end else begin
        if (!l1_req_i.ready) cache_req_q <= flush && flush_index != IDX_WIDTH'(NUM_SET - 1) ? '0 : cache_req_q;
        else cache_req_q <= flush && flush_index != IDX_WIDTH'(NUM_SET - 1) ? '0 : l1_req_i;
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
  // Dirty Array as Register Array
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
    wr_idx = flush ? flush_index : cache_miss ? cache_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET] : rd_idx;

    cache_wr_en = cache_miss && mem_res_i.valid || flush;
    cache_idx = cache_wr_en ? wr_idx : rd_idx;

    cache_wr_way = cache_hit ? cache_hit_vec : evict_way;
  end

  // L2 cache data control signals
  // FIRST: Compute control signals without reading dirty bits

  always_comb begin
    // Merge write data with existing cache line (like DCache)
    data_wr_pre = cache_hit ? cache_select_data : mem_res_i.data;

    case (cache_req_q.rw_size)
      WORD:    data_wr_pre[cache_req_q.addr[BOFFSET-1:2]*32+:32] = cache_req_q.data[31:0];
      HALF:    data_wr_pre[cache_req_q.addr[BOFFSET-1:1]*16+:16] = cache_req_q.data[15:0];
      BYTE:    data_wr_pre[cache_req_q.addr[BOFFSET-1:0]*8+:8] = cache_req_q.data[7:0];
      NO_SIZE: data_wr_pre = data_wr_pre;  // No change
    endcase

    // Compute index first (used for dirty read)
    dirty_idx_temp = cache_idx;
  end

  // SECOND: Read dirty bits using the computed index
  always_comb begin
    // Default to avoid X propagation
    dirty_read_vec = '0;

    for (int w = 0; w < NUM_WAY; w++) begin
      dirty_read_vec[w] = dirty_reg[dirty_idx_temp][w];
    end
  end

  // THIRD: Compute write_back and other signals using dirty bits
  // A) write_back decision
  always_comb begin
    write_back = 1'b0;
    if (cache_miss) begin
      write_back = |(dirty_read_vec & evict_way & cache_valid_vec);
    end
    if (lowx_req_valid_q) write_back = 1'b1;
  end

  // B) block data/tag array writes during writeback
  always_comb begin
    // Write to data array on: 1) cache hit write, 2) cache miss fill (not during writeback)
    data_array_wr_en = ((cache_hit && cache_req_q.rw) || (cache_miss && mem_res_i.valid && !cache_req_q.uncached)) && !write_back && !flush;
    // Write to tag array on: 1) cache hit write (to update LRU), 2) cache miss fill
    tag_array_wr_en  = ((cache_hit && cache_req_q.rw) || (cache_miss && mem_res_i.valid && !cache_req_q.uncached)) && !write_back && !flush;
  end

  // C) Dirty bit control signals
  always_comb begin
    // L2 cache: mark dirty on write requests from L1 (rw = 1 means write)
    dirty_wdirty_temp = (flush) ? '0 : (write_back ? 1'b0 : (cache_req_q.rw ? 1'b1 : 1'b0));
    dirty_wr_val = dirty_wdirty_temp;

    dirty_rw_en_temp = ((cache_req_q.rw && cache_hit) ||
                        (cache_miss && mem_res_i.valid) ||
                        (write_back && mem_res_i.valid)) || (flush);
    dirty_wr_en  = dirty_rw_en_temp;

    dirty_wr_idx    = dirty_idx_temp;

    for (int i = 0; i < NUM_WAY; i++) begin
      dirty_way_temp[i] = flush ? '1 : cache_wr_way[i] && dirty_rw_en_temp;
      dirty_wr_way[i]   = dirty_way_temp[i];
    end
  end

  // D) nsram/tsram/dsram updates and evict selection
  always_comb begin
    nsram.rw_en = (flush) || data_array_wr_en;
    nsram.wnode = (flush) ? '0 : updated_node;
    nsram.idx   = cache_idx;

    tsram.way   = '0;
    tsram.idx   = cache_idx;
    tsram.wtag  = (flush) ? '0 : {1'b1, cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET]};
    for (int i = 0; i < NUM_WAY; i++) tsram.way[i] = (flush) ? '1 : cache_wr_way[i] && tag_array_wr_en;

    dsram.way   = '0;
    dsram.idx   = cache_idx;
    dsram.wdata = cache_req_q.rw ? data_wr_pre : mem_res_i.data;
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
    // Priority: writeback > cache miss
    if (lowx_req_valid_q) begin
      // Hold previously latched writeback request
      mem_req_o = lowx_req_q;
    end else begin
      // Normal cache miss handling (includes writeback)
      mem_req_o.valid    = cache_miss && mem_res_i.ready;
      mem_req_o.ready    = 1'b1;
      mem_req_o.uncached = write_back ? 1'b0 : cache_req_q.uncached;
      mem_req_o.addr     = write_back ? {evict_tag, rd_idx, {BOFFSET{1'b0}}} : (cache_req_q.uncached ? cache_req_q.addr : {cache_req_q.addr[31:BOFFSET], {BOFFSET{1'b0}}});
      mem_req_o.rw       = write_back ? 1'b1 : cache_req_q.rw;
      mem_req_o.rw_size  = write_back ? WORD : cache_req_q.rw_size;
      mem_req_o.data     = write_back ? evict_data : BLK_SIZE'(cache_req_q.data);
    end

    // Cache response - match DCache logic exactly
    l1_res_o.valid = !write_back &&
                     (!cache_req_q.rw ? (cache_req_q.valid && (cache_hit || (cache_miss && mem_req_o.ready && mem_res_i.valid))) :
                                        (cache_req_q.valid && l1_req_i.ready && (cache_hit || (cache_miss && mem_req_o.ready && mem_res_i.valid))));
    l1_res_o.ready = !write_back && (!cache_req_q.rw ? ((!cache_miss || mem_res_i.valid) && !flush && !tag_array_wr_en) : (!tag_array_wr_en && mem_req_o.ready && mem_res_i.valid && !flush));
    l1_res_o.data = (cache_miss && mem_res_i.valid) ? mem_res_i.data : cache_select_data;
  end

  // Latch writeback requests
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      lowx_req_q <= '0;
      lowx_req_valid_q <= 1'b0;
    end else begin
      if (lowx_req_valid_q) begin
        // Waiting for memory response to clear saved request
        if (mem_res_i.valid) begin
          lowx_req_q <= '0;
          lowx_req_valid_q <= 1'b0;
        end else begin
          lowx_req_q <= lowx_req_q;
          lowx_req_valid_q <= 1'b1;
        end
      end else begin
        // Capture a new writeback request when it would be issued
        if (write_back && cache_miss && mem_res_i.ready) begin
          lowx_req_valid_q    <= 1'b1;
          lowx_req_q.valid    <= 1'b1;
          lowx_req_q.ready    <= 1'b1;
          lowx_req_q.addr     <= {evict_tag, rd_idx, {BOFFSET{1'b0}}};
          lowx_req_q.rw       <= 1'b1;  // Write operation
          lowx_req_q.rw_size  <= WORD;  // Full cache line
          lowx_req_q.uncached <= 1'b0;  // Cache line write
          lowx_req_q.data     <= evict_data;
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
