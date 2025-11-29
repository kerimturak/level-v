/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
/* verilator lint_off VARHIDDEN */
module cache
  import ceres_param::*;
#(
    parameter      IS_ICACHE   = 1,                      // When 1, behave like an icache; when 0, behave like a dcache.
    parameter type cache_req_t = logic,
    parameter type cache_res_t = logic,
    parameter type lowX_res_t  = logic,
    parameter type lowX_req_t  = logic,
    parameter      CACHE_SIZE  = 1024,
    parameter      BLK_SIZE    = ceres_param::BLK_SIZE,
    parameter      XLEN        = ceres_param::XLEN,
    parameter      NUM_WAY     = 4
) (
    input  logic       clk_i,
    input  logic       rst_ni,
    input  logic       flush_i,
    input  cache_req_t cache_req_i,
    output cache_res_t cache_res_o,
    input  lowX_res_t  lowX_res_i,
    output lowX_req_t  lowX_req_o
);

  // COMMON SIGNALS & Parameters
  localparam NUM_SET = (CACHE_SIZE / BLK_SIZE) / NUM_WAY;
  localparam IDX_WIDTH = $clog2(NUM_SET) == 0 ? 1 : $clog2(NUM_SET);
  localparam BOFFSET = $clog2(BLK_SIZE / 8);
  localparam WOFFSET = $clog2(BLK_SIZE / 32);
  localparam TAG_SIZE = XLEN - IDX_WIDTH - BOFFSET;

  // Common registers and wires
  logic                       flush;
  logic       [IDX_WIDTH-1:0] flush_index;
  cache_req_t                 cache_req_q;
  logic       [IDX_WIDTH-1:0] rd_idx;
  logic       [IDX_WIDTH-1:0] wr_idx;
  logic       [IDX_WIDTH-1:0] cache_idx;
  logic                       cache_miss;
  logic                       cache_hit;
  logic       [  NUM_WAY-2:0] updated_node;
  logic       [  NUM_WAY-1:0] cache_valid_vec;
  logic       [  NUM_WAY-1:0] cache_hit_vec;
  logic       [  NUM_WAY-1:0] evict_way;
  logic       [ BLK_SIZE-1:0] cache_select_data;
  logic       [  NUM_WAY-1:0] cache_wr_way;
  logic                       cache_wr_en;
  logic                       lookup_ack;

  // Shared memory structures (used by both caches)
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

  dsram_t dsram;
  tsram_t tsram;
  nsram_t nsram;

  typedef struct packed {
    logic [IDX_WIDTH-1:0] idx;
    logic [NUM_WAY-1:0]   way;
    logic                 rw_en;
    logic                 wdirty;
    logic [NUM_WAY-1:0]   rdirty;
  } drsram_t;

  drsram_t                drsram;

  // Additional wires for dcache writeback, mask data, etc.
  logic    [BLK_SIZE-1:0] mask_data;
  logic                   data_array_wr_en;
  logic    [BLK_SIZE-1:0] data_wr_pre;
  logic                   tag_array_wr_en;
  logic    [ WOFFSET-1:0] word_idx;
  logic                   write_back;
  logic    [TAG_SIZE-1:0] evict_tag;
  logic    [BLK_SIZE-1:0] evict_data;

  // Common non-memory logic (same for both caches)
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      cache_req_q <= '0;
    end else begin
      if (cache_miss) begin
        if (!lowX_res_i.valid || !cache_req_i.ready) cache_req_q <= cache_req_q;
        else cache_req_q <= cache_req_i;
      end else begin
        if (!cache_req_i.ready) cache_req_q <= flush && flush_index != IDX_WIDTH'(NUM_SET - 1) ? '0 : cache_req_q;
        else cache_req_q <= flush && flush_index != IDX_WIDTH'(NUM_SET - 1) ? '0 : cache_req_i;
      end
    end
  end

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

  // Memory instantiation: Data and tag arrays as common blocks.
  for (genvar i = 0; i < NUM_WAY; i++) begin : data_array
    sp_bram #(
        .DATA_WIDTH(BLK_SIZE),
        .NUM_SETS  (NUM_SET)
    ) data_array (
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
    ) tag_array (
        .clk    (clk_i),
        .chip_en(1'b1),
        .addr   (tsram.idx),
        .wr_en  (tsram.way[i]),
        .wr_data(tsram.wtag),
        .rd_data(tsram.rtag[i])
    );
  end

  sp_bram #(
      .DATA_WIDTH(NUM_WAY - 1),
      .NUM_SETS  (NUM_SET)
  ) node_array (
      .clk    (clk_i),
      .chip_en(1'b1),
      .addr   (nsram.idx),
      .wr_en  (nsram.rw_en),
      .wr_data(nsram.wnode),
      .rd_data(nsram.rnode)
  );

  // PLRU functions (assume update_node and compute_evict_way are defined elsewhere)
  always_comb begin
    updated_node = update_node(nsram.rnode, cache_wr_way);
    evict_way    = compute_evict_way(nsram.rnode);
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

    rd_idx = cache_req_q.valid ? cache_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET] : cache_req_i.addr[IDX_WIDTH+BOFFSET-1:BOFFSET];
    wr_idx = flush ? flush_index : (cache_miss ? cache_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET] : rd_idx);

    cache_wr_en = (cache_miss && lowX_res_i.valid && !cache_req_q.uncached) || flush;
    cache_idx = cache_wr_en ? wr_idx : rd_idx;

    // Select the write way: if there's a hit use the hit vector; else, choose the eviction way.
    cache_wr_way = cache_hit ? cache_hit_vec : evict_way;
  end

  // Generate different behavior for i-cache versus d-cache.

  if (IS_ICACHE) begin : icache_impl
    always_comb begin
      nsram.rw_en = cache_wr_en || cache_hit;
      nsram.wnode = flush ? '0 : updated_node;
      nsram.idx   = cache_idx;

      tsram.way   = '0;
      tsram.idx   = cache_idx;
      tsram.wtag  = flush ? '0 : {1'b1, cache_req_q.addr[XLEN-1 : IDX_WIDTH+BOFFSET]};
      for (int i = 0; i < NUM_WAY; i++) tsram.way[i] = flush ? '1 : cache_wr_way[i] && cache_wr_en;

      dsram.way   = '0;
      dsram.idx   = cache_idx;
      dsram.wdata = lowX_res_i.blk;
      for (int i = 0; i < NUM_WAY; i++) dsram.way[i] = cache_wr_way[i] && cache_wr_en;
    end

    // For i-cache, simply drive the lowX interface and cache response using common signals.
    always_comb begin
      lowX_req_o.valid    = !lookup_ack && cache_miss;
      lowX_req_o.ready    = !flush;
      lowX_req_o.addr     = cache_req_q.addr;
      lowX_req_o.uncached = cache_req_q.uncached;
      cache_res_o.miss    = cache_miss;
      cache_res_o.valid   = cache_req_i.ready && (cache_hit || (cache_miss && lowX_req_o.ready && lowX_res_i.valid));
      cache_res_o.ready   = (!cache_miss || lowX_res_i.valid) && !flush;
      cache_res_o.blk     = (cache_miss && lowX_res_i.valid) ? lowX_res_i.blk : cache_select_data;
    end

  end else begin : dcache_impl
    // For d-cache, instantiate additional signals (such as dirty arrays, write-back logic, etc.)
    // Example: extra generate block for the dirty array and data masking.
    // The following logic is adapted from your dcache code.
    // You can instantiate the dirty array memories here (using a generate block as needed)
    for (genvar i = 0; i < NUM_WAY; i++) begin : dirty_array
      sp_bram #(
          .DATA_WIDTH(1),
          .NUM_SETS  (NUM_SET)
      ) dirty_array (
          .clk    (clk_i),
          .chip_en(1'b1),
          .addr   (drsram.idx),
          .wr_en  (drsram.way[i]),
          .wr_data(drsram.wdirty),
          .rd_data(drsram.rdirty[i])
      );
    end

    // Additional d-cache logic: data masking, writeback, etc.
    always_comb begin
      mask_data   = cache_hit ? cache_select_data : lowX_res_i.data;
      data_wr_pre = mask_data;
      case (cache_req_q.rw_size)
        2'b11: data_wr_pre[cache_req_q.addr[BOFFSET-1:2]*32+:32] = cache_req_q.data;
        2'b10: data_wr_pre[cache_req_q.addr[BOFFSET-1:1]*16+:16] = cache_req_q.data[15:0];
        2'b01: data_wr_pre[cache_req_q.addr[BOFFSET-1:0]*8+:8] = cache_req_q.data[7:0];
        2'b00: data_wr_pre = '0;
      endcase

      word_idx = cache_req_q.addr[(WOFFSET+2)-1:2];
      write_back = cache_miss && (|(drsram.rdirty & evict_way & cache_valid_vec));

      data_array_wr_en = ((cache_hit && cache_req_q.rw) ||
           (cache_miss && lowX_res_i.valid && !cache_req_q.uncached)) && !write_back;
      tag_array_wr_en = (cache_miss && lowX_res_i.valid && !cache_req_q.uncached) && !write_back;

      // Update dcache specific memories
      drsram.wdirty = flush ? '0 : (write_back ? '0 : (cache_req_q.rw ? '1 : '0));
      drsram.rw_en  = (cache_req_q.rw && (cache_hit || (cache_miss && lowX_res_i.valid))) ||
                        (write_back && lowX_res_i.valid);
      drsram.idx    = cache_idx;
      for (int i = 0; i < NUM_WAY; i++) drsram.way[i] = flush ? '1 : (cache_wr_way[i] && drsram.rw_en) || flush;

      nsram.rw_en = flush || data_array_wr_en;
      nsram.wnode = flush ? '0 : updated_node;
      nsram.idx   = cache_idx;

      tsram.way   = '0;
      tsram.idx   = cache_idx;
      tsram.wtag  = flush ? '0 : {1'b1, cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET]};
      for (int i = 0; i < NUM_WAY; i++) tsram.way[i] = flush ? '1 : (cache_wr_way[i] && tag_array_wr_en);

      dsram.way   = '0;
      dsram.idx   = cache_idx;
      dsram.wdata = cache_req_q.rw ? data_wr_pre : lowX_res_i.data;
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

    always_comb begin
      lowX_req_o.valid = !lookup_ack && cache_miss;
      lowX_req_o.ready = !flush;
      lowX_req_o.uncached = write_back ? '0 : cache_req_q.uncached;
      lowX_req_o.addr = write_back ? {evict_tag, rd_idx, {BOFFSET{1'b0}}} : {cache_req_q.addr[31:BOFFSET], {BOFFSET{1'b0}}};
      lowX_req_o.rw = write_back ? '1 : '0;
      lowX_req_o.rw_size = write_back ? 2'b11 : cache_req_q.rw_size;
      lowX_req_o.data = write_back ? evict_data : '0;

      cache_res_o.valid   = !cache_req_q.rw ? (!write_back && cache_req_q.valid &&
                              (cache_hit || (cache_miss && lowX_req_o.ready && lowX_res_i.valid))) :
                              (!write_back && cache_req_q.valid && cache_req_i.ready &&
                              (cache_hit || (cache_miss && lowX_req_o.ready && lowX_res_i.valid)));
      cache_res_o.ready   = !cache_req_q.rw ? (!write_back && (!cache_miss || lowX_res_i.valid) && !flush && !tag_array_wr_en) :
                              (!write_back && !tag_array_wr_en && lowX_req_o.ready &&
                              lowX_res_i.valid && !flush);
      cache_res_o.miss = cache_miss;
      cache_res_o.data = (cache_miss && lowX_res_i.valid) ? lowX_res_i.data[word_idx*32+:32] : cache_select_data[word_idx*32+:32];
    end
  end

  // Final lookup_ack logic common to both modes
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      lookup_ack <= '0;
    end else begin
      lookup_ack <= lowX_res_i.valid ? !lowX_req_o.ready : (!lookup_ack ? lowX_req_o.valid && lowX_res_i.ready : lookup_ack);
    end
  end

  // Fonksiyon: PLRU node güncellemesi
  function automatic [NUM_WAY-2:0] update_node(input logic [NUM_WAY-2:0] node_in, input logic [NUM_WAY-1:0] hit_vec);
    logic [NUM_WAY-2:0] node_tmp;
    int idx_base, shift;
    node_tmp = node_in;
    for (int unsigned i = 0; i < NUM_WAY; i++) begin
      if (hit_vec[i]) begin
        for (int unsigned lvl = 0; lvl < $clog2(NUM_WAY); lvl++) begin
          idx_base = (2 ** lvl) - 1;
          shift = $clog2(NUM_WAY) - lvl;
          // Güncelleme: ilgili bit tersleniyor
          node_tmp[idx_base+(i>>shift)] = ((i >> (shift - 1)) & 1) == 0;
        end
      end
    end
    return node_tmp;
  endfunction

  // Fonksiyon: PLRU evict_way belirleme
  function automatic [NUM_WAY-1:0] compute_evict_way(input logic [NUM_WAY-2:0] node_in);
    logic [NUM_WAY-1:0] way;
    int idx_base, shift;
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
