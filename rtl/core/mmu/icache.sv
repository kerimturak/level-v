/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps

/* verilator lint_off VARHIDDEN */
module icache
  import ceres_param::*;
#(
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

  dsram_t dsram;
  tsram_t tsram;
  nsram_t nsram;

  // Request pipeline register
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

  // Register the node read from BRAM to break combinational loops for PLRU
  logic [NUM_WAY-2:0] node_q;
  always_ff @(posedge clk_i) begin
    if (!rst_ni) node_q <= '0;
    else node_q <= nsram.rnode;
  end

  // PLRU logic
  always_comb begin
    logic [NUM_WAY-1:0] invalid_mask;
    logic [NUM_WAY-1:0] plru_candidate;
    logic               found_invalid;
    updated_node = update_node(node_q, cache_wr_way);

    invalid_mask = ~cache_valid_vec;
    plru_candidate = compute_evict_way(node_q);

    evict_way = '0;
    found_invalid = 1'b0;
    for (int ii = 0; ii < NUM_WAY; ii++) begin
      if (!found_invalid && invalid_mask[ii]) begin
        evict_way[ii] = 1'b1;
        found_invalid = 1'b1;
      end else begin
        evict_way[ii] = 1'b0;
      end
    end

    if (!found_invalid) begin
      evict_way = plru_candidate;
    end
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

    cache_wr_way = cache_hit ? cache_hit_vec : evict_way;
  end

  // I-Cache specific logic
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

  // I-Cache response logic
  always_comb begin
    lowX_req_o.valid    = !lookup_ack && cache_miss;
    lowX_req_o.ready    = !flush;
    lowX_req_o.addr     = cache_req_q.addr;
    lowX_req_o.uncached = cache_req_q.uncached;
    lowX_req_o.id       = cache_req_q.id;  // Pass through ID from fetch module
    cache_res_o.miss    = cache_miss;
    cache_res_o.valid   = cache_req_i.ready && (cache_hit || (cache_miss && lowX_req_o.ready && lowX_res_i.valid));
    cache_res_o.ready   = (!cache_miss || lowX_res_i.valid) && !flush;
    cache_res_o.blk     = (cache_miss && lowX_res_i.valid) ? lowX_res_i.blk : cache_select_data;
    cache_res_o.id      = lowX_res_i.valid ? lowX_res_i.id : cache_req_q.id;  // Return ID from response or request
  end

  // Lookup acknowledgment logic
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      lookup_ack <= '0;
    end else begin
      lookup_ack <= lowX_res_i.valid ? !lowX_req_o.ready : (!lookup_ack ? lowX_req_o.valid && lowX_res_i.ready : lookup_ack);
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
