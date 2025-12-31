/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps

/* verilator lint_off VARHIDDEN */
module dcache
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
    output lowX_req_t  lowX_req_o,
    output logic       fencei_stall_o  // Dcache dirty writeback stall for fence.i
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

  dsram_t                    dsram;
  tsram_t                    tsram;
  nsram_t                    nsram;

  // Dirty bit array signals (renamed for clarity)
  // `dirty_reg` holds per-set dirty bits for each way. Signals below
  // control writes to that register array and read the current dirty
  // vector for the computed index.
  logic      [IDX_WIDTH-1:0] dirty_wr_idx;  // set index to write dirty bit
  logic      [  NUM_WAY-1:0] dirty_wr_way;  // which way(s) to update
  logic                      dirty_wr_en;  // write enable for dirty write
  logic                      dirty_wr_val;  // value to write (1 = dirty, 0 = clean)
  logic      [  NUM_WAY-1:0] dirty_read_vec;  // read vector of dirty bits for current index

  // Internal low-level request latch to hold writeback requests
  lowX_req_t                 lowx_req_q;
  logic                      lowx_req_valid_q;

  // Temporary variables to break combinatorial loops
  logic      [IDX_WIDTH-1:0] dirty_idx_temp;
  logic                      dirty_rw_en_temp;
  logic      [  NUM_WAY-1:0] dirty_way_temp;
  logic                      dirty_wdirty_temp;

  // D-cache specific wires
  logic      [ BLK_SIZE-1:0] mask_data;
  logic                      data_array_wr_en;
  logic      [ BLK_SIZE-1:0] data_wr_pre;
  logic                      tag_array_wr_en;
  logic      [  WOFFSET-1:0] word_idx;
  logic                      write_back;
  logic      [ TAG_SIZE-1:0] evict_tag;
  logic      [ BLK_SIZE-1:0] evict_data;
  logic                      fi_active;
  logic                      fi_writeback_req;
  logic                      fi_mark_clean;
  logic      [ TAG_SIZE-1:0] fi_evict_tag;
  logic      [ BLK_SIZE-1:0] fi_evict_data;
  logic      [     XLEN-1:0] fi_evict_addr;
  logic      [  NUM_WAY-1:0] fi_way_onehot;
  logic      [IDX_WIDTH-1:0] fi_set_idx_q;
  // Writeback is handled combinationally like old dcache
  // No FSM needed - writeback and fill happen in same cycle
  // ============================================================================
  // Fence.i writeback helper (extracted to separate module)
  // Request pipeline register
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      cache_req_q <= '0;
    end else begin
      if (cache_miss) begin
        // Only advance pipeline on valid response from lowX (not during writeback or fence.i)
        if (!(lowX_res_i.valid && !write_back && !fi_active) || !cache_req_i.ready) cache_req_q <= cache_req_q;
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

  // ============================================================================
  // WRITEBACK - Combinational (like old dcache)
  // ----------------------------------------------------------------------------
  // Writeback and cache fill happen together in the same cycle
  // No FSM needed - simpler and avoids multi-cycle writeback delays

  // Fence.i state machine moved to helper module `dcache_fencei`
  // Instantiate fence helper


  dcache_fencei #(
      .TAG_SIZE (TAG_SIZE),
      .BLK_SIZE (BLK_SIZE),
      .XLEN     (XLEN),
      .NUM_WAY  (NUM_WAY),
      .IDX_WIDTH(IDX_WIDTH),
      .BOFFSET  (BOFFSET),
      .NUM_SET  (NUM_SET)
  ) i_dcache_fencei (
      .clk_i           (clk_i),
      .rst_ni          (rst_ni),
      .flush_i         (flush_i),
      .lowx_res_ready  (lowX_res_i.ready),
      .lowx_res_valid  (lowX_res_i.valid),
      .drsram_rd_rdirty(dirty_read_vec),
      .tsram_rtag      (tsram.rtag),
      .dsram_rdata     (dsram.rdata),
      .fi_active       (fi_active),
      .fi_writeback_req(fi_writeback_req),
      .fi_mark_clean   (fi_mark_clean),
      .fi_evict_tag    (fi_evict_tag),
      .fi_evict_data   (fi_evict_data),
      .fi_evict_addr   (fi_evict_addr),
      .fi_way_onehot   (fi_way_onehot),
      .fi_set_idx      (fi_set_idx_q)
  );

  // fencei_stall_o: stall CPU while dirty writeback is in progress
  assign fencei_stall_o = fi_active;

  // ============================================================================
  // Dirty Array as Register Array (not SRAM)
  // ----------------------------------------------------------------------------
  // Using registers allows instant visibility of all dirty bits in one cycle,
  // which is essential for fence.i dirty writeback scanning.
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

    rd_idx = cache_req_q.valid ? cache_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET] : cache_req_i.addr[IDX_WIDTH+BOFFSET-1:BOFFSET];
    wr_idx = flush ? flush_index : (cache_miss ? cache_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET] : rd_idx);

    cache_wr_en = (cache_miss && lowX_res_i.valid && !cache_req_q.uncached) || flush;
    cache_idx = cache_wr_en ? wr_idx : rd_idx;

    cache_wr_way = cache_hit ? cache_hit_vec : evict_way;
  end

  // D-cache data masking and control signals
  // FIRST: Compute control signals without reading dirty bits
  always_comb begin
    mask_data   = cache_hit ? cache_select_data : lowX_res_i.data;
    data_wr_pre = mask_data;

    case (cache_req_q.rw_size)
      WORD:    data_wr_pre[cache_req_q.addr[BOFFSET-1:2]*32+:32] = cache_req_q.data;
      HALF:    data_wr_pre[cache_req_q.addr[BOFFSET-1:1]*16+:16] = cache_req_q.data[15:0];
      BYTE:    data_wr_pre[cache_req_q.addr[BOFFSET-1:0]*8+:8] = cache_req_q.data[7:0];
      NO_SIZE: data_wr_pre = '0;
    endcase

    word_idx = cache_req_q.addr[(WOFFSET+2)-1:2];

    // Compute index first (used for dirty read)
    // During fence.i scanning we use `fi_set_idx_q`, otherwise normal cache index
    dirty_idx_temp = fi_active ? fi_set_idx_q : cache_idx;
  end

  // SECOND: Read dirty bits using the computed index
  always_comb begin
    // Default to avoid X propagation
    dirty_read_vec = '0;

    for (int w = 0; w < NUM_WAY; w++) begin
      dirty_read_vec[w] = dirty_reg[dirty_idx_temp][w];
    end
  end

  /* verilator lint_on WIDTHEXPAND */

  // THIRD: Compute write_back and other signals using dirty bits
  // THIRD: Compute write_back (separate smaller blocks)

  // A) write_back decision and debug
  always_comb begin
    write_back = 1'b0;
    if (cache_miss) begin
      write_back = |(dirty_read_vec & evict_way & cache_valid_vec);
    end
    if (lowx_req_valid_q) write_back = 1'b1;
  end

  // B) block data/tag array writes during writeback
  always_comb begin
    data_array_wr_en = ((cache_hit && cache_req_q.rw) || (cache_miss && lowX_res_i.valid && !cache_req_q.uncached)) && !write_back && !fi_active;
    tag_array_wr_en  = ((cache_hit && cache_req_q.rw) || (cache_miss && lowX_res_i.valid && !cache_req_q.uncached)) && !write_back && !fi_active;
  end

  // C) DR SRAM dirty control signals
  always_comb begin
    dirty_wdirty_temp = fi_mark_clean ? 1'b0 : ((flush && !fi_active) ? '0 : (write_back ? '0 : (cache_req_q.rw ? '1 : '0)));
    dirty_wr_val = dirty_wdirty_temp;

    dirty_rw_en_temp = fi_mark_clean || ((cache_req_q.rw && (cache_hit || (cache_miss && lowX_res_i.valid))) ||
                      (write_back && lowX_res_i.valid) || (flush && !fi_active));
    dirty_wr_en  = dirty_rw_en_temp;

    dirty_wr_idx    = dirty_idx_temp;

    for (int i = 0; i < NUM_WAY; i++) begin
      if (fi_mark_clean) begin
        dirty_way_temp[i] = fi_way_onehot[i];
      end else begin
        dirty_way_temp[i] = (flush && !fi_active && !write_back) ? '1 : (cache_wr_way[i] && dirty_rw_en_temp);
      end
      dirty_wr_way[i] = dirty_way_temp[i];
    end
  end

  // D) nsram/tsram/dsram updates and evict selection
  always_comb begin
    nsram.rw_en = (flush && !fi_active) || data_array_wr_en;
    nsram.wnode = (flush && !fi_active) ? '0 : updated_node;
    nsram.idx   = fi_active ? fi_set_idx_q : cache_idx;

    tsram.way   = '0;
    tsram.idx   = fi_active ? fi_set_idx_q : cache_idx;
    tsram.wtag  = (flush && !fi_active) ? '0 : {1'b1, cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET]};
    for (int i = 0; i < NUM_WAY; i++) tsram.way[i] = (flush && !fi_active) ? '1 : (cache_wr_way[i] && tag_array_wr_en);

    dsram.way   = '0;
    dsram.idx   = fi_active ? fi_set_idx_q : cache_idx;
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

  // D-cache response and request logic
  always_comb begin
    // Priority: fence.i writeback > normal writeback > cache miss
    // Writeback is combinational like old dcache - no FSM
    if (fi_writeback_req) begin
      // fence.i writeback has highest priority
      lowX_req_o.valid = 1'b1;
      lowX_req_o.ready = 1'b1;
      lowX_req_o.uncached = 1'b0;
      lowX_req_o.addr = fi_evict_addr;
      lowX_req_o.rw = 1'b1;  // Write operation
      lowX_req_o.rw_size = WORD;  // Full cache line
      lowX_req_o.data = fi_evict_data;
      lowX_req_o.id = cache_req_q.id;  // Use ID from current request for fence.i writeback
    end else if (lowx_req_valid_q) begin
      // Hold previously latched writeback request
      lowX_req_o = lowx_req_q;
    end else begin
      // Normal cache miss handling (includes writeback)
      // Like old dcache: writeback and fill happen together
      lowX_req_o.valid = cache_miss && lowX_res_i.ready;
      lowX_req_o.ready = 1'b1;
      lowX_req_o.uncached = write_back ? 1'b0 : cache_req_q.uncached;
      lowX_req_o.addr = write_back ? {evict_tag, rd_idx, {BOFFSET{1'b0}}} : (cache_req_q.uncached ? cache_req_q.addr : {cache_req_q.addr[31:BOFFSET], {BOFFSET{1'b0}}});
      lowX_req_o.rw = write_back ? 1'b1 : (cache_req_q.uncached ? cache_req_q.rw : 1'b0);
      lowX_req_o.rw_size = write_back ? WORD : cache_req_q.rw_size;
      lowX_req_o.data = write_back ? evict_data : (cache_req_q.uncached ? BLK_SIZE'(cache_req_q.data) : '0);
      lowX_req_o.id = cache_req_q.id;  // Pass through ID from memory module
    end

    // Cache response - simpler now without FSM
    cache_res_o.valid   = !fi_active && !write_back &&
                          (!cache_req_q.rw ? (cache_req_q.valid && (cache_hit || (cache_miss && lowX_req_o.ready && lowX_res_i.valid))) :
                                             (cache_req_q.valid && cache_req_i.ready && (cache_hit || (cache_miss && lowX_req_o.ready && lowX_res_i.valid))));
    cache_res_o.ready   = !fi_active && !write_back &&
                          (!cache_req_q.rw ? ((!cache_miss || lowX_res_i.valid) && !flush && !tag_array_wr_en) :
                                             (!tag_array_wr_en && lowX_req_o.ready && lowX_res_i.valid && !flush));
    cache_res_o.miss = cache_miss;
    cache_res_o.data = (cache_miss && lowX_res_i.valid) ? lowX_res_i.data[word_idx*32+:32] : cache_select_data[word_idx*32+:32];
    cache_res_o.id = lowX_res_i.valid ? lowX_res_i.id : cache_req_q.id;  // Return ID from response or request
  end

  // Lookup acknowledgment logic
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      lookup_ack <= '0;
    end else begin
      lookup_ack <= lowX_res_i.valid ? !lowX_req_o.ready : (!lookup_ack ? lowX_req_o.valid && lowX_res_i.ready : lookup_ack);
    end
  end

  // Latch normal writeback requests so they are held stable across cycles
  // when eviction way/addr might change in the next cycle.
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      lowx_req_q <= '0;
      lowx_req_valid_q <= 1'b0;
    end else begin
      if (lowx_req_valid_q) begin
        // Waiting for low-level response to clear saved request
        if (lowX_res_i.valid) begin
          lowx_req_q <= '0;
          lowx_req_valid_q <= 1'b0;
        end else begin
          lowx_req_q <= lowx_req_q;
          lowx_req_valid_q <= 1'b1;
        end
      end else begin
        // Capture a new writeback request when it would be issued
        if (write_back && cache_miss && lowX_res_i.ready) begin
          lowx_req_valid_q    <= 1'b1;
          lowx_req_q.valid    <= 1'b1;
          lowx_req_q.ready    <= 1'b1;
          lowx_req_q.addr     <= {evict_tag, rd_idx, {BOFFSET{1'b0}}};
          // dcache uses full-line writeback fields (dlowX_req_t)
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

  `include "cache_debug_log.svh"

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
