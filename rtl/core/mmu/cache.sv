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
  // ============================================================================
  // VERILATOR FIX: split_var directives for UNOPTFLAT circular logic warnings
  // These signals have circular dependencies in cache hit/miss/eviction logic.
  // 2-state simulation may evaluate them in wrong order without this directive.
  // See: docs/verilator/bugs/002_combinational_loop_instruction_corruption.md
  // ============================================================================
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

  // VERILATOR FIX: Struct types also need split_var for circular dependency resolution
  dsram_t                 dsram;
  tsram_t                 tsram;
  nsram_t                 nsram;

  // Dirty SRAM signals - broken out to avoid combinatorial loops
  logic   [IDX_WIDTH-1:0] drsram_wr_idx;
  logic   [  NUM_WAY-1:0] drsram_wr_way;
  logic                   drsram_wr_rw_en;
  logic                   drsram_wr_wdirty;
  logic   [  NUM_WAY-1:0] drsram_rd_rdirty;

  // Temporary variables to break combinatorial loops
  logic   [IDX_WIDTH-1:0] drsram_idx_temp;
  logic                   drsram_rw_en_temp;
  logic   [  NUM_WAY-1:0] drsram_way_temp;
  logic                   drsram_wdirty_temp;

  // Additional wires for dcache writeback, mask data, etc.
  logic   [ BLK_SIZE-1:0] mask_data;
  logic                   data_array_wr_en;
  logic   [ BLK_SIZE-1:0] data_wr_pre;
  logic                   tag_array_wr_en;
  logic   [  WOFFSET-1:0] word_idx;
  logic                   write_back;
  logic   [ TAG_SIZE-1:0] evict_tag;
  logic   [ BLK_SIZE-1:0] evict_data;

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

  // PLRU functions (assume update_node and compute_evict_way are defined elsewhere)
  always_comb begin

    // Prefer an invalid way (if any) when allocating a new line. If all ways
    // are valid, fall back to PLRU candidate computed from the node bits.
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

    // Select the write way: if there's a hit use the hit vector; else, choose the eviction way.
    cache_wr_way = cache_hit ? cache_hit_vec : evict_way;
  end

  // Generate different behavior for i-cache versus d-cache.

  if (IS_ICACHE) begin : icache_impl
    // icache has no dirty writeback, so fencei_stall is always 0
    assign fencei_stall_o = 1'b0;

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

    // ============================================================================
    // WRITEBACK STATE MACHINE
    // ----------------------------------------------------------------------------
    // Prevents combinational loops by using registered writeback state
    // ============================================================================
    typedef enum logic [1:0] {
      WB_IDLE,     // No writeback in progress
      WB_REQUEST,  // Sending writeback request to lowX
      WB_WAIT,     // Waiting for writeback completion
      WB_DONE      // Writeback complete, return to normal operation
    } wb_state_e;

    wb_state_e wb_state_q, wb_state_d;
    logic [ TAG_SIZE-1:0] wb_evict_tag_q;
    logic [ BLK_SIZE-1:0] wb_evict_data_q;
    logic [IDX_WIDTH-1:0] wb_evict_idx_q;
    logic                 write_back;  // Combinational signal indicating writeback needed
    logic                 wb_in_progress;  // Registered signal indicating writeback FSM active

    // Writeback FSM
    always_ff @(posedge clk_i) begin
      if (!rst_ni) begin
        wb_state_q <= WB_IDLE;
        wb_evict_tag_q <= '0;
        wb_evict_data_q <= '0;
        wb_evict_idx_q <= '0;
      end else begin
        wb_state_q <= wb_state_d;
        // Capture eviction info when entering WB_REQUEST state
        if (wb_state_d == WB_REQUEST && wb_state_q == WB_IDLE) begin
          wb_evict_tag_q  <= evict_tag;
          wb_evict_data_q <= evict_data;
          wb_evict_idx_q  <= rd_idx;
        end
      end
    end

    always_comb begin
      wb_state_d = wb_state_q;
      wb_in_progress = (wb_state_q != WB_IDLE);

      case (wb_state_q)
        WB_IDLE: begin
          // Detect if writeback is needed
          if (write_back && !fi_active) begin
            wb_state_d = WB_REQUEST;
          end
        end

        WB_REQUEST: begin
          // Wait for lowX to accept the request
          if (lowX_res_i.ready) begin
            wb_state_d = WB_WAIT;
          end
        end

        WB_WAIT: begin
          // Wait for writeback completion
          if (lowX_res_i.valid) begin
            wb_state_d = WB_DONE;
          end
        end

        WB_DONE: begin
          // Complete writeback and return to idle
          wb_state_d = WB_IDLE;
        end

        default: wb_state_d = WB_IDLE;
      endcase
    end

    // ============================================================================
    // FENCE.I Dirty Writeback State Machine
    // ----------------------------------------------------------------------------
    // When fence.i is issued (flush_i rises), dcache must:
    // 1. Scan all sets and all ways for dirty lines
    // 2. Write dirty lines back to memory
    // 3. Mark written lines as clean
    // 4. Assert fencei_stall_o until all dirty lines are written back
    // 5. IMPORTANT: Dcache does NOT invalidate lines on fence.i, only writes back dirty data
    // ============================================================================
    // 3. Mark written lines as clean
    // 4. Assert fencei_stall_o until all dirty lines are written back
    // ============================================================================
    typedef enum logic [2:0] {
      FI_IDLE,            // Normal operation
      FI_SCAN,            // Scanning sets for dirty lines
      FI_CHECK_WAY,       // Check each way for dirty data
      FI_WRITEBACK_REQ,   // Send writeback request to memory
      FI_WRITEBACK_WAIT,  // Wait for writeback completion
      FI_MARK_CLEAN,      // Mark the line as clean
      FI_NEXT_WAY,        // Move to next way
      FI_DONE             // Writeback complete
    } fencei_state_e;

    fencei_state_e fi_state_q, fi_state_d;
    logic [IDX_WIDTH-1:0] fi_set_idx_q, fi_set_idx_d;
    logic [$clog2(NUM_WAY)-1:0] fi_way_idx_q, fi_way_idx_d;
    logic                fi_active;
    logic                fi_writeback_req;
    logic [TAG_SIZE-1:0] fi_evict_tag;
    logic [BLK_SIZE-1:0] fi_evict_data;
    logic [    XLEN-1:0] fi_evict_addr;
    logic                fi_mark_clean;
    logic [ NUM_WAY-1:0] fi_way_onehot;
    logic                fi_has_dirty;
    logic                flush_i_prev;  // To detect rising edge

    // Detect rising edge of flush_i
    always_ff @(posedge clk_i) begin
      if (!rst_ni) flush_i_prev <= 1'b0;
      else flush_i_prev <= flush_i;
    end

    wire fi_start = flush_i && !flush_i_prev && (fi_state_q == FI_IDLE);

    // One-hot encoding of current way
    always_comb begin
      fi_way_onehot = '0;
      fi_way_onehot[fi_way_idx_q] = 1'b1;
    end

    // Check if current way in current set is dirty and valid
    assign fi_has_dirty = drsram_rd_rdirty[fi_way_idx_q] && tsram.rtag[fi_way_idx_q][TAG_SIZE];

    // Get eviction data for fence.i writeback
    always_comb begin
      fi_evict_tag  = tsram.rtag[fi_way_idx_q][TAG_SIZE-1:0];
      fi_evict_data = dsram.rdata[fi_way_idx_q];
      fi_evict_addr = {fi_evict_tag, fi_set_idx_q, {BOFFSET{1'b0}}};
    end

    // Fence.i state machine
    always_ff @(posedge clk_i) begin
      if (!rst_ni) begin
        fi_state_q   <= FI_IDLE;
        fi_set_idx_q <= '0;
        fi_way_idx_q <= '0;
      end else begin
        fi_state_q   <= fi_state_d;
        fi_set_idx_q <= fi_set_idx_d;
        fi_way_idx_q <= fi_way_idx_d;
      end
    end

    always_comb begin
      fi_state_d       = fi_state_q;
      fi_set_idx_d     = fi_set_idx_q;
      fi_way_idx_d     = fi_way_idx_q;
      fi_active        = 1'b0;
      fi_writeback_req = 1'b0;
      fi_mark_clean    = 1'b0;

      unique case (fi_state_q)
        FI_IDLE: begin
          if (fi_start) begin
            // fence.i detected (rising edge of flush_i), start scanning
            // Set address for first set, wait one cycle for BRAM read
            fi_state_d   = FI_SCAN;
            fi_set_idx_d = '0;
            fi_way_idx_d = '0;
            fi_active    = 1'b1;
          end
        end

        FI_SCAN: begin
          fi_active  = 1'b1;
          // Address is set, wait one cycle for BRAM to output data
          // Then move to check ways
          fi_state_d = FI_CHECK_WAY;
        end

        FI_CHECK_WAY: begin
          fi_active = 1'b1;
          // Now BRAM data is valid, check if dirty
          if (fi_has_dirty) begin
            // Found a dirty line, initiate writeback
            fi_state_d = FI_WRITEBACK_REQ;
          end else begin
            // Not dirty, move to next way
            fi_state_d = FI_NEXT_WAY;
          end
        end

        FI_WRITEBACK_REQ: begin
          fi_active = 1'b1;
          fi_writeback_req = 1'b1;
          // Wait for memory to accept our request
          if (lowX_res_i.ready) begin
            fi_state_d = FI_WRITEBACK_WAIT;
          end
        end

        FI_WRITEBACK_WAIT: begin
          fi_active = 1'b1;
          fi_writeback_req = 1'b1;
          // Wait for memory write to complete
          if (lowX_res_i.valid) begin
            // Writeback complete, mark line as clean
            fi_state_d = FI_MARK_CLEAN;
          end
        end

        FI_MARK_CLEAN: begin
          fi_active = 1'b1;
          fi_mark_clean = 1'b1;
          fi_state_d = FI_NEXT_WAY;
        end

        FI_NEXT_WAY: begin
          fi_active = 1'b1;
          if (fi_way_idx_q == $clog2(NUM_WAY)'(NUM_WAY - 1)) begin
            // All ways checked, move to next set
            if (fi_set_idx_q == IDX_WIDTH'(NUM_SET - 1)) begin
              // All sets done
              fi_state_d = FI_DONE;
            end else begin
              fi_set_idx_d = fi_set_idx_q + 1'b1;
              fi_way_idx_d = '0;
              // Go to SCAN to wait for BRAM read latency
              fi_state_d   = FI_SCAN;
            end
          end else begin
            fi_way_idx_d = fi_way_idx_q + 1'b1;
            // Same set, data already available, go directly to check
            fi_state_d   = FI_CHECK_WAY;
          end
        end

        FI_DONE: begin
          // Writeback complete, no longer stalling
          // Stay in DONE until flush_i goes low (will happen when pipeline advances)
          fi_active = 1'b0;  // Release stall - this is the key!
          if (!flush_i) begin
            fi_state_d = FI_IDLE;
          end
        end

        default: fi_state_d = FI_IDLE;
      endcase
    end

    // fencei_stall_o: stall CPU while dirty writeback is in progress
    // fi_active is 0 in FI_IDLE and FI_DONE states
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
          if (drsram_wr_way[w]) begin
            dirty_reg[drsram_wr_idx][w] <= drsram_wr_wdirty;
          end
        end
      end
    end

    // Additional d-cache logic: data masking, writeback, etc.
    // FIRST: Compute control signals without reading dirty bits
    always_comb begin
      mask_data   = cache_hit ? cache_select_data : lowX_res_i.data;
      data_wr_pre = mask_data;

`ifdef LOG_CACHE_DEBUG
      // Debug logging for cache operations
      if (cache_req_q.valid && !IS_ICACHE) begin
        if (write_back) begin
          $display("[DCACHE] WRITEBACK @ %0t: addr=0x%08h evict_addr=0x%08h valid=%b ready=%b lowX_ready=%b lowX_valid=%b", $time, cache_req_q.addr, {evict_tag, rd_idx, {BOFFSET{1'b0}}},
                   lowX_req_o.valid, lowX_req_o.ready, lowX_res_i.ready, lowX_res_i.valid);
        end
      end
`endif
      case (cache_req_q.rw_size)
        2'b11: data_wr_pre[cache_req_q.addr[BOFFSET-1:2]*32+:32] = cache_req_q.data;
        2'b10: data_wr_pre[cache_req_q.addr[BOFFSET-1:1]*16+:16] = cache_req_q.data[15:0];
        2'b01: data_wr_pre[cache_req_q.addr[BOFFSET-1:0]*8+:8] = cache_req_q.data[7:0];
        2'b00: data_wr_pre = '0;
      endcase

      word_idx = cache_req_q.addr[(WOFFSET+2)-1:2];

      // Compute index first (used for dirty read)
      drsram_idx_temp = fi_active ? fi_set_idx_q : cache_idx;
    end

    // SECOND: Read dirty bits using the computed index
    always_comb begin
      // Default to avoid X propagation
      drsram_rd_rdirty = '0;

      for (int w = 0; w < NUM_WAY; w++) begin
        drsram_rd_rdirty[w] = dirty_reg[drsram_idx_temp][w];
      end
    end

    // THIRD: Compute write_back and other signals using dirty bits
    always_comb begin
      // write_back is combinational but only used to trigger FSM transition
      // Default to 0 to avoid X propagation
      write_back = 1'b0;

      if (cache_miss && !wb_in_progress) begin
        write_back = |(drsram_rd_rdirty & evict_way & cache_valid_vec);
      end

      // Block data/tag array writes during writeback FSM operation
      data_array_wr_en = ((cache_hit && cache_req_q.rw) ||
           (cache_miss && lowX_res_i.valid && !cache_req_q.uncached)) && !wb_in_progress && !fi_active;
      tag_array_wr_en = (cache_miss && lowX_res_i.valid && !cache_req_q.uncached) && !wb_in_progress && !fi_active;

      // Update dcache specific memories
      // During fence.i writeback, we use fi_mark_clean to clear dirty bit
      // IMPORTANT: During fi_active, we must NOT let flush invalidate tags/dirty bits
      drsram_wdirty_temp = fi_mark_clean ? 1'b0 : ((flush && !fi_active) ? '0 : (wb_in_progress ? '0 : (cache_req_q.rw ? '1 : '0)));
      drsram_wr_wdirty = drsram_wdirty_temp;

      // Compute rw_en without self-reference
      // Clear dirty bit when writeback completes (WB_DONE state)
      drsram_rw_en_temp = fi_mark_clean || ((cache_req_q.rw && (cache_hit || (cache_miss && lowX_res_i.valid))) ||
                        (wb_state_q == WB_DONE));
      drsram_wr_rw_en  = drsram_rw_en_temp;

      // During fence.i, use fi_set_idx_q for reading dirty bits
      // When clearing dirty bit after a writeback completes (WB_DONE), make
      // sure we target the index of the evicted line captured by the FSM
      // (wb_evict_idx_q). Otherwise we may clear the wrong set's dirty bit.
      drsram_wr_idx    = (wb_state_q == WB_DONE) ? wb_evict_idx_q : drsram_idx_temp;

      for (int i = 0; i < NUM_WAY; i++) begin
        if (fi_mark_clean) begin
          drsram_way_temp[i] = fi_way_onehot[i];
        end else if (wb_state_q == WB_DONE) begin
          // Clear dirty bit of evicted way after writeback completes
          drsram_way_temp[i] = evict_way[i];
        end else begin
          // Don't let flush write during fi_active or wb_in_progress
          drsram_way_temp[i] = (flush && !fi_active && !wb_in_progress) ? '1 : (cache_wr_way[i] && drsram_rw_en_temp);
        end
        drsram_wr_way[i] = drsram_way_temp[i];
      end

      nsram.rw_en = (flush && !fi_active) || data_array_wr_en;
      nsram.wnode = (flush && !fi_active) ? '0 : updated_node;
      nsram.idx   = fi_active ? fi_set_idx_q : cache_idx;

      tsram.way   = '0;
      tsram.idx   = fi_active ? fi_set_idx_q : cache_idx;
      tsram.wtag  = (flush && !fi_active) ? '0 : {1'b1, cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET]};
      // CRITICAL: Don't invalidate tags during fence.i - only writeback dirty data
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

    always_comb begin
      // Priority: fence.i writeback > normal writeback > cache miss
      if (fi_writeback_req) begin
        // fence.i writeback has highest priority
        lowX_req_o.valid = 1'b1;
        lowX_req_o.ready = 1'b1;
        lowX_req_o.uncached = 1'b0;
        lowX_req_o.addr = fi_evict_addr;
        lowX_req_o.rw = 1'b1;  // Write operation
        lowX_req_o.rw_size = 2'b11;  // Full cache line
        lowX_req_o.data = fi_evict_data;
      end else if (wb_in_progress) begin
        // Use FSM state for writeback to prevent combinational loops
        lowX_req_o.valid = (wb_state_q == WB_REQUEST || wb_state_q == WB_WAIT);
        lowX_req_o.ready = !flush && !fi_active;
        lowX_req_o.uncached = 1'b0;
        lowX_req_o.addr = {wb_evict_tag_q, wb_evict_idx_q, {BOFFSET{1'b0}}};
        lowX_req_o.rw = 1'b1;  // Always write during writeback
        lowX_req_o.rw_size = 2'b11;  // Full cache line
        lowX_req_o.data = wb_evict_data_q;
      end else begin
        // Normal cache miss handling
        lowX_req_o.valid = !lookup_ack && cache_miss;
        lowX_req_o.ready = !flush && !fi_active && !wb_in_progress;
        lowX_req_o.uncached = cache_req_q.uncached;
        // For uncached accesses, preserve full address; for cached, align to cache line
        lowX_req_o.addr = cache_req_q.uncached ? cache_req_q.addr : {cache_req_q.addr[31:BOFFSET], {BOFFSET{1'b0}}};
        // For uncached writes, pass through the write signal; for cache miss, read
        lowX_req_o.rw = cache_req_q.uncached ? cache_req_q.rw : 1'b0;
        lowX_req_o.rw_size = cache_req_q.rw_size;
        // For uncached writes, pass through the data
        lowX_req_o.data = cache_req_q.uncached ? BLK_SIZE'(cache_req_q.data) : '0;
      end

      // Cache response - block during writeback FSM operation
      cache_res_o.valid   = !fi_active && !wb_in_progress &&
                            (!cache_req_q.rw ? (cache_req_q.valid && (cache_hit || (cache_miss && lowX_req_o.ready && lowX_res_i.valid))) :
                                               (cache_req_q.valid && cache_req_i.ready && (cache_hit || (cache_miss && lowX_req_o.ready && lowX_res_i.valid))));
      cache_res_o.ready   = !fi_active && !wb_in_progress &&
                            (!cache_req_q.rw ? ((!cache_miss || lowX_res_i.valid) && !flush && !tag_array_wr_en) :
                                               (!tag_array_wr_en && lowX_req_o.ready && lowX_res_i.valid && !flush));
      cache_res_o.miss = cache_miss;
      cache_res_o.data = (cache_miss && lowX_res_i.valid) ? lowX_res_i.data[word_idx*32+:32] : cache_select_data[word_idx*32+:32];
    end
`ifndef SYNTHESIS
    `include "cache_debug_log.svh"
`endif
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
    int unsigned idx_base, shift;
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
