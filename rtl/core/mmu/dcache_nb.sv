/*
 * Non-Blocking Dual-Port D-Cache with MSHR
 *
 * Architecture:
 *   Load port (ld)  ──► LD-pipe FSM ──┐
 *                                      ├──► shared mem controller → lowX (L2)
 *   Store port (st) ──► ST-pipe FSM ──┘
 *
 * Design:
 *   - Dual-port dp_bram: Port A = LD pipe reads, Port B = ST pipe reads/writes + fill writes
 *   - Register-based PLRU (dual read, merged update)
 *   - Register-based dirty array (dual read, merged update)
 *   - Central MSHR (DC_MSHR_DEPTH entries) for miss tracking & coalescing
 *   - Shared memory controller for victim writeback + fill fetch
 *   - Parametric multi-bank support (DC_NUM_BANK)
 *   - Set-conflict hazard protection between pipelines
 *   - fence.i dirty writeback via dcache_fencei helper
 *
 * Pipeline timing (per pipe):
 *   Cycle 0 (IDLE):       Request accepted, address driven to SRAMs
 *   Cycle 1 (TAG_LOOKUP): Registered SRAM outputs settle; hit/miss resolved combinationally.
 *                          LD hit → respond same cycle, return to IDLE (1-cycle hit).
 *                          ST hit → HIT_RESPOND (SRAM write next cycle, 2-cycle hit).
 *                          Miss → MSHR + evict/fill.
 */
`timescale 1ns / 1ps
`include "level_defines.svh"

/* verilator lint_off VARHIDDEN */
module dcache_nb
  import level_param::*;
#(
    parameter type cache_req_t = dcache_req_t,
    parameter type cache_res_t = dcache_res_t,
    parameter type lowX_res_t  = dlowX_res_t,
    parameter type lowX_req_t  = dlowX_req_t,
    parameter      CACHE_SIZE  = DC_CAPACITY,
    parameter      BLK_SIZE    = level_param::BLK_SIZE,
    parameter      XLEN        = level_param::XLEN,
    parameter      NUM_WAY     = DC_WAY
) (
    input logic clk_i,
    input logic rst_ni,
    input logic flush_i,

    // Load port (pipeline loads + uncached reads)
    input  cache_req_t ld_req_i,
    output cache_res_t ld_res_o,

    // Store port (SB drains + uncached stores)
    input  cache_req_t st_req_i,
    output cache_res_t st_res_o,

    // Lower-level memory interface (L2)
    input  lowX_res_t lowX_res_i,
    output lowX_req_t lowX_req_o,

    output logic fencei_stall_o,
    output logic pipes_idle_o
);

  // ===========================================================================
  // Local parameters
  // ===========================================================================
  localparam int NUM_SET = (CACHE_SIZE / BLK_SIZE) / NUM_WAY;
  localparam int IDX_WIDTH = $clog2(NUM_SET) == 0 ? 1 : $clog2(NUM_SET);
  localparam int BOFFSET = $clog2(BLK_SIZE / 8);
  localparam int WOFFSET = $clog2(BLK_SIZE / 32);
  localparam int TAG_SIZE = XLEN - IDX_WIDTH - BOFFSET;
  localparam int NUM_BANK = DC_NUM_BANK;
  localparam int BANK_SETS = NUM_SET / NUM_BANK;
  localparam int BANK_SEL_W = NUM_BANK > 1 ? $clog2(NUM_BANK) : 1;
  localparam int BANK_ADDR_W = $clog2(BANK_SETS);
  localparam int MSHR_DEPTH = DC_MSHR_DEPTH;
  localparam int MSHR_PTR_W = DC_MSHR_PTR_W;

  // ===========================================================================
  // FSM enums
  // ===========================================================================
  typedef enum logic [2:0] {
    PIPE_IDLE,
    PIPE_TAG_LOOKUP,
    PIPE_RESOLVE,
    PIPE_HIT_RESPOND,
    PIPE_WB_EVICT,
    PIPE_MISS_WAIT,
    PIPE_FILL_RESPOND,
    PIPE_BYPASS
  } pipe_state_t;

  typedef enum logic [1:0] {
    MEM_IDLE,
    MEM_WB_SEND,
    MEM_FILL_SEND
  } mem_state_t;

  // ===========================================================================
  // Internal request type (captured in pipe)
  // ===========================================================================
  typedef struct packed {
    logic [XLEN-1:0] addr;
    logic            is_write;
    rw_size_e        rw_size;
    logic [31:0]     wdata;
    logic            uncached;
  } dc_pipe_req_t;

  // ===========================================================================
  // Per-pipe state
  // ===========================================================================
  pipe_state_t ld_pipe_state, st_pipe_state;
  dc_pipe_req_t ld_req_q, st_req_q;

  // ===========================================================================
  // Flush logic
  // ===========================================================================
  logic                 flush_active;
  logic [IDX_WIDTH-1:0] flush_cnt;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      flush_active <= 1'b1;
      flush_cnt    <= '0;
    end else if (flush_active) begin
      if (flush_cnt == IDX_WIDTH'(NUM_SET - 1)) begin
        flush_active <= 1'b0;
        flush_cnt    <= '0;
      end else begin
        flush_cnt <= flush_cnt + 1;
      end
    end else if (flush_i && ld_pipe_state == PIPE_IDLE && st_pipe_state == PIPE_IDLE) begin
      flush_active <= 1'b1;
      flush_cnt    <= '0;
    end
  end

  // ===========================================================================
  // Per-pipe SRAM addressing & bank decode
  // ===========================================================================
  logic [IDX_WIDTH-1:0] ld_next_set, st_next_set;
  assign ld_next_set = ld_req_i.addr[IDX_WIDTH+BOFFSET-1:BOFFSET];
  assign st_next_set = st_req_i.addr[IDX_WIDTH+BOFFSET-1:BOFFSET];

  logic [IDX_WIDTH-1:0] ld_req_set, st_req_set;
  assign ld_req_set = ld_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET];
  assign st_req_set = st_req_q.addr[IDX_WIDTH+BOFFSET-1:BOFFSET];

  logic [TAG_SIZE-1:0] ld_req_tag, st_req_tag;
  assign ld_req_tag = ld_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET];
  assign st_req_tag = st_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET];

  // SRAM index mux: IDLE → use next request address; otherwise → use latched
  logic [IDX_WIDTH-1:0] ld_sram_idx, st_sram_idx;

  // Fence.i signals (from dcache_fencei)
  logic                 fi_active;
  logic                 fi_writeback_req;
  logic                 fi_mark_clean;
  logic [ TAG_SIZE-1:0] fi_evict_tag;
  logic [ BLK_SIZE-1:0] fi_evict_data;
  logic [     XLEN-1:0] fi_evict_addr;
  logic [  NUM_WAY-1:0] fi_way_onehot;
  logic [IDX_WIDTH-1:0] fi_set_idx_q;

  assign ld_sram_idx = flush_active ? flush_cnt : (ld_pipe_state == PIPE_IDLE) ? ld_next_set : ld_req_set;

  assign st_sram_idx = fi_active ? fi_set_idx_q : (st_pipe_state == PIPE_IDLE) ? st_next_set : st_req_set;

  // Bank decode
  logic [BANK_SEL_W-1:0] ld_bank_sel, st_bank_sel;
  logic [BANK_ADDR_W-1:0] ld_bank_addr, st_bank_addr;
  logic [BANK_SEL_W-1:0] ld_bank_sel_q, st_bank_sel_q;

  if (NUM_BANK > 1) begin : gen_bank_decode
    assign ld_bank_sel  = ld_sram_idx[$clog2(NUM_BANK)-1:0];
    assign ld_bank_addr = ld_sram_idx[IDX_WIDTH-1:$clog2(NUM_BANK)];
    assign st_bank_sel  = st_sram_idx[$clog2(NUM_BANK)-1:0];
    assign st_bank_addr = st_sram_idx[IDX_WIDTH-1:$clog2(NUM_BANK)];
  end else begin : gen_single_bank
    assign ld_bank_sel  = '0;
    assign ld_bank_addr = ld_sram_idx;
    assign st_bank_sel  = '0;
    assign st_bank_addr = st_sram_idx;
  end

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      ld_bank_sel_q <= '0;
      st_bank_sel_q <= '0;
    end else begin
      ld_bank_sel_q <= ld_bank_sel;
      st_bank_sel_q <= st_bank_sel;
    end
  end

  // ===========================================================================
  // Per-pipe SRAM read/write signals
  // ===========================================================================
  logic [NUM_WAY-1:0] ld_tag_we, st_tag_we;
  logic [TAG_SIZE:0] ld_tag_wdata, st_tag_wdata;
  logic [NUM_WAY-1:0][TAG_SIZE:0] ld_tag_rdata, st_tag_rdata;

  logic [NUM_WAY-1:0] ld_data_we, st_data_we;
  logic [BLK_SIZE-1:0] ld_data_wdata, st_data_wdata;
  logic [NUM_WAY-1:0][BLK_SIZE-1:0] ld_data_rdata, st_data_rdata;

  // ===========================================================================
  // dp_bram instantiation (multi-bank, parametric)
  // Port A = LD pipe (+ flush writes), Port B = ST pipe (+ fill writes)
  // ===========================================================================
  for (genvar w = 0; w < NUM_WAY; w++) begin : gen_data_way
    logic [BLK_SIZE-1:0] a_bank_rd[NUM_BANK];
    logic [BLK_SIZE-1:0] b_bank_rd[NUM_BANK];
    for (genvar b = 0; b < NUM_BANK; b++) begin : gen_data_bank
      dp_bram #(
          .DATA_WIDTH(BLK_SIZE),
          .NUM_SETS  (BANK_SETS)
      ) i_data (
          .clk      (clk_i),
          .a_chip_en(ld_bank_sel == BANK_SEL_W'(b)),
          .a_addr   (ld_bank_addr),
          .a_wr_en  (ld_data_we[w]),
          .a_wr_data(ld_data_wdata),
          .a_rd_data(a_bank_rd[b]),
          .b_chip_en(st_bank_sel == BANK_SEL_W'(b)),
          .b_addr   (st_bank_addr),
          .b_wr_en  (st_data_we[w]),
          .b_wr_data(st_data_wdata),
          .b_rd_data(b_bank_rd[b])
      );
    end
    assign ld_data_rdata[w] = a_bank_rd[ld_bank_sel_q];
    assign st_data_rdata[w] = b_bank_rd[st_bank_sel_q];
  end

  for (genvar w = 0; w < NUM_WAY; w++) begin : gen_tag_way
    logic [TAG_SIZE:0] a_bank_rd[NUM_BANK];
    logic [TAG_SIZE:0] b_bank_rd[NUM_BANK];
    for (genvar b = 0; b < NUM_BANK; b++) begin : gen_tag_bank
      dp_bram #(
          .DATA_WIDTH(TAG_SIZE + 1),
          .NUM_SETS  (BANK_SETS)
      ) i_tag (
          .clk      (clk_i),
          .a_chip_en(ld_bank_sel == BANK_SEL_W'(b)),
          .a_addr   (ld_bank_addr),
          .a_wr_en  (ld_tag_we[w]),
          .a_wr_data(ld_tag_wdata),
          .a_rd_data(a_bank_rd[b]),
          .b_chip_en(st_bank_sel == BANK_SEL_W'(b)),
          .b_addr   (st_bank_addr),
          .b_wr_en  (st_tag_we[w]),
          .b_wr_data(st_tag_wdata),
          .b_rd_data(b_bank_rd[b])
      );
    end
    assign ld_tag_rdata[w] = a_bank_rd[ld_bank_sel_q];
    assign st_tag_rdata[w] = b_bank_rd[st_bank_sel_q];
  end

  // ===========================================================================
  // PLRU — register-based (dual read, merged update)
  // ===========================================================================
  logic [NUM_WAY-2:0] plru_reg[NUM_SET];
  logic ld_plru_wr, st_plru_wr;
  logic [NUM_WAY-2:0] ld_plru_wdata, st_plru_wdata;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      for (int s = 0; s < NUM_SET; s++) plru_reg[s] <= '0;
    end else if (flush_active) begin
      plru_reg[flush_cnt] <= '0;
    end else begin
      if (ld_plru_wr && st_plru_wr && ld_req_set == st_req_set) begin
        plru_reg[ld_req_set] <= update_node(ld_plru_wdata, st_hit_way_oh());
      end else begin
        if (ld_plru_wr) plru_reg[ld_req_set] <= ld_plru_wdata;
        if (st_plru_wr) plru_reg[st_req_set] <= st_plru_wdata;
      end
    end
  end

  logic [NUM_WAY-2:0] ld_plru_rdata, st_plru_rdata;
  assign ld_plru_rdata = plru_reg[ld_req_set];
  assign st_plru_rdata = plru_reg[st_req_set];

  // ===========================================================================
  // Dirty array — register-based (dual read, merged update)
  // ===========================================================================
  logic [NUM_WAY-1:0] dirty_reg[NUM_SET];

  logic ld_dirty_wr, st_dirty_wr;
  logic [IDX_WIDTH-1:0] ld_dirty_idx, st_dirty_idx;
  logic [NUM_WAY-1:0] ld_dirty_way, st_dirty_way;
  logic ld_dirty_val, st_dirty_val;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      for (int s = 0; s < NUM_SET; s++) dirty_reg[s] <= '0;
    end else if (flush_active) begin
      dirty_reg[flush_cnt] <= '0;
    end else begin
      if (ld_dirty_wr && st_dirty_wr && ld_dirty_idx == st_dirty_idx) begin
        for (int w = 0; w < NUM_WAY; w++) begin
          if (ld_dirty_way[w]) dirty_reg[ld_dirty_idx][w] <= ld_dirty_val;
          if (st_dirty_way[w]) dirty_reg[st_dirty_idx][w] <= st_dirty_val;
        end
      end else begin
        if (ld_dirty_wr) for (int w = 0; w < NUM_WAY; w++) if (ld_dirty_way[w]) dirty_reg[ld_dirty_idx][w] <= ld_dirty_val;
        if (st_dirty_wr) for (int w = 0; w < NUM_WAY; w++) if (st_dirty_way[w]) dirty_reg[st_dirty_idx][w] <= st_dirty_val;
      end
    end
  end

  logic [NUM_WAY-1:0] ld_dirty_read, st_dirty_read;
  assign ld_dirty_read = dirty_reg[ld_req_set];
  assign st_dirty_read = fi_active ? dirty_reg[fi_set_idx_q] : dirty_reg[st_req_set];

  // ===========================================================================
  // Per-pipe hit/miss detection
  // ===========================================================================
  logic [NUM_WAY-1:0] ld_valid_vec, ld_hit_vec, ld_hit_way_oh;
  logic ld_hit_any, ld_miss;
  logic [BLK_SIZE-1:0] ld_select_data;

  // ST→LD bypass: when ST pipe is writing (HIT_RESPOND) to the same line
  // LD pipe is reading, LD must see the updated data.
  logic                st_to_ld_bypass;
  logic [NUM_WAY-1:0] st_valid_vec, st_hit_vec, st_hit_way_oh_raw;
  logic st_hit_any, st_miss;
  logic [BLK_SIZE-1:0] st_select_data;
  logic [BLK_SIZE-1:0] st_hit_wr_merged;

  always_comb begin
    for (int w = 0; w < NUM_WAY; w++) begin
      ld_valid_vec[w] = ld_tag_rdata[w][TAG_SIZE];
      ld_hit_vec[w]   = ld_tag_rdata[w][TAG_SIZE-1:0] == ld_req_tag;
    end
    ld_hit_way_oh  = ld_valid_vec & ld_hit_vec;
    ld_hit_any     = |ld_hit_way_oh;
    ld_miss        = !ld_hit_any;
    ld_select_data = '0;
    for (int w = 0; w < NUM_WAY; w++) if (ld_hit_way_oh[w]) ld_select_data = ld_data_rdata[w];

    // Bypass: ST pipe writes merged line; LD needs the updated version.
    // Covers both: ST already in HIT_RESPOND, or ST in TAG_LOOKUP (same cycle as LD)
    // about to write the same line.
    st_to_ld_bypass = st_req_q.is_write && (ld_req_set == st_req_set) && |(ld_hit_way_oh & st_hit_way_oh_raw)
                    && ((st_pipe_state == PIPE_HIT_RESPOND) || (st_pipe_state == PIPE_TAG_LOOKUP && st_hit_any));
    if (st_to_ld_bypass) ld_select_data = st_hit_wr_merged;
  end

  always_comb begin
    for (int w = 0; w < NUM_WAY; w++) begin
      st_valid_vec[w] = st_tag_rdata[w][TAG_SIZE];
      st_hit_vec[w]   = st_tag_rdata[w][TAG_SIZE-1:0] == st_req_tag;
    end
    st_hit_way_oh_raw = st_valid_vec & st_hit_vec;
    st_hit_any        = |st_hit_way_oh_raw;
    st_miss           = !st_hit_any;
    st_select_data    = '0;
    for (int w = 0; w < NUM_WAY; w++) if (st_hit_way_oh_raw[w]) st_select_data = st_data_rdata[w];
  end

  // ===========================================================================
  // Per-pipe PLRU eviction
  // ===========================================================================
  /* verilator lint_off UNOPTFLAT */
  logic [NUM_WAY-1:0] ld_evict_way, st_evict_way;
  logic [NUM_WAY-2:0] ld_updated_node, st_updated_node;

  always_comb begin
    ld_updated_node = update_node(ld_plru_rdata, ld_hit_way_oh);
    ld_evict_way    = compute_evict_way(ld_plru_rdata);
  end

  always_comb begin
    st_updated_node = update_node(st_plru_rdata, st_hit_way_oh_raw);
    st_evict_way    = compute_evict_way(st_plru_rdata);
  end
  /* verilator lint_on UNOPTFLAT */

  // Latched victim way (stable during miss handling)
  logic [NUM_WAY-1:0] ld_victim_way_q, st_victim_way_q;

  logic [NUM_WAY-1:0] ld_evict_way_sel, st_evict_way_sel;
  assign ld_evict_way_sel = ((ld_pipe_state == PIPE_WB_EVICT) || (ld_pipe_state == PIPE_MISS_WAIT) || (ld_pipe_state == PIPE_FILL_RESPOND)) ? ld_victim_way_q : ld_evict_way;
  assign st_evict_way_sel = ((st_pipe_state == PIPE_WB_EVICT) || (st_pipe_state == PIPE_MISS_WAIT) || (st_pipe_state == PIPE_FILL_RESPOND)) ? st_victim_way_q : st_evict_way;

  // ===========================================================================
  // Per-pipe eviction data
  // ===========================================================================
  logic                ld_evict_dirty;
  logic [TAG_SIZE-1:0] ld_evict_tag;
  logic [    XLEN-1:0] ld_evict_addr;
  logic [BLK_SIZE-1:0] ld_evict_data;

  always_comb begin
    ld_evict_dirty = 1'b0;
    ld_evict_tag   = '0;
    ld_evict_data  = '0;
    for (int w = 0; w < NUM_WAY; w++) begin
      if (ld_evict_way_sel[w]) begin
        ld_evict_dirty = ld_dirty_read[w] && ld_tag_rdata[w][TAG_SIZE];
        ld_evict_tag   = ld_tag_rdata[w][TAG_SIZE-1:0];
        ld_evict_data  = ld_data_rdata[w];
      end
    end
    ld_evict_addr = {ld_evict_tag, ld_req_set, {BOFFSET{1'b0}}};
  end

  logic                st_evict_dirty;
  logic [TAG_SIZE-1:0] st_evict_tag;
  logic [    XLEN-1:0] st_evict_addr;
  logic [BLK_SIZE-1:0] st_evict_data;

  always_comb begin
    st_evict_dirty = 1'b0;
    st_evict_tag   = '0;
    st_evict_data  = '0;
    for (int w = 0; w < NUM_WAY; w++) begin
      if (st_evict_way_sel[w]) begin
        st_evict_dirty = st_dirty_read[w] && st_tag_rdata[w][TAG_SIZE];
        st_evict_tag   = st_tag_rdata[w][TAG_SIZE-1:0];
        st_evict_data  = st_data_rdata[w];
      end
    end
    st_evict_addr = {st_evict_tag, st_req_set, {BOFFSET{1'b0}}};
  end

  // ===========================================================================
  // Write-merge for ST-pipe hit writes
  // ===========================================================================
  always_comb begin
    st_hit_wr_merged = st_select_data;
    case (st_req_q.rw_size)
      WORD:    st_hit_wr_merged[st_req_q.addr[BOFFSET-1:2]*32+:32] = st_req_q.wdata;
      HALF:    st_hit_wr_merged[st_req_q.addr[BOFFSET-1:1]*16+:16] = st_req_q.wdata[15:0];
      BYTE:    st_hit_wr_merged[st_req_q.addr[BOFFSET-1:0]*8+:8] = st_req_q.wdata[7:0];
      NO_SIZE: st_hit_wr_merged = st_select_data;
    endcase
  end

  // ===========================================================================
  // MSHR (central, shared between pipes)
  // ===========================================================================
  dc_mshr_entry_t mshr_entries[MSHR_DEPTH];

  logic [MSHR_DEPTH-1:0] ld_mshr_line_match, st_mshr_line_match;
  logic ld_mshr_any_match, st_mshr_any_match;
  logic [MSHR_DEPTH-1:0] mshr_free_vec;
  logic [MSHR_PTR_W-1:0] mshr_free_idx;
  logic                  mshr_any_free;
  logic [MSHR_DEPTH-1:0] mshr_pending_vec;
  logic [MSHR_PTR_W-1:0] mshr_pending_idx;
  logic                  mshr_pending_valid;
  logic [      XLEN-1:0] mshr_pending_addr;
  logic                  mshr_pending_from_st;
  logic [MSHR_DEPTH-1:0] mshr_complete_vec;
  logic [MSHR_DEPTH-1:0] mshr_fill_match_vec;
  logic [MSHR_PTR_W-1:0] mshr_fill_entry_idx;
  logic                  mshr_fill_from_st;
  logic [MSHR_DEPTH-1:0] mshr_wb_vec;
  logic                  mshr_wb_valid;

  logic ld_mshr_alloc_req, st_mshr_alloc_req;
  logic ld_mshr_full, st_mshr_full;
  logic ld_mshr_do_alloc, st_mshr_do_alloc;
  logic ld_fill_complete, st_fill_complete;
  logic ld_wb_req, st_wb_req;
  logic ld_fill_writing, st_fill_writing;
  logic ld_resolve_stall, st_resolve_stall;
  logic dual_miss_same_set;

  // MSHR line match (same cache line already in MSHR?)
  always_comb begin
    for (int i = 0; i < MSHR_DEPTH; i++) begin
      ld_mshr_line_match[i] = mshr_entries[i].valid && (mshr_entries[i].addr[XLEN-1:BOFFSET] == ld_req_q.addr[XLEN-1:BOFFSET]);
      st_mshr_line_match[i] = mshr_entries[i].valid && (mshr_entries[i].addr[XLEN-1:BOFFSET] == st_req_q.addr[XLEN-1:BOFFSET]);
    end
    ld_mshr_any_match = |ld_mshr_line_match;
    st_mshr_any_match = |st_mshr_line_match;
  end

  // Free entry search
  always_comb begin
    for (int i = 0; i < MSHR_DEPTH; i++) mshr_free_vec[i] = !mshr_entries[i].valid;
    mshr_any_free = |mshr_free_vec;
    mshr_free_idx = '0;
    for (int i = MSHR_DEPTH - 1; i >= 0; i--) if (mshr_free_vec[i]) mshr_free_idx = MSHR_PTR_W'(i);
  end

  assign ld_mshr_full = !mshr_any_free && !ld_mshr_any_match;
  assign st_mshr_full = !mshr_any_free && !st_mshr_any_match;

  // Allocation requests from RESOLVE stage
  assign ld_mshr_alloc_req = (ld_pipe_state == PIPE_TAG_LOOKUP) && ld_miss && !ld_resolve_stall && !ld_req_q.uncached;
  assign st_mshr_alloc_req = (st_pipe_state == PIPE_TAG_LOOKUP) && st_miss && !st_resolve_stall && !st_req_q.uncached;

  // LD wins on simultaneous alloc to same free slot
  assign ld_mshr_do_alloc = ld_mshr_alloc_req && !ld_mshr_any_match && !ld_mshr_full;
  assign st_mshr_do_alloc = st_mshr_alloc_req && !st_mshr_any_match && !st_mshr_full && !(ld_mshr_do_alloc && mshr_free_vec == (1 << mshr_free_idx));

  // Pending MSHR for memory controller
  always_comb begin
    for (int i = 0; i < MSHR_DEPTH; i++) mshr_pending_vec[i] = mshr_entries[i].valid && (mshr_entries[i].state == DC_MSHR_PENDING);
    mshr_pending_valid = |mshr_pending_vec;
    mshr_pending_idx   = '0;
    for (int i = MSHR_DEPTH - 1; i >= 0; i--) if (mshr_pending_vec[i]) mshr_pending_idx = MSHR_PTR_W'(i);
    mshr_pending_addr    = mshr_entries[mshr_pending_idx].addr;
    mshr_pending_from_st = mshr_entries[mshr_pending_idx].from_st;
  end

  // Fill matching (FILL_ACTIVE entry)
  always_comb begin
    for (int i = 0; i < MSHR_DEPTH; i++) mshr_fill_match_vec[i] = mshr_entries[i].valid && (mshr_entries[i].state == DC_MSHR_FILL_ACTIVE);
    mshr_fill_entry_idx = '0;
    for (int i = MSHR_DEPTH - 1; i >= 0; i--) if (mshr_fill_match_vec[i]) mshr_fill_entry_idx = MSHR_PTR_W'(i);
    mshr_fill_from_st = mshr_entries[mshr_fill_entry_idx].from_st;
  end

  // Complete entries
  always_comb begin
    for (int i = 0; i < MSHR_DEPTH; i++) mshr_complete_vec[i] = mshr_entries[i].valid && (mshr_entries[i].state == DC_MSHR_COMPLETE);
  end

  // WB pending entries
  always_comb begin
    for (int i = 0; i < MSHR_DEPTH; i++) mshr_wb_vec[i] = mshr_entries[i].valid && (mshr_entries[i].state == DC_MSHR_WB_PENDING);
    mshr_wb_valid = |mshr_wb_vec;
  end

  // ===========================================================================
  // Memory controller signals
  // ===========================================================================
  logic                      fill_resp_valid;
  logic       [BLK_SIZE-1:0] fill_resp_data;
  logic                      fill_issued;
  logic                      wb_done;
  logic                      mem_busy;
  logic       [    XLEN-1:0] mem_addr_q;
  logic       [BLK_SIZE-1:0] mem_data_q;
  mem_state_t                mem_state;
  logic                      wb_from_st;

  // Fill routing to pipes
  assign ld_fill_complete = fill_resp_valid && !mshr_fill_from_st;
  assign st_fill_complete = fill_resp_valid && mshr_fill_from_st;

  // WB/fill requests
  assign ld_wb_req = (ld_pipe_state == PIPE_WB_EVICT);
  assign st_wb_req = (st_pipe_state == PIPE_WB_EVICT);

  logic ld_miss_wait, st_miss_wait;
  assign ld_miss_wait = (ld_pipe_state == PIPE_MISS_WAIT);
  assign st_miss_wait = (st_pipe_state == PIPE_MISS_WAIT);

  logic fill_req_valid, wb_req_valid;
  assign fill_req_valid = (ld_miss_wait || st_miss_wait) && mshr_pending_valid && !mem_busy;
  assign wb_req_valid = (ld_wb_req || st_wb_req) && !mem_busy;

  // ===========================================================================
  // Set-conflict hazard detection
  // ===========================================================================


  assign ld_fill_writing = (ld_pipe_state == PIPE_FILL_RESPOND);
  assign st_fill_writing = (st_pipe_state == PIPE_FILL_RESPOND);

  assign ld_resolve_stall = (ld_pipe_state == PIPE_TAG_LOOKUP) && (st_fill_writing && st_req_set == ld_req_set);
  assign st_resolve_stall = (st_pipe_state == PIPE_TAG_LOOKUP) && (ld_fill_writing && ld_req_set == st_req_set);

  // If both pipes miss same set, ST defers to LD
  assign dual_miss_same_set = (ld_pipe_state == PIPE_TAG_LOOKUP) && ld_miss && (st_pipe_state == PIPE_TAG_LOOKUP) && st_miss && (ld_req_set == st_req_set);

  // ===========================================================================
  // MSHR state machine
  // ===========================================================================
  logic ld_mshr_resp_accepted, st_mshr_resp_accepted;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      for (int i = 0; i < MSHR_DEPTH; i++) mshr_entries[i] <= '0;
    end else begin
      // LD-pipe allocation
      if (ld_mshr_do_alloc) begin
        mshr_entries[mshr_free_idx].valid      <= 1'b1;
        mshr_entries[mshr_free_idx].state      <= ld_evict_dirty ? DC_MSHR_WB_PENDING : DC_MSHR_PENDING;
        mshr_entries[mshr_free_idx].addr       <= ld_req_q.addr;
        mshr_entries[mshr_free_idx].is_write   <= ld_req_q.is_write;
        mshr_entries[mshr_free_idx].rw_size    <= ld_req_q.rw_size;
        mshr_entries[mshr_free_idx].wdata      <= ld_req_q.wdata;
        mshr_entries[mshr_free_idx].from_st    <= 1'b0;
        mshr_entries[mshr_free_idx].victim_way <= ld_evict_way;
        mshr_entries[mshr_free_idx].uncached   <= 1'b0;
      end

      // ST-pipe allocation
      if (st_mshr_do_alloc) begin
        automatic logic [MSHR_PTR_W-1:0] st_idx;
        if (ld_mshr_do_alloc) begin
          st_idx = '0;
          for (int i = MSHR_DEPTH - 1; i >= 0; i--) if (mshr_free_vec[i] && MSHR_PTR_W'(i) != mshr_free_idx) st_idx = MSHR_PTR_W'(i);
        end else begin
          st_idx = mshr_free_idx;
        end
        mshr_entries[st_idx].valid      <= 1'b1;
        mshr_entries[st_idx].state      <= st_evict_dirty ? DC_MSHR_WB_PENDING : DC_MSHR_PENDING;
        mshr_entries[st_idx].addr       <= st_req_q.addr;
        mshr_entries[st_idx].is_write   <= st_req_q.is_write;
        mshr_entries[st_idx].rw_size    <= st_req_q.rw_size;
        mshr_entries[st_idx].wdata      <= st_req_q.wdata;
        mshr_entries[st_idx].from_st    <= 1'b1;
        mshr_entries[st_idx].victim_way <= st_evict_way;
        mshr_entries[st_idx].uncached   <= 1'b0;
      end

      // Fill issued → PENDING → FILL_ACTIVE
      if (fill_issued) mshr_entries[mshr_pending_idx].state <= DC_MSHR_FILL_ACTIVE;

      // Fill response → FILL_ACTIVE → COMPLETE
      if (fill_resp_valid && |mshr_fill_match_vec) mshr_entries[mshr_fill_entry_idx].state <= DC_MSHR_COMPLETE;

      // Response accepted → clear entry
      if (ld_mshr_resp_accepted) begin
        for (int i = 0; i < MSHR_DEPTH; i++)
        if (mshr_entries[i].valid && mshr_entries[i].state == DC_MSHR_COMPLETE && !mshr_entries[i].from_st) begin
          mshr_entries[i].valid <= 1'b0;
          mshr_entries[i].state <= DC_MSHR_IDLE;
          break;
        end
      end
      if (st_mshr_resp_accepted) begin
        for (int i = 0; i < MSHR_DEPTH; i++)
        if (mshr_entries[i].valid && mshr_entries[i].state == DC_MSHR_COMPLETE && mshr_entries[i].from_st) begin
          mshr_entries[i].valid <= 1'b0;
          mshr_entries[i].state <= DC_MSHR_IDLE;
          break;
        end
      end

      // WB done → WB_PENDING → PENDING
      if (mshr_wb_valid && wb_done) begin
        for (int i = 0; i < MSHR_DEPTH; i++) if (mshr_entries[i].valid && mshr_entries[i].state == DC_MSHR_WB_PENDING) mshr_entries[i].state <= DC_MSHR_PENDING;
      end
    end
  end

  // ===========================================================================
  // Memory controller FSM
  // ===========================================================================
  assign mem_busy = (mem_state != MEM_IDLE);

  // Bypass mux signals
  logic ld_bypass_active, st_bypass_active;
  assign ld_bypass_active = (ld_pipe_state == PIPE_BYPASS);
  assign st_bypass_active = (st_pipe_state == PIPE_BYPASS);

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      mem_state       <= MEM_IDLE;
      mem_addr_q      <= '0;
      mem_data_q      <= '0;
      fill_resp_valid <= 1'b0;
      fill_resp_data  <= '0;
      fill_issued     <= 1'b0;
      wb_done         <= 1'b0;
      wb_from_st      <= 1'b0;
    end else begin
      fill_resp_valid <= 1'b0;
      fill_issued     <= 1'b0;
      wb_done         <= 1'b0;

      unique case (mem_state)
        MEM_IDLE: begin
          if (wb_req_valid) begin
            mem_state <= MEM_WB_SEND;
            if (st_wb_req && !ld_wb_req) begin
              mem_addr_q <= st_evict_addr;
              mem_data_q <= st_evict_data;
              wb_from_st <= 1'b1;
            end else begin
              mem_addr_q <= ld_evict_addr;
              mem_data_q <= ld_evict_data;
              wb_from_st <= 1'b0;
            end
          end else if (fill_req_valid) begin
            mem_state   <= MEM_FILL_SEND;
            mem_addr_q  <= {mshr_pending_addr[XLEN-1:BOFFSET], {BOFFSET{1'b0}}};
            fill_issued <= 1'b1;
          end
        end

        MEM_WB_SEND: begin
          if (lowX_res_i.valid) begin
            wb_done <= 1'b1;
            if (fill_req_valid) begin
              mem_state   <= MEM_FILL_SEND;
              mem_addr_q  <= {mshr_pending_addr[XLEN-1:BOFFSET], {BOFFSET{1'b0}}};
              fill_issued <= 1'b1;
            end else begin
              mem_state <= MEM_IDLE;
            end
          end
        end

        MEM_FILL_SEND: begin
          if (lowX_res_i.valid) begin
            fill_resp_valid <= 1'b1;
            fill_resp_data  <= lowX_res_i.data;
            mem_state       <= MEM_IDLE;
          end
        end

        default: mem_state <= MEM_IDLE;
      endcase
    end
  end

  // Memory controller output mux + bypass
  always_comb begin
    if (fi_writeback_req) begin
      // fence.i writeback has highest priority
      lowX_req_o.valid    = 1'b1;
      lowX_req_o.ready    = 1'b1;
      lowX_req_o.uncached = 1'b0;
      lowX_req_o.addr     = fi_evict_addr;
      lowX_req_o.rw       = 1'b1;
      lowX_req_o.rw_size  = WORD;
      lowX_req_o.data     = fi_evict_data;
    end else if (ld_bypass_active) begin
      lowX_req_o.valid    = 1'b1;
      lowX_req_o.ready    = 1'b1;
      lowX_req_o.addr     = ld_req_q.addr;
      lowX_req_o.data     = '0;
      lowX_req_o.rw       = 1'b0;
      lowX_req_o.rw_size  = ld_req_q.rw_size;
      lowX_req_o.uncached = 1'b1;
    end else if (st_bypass_active) begin
      lowX_req_o.valid    = 1'b1;
      lowX_req_o.ready    = 1'b1;
      lowX_req_o.addr     = st_req_q.addr;
      lowX_req_o.data     = BLK_SIZE'(st_req_q.wdata);
      lowX_req_o.rw       = st_req_q.is_write;
      lowX_req_o.rw_size  = st_req_q.rw_size;
      lowX_req_o.uncached = 1'b1;
    end else begin
      lowX_req_o.valid    = 1'b0;
      lowX_req_o.ready    = 1'b1;
      lowX_req_o.addr     = mem_addr_q;
      lowX_req_o.data     = mem_data_q;
      lowX_req_o.rw       = '0;
      lowX_req_o.rw_size  = WORD;
      lowX_req_o.uncached = 1'b0;
      unique case (mem_state)
        MEM_WB_SEND: begin
          lowX_req_o.valid = 1'b1;
          lowX_req_o.rw    = 1'b1;
        end
        MEM_FILL_SEND: begin
          lowX_req_o.valid = 1'b1;
          lowX_req_o.rw    = '0;
        end
        default: ;
      endcase
    end
  end

  // ===========================================================================
  // Write-merge for fill write (MSHR write data merged into fill line)
  // ===========================================================================
  logic [BLK_SIZE-1:0] fill_merged_data;
  always_comb begin
    fill_merged_data = fill_resp_data;
    // If the MSHR entry was a write, merge store data into the fill line
    if (mshr_entries[mshr_fill_entry_idx].is_write) begin
      automatic logic [XLEN-1:0] maddr = mshr_entries[mshr_fill_entry_idx].addr;
      automatic logic [    31:0] mdata = mshr_entries[mshr_fill_entry_idx].wdata;
      case (mshr_entries[mshr_fill_entry_idx].rw_size)
        WORD:    fill_merged_data[maddr[BOFFSET-1:2]*32+:32] = mdata;
        HALF:    fill_merged_data[maddr[BOFFSET-1:1]*16+:16] = mdata[15:0];
        BYTE:    fill_merged_data[maddr[BOFFSET-1:0]*8+:8] = mdata[7:0];
        NO_SIZE: ;
      endcase
    end
  end

  // ===========================================================================
  // LD-pipe SRAM control
  // ===========================================================================
  always_comb begin
    ld_tag_we    = '0;
    ld_tag_wdata = '0;
    ld_data_we   = '0;
    ld_data_wdata = '0;

    if (flush_active) begin
      ld_tag_we    = '1;
      ld_tag_wdata = '0;
    end else if (ld_fill_complete) begin
      ld_tag_we    = ld_evict_way_sel;
      ld_tag_wdata = {1'b1, ld_req_tag};
      ld_data_we   = ld_evict_way_sel;
      ld_data_wdata = fill_merged_data;
    end
  end

  // ===========================================================================
  // ST-pipe SRAM control
  // ===========================================================================
  always_comb begin
    st_tag_we    = '0;
    st_tag_wdata = '0;
    st_data_we   = '0;
    st_data_wdata = '0;

    if (st_pipe_state == PIPE_HIT_RESPOND && st_req_q.is_write) begin
      st_data_we    = st_hit_way_oh_raw;
      st_data_wdata = st_hit_wr_merged;
    end else if (st_fill_complete) begin
      st_tag_we    = st_evict_way_sel;
      st_tag_wdata = {1'b1, st_req_tag};
      st_data_we   = st_evict_way_sel;
      st_data_wdata = fill_merged_data;
    end
  end

  // ===========================================================================
  // PLRU update control
  // ===========================================================================
  always_comb begin
    ld_plru_wr    = 1'b0;
    ld_plru_wdata = '0;
    if (ld_hit_respond) begin
      ld_plru_wr    = 1'b1;
      ld_plru_wdata = ld_updated_node;
    end else if (ld_pipe_state == PIPE_FILL_RESPOND) begin
      ld_plru_wr    = 1'b1;
      ld_plru_wdata = update_node(ld_plru_rdata, ld_evict_way_sel);
    end
  end

  always_comb begin
    st_plru_wr    = 1'b0;
    st_plru_wdata = '0;
    if (st_pipe_state == PIPE_HIT_RESPOND) begin
      st_plru_wr    = 1'b1;
      st_plru_wdata = st_updated_node;
    end else if (st_pipe_state == PIPE_FILL_RESPOND) begin
      st_plru_wr    = 1'b1;
      st_plru_wdata = update_node(st_plru_rdata, st_evict_way_sel);
    end
  end

  // Helper: extract ST-pipe hit way for merged PLRU update
  function automatic [NUM_WAY-1:0] st_hit_way_oh();
    if (st_pipe_state == PIPE_HIT_RESPOND) return st_hit_way_oh_raw;
    else return st_evict_way_sel;
  endfunction

  // ===========================================================================
  // Dirty update control
  // ===========================================================================
  always_comb begin
    ld_dirty_wr  = 1'b0;
    ld_dirty_idx = ld_req_set;
    ld_dirty_way = '0;
    ld_dirty_val = 1'b0;
    if (ld_fill_complete) begin
      ld_dirty_wr  = 1'b1;
      ld_dirty_way = ld_evict_way_sel;
      ld_dirty_val = ld_req_q.is_write;
    end
  end

  always_comb begin
    st_dirty_wr  = 1'b0;
    st_dirty_idx = fi_active ? fi_set_idx_q : st_req_set;
    st_dirty_way = '0;
    st_dirty_val = 1'b0;
    if (fi_mark_clean) begin
      st_dirty_wr  = 1'b1;
      st_dirty_way = fi_way_onehot;
      st_dirty_val = 1'b0;
    end else if (st_pipe_state == PIPE_HIT_RESPOND && st_req_q.is_write) begin
      st_dirty_wr  = 1'b1;
      st_dirty_way = st_hit_way_oh_raw;
      st_dirty_val = 1'b1;
    end else if (st_fill_complete) begin
      st_dirty_wr  = 1'b1;
      st_dirty_way = st_evict_way_sel;
      st_dirty_val = st_req_q.is_write;
    end
  end

  // ===========================================================================
  // Quiescent indicator: both pipes idle, all MSHRs drained, mem controller idle
  // Used by memory.sv to gate fence.i flush until all in-flight ops complete.
  // ===========================================================================
  logic mshr_all_empty;
  always_comb begin
    mshr_all_empty = 1'b1;
    for (int i = 0; i < MSHR_DEPTH; i++) if (mshr_entries[i].valid) mshr_all_empty = 1'b0;
  end

  assign pipes_idle_o = (ld_pipe_state == PIPE_IDLE) && (st_pipe_state == PIPE_IDLE) && mshr_all_empty && (mem_state == MEM_IDLE);

  // ===========================================================================
  // Fence.i helper (uses ST-pipe's Port B for SRAM reads)
  // Gate flush_i so fence.i only starts when cache is fully quiescent —
  // both pipes idle, all MSHRs drained, memory controller idle.
  // ===========================================================================
  logic fi_flush_gated;
  assign fi_flush_gated = flush_i && pipes_idle_o;

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
      .flush_i         (fi_flush_gated),
      .lowx_res_ready  (lowX_res_i.ready),
      .lowx_res_valid  (lowX_res_i.valid),
      .drsram_rd_rdirty(st_dirty_read),
      .tsram_rtag      (st_tag_rdata),
      .dsram_rdata     (st_data_rdata),
      .fi_active       (fi_active),
      .fi_writeback_req(fi_writeback_req),
      .fi_mark_clean   (fi_mark_clean),
      .fi_evict_tag    (fi_evict_tag),
      .fi_evict_data   (fi_evict_data),
      .fi_evict_addr   (fi_evict_addr),
      .fi_way_onehot   (fi_way_onehot),
      .fi_set_idx      (fi_set_idx_q)
  );

  assign fencei_stall_o = fi_active || (flush_i && !pipes_idle_o);

  // ===========================================================================
  // LD-pipe FSM
  // ===========================================================================
  logic ld_pipe_accept;
  assign ld_pipe_accept = (ld_pipe_state == PIPE_IDLE) && !flush_active && !fi_active && ld_req_i.valid;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      ld_pipe_state         <= PIPE_IDLE;
      ld_req_q              <= '0;
      ld_mshr_resp_accepted <= 1'b0;
      ld_victim_way_q       <= '0;
    end else begin
      ld_mshr_resp_accepted <= 1'b0;

      unique case (ld_pipe_state)
        PIPE_IDLE: begin
          if (ld_pipe_accept) begin
            ld_req_q.addr     <= ld_req_i.addr;
            ld_req_q.is_write <= ld_req_i.rw;
            ld_req_q.rw_size  <= ld_req_i.rw_size;
            ld_req_q.wdata    <= ld_req_i.data;
            ld_req_q.uncached <= ld_req_i.uncached;
            ld_pipe_state     <= ld_req_i.uncached ? PIPE_BYPASS : PIPE_TAG_LOOKUP;
          end
        end

        PIPE_TAG_LOOKUP: begin
          // SRAM data valid this cycle — resolve hit/miss combinationally
          if (ld_resolve_stall || (ld_mshr_any_match && ld_miss && !ld_req_q.uncached)) begin
            ld_pipe_state <= PIPE_TAG_LOOKUP;  // retry (re-read same set)
          end else if (ld_hit_any) begin
            // 1-cycle hit: respond combinationally this cycle, return to IDLE
            ld_pipe_state <= PIPE_IDLE;
          end else if (ld_mshr_full) begin
            ld_pipe_state <= PIPE_TAG_LOOKUP;  // structural stall — retry
          end else if (ld_evict_dirty) begin
            ld_victim_way_q <= ld_evict_way;
            ld_pipe_state   <= PIPE_WB_EVICT;
          end else begin
            ld_victim_way_q <= ld_evict_way;
            ld_pipe_state   <= PIPE_MISS_WAIT;
          end
        end

        PIPE_WB_EVICT: if (wb_done && !wb_from_st) ld_pipe_state <= PIPE_MISS_WAIT;

        PIPE_MISS_WAIT: if (ld_fill_complete) ld_pipe_state <= PIPE_FILL_RESPOND;

        PIPE_FILL_RESPOND: begin
          ld_mshr_resp_accepted <= 1'b1;
          ld_pipe_state <= PIPE_IDLE;
        end

        PIPE_BYPASS: if (lowX_res_i.valid && !st_bypass_active && !fi_writeback_req) ld_pipe_state <= PIPE_IDLE;

        default: ld_pipe_state <= PIPE_IDLE;
      endcase
    end
  end

  // ===========================================================================
  // ST-pipe FSM
  // ===========================================================================
  logic st_pipe_accept;
  assign st_pipe_accept = (st_pipe_state == PIPE_IDLE) && !flush_active && !fi_active && st_req_i.valid;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      st_pipe_state         <= PIPE_IDLE;
      st_req_q              <= '0;
      st_mshr_resp_accepted <= 1'b0;
      st_victim_way_q       <= '0;
    end else begin
      st_mshr_resp_accepted <= 1'b0;

      unique case (st_pipe_state)
        PIPE_IDLE: begin
          if (st_pipe_accept) begin
            st_req_q.addr     <= st_req_i.addr;
            st_req_q.is_write <= st_req_i.rw;
            st_req_q.rw_size  <= st_req_i.rw_size;
            st_req_q.wdata    <= st_req_i.data;
            st_req_q.uncached <= st_req_i.uncached;
            st_pipe_state     <= st_req_i.uncached ? PIPE_BYPASS : PIPE_TAG_LOOKUP;
          end
        end

        PIPE_TAG_LOOKUP: begin
          // SRAM data valid this cycle — resolve hit/miss combinationally
          if (st_resolve_stall || dual_miss_same_set || (st_mshr_any_match && st_miss && !st_req_q.uncached)) begin
            st_pipe_state <= PIPE_TAG_LOOKUP;  // retry (re-read same set)
          end else if (st_hit_any) begin
            st_pipe_state <= PIPE_HIT_RESPOND;
          end else if (st_mshr_full) begin
            st_pipe_state <= PIPE_TAG_LOOKUP;  // structural stall — retry
          end else if (st_evict_dirty) begin
            st_victim_way_q <= st_evict_way;
            st_pipe_state   <= PIPE_WB_EVICT;
          end else begin
            st_victim_way_q <= st_evict_way;
            st_pipe_state   <= PIPE_MISS_WAIT;
          end
        end

        PIPE_HIT_RESPOND: st_pipe_state <= PIPE_IDLE;

        PIPE_WB_EVICT: if (wb_done && wb_from_st) st_pipe_state <= PIPE_MISS_WAIT;

        PIPE_MISS_WAIT: if (st_fill_complete) st_pipe_state <= PIPE_FILL_RESPOND;

        PIPE_FILL_RESPOND: begin
          st_mshr_resp_accepted <= 1'b1;
          st_pipe_state <= PIPE_IDLE;
        end

        PIPE_BYPASS: begin
          if (lowX_res_i.valid && !ld_bypass_active && !fi_writeback_req) st_pipe_state <= PIPE_IDLE;
        end

        default: st_pipe_state <= PIPE_IDLE;
      endcase
    end
  end

  // ===========================================================================
  // Response outputs
  // ===========================================================================
  logic [WOFFSET-1:0] ld_word_idx, st_word_idx;
  assign ld_word_idx = ld_req_q.addr[(WOFFSET+2)-1:2];
  assign st_word_idx = st_req_q.addr[(WOFFSET+2)-1:2];

  // 1-cycle LD hit: respond in TAG_LOOKUP when hit detected
  logic ld_hit_respond;
  assign ld_hit_respond = (ld_pipe_state == PIPE_TAG_LOOKUP) && ld_hit_any && !ld_resolve_stall && !(ld_mshr_any_match && ld_miss && !ld_req_q.uncached);

  // LD response
  always_comb begin
    ld_res_o.valid = 1'b0;
    ld_res_o.miss  = 1'b0;
    ld_res_o.ready = (ld_pipe_state == PIPE_IDLE) && !flush_active && !fi_active;
    ld_res_o.data  = '0;

    if (ld_hit_respond) begin
      ld_res_o.valid = 1'b1;
      ld_res_o.data  = ld_select_data[ld_word_idx*32+:32];
    end else if (ld_pipe_state == PIPE_FILL_RESPOND) begin
      ld_res_o.valid = 1'b1;
      ld_res_o.data  = fill_merged_data[ld_word_idx*32+:32];
    end else if (ld_bypass_active && lowX_res_i.valid && !st_bypass_active && !fi_writeback_req) begin
      ld_res_o.valid = 1'b1;
      ld_res_o.data  = lowX_res_i.data[ld_word_idx*32+:32];
    end
  end

  // ST response
  always_comb begin
    st_res_o.valid = 1'b0;
    st_res_o.miss  = 1'b0;
    st_res_o.ready = (st_pipe_state == PIPE_IDLE) && !flush_active && !fi_active;
    st_res_o.data  = '0;

    if (st_pipe_state == PIPE_HIT_RESPOND) begin
      st_res_o.valid = 1'b1;
      st_res_o.data  = st_select_data[st_word_idx*32+:32];
    end else if (st_pipe_state == PIPE_FILL_RESPOND) begin
      st_res_o.valid = 1'b1;
      st_res_o.data  = fill_merged_data[st_word_idx*32+:32];
    end else if (st_bypass_active && lowX_res_i.valid && !ld_bypass_active && !fi_writeback_req) begin
      st_res_o.valid = 1'b1;
      st_res_o.data  = lowX_res_i.data[st_word_idx*32+:32];
    end
  end

  // ===========================================================================
  // Helper functions (PLRU)
  // ===========================================================================
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
