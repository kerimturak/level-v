/*
 * Non-Blocking Dual-Port D-Cache with MSHR — Miss-Under-Miss
 *
 * Architecture:
 *   Load port (ld)  ──► LD-pipe FSM ──┐
 *                                      ├──► shared MSHR ──► mem controller → lowX (L2)
 *   Store port (st) ──► ST-pipe FSM ──┘          │
 *                                           fill writer ──► SRAM write-back + response
 *
 * Design:
 *   - Miss-under-miss: pipes return to IDLE after MSHR allocation, freeing the port
 *     for new requests while fills are in-flight.
 *   - MSHR entries store eviction data for autonomous writeback by memory controller.
 *   - Fill writer monitors MSHR_COMPLETE entries, arbitrates SRAM write ports, writes
 *     fill data, and generates response pulses back to memory.sv.
 *   - Dual-port dp_bram: Port A = LD pipe reads + LD fill writes,
 *                         Port B = ST pipe reads/writes + ST fill writes
 *   - Register-based PLRU (dual read, merged update)
 *   - Register-based dirty array (dual read, merged update)
 *   - Parametric multi-bank support (DC_NUM_BANK)
 *   - Set-conflict hazard protection between pipelines and fill writer
 *   - fence.i dirty writeback via dcache_fencei helper
 *
 * Pipeline timing (per pipe):
 *   Cycle 0 (IDLE):       Request accepted, address driven to SRAMs
 *   Cycle 1 (TAG_LOOKUP): Registered SRAM outputs settle; hit/miss resolved combinationally.
 *                          LD hit → respond same cycle, return to IDLE (1-cycle hit).
 *                          ST hit → HIT_RESPOND (SRAM write next cycle, 2-cycle hit).
 *                          Miss → allocate MSHR (with eviction data) → return to IDLE.
 *   Fill writer:           Asynchronously writes completed fills to SRAM and responds.
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
  typedef enum logic [1:0] {
    PIPE_IDLE,
    PIPE_TAG_LOOKUP,
    PIPE_HIT_RESPOND,
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
  // Flush logic — tag invalidation
  // Only triggers on reset. Run-time flush_i (fence.i) must NOT invalidate
  // D-cache tags — only dirty writeback (via dcache_fencei FSM) is needed.
  // D-cache data and tags are preserved across fence.i; the I-cache handles
  // its own invalidation separately.
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

  // Forward-declare fill writer signals needed for SRAM address mux
  logic fw_ld_writing_fwd, fw_st_writing_fwd;
  logic [IDX_WIDTH-1:0] fw_ld_set_fwd, fw_st_set_fwd;

  assign ld_sram_idx = flush_active ? flush_cnt : fw_ld_writing_fwd ? fw_ld_set_fwd : (ld_pipe_state == PIPE_IDLE) ? ld_next_set : ld_req_set;

  assign st_sram_idx = fi_active ? fi_set_idx_q : fw_st_writing_fwd ? fw_st_set_fwd : (st_pipe_state == PIPE_IDLE) ? st_next_set : st_req_set;

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

  // Latched victim way — no longer used by pipe FSM for miss handling;
  // eviction way is stored directly in MSHR entry during allocation.
  // Kept for potential future use.
  logic [NUM_WAY-1:0] ld_victim_way_q, st_victim_way_q;

  logic [NUM_WAY-1:0] ld_evict_way_sel, st_evict_way_sel;
  assign ld_evict_way_sel = ld_evict_way;
  assign st_evict_way_sel = st_evict_way;

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

  // Fill routing to pipes (via fill writer, not pipe FSM)
  assign ld_fill_complete = fill_resp_valid && !mshr_fill_from_st;
  assign st_fill_complete = fill_resp_valid && mshr_fill_from_st;

  // WB requests now come from MSHR (autonomous), no pipe involvement
  logic ld_miss_wait, st_miss_wait;
  assign ld_miss_wait = 1'b0;  // pipes no longer have MISS_WAIT state
  assign st_miss_wait = 1'b0;

  // Memory controller servicing: autonomous from MSHR state
  logic fill_req_valid, wb_req_valid;
  assign fill_req_valid = mshr_pending_valid && !mem_busy;
  assign wb_req_valid   = mshr_wb_valid && !mem_busy;

  // Forward declarations — Mentor/Questa vlog requires names before first use
  // (assigns for these signals appear in the fill-writer / pipe sections below).
  logic fw_ld_writing, fw_st_writing;
  logic [IDX_WIDTH-1:0] fw_ld_set, fw_st_set;
  logic ld_pipe_retrying, st_pipe_retrying;
  logic ld_pipe_accept, st_pipe_accept;
  logic ld_hit_respond;

  // ===========================================================================
  // Set-conflict hazard detection
  // ===========================================================================

  // Fill writer drives SRAM writes — stall pipe if it's writing to the same set
  assign ld_fill_writing = fw_ld_writing;
  assign st_fill_writing = fw_st_writing;

  // When fill writer preempts a retrying pipe, the SRAM reads are from the fill
  // set, not the pipe set. Force 1-cycle re-read stall after preemption.
  logic ld_fw_preempted_q, st_fw_preempted_q;
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      ld_fw_preempted_q <= 1'b0;
      st_fw_preempted_q <= 1'b0;
    end else begin
      ld_fw_preempted_q <= fw_ld_writing && ld_pipe_retrying;
      st_fw_preempted_q <= fw_st_writing && st_pipe_retrying;
    end
  end

  assign ld_resolve_stall = (ld_pipe_state == PIPE_TAG_LOOKUP) && ((st_fill_writing && fw_st_set == ld_req_set) ||  // cross-port fill conflict
      (fw_ld_writing && ld_pipe_retrying) ||  // same-port fill preemption
      ld_fw_preempted_q);  // re-read after preemption

  assign st_resolve_stall = (st_pipe_state == PIPE_TAG_LOOKUP) && ((ld_fill_writing && fw_ld_set == st_req_set) ||  // cross-port fill conflict
      (fw_st_writing && st_pipe_retrying) ||  // same-port fill preemption
      st_fw_preempted_q);  // re-read after preemption

  // If both pipes miss same set, ST defers to LD
  assign dual_miss_same_set = (ld_pipe_state == PIPE_TAG_LOOKUP) && ld_miss && (st_pipe_state == PIPE_TAG_LOOKUP) && st_miss && (ld_req_set == st_req_set);

  // Also stall TAG_LOOKUP if the set has an in-flight MSHR entry (fill writer may
  // write to that set at any time). This prevents SRAM read/write port conflicts.
  logic ld_mshr_set_conflict, st_mshr_set_conflict;
  always_comb begin
    ld_mshr_set_conflict = 1'b0;
    st_mshr_set_conflict = 1'b0;
    for (int i = 0; i < MSHR_DEPTH; i++) begin
      if (mshr_entries[i].valid && mshr_entries[i].state == DC_MSHR_COMPLETE) begin
        if (!mshr_entries[i].from_st && mshr_entries[i].addr[IDX_WIDTH+BOFFSET-1:BOFFSET] == ld_req_set) ld_mshr_set_conflict = 1'b1;
        if (mshr_entries[i].from_st && mshr_entries[i].addr[IDX_WIDTH+BOFFSET-1:BOFFSET] == st_req_set) st_mshr_set_conflict = 1'b1;
      end
    end
  end

  // 1-cycle LD hit: TAG_LOOKUP when hit resolves (needs ld_mshr_set_conflict above)
  assign ld_hit_respond = (ld_pipe_state == PIPE_TAG_LOOKUP) && ld_hit_any && !ld_resolve_stall && !ld_mshr_set_conflict && !(ld_mshr_any_match && ld_miss && !ld_req_q.uncached);

  // ===========================================================================
  // MSHR state machine
  // ===========================================================================
  // Fill writer control signals (forward declarations)
  logic fw_ld_done, fw_st_done, fw_ld_accepted, fw_st_accepted;
  logic [MSHR_PTR_W-1:0] fw_ld_idx, fw_st_idx;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      for (int i = 0; i < MSHR_DEPTH; i++) mshr_entries[i] <= '0;
    end else begin
      // LD-pipe allocation (with eviction data for autonomous WB)
      if (ld_mshr_do_alloc) begin
        mshr_entries[mshr_free_idx].valid       <= 1'b1;
        mshr_entries[mshr_free_idx].state       <= ld_evict_dirty ? DC_MSHR_WB_PENDING : DC_MSHR_PENDING;
        mshr_entries[mshr_free_idx].addr        <= ld_req_q.addr;
        mshr_entries[mshr_free_idx].is_write    <= ld_req_q.is_write;
        mshr_entries[mshr_free_idx].rw_size     <= ld_req_q.rw_size;
        mshr_entries[mshr_free_idx].wdata       <= ld_req_q.wdata;
        mshr_entries[mshr_free_idx].from_st     <= 1'b0;
        mshr_entries[mshr_free_idx].victim_way  <= ld_evict_way;
        mshr_entries[mshr_free_idx].uncached    <= 1'b0;
        mshr_entries[mshr_free_idx].evict_dirty <= ld_evict_dirty;
        mshr_entries[mshr_free_idx].evict_addr  <= ld_evict_addr;
        mshr_entries[mshr_free_idx].evict_data  <= ld_evict_data;
        mshr_entries[mshr_free_idx].fill_data   <= '0;
      end

      // ST-pipe allocation (with eviction data for autonomous WB)
      if (st_mshr_do_alloc) begin
        automatic logic [MSHR_PTR_W-1:0] st_idx;
        if (ld_mshr_do_alloc) begin
          st_idx = '0;
          for (int i = MSHR_DEPTH - 1; i >= 0; i--) if (mshr_free_vec[i] && MSHR_PTR_W'(i) != mshr_free_idx) st_idx = MSHR_PTR_W'(i);
        end else begin
          st_idx = mshr_free_idx;
        end
        mshr_entries[st_idx].valid       <= 1'b1;
        mshr_entries[st_idx].state       <= st_evict_dirty ? DC_MSHR_WB_PENDING : DC_MSHR_PENDING;
        mshr_entries[st_idx].addr        <= st_req_q.addr;
        mshr_entries[st_idx].is_write    <= st_req_q.is_write;
        mshr_entries[st_idx].rw_size     <= st_req_q.rw_size;
        mshr_entries[st_idx].wdata       <= st_req_q.wdata;
        mshr_entries[st_idx].from_st     <= 1'b1;
        mshr_entries[st_idx].victim_way  <= st_evict_way;
        mshr_entries[st_idx].uncached    <= 1'b0;
        mshr_entries[st_idx].evict_dirty <= st_evict_dirty;
        mshr_entries[st_idx].evict_addr  <= st_evict_addr;
        mshr_entries[st_idx].evict_data  <= st_evict_data;
        mshr_entries[st_idx].fill_data   <= '0;
      end

      // Fill issued → PENDING → FILL_ACTIVE
      if (fill_issued) mshr_entries[mshr_pending_idx].state <= DC_MSHR_FILL_ACTIVE;

      // Fill response → FILL_ACTIVE → COMPLETE (with fill data stored)
      if (fill_resp_valid && |mshr_fill_match_vec) begin
        mshr_entries[mshr_fill_entry_idx].state     <= DC_MSHR_COMPLETE;
        mshr_entries[mshr_fill_entry_idx].fill_data <= fill_resp_data;
      end

      // Fill writer accepted → clear entry
      if (fw_ld_accepted) begin
        for (int i = 0; i < MSHR_DEPTH; i++)
        if (mshr_entries[i].valid && mshr_entries[i].state == DC_MSHR_IDLE && !mshr_entries[i].from_st) begin
          mshr_entries[i].valid <= 1'b0;
          break;
        end
      end
      if (fw_st_accepted) begin
        for (int i = 0; i < MSHR_DEPTH; i++)
        if (mshr_entries[i].valid && mshr_entries[i].state == DC_MSHR_IDLE && mshr_entries[i].from_st) begin
          mshr_entries[i].valid <= 1'b0;
          break;
        end
      end

      // WB done → WB_PENDING → PENDING (memory controller handled WB from MSHR data)
      if (mshr_wb_valid && wb_done) begin
        for (int i = 0; i < MSHR_DEPTH; i++) if (mshr_entries[i].valid && mshr_entries[i].state == DC_MSHR_WB_PENDING) mshr_entries[i].state <= DC_MSHR_PENDING;
      end

      // Fill writer writes SRAM → COMPLETE → IDLE (entry pending dealloc)
      if (fw_ld_done) begin
        mshr_entries[fw_ld_idx].state <= DC_MSHR_IDLE;
      end
      if (fw_st_done) begin
        mshr_entries[fw_st_idx].state <= DC_MSHR_IDLE;
      end
    end
  end

  // ===========================================================================
  // Memory controller FSM — autonomous from pipe state
  // WB data comes from MSHR eviction fields; fills serviced by MSHR state.
  // ===========================================================================
  assign mem_busy = (mem_state != MEM_IDLE);

  // Bypass mux signals
  logic ld_bypass_active, st_bypass_active;
  assign ld_bypass_active = (ld_pipe_state == PIPE_BYPASS);
  assign st_bypass_active = (st_pipe_state == PIPE_BYPASS);

  // Select WB entry from MSHR (first WB_PENDING entry)
  logic [MSHR_PTR_W-1:0] mshr_wb_idx;
  logic [      XLEN-1:0] mshr_wb_addr;
  logic [  BLK_SIZE-1:0] mshr_wb_data;
  logic                  mshr_wb_from_st;

  always_comb begin
    mshr_wb_idx = '0;
    for (int i = MSHR_DEPTH - 1; i >= 0; i--) if (mshr_wb_vec[i]) mshr_wb_idx = MSHR_PTR_W'(i);
    mshr_wb_addr    = mshr_entries[mshr_wb_idx].evict_addr;
    mshr_wb_data    = mshr_entries[mshr_wb_idx].evict_data;
    mshr_wb_from_st = mshr_entries[mshr_wb_idx].from_st;
  end

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
            mem_state  <= MEM_WB_SEND;
            mem_addr_q <= mshr_wb_addr;
            mem_data_q <= mshr_wb_data;
            wb_from_st <= mshr_wb_from_st;
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
  // Write-merge function: merge store data into a fill line
  // Used by fill writer when writing completed fills to SRAM.
  // ===========================================================================
  function automatic [BLK_SIZE-1:0] merge_fill_data(input logic [BLK_SIZE-1:0] raw_data, input logic do_merge, input logic [XLEN-1:0] maddr, input logic [31:0] mdata, input rw_size_e msize);
    logic [BLK_SIZE-1:0] merged;
    merged = raw_data;
    if (do_merge) begin
      case (msize)
        WORD:    merged[maddr[BOFFSET-1:2]*32+:32] = mdata;
        HALF:    merged[maddr[BOFFSET-1:1]*16+:16] = mdata[15:0];
        BYTE:    merged[maddr[BOFFSET-1:0]*8+:8] = mdata[7:0];
        NO_SIZE: ;
      endcase
    end
    return merged;
  endfunction

  // Legacy fill_merged_data — used by fill writer for the currently completing entry
  logic [BLK_SIZE-1:0] fill_merged_data;
  always_comb begin
    fill_merged_data = fill_resp_data;
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
  // Fill writer — autonomous SRAM write-back for completed MSHR entries
  //
  // Monitors MSHR COMPLETE entries and writes fill data to SRAM when the
  // corresponding pipe's SRAM port is available. Generates response pulses
  // back to memory.sv. Uses Port A for LD-originated fills, Port B for
  // ST-originated fills.
  // ===========================================================================
  // fw_ld_writing/fw_st_writing/fw_ld_set/fw_st_set forward-declared above
  // fw_ld_done, fw_st_done, fw_ld_accepted, fw_st_accepted, fw_ld_idx, fw_st_idx
  // are forward-declared above (before MSHR state machine)

  // Fill writer merge: compute merged data from MSHR entry's fill_data + store merge
  logic [BLK_SIZE-1:0] fw_ld_merged, fw_st_merged;
  logic [NUM_WAY-1:0] fw_ld_way, fw_st_way;
  logic [TAG_SIZE-1:0] fw_ld_tag, fw_st_tag;
  logic [WOFFSET-1:0] fw_ld_word_idx, fw_st_word_idx;

  // Find COMPLETE entries for each port
  logic [MSHR_DEPTH-1:0] fw_ld_complete_vec, fw_st_complete_vec;
  logic fw_ld_pending, fw_st_pending;

  always_comb begin
    for (int i = 0; i < MSHR_DEPTH; i++) begin
      fw_ld_complete_vec[i] = mshr_entries[i].valid && (mshr_entries[i].state == DC_MSHR_COMPLETE) && !mshr_entries[i].from_st;
      fw_st_complete_vec[i] = mshr_entries[i].valid && (mshr_entries[i].state == DC_MSHR_COMPLETE) && mshr_entries[i].from_st;
    end
    fw_ld_pending = |fw_ld_complete_vec;
    fw_st_pending = |fw_st_complete_vec;

    fw_ld_idx = '0;
    for (int i = MSHR_DEPTH - 1; i >= 0; i--) if (fw_ld_complete_vec[i]) fw_ld_idx = MSHR_PTR_W'(i);
    fw_st_idx = '0;
    for (int i = MSHR_DEPTH - 1; i >= 0; i--) if (fw_st_complete_vec[i]) fw_st_idx = MSHR_PTR_W'(i);
  end

  // Fill writer can write when corresponding pipe's SRAM port is available:
  //   1. Pipe is IDLE and not accepting a new request, OR
  //   2. Pipe is stuck retrying in TAG_LOOKUP (mshr match / set conflict / full)
  //      — the SRAM port is just re-reading stale data, safe to preempt.
  // Case 2 breaks the deadlock where the pipe waits for MSHR to drain but the
  // fill writer waits for the pipe to go IDLE.
  //
  // Note: ld_pipe_retrying / st_pipe_retrying intentionally exclude ld_resolve_stall
  // and st_resolve_stall to avoid circular dependency (resolve_stall depends on
  // fill writer state which depends on pipe_retrying).
  logic fw_ld_can_write, fw_st_can_write;

  assign ld_pipe_retrying = (ld_pipe_state == PIPE_TAG_LOOKUP) && (ld_mshr_set_conflict || ld_mshr_full || ld_fw_preempted_q || (ld_mshr_any_match && ld_miss && !ld_req_q.uncached));

  assign st_pipe_retrying = (st_pipe_state == PIPE_TAG_LOOKUP) &&
    (st_mshr_set_conflict || st_mshr_full || st_fw_preempted_q || dual_miss_same_set ||
     (st_mshr_any_match && st_miss && !st_req_q.uncached));

  // Fill writer gets unconditional priority when pipe is IDLE.
  // Previous code used !*_pipe_accept here, but *_pipe_accept depends on
  // !fw_*_writing creating a combinatorial loop (LUTLP-1 / Synth 8-295).
  // Since *_pipe_accept already checks !fw_*_writing, the fill writer
  // naturally blocks new pipe accepts when it writes — no need to check accept.
  assign fw_ld_can_write = fw_ld_pending && !flush_active && !fi_active && ((ld_pipe_state == PIPE_IDLE) || ld_pipe_retrying);
  assign fw_st_can_write = fw_st_pending && !flush_active && !fi_active && ((st_pipe_state == PIPE_IDLE) || st_pipe_retrying);

  // Compute merged fill data for the entry being written
  always_comb begin
    fw_ld_merged   = merge_fill_data(mshr_entries[fw_ld_idx].fill_data, mshr_entries[fw_ld_idx].is_write, mshr_entries[fw_ld_idx].addr, mshr_entries[fw_ld_idx].wdata, mshr_entries[fw_ld_idx].rw_size);
    fw_st_merged   = merge_fill_data(mshr_entries[fw_st_idx].fill_data, mshr_entries[fw_st_idx].is_write, mshr_entries[fw_st_idx].addr, mshr_entries[fw_st_idx].wdata, mshr_entries[fw_st_idx].rw_size);
    fw_ld_way      = mshr_entries[fw_ld_idx].victim_way;
    fw_st_way      = mshr_entries[fw_st_idx].victim_way;
    fw_ld_tag      = mshr_entries[fw_ld_idx].addr[XLEN-1:IDX_WIDTH+BOFFSET];
    fw_st_tag      = mshr_entries[fw_st_idx].addr[XLEN-1:IDX_WIDTH+BOFFSET];
    fw_ld_set      = mshr_entries[fw_ld_idx].addr[IDX_WIDTH+BOFFSET-1:BOFFSET];
    fw_st_set      = mshr_entries[fw_st_idx].addr[IDX_WIDTH+BOFFSET-1:BOFFSET];
    fw_ld_word_idx = mshr_entries[fw_ld_idx].addr[(WOFFSET+2)-1:2];
    fw_st_word_idx = mshr_entries[fw_st_idx].addr[(WOFFSET+2)-1:2];
  end

  // Fill writer: 1-cycle write to SRAM + response generation
  // fw_*_writing is high for exactly 1 cycle when writing
  assign fw_ld_writing     = fw_ld_can_write;
  assign fw_st_writing     = fw_st_can_write;

  // Connect forward-declared signals for SRAM address mux
  assign fw_ld_writing_fwd = fw_ld_writing;
  assign fw_st_writing_fwd = fw_st_writing;
  assign fw_ld_set_fwd     = fw_ld_set;
  assign fw_st_set_fwd     = fw_st_set;

  // fw_*_done: signals MSHR state machine to transition COMPLETE → IDLE
  assign fw_ld_done        = fw_ld_writing;
  assign fw_st_done        = fw_st_writing;

  // fw_*_accepted: signals MSHR to deallocate entry (1 cycle after done)
  logic fw_ld_done_q, fw_st_done_q;
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      fw_ld_done_q <= 1'b0;
      fw_st_done_q <= 1'b0;
    end else begin
      fw_ld_done_q <= fw_ld_done;
      fw_st_done_q <= fw_st_done;
    end
  end
  assign fw_ld_accepted = fw_ld_done_q;
  assign fw_st_accepted = fw_st_done_q;

  // ===========================================================================
  // LD-pipe SRAM control (pipe operations + fill writer)
  // ===========================================================================
  always_comb begin
    ld_tag_we    = '0;
    ld_tag_wdata = '0;
    ld_data_we   = '0;
    ld_data_wdata = '0;

    if (flush_active) begin
      ld_tag_we    = '1;
      ld_tag_wdata = '0;
    end else if (fw_ld_writing) begin
      ld_tag_we    = fw_ld_way;
      ld_tag_wdata = {1'b1, fw_ld_tag};
      ld_data_we   = fw_ld_way;
      ld_data_wdata = fw_ld_merged;
    end
  end

  // ===========================================================================
  // ST-pipe SRAM control (pipe operations + fill writer)
  // ===========================================================================
  always_comb begin
    st_tag_we    = '0;
    st_tag_wdata = '0;
    st_data_we   = '0;
    st_data_wdata = '0;

    if (st_pipe_state == PIPE_HIT_RESPOND && st_req_q.is_write) begin
      st_data_we    = st_hit_way_oh_raw;
      st_data_wdata = st_hit_wr_merged;
    end else if (fw_st_writing) begin
      st_tag_we    = fw_st_way;
      st_tag_wdata = {1'b1, fw_st_tag};
      st_data_we   = fw_st_way;
      st_data_wdata = fw_st_merged;
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
    end else if (fw_ld_writing) begin
      ld_plru_wr    = 1'b1;
      ld_plru_wdata = update_node(plru_reg[fw_ld_set], fw_ld_way);
    end
  end

  always_comb begin
    st_plru_wr    = 1'b0;
    st_plru_wdata = '0;
    if (st_pipe_state == PIPE_HIT_RESPOND) begin
      st_plru_wr    = 1'b1;
      st_plru_wdata = st_updated_node;
    end else if (fw_st_writing) begin
      st_plru_wr    = 1'b1;
      st_plru_wdata = update_node(plru_reg[fw_st_set], fw_st_way);
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
    ld_dirty_idx = fw_ld_writing ? fw_ld_set : ld_req_set;
    ld_dirty_way = '0;
    ld_dirty_val = 1'b0;
    if (fw_ld_writing) begin
      ld_dirty_wr  = 1'b1;
      ld_dirty_way = fw_ld_way;
      ld_dirty_val = mshr_entries[fw_ld_idx].is_write;
    end
  end

  always_comb begin
    st_dirty_wr  = 1'b0;
    st_dirty_idx = fi_active ? fi_set_idx_q : (fw_st_writing ? fw_st_set : st_req_set);
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
    end else if (fw_st_writing) begin
      st_dirty_wr  = 1'b1;
      st_dirty_way = fw_st_way;
      st_dirty_val = mshr_entries[fw_st_idx].is_write;
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

  // Fence.i debug logger — Enable with: +define+LOG_FENCEI_DEBUG
  // synthesis translate_off
`ifdef LOG_FENCEI_DEBUG
  logic fi_dbg_prev_nb;
  always_ff @(posedge clk_i) begin
    if (!rst_ni) fi_dbg_prev_nb <= 1'b0;
    else fi_dbg_prev_nb <= flush_i;
  end
  always_ff @(posedge clk_i) begin
    if (rst_ni && (flush_i || fi_active || fi_dbg_prev_nb)) begin
      if (flush_i && !fi_dbg_prev_nb)
        $display(
            "[FENCEI-DBG][DC_NB] %0t FLUSH_I RISE pipes_idle=%b ld_st=%0d/%0d mshr_empty=%b mem_st=%0d flush_active=%b fi_gated=%b",
            $time,
            pipes_idle_o,
            ld_pipe_state,
            st_pipe_state,
            mshr_all_empty,
            mem_state,
            flush_active,
            fi_flush_gated
        );
      if ($time % 100 == 0 && flush_i)
        $display(
            "[FENCEI-DBG][DC_NB] %0t STATUS flush_i=%b fi_active=%b fi_gated=%b flush_active=%b pipes_idle=%b ld=%0d st=%0d mshr_empty=%b mem=%0d fencei_stall=%b",
            $time,
            flush_i,
            fi_active,
            fi_flush_gated,
            flush_active,
            pipes_idle_o,
            ld_pipe_state,
            st_pipe_state,
            mshr_all_empty,
            mem_state,
            fencei_stall_o
        );
      if (fi_dbg_prev_nb && !flush_i) $display("[FENCEI-DBG][DC_NB] %0t FLUSH_I FALL fi_active=%b fencei_stall=%b", $time, fi_active, fencei_stall_o);
    end
    // Log ST pipe activity during fence.i period
    if (rst_ni && st_pipe_accept) $display("[FENCEI-DBG][DC_NB] %0t ST_ACCEPT addr=%08x rw=%b size=%0d", $time, st_req_i.addr, st_req_i.rw, st_req_i.rw_size);
    if (rst_ni && st_pipe_state == PIPE_TAG_LOOKUP && st_hit_any)
      $display("[FENCEI-DBG][DC_NB] %0t ST_HIT addr=%08x set=%0d dirty_before=%04b", $time, st_req_q.addr, st_req_set, dirty_reg[st_req_set]);
    if (rst_ni && st_pipe_state == PIPE_TAG_LOOKUP && !st_hit_any && !st_resolve_stall) $display("[FENCEI-DBG][DC_NB] %0t ST_MISS addr=%08x set=%0d", $time, st_req_q.addr, st_req_set);
    if (rst_ni && st_dirty_wr) $display("[FENCEI-DBG][DC_NB] %0t DIRTY_WR set=%0d way=%04b val=%b", $time, st_dirty_idx, st_dirty_way, st_dirty_val);
  end
`endif
  // synthesis translate_on

  // ===========================================================================
  // LD-pipe FSM — miss-under-miss: returns to IDLE after MSHR allocation
  // ===========================================================================
  assign ld_pipe_accept = (ld_pipe_state == PIPE_IDLE) && !flush_active && !fi_active && !fw_ld_writing && ld_req_i.valid;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      ld_pipe_state   <= PIPE_IDLE;
      ld_req_q        <= '0;
      ld_victim_way_q <= '0;
    end else begin
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
          if (ld_resolve_stall || ld_mshr_set_conflict || (ld_mshr_any_match && ld_miss && !ld_req_q.uncached)) begin
            ld_pipe_state <= PIPE_TAG_LOOKUP;  // retry
          end else if (ld_hit_any) begin
            ld_pipe_state <= PIPE_IDLE;  // 1-cycle hit
          end else if (ld_mshr_full) begin
            ld_pipe_state <= PIPE_TAG_LOOKUP;  // structural stall — retry
          end else begin
            // Miss: MSHR allocated this cycle (via ld_mshr_do_alloc), return to IDLE
            ld_pipe_state <= PIPE_IDLE;
          end
        end

        PIPE_BYPASS: if (lowX_res_i.valid && !st_bypass_active && !fi_writeback_req) ld_pipe_state <= PIPE_IDLE;

        default: ld_pipe_state <= PIPE_IDLE;
      endcase
    end
  end

  // ===========================================================================
  // DEBUG: dcache miss-under-miss diagnostics
  // ===========================================================================
`ifdef DCACHE_DBG
  // synopsys translate_off
  always_ff @(posedge clk_i)
    if (rst_ni && !flush_active) begin
      // LD pipe stall diagnosis
      if (ld_pipe_state == PIPE_TAG_LOOKUP) begin
        if (ld_resolve_stall) $display("[DCACHE-DBG] %0t LD TAG_LOOKUP STALL: resolve_stall addr=%08x set=%0d", $time, ld_req_q.addr, ld_req_set);
        if (ld_mshr_set_conflict) $display("[DCACHE-DBG] %0t LD TAG_LOOKUP STALL: mshr_set_conflict addr=%08x set=%0d", $time, ld_req_q.addr, ld_req_set);
        if (ld_mshr_any_match && ld_miss && !ld_req_q.uncached)
          $display("[DCACHE-DBG] %0t LD TAG_LOOKUP STALL: mshr_match addr=%08x set=%0d hit_any=%0b miss=%0b", $time, ld_req_q.addr, ld_req_set, ld_hit_any, ld_miss);
        if (ld_hit_any && !ld_resolve_stall && !ld_mshr_set_conflict && !(ld_mshr_any_match && ld_miss && !ld_req_q.uncached))
          $display("[DCACHE-DBG] %0t LD TAG_LOOKUP HIT addr=%08x set=%0d", $time, ld_req_q.addr, ld_req_set);
        if (ld_miss && !ld_mshr_any_match && !ld_mshr_full && !ld_resolve_stall && !ld_mshr_set_conflict)
          $display("[DCACHE-DBG] %0t LD TAG_LOOKUP MISS→MSHR addr=%08x set=%0d", $time, ld_req_q.addr, ld_req_set);
      end
      // ST pipe stall diagnosis
      if (st_pipe_state == PIPE_TAG_LOOKUP) begin
        if (st_resolve_stall) $display("[DCACHE-DBG] %0t ST TAG_LOOKUP STALL: resolve_stall addr=%08x set=%0d", $time, st_req_q.addr, st_req_set);
        if (st_mshr_set_conflict) $display("[DCACHE-DBG] %0t ST TAG_LOOKUP STALL: mshr_set_conflict addr=%08x set=%0d", $time, st_req_q.addr, st_req_set);
        if (st_mshr_any_match && st_miss && !st_req_q.uncached) $display("[DCACHE-DBG] %0t ST TAG_LOOKUP STALL: mshr_match addr=%08x set=%0d", $time, st_req_q.addr, st_req_set);
        if (st_hit_any && !st_resolve_stall && !st_mshr_set_conflict && !dual_miss_same_set && !(st_mshr_any_match && st_miss && !st_req_q.uncached))
          $display("[DCACHE-DBG] %0t ST TAG_LOOKUP HIT addr=%08x set=%0d", $time, st_req_q.addr, st_req_set);
        if (st_miss && !st_mshr_any_match && !st_mshr_full && !st_resolve_stall && !st_mshr_set_conflict && !dual_miss_same_set)
          $display("[DCACHE-DBG] %0t ST TAG_LOOKUP MISS→MSHR addr=%08x set=%0d", $time, st_req_q.addr, st_req_set);
      end
      // Fill writer events
      if (fw_ld_writing) $display("[DCACHE-DBG] %0t FW_LD_WRITE set=%0d idx=%0d way=%0b tag=%06x", $time, fw_ld_set, fw_ld_idx, fw_ld_way, fw_ld_tag);
      if (fw_st_writing) $display("[DCACHE-DBG] %0t FW_ST_WRITE set=%0d idx=%0d way=%0b tag=%06x", $time, fw_st_set, fw_st_idx, fw_st_way, fw_st_tag);
      // MSHR alloc events
      if (ld_mshr_do_alloc) $display("[DCACHE-DBG] %0t LD_MSHR_ALLOC idx=%0d addr=%08x evict_dirty=%0b", $time, mshr_free_idx, ld_req_q.addr, ld_evict_dirty);
      if (st_mshr_do_alloc) $display("[DCACHE-DBG] %0t ST_MSHR_ALLOC idx=%0d addr=%08x evict_dirty=%0b", $time, mshr_free_idx, st_req_q.addr, st_evict_dirty);
      // Fill response
      if (fill_resp_valid) $display("[DCACHE-DBG] %0t FILL_RESP from_st=%0b entry=%0d", $time, mshr_fill_from_st, mshr_fill_entry_idx);
      // MSHR state dump (compact)
      for (int i = 0; i < MSHR_DEPTH; i++) begin
        if (mshr_entries[i].valid) $display("[DCACHE-DBG] %0t MSHR[%0d] state=%0d addr=%08x from_st=%0b", $time, i, mshr_entries[i].state, mshr_entries[i].addr, mshr_entries[i].from_st);
      end
      // Memory controller
      if (mem_state != MEM_IDLE) $display("[DCACHE-DBG] %0t MEM_STATE=%0d addr=%08x", $time, mem_state, mem_addr_q);
    end
  // synopsys translate_on
`endif

  // ===========================================================================
  // ST-pipe FSM — miss-under-miss: returns to IDLE after MSHR allocation
  // ===========================================================================
  assign st_pipe_accept = (st_pipe_state == PIPE_IDLE) && !flush_active && !fi_active && !fw_st_writing && st_req_i.valid;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      st_pipe_state   <= PIPE_IDLE;
      st_req_q        <= '0;
      st_victim_way_q <= '0;
    end else begin
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
          if (st_resolve_stall || st_mshr_set_conflict || dual_miss_same_set || (st_mshr_any_match && st_miss && !st_req_q.uncached)) begin
            st_pipe_state <= PIPE_TAG_LOOKUP;  // retry
          end else if (st_hit_any) begin
            st_pipe_state <= PIPE_HIT_RESPOND;
          end else if (st_mshr_full) begin
            st_pipe_state <= PIPE_TAG_LOOKUP;  // structural stall — retry
          end else begin
            // Miss: MSHR allocated this cycle, return to IDLE
            st_pipe_state <= PIPE_IDLE;
          end
        end

        PIPE_HIT_RESPOND: st_pipe_state <= PIPE_IDLE;

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

  // ld_hit_respond assigned above (after ld_resolve_stall)

  // LD response: hit from pipe OR fill from fill writer
  always_comb begin
    ld_res_o.valid = 1'b0;
    ld_res_o.miss  = 1'b0;
    ld_res_o.ready = (ld_pipe_state == PIPE_IDLE) && !flush_active && !fi_active && !fw_ld_writing;
    ld_res_o.data  = '0;

    if (ld_hit_respond) begin
      ld_res_o.valid = 1'b1;
      ld_res_o.data  = ld_select_data[ld_word_idx*32+:32];
    end else if (fw_ld_writing) begin
      // Fill writer is writing SRAM — also generate response to memory.sv
      ld_res_o.valid = 1'b1;
      ld_res_o.data  = fw_ld_merged[fw_ld_word_idx*32+:32];
    end else if (ld_bypass_active && lowX_res_i.valid && !st_bypass_active && !fi_writeback_req) begin
      ld_res_o.valid = 1'b1;
      ld_res_o.data  = lowX_res_i.data[ld_word_idx*32+:32];
    end
  end

  // ST miss accepted: MSHR allocated, store data captured — signal memory.sv immediately
  logic st_miss_accepted;
  assign st_miss_accepted = st_mshr_do_alloc;

  // ST response: hit from pipe, miss-accepted, fill from fill writer, or bypass
  always_comb begin
    st_res_o.valid = 1'b0;
    st_res_o.miss  = 1'b0;
    st_res_o.ready = (st_pipe_state == PIPE_IDLE) && !flush_active && !fi_active && !fw_st_writing;
    st_res_o.data  = '0;

    if (st_pipe_state == PIPE_HIT_RESPOND) begin
      st_res_o.valid = 1'b1;
      st_res_o.data  = st_select_data[st_word_idx*32+:32];
    end else if (st_miss_accepted) begin
      // Store miss: MSHR captured the data, tell memory.sv the store port is done
      st_res_o.valid = 1'b1;
      st_res_o.data  = '0;
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

  // ===========================================================================
  // dcache multi-fill mem controller logger (LOG_DC_MFILL=1)
  // ===========================================================================
`ifdef LOG_DC_MFILL
  // synthesis translate_off
  integer dcm_log_fd;
  string  dcm_log_path;

  // Counters
  int unsigned dcm_ld_allocs, dcm_st_allocs, dcm_fills_issued, dcm_fills_done;
  int unsigned dcm_wb_issued, dcm_wb_done;
  int unsigned dcm_max_active, dcm_cycles_multi;
  int unsigned dcm_lowx_req_cycles, dcm_lowx_busy_cycles;

  // Edge detection
  logic        [MSHR_DEPTH-1:0] dcm_mshr_valid_q;

  // Working variables (module scope for Verilator)
  int unsigned                  dcm_active_now;
  logic        [MSHR_DEPTH-1:0] dcm_valid_now;

  initial begin
    if (!$value$plusargs("dc_mfill_log=%s", dcm_log_path)) dcm_log_path = "dc_mfill_trace.log";
    dcm_log_fd = $fopen(dcm_log_path, "w");
    if (dcm_log_fd == 0) $display("[LOG_DC_MFILL] ERROR: Cannot open %s", dcm_log_path);
    else begin
      $display("[LOG_DC_MFILL] Writing to: %s", dcm_log_path);
      $fwrite(dcm_log_fd, "# dcache Multi-Fill Mem Controller Trace\n");
      $fwrite(dcm_log_fd, "# mshr_state: 0=IDLE 1=PENDING 2=FILL_ACTIVE 3=WB_PENDING 4=COMPLETE\n");
      $fwrite(dcm_log_fd, "# pipe_state: 0=IDLE 1=TAG_LOOKUP 2=HIT_RESPOND 3=BYPASS\n");
      $fwrite(dcm_log_fd, "# mem_state:  0=MEM_IDLE 1=MEM_WB_SEND 2=MEM_FILL_SEND\n");
      $fwrite(dcm_log_fd, "#\n");
      $fflush(dcm_log_fd);
    end
  end

  function automatic int unsigned dc_count_active_mshr();
    int unsigned cnt;
    cnt = 0;
    for (int i = 0; i < MSHR_DEPTH; i++) if (mshr_entries[i].valid) cnt = cnt + 1;
    return cnt;
  endfunction

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      dcm_ld_allocs        <= 0;
      dcm_st_allocs        <= 0;
      dcm_fills_issued     <= 0;
      dcm_fills_done       <= 0;
      dcm_wb_issued        <= 0;
      dcm_wb_done          <= 0;
      dcm_max_active       <= 0;
      dcm_cycles_multi     <= 0;
      dcm_lowx_req_cycles  <= 0;
      dcm_lowx_busy_cycles <= 0;
      dcm_mshr_valid_q     <= '0;
    end else if (dcm_log_fd != 0) begin
      for (int i = 0; i < MSHR_DEPTH; i++) dcm_mshr_valid_q[i] <= mshr_entries[i].valid;

      dcm_active_now = dc_count_active_mshr();
      if (dcm_active_now > dcm_max_active) dcm_max_active <= dcm_active_now;
      if (dcm_active_now > 1) dcm_cycles_multi <= dcm_cycles_multi + 1;

      // lowX utilization
      if (lowX_req_o.valid) dcm_lowx_req_cycles <= dcm_lowx_req_cycles + 1;
      if (mem_busy) dcm_lowx_busy_cycles <= dcm_lowx_busy_cycles + 1;

      // [DC_LD_ALLOC]
      if (ld_mshr_do_alloc) begin
        dcm_ld_allocs <= dcm_ld_allocs + 1;
        $fwrite(dcm_log_fd, "%0t [DC_LD_ALLOC] slot=%0d addr=%08x active=%0d free=%b\n", $time, mshr_free_idx, ld_req_q.addr, dcm_active_now, mshr_free_vec);
        $fflush(dcm_log_fd);
      end

      // [DC_ST_ALLOC]
      if (st_mshr_do_alloc) begin
        dcm_st_allocs <= dcm_st_allocs + 1;
        $fwrite(dcm_log_fd, "%0t [DC_ST_ALLOC] addr=%08x active=%0d free=%b\n", $time, st_req_q.addr, dcm_active_now, mshr_free_vec);
        $fflush(dcm_log_fd);
      end

      // [DC_FILL_ISSUE]
      if (fill_issued) begin
        dcm_fills_issued <= dcm_fills_issued + 1;
        $fwrite(dcm_log_fd, "%0t [DC_FILL_ISSUE] slot=%0d addr=%08x from_st=%b pend=%b ms=%0d\n", $time, mshr_pending_idx, mshr_pending_addr, mshr_pending_from_st, mshr_pending_vec, int'(mem_state));
        $fflush(dcm_log_fd);
      end

      // [DC_FILL_DONE]
      if (fill_resp_valid) begin
        dcm_fills_done <= dcm_fills_done + 1;
        $fwrite(dcm_log_fd, "%0t [DC_FILL_DONE] slot=%0d from_st=%b data[31:0]=%08x\n", $time, mshr_fill_entry_idx, mshr_fill_from_st, fill_resp_data[31:0]);
        $fflush(dcm_log_fd);
      end

      // [DC_WB_START]
      if (mem_state == MEM_IDLE && wb_req_valid) begin
        dcm_wb_issued <= dcm_wb_issued + 1;
        $fwrite(dcm_log_fd, "%0t [DC_WB_START] addr=%08x from_st=%b wb_vec=%b\n", $time, mshr_wb_addr, mshr_wb_from_st, mshr_wb_vec);
        $fflush(dcm_log_fd);
      end

      // [DC_WB_DONE]
      if (wb_done) begin
        dcm_wb_done <= dcm_wb_done + 1;
        $fwrite(dcm_log_fd, "%0t [DC_WB_DONE] from_st=%b\n", $time, wb_from_st);
        $fflush(dcm_log_fd);
      end

      // MSHR snapshot on change
      for (int i = 0; i < MSHR_DEPTH; i++) dcm_valid_now[i] = mshr_entries[i].valid;
      if (dcm_valid_now != dcm_mshr_valid_q) begin
        $fwrite(dcm_log_fd, "%0t [DC_SNAP]", $time);
        for (int i = 0; i < MSHR_DEPTH; i++) begin
          if (mshr_entries[i].valid) $fwrite(dcm_log_fd, " s%0d{st=%0d a=%08x}", i, int'(mshr_entries[i].state), mshr_entries[i].addr);
          else $fwrite(dcm_log_fd, " s%0d{free}", i);
        end
        $fwrite(dcm_log_fd, " | ld_ps=%0d st_ps=%0d ms=%0d lowX_rdy=%b\n", int'(ld_pipe_state), int'(st_pipe_state), int'(mem_state), lowX_res_i.ready);
        $fflush(dcm_log_fd);
      end
    end
  end

  final begin
    if (dcm_log_fd != 0) begin
      $fwrite(dcm_log_fd, "\n# === DC MULTI-FILL SUMMARY ===\n");
      $fwrite(dcm_log_fd, "# ld_allocs       = %0d\n", dcm_ld_allocs);
      $fwrite(dcm_log_fd, "# st_allocs       = %0d\n", dcm_st_allocs);
      $fwrite(dcm_log_fd, "# fills_issued    = %0d\n", dcm_fills_issued);
      $fwrite(dcm_log_fd, "# fills_done      = %0d\n", dcm_fills_done);
      $fwrite(dcm_log_fd, "# wb_issued       = %0d\n", dcm_wb_issued);
      $fwrite(dcm_log_fd, "# wb_done         = %0d\n", dcm_wb_done);
      $fwrite(dcm_log_fd, "# max_active      = %0d / %0d\n", dcm_max_active, MSHR_DEPTH);
      $fwrite(dcm_log_fd, "# cycles_multi    = %0d (>1 MSHR active)\n", dcm_cycles_multi);
      $fwrite(dcm_log_fd, "# lowx_req_cycles = %0d\n", dcm_lowx_req_cycles);
      $fwrite(dcm_log_fd, "# lowx_busy_cycles= %0d\n", dcm_lowx_busy_cycles);
      $fclose(dcm_log_fd);
    end
    $display("[LOG_DC_MFILL] ld_alloc=%0d st_alloc=%0d fills=%0d/%0d wb=%0d/%0d max_active=%0d/%0d", dcm_ld_allocs, dcm_st_allocs, dcm_fills_issued, dcm_fills_done, dcm_wb_issued, dcm_wb_done,
             dcm_max_active, MSHR_DEPTH);
  end
  // synthesis translate_on
`endif

endmodule
