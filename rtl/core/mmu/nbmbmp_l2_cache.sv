/*
 * L2 Cache — Level true dual-port Non-blocking Write-back Cache
 *
 * Architecture:
 *   I-cache (ilowX) ──► I-pipe ──┐
 *                                 ├──► shared mem controller → wb_master_bridge
 *   D-cache (dlowX) ──► D-pipe ──┘
 *
 * Design:
 *   - Two independent pipeline FSMs (I-pipe, D-pipe)
 *   - dp_bram per way per bank for data and tag arrays (Port A = I-pipe, Port B = D-pipe)
 *   - Register-based PLRU node array (dual read, merged update)
 *   - Register-based dirty array (dual read, merged update)
 *   - Inlined MSHR with from_dport for fill routing
 *   - Shared memory controller with arbitration between pipes
 *   - Shared uncached bypass (D-port only; I-port bypass via I-pipe)
 *   - Set-conflict hazard protection between pipelines
 *   - Parametric multi-bank support (L2_NUM_BANKS)
 *
 * Pipeline timing (per pipe):
 *   Cycle 0 (IDLE):       Request accepted, address driven to SRAMs
 *   Cycle 1 (TAG_LOOKUP): Registered SRAM outputs settle
 *   Cycle 2 (RESOLVE):    Hit/miss resolved. Hit → respond. Miss → MSHR + evict/fill.
 */
 `timescale 1ns / 1ps
 `include "level_defines.svh"
 // non-blocking multi-bank multi-port cache
 module nbmbmp_l2_cache
   import level_param::*;
 (
     input  logic       clk_i,
     input  logic       rst_ni,
     input  logic       flush_i,
 
     input  ilowX_req_t icache_req_i,
     output ilowX_res_t icache_res_o,
 
     input  dlowX_req_t dcache_req_i,
     output dlowX_res_t dcache_res_o,
 
     output iomem_req_t mem_req_o,
     input  iomem_res_t mem_res_i
 );
 
   // =========================================================================
   // Local parameters
   // =========================================================================
   localparam int BANK_SEL_W  = L2_NUM_BANKS > 1 ? $clog2(L2_NUM_BANKS) : 1;
   localparam int BANK_ADDR_W = $clog2(L2_BANK_SETS);
   localparam int BOFFSET     = $clog2(BLK_SIZE / 8);
 
   // =========================================================================
   // FSM enums
   // =========================================================================
   typedef enum logic [2:0] {
     PIPE_IDLE,
     PIPE_TAG_LOOKUP,
     PIPE_RESOLVE,
     PIPE_HIT_RESPOND,
     PIPE_MISS_WAIT,
     PIPE_FILL_RESPOND,
     PIPE_WB_EVICT,
     PIPE_BYPASS
   } pipe_state_t;
 
   typedef enum logic [1:0] {
     MEM_IDLE,
     MEM_WB_SEND,
     MEM_FILL_SEND
   } mem_state_t;
 
   // =========================================================================
   // Internal pipeline request type
   // =========================================================================
   typedef struct packed {
     logic [XLEN-1:0]       addr;
     logic                  is_write;
     rw_size_e              rw_size;
     logic [BLK_SIZE-1:0]   wdata;
     logic [BLK_SIZE/8-1:0] wstrb;
     logic                  uncached;
     logic                  from_dport;
   } l2_req_t;
 
   // =========================================================================
   // Per-pipe state
   // =========================================================================
   pipe_state_t i_pipe_state, d_pipe_state;
   l2_req_t     i_req_q,      d_req_q;
 
   logic i_miss_wait;
   logic d_miss_wait;
   logic fill_req_valid;
   logic wb_req_valid;
   logic i_fill_writing;
   logic d_fill_writing;
   logic i_resolve_stall;
   logic d_resolve_stall;
   logic dual_miss_same_set;
 
   logic [L2_INDEX_BITS-1:0] i_req_set;
   logic [L2_TAG_BITS-1:0]   i_req_tag;
   logic [L2_INDEX_BITS-1:0] d_req_set;
   logic [L2_TAG_BITS-1:0]   d_req_tag;
   logic                     d_req_wr;
   assign i_req_set = i_req_q.addr[L2_INDEX_BITS+L2_OFFSET_BITS-1:L2_OFFSET_BITS];
   assign i_req_tag = i_req_q.addr[XLEN-1:L2_INDEX_BITS+L2_OFFSET_BITS];
   assign d_req_set = d_req_q.addr[L2_INDEX_BITS+L2_OFFSET_BITS-1:L2_OFFSET_BITS];
   assign d_req_tag = d_req_q.addr[XLEN-1:L2_INDEX_BITS+L2_OFFSET_BITS];
   assign d_req_wr  = d_req_q.is_write;
 
   // =========================================================================
   // Flush logic
   // =========================================================================
   logic                     flush_active;
   logic [L2_INDEX_BITS-1:0] flush_cnt;
 
   always_ff @(posedge clk_i) begin
     if (!rst_ni) begin
       flush_active <= 1'b1;
       flush_cnt    <= '0;
     end else if (flush_active) begin
       if (flush_cnt == L2_INDEX_BITS'(L2_NUM_SETS - 1)) begin
         flush_active <= 1'b0;
         flush_cnt    <= '0;
       end else begin
         flush_cnt <= flush_cnt + 1;
       end
     end else if (flush_i && i_pipe_state == PIPE_IDLE && d_pipe_state == PIPE_IDLE) begin
       flush_active <= 1'b1;
       flush_cnt    <= '0;
     end
   end
 
   // =========================================================================
   // Per-pipe SRAM addressing & bank decode
   // =========================================================================
   logic [L2_INDEX_BITS-1:0] i_next_set;
   logic [L2_INDEX_BITS-1:0] d_next_set;
   assign i_next_set = icache_req_i.addr[L2_INDEX_BITS+L2_OFFSET_BITS-1:L2_OFFSET_BITS];
   assign d_next_set = dcache_req_i.addr[L2_INDEX_BITS+L2_OFFSET_BITS-1:L2_OFFSET_BITS];
 
   logic [L2_INDEX_BITS-1:0] i_sram_idx, d_sram_idx;
 
   assign i_sram_idx = flush_active                    ? flush_cnt
                     : (i_pipe_state == PIPE_IDLE)      ? i_next_set
                     :                                    i_req_set;
 
   assign d_sram_idx = (d_pipe_state == PIPE_IDLE)      ? d_next_set
                     :                                    d_req_set;
 
   logic [BANK_SEL_W-1:0]  i_bank_sel, d_bank_sel;
   logic [BANK_ADDR_W-1:0] i_bank_addr, d_bank_addr;
   logic [BANK_SEL_W-1:0]  i_bank_sel_q, d_bank_sel_q;
 
   if (L2_NUM_BANKS > 1) begin : gen_bank_decode
     assign i_bank_sel  = i_sram_idx[$clog2(L2_NUM_BANKS)-1:0];
     assign i_bank_addr = i_sram_idx[L2_INDEX_BITS-1:$clog2(L2_NUM_BANKS)];
     assign d_bank_sel  = d_sram_idx[$clog2(L2_NUM_BANKS)-1:0];
     assign d_bank_addr = d_sram_idx[L2_INDEX_BITS-1:$clog2(L2_NUM_BANKS)];
   end else begin : gen_single_bank
     assign i_bank_sel  = '0;
     assign i_bank_addr = i_sram_idx;
     assign d_bank_sel  = '0;
     assign d_bank_addr = d_sram_idx;
   end
 
   always_ff @(posedge clk_i) begin
     if (!rst_ni) begin
       i_bank_sel_q <= '0;
       d_bank_sel_q <= '0;
     end else begin
       i_bank_sel_q <= i_bank_sel;
       d_bank_sel_q <= d_bank_sel;
     end
   end
 
   // =========================================================================
   // Per-pipe SRAM read/write signals
   // =========================================================================
 
   // Tag SRAM control (per pipe)
   logic [L2_NUM_WAY-1:0]  i_tag_we, d_tag_we;
   logic [L2_TAG_BITS:0]   i_tag_wdata, d_tag_wdata;
   logic [L2_NUM_WAY-1:0][L2_TAG_BITS:0] i_tag_rdata, d_tag_rdata;
 
   // Data SRAM control (per pipe)
   logic [L2_NUM_WAY-1:0]  i_data_we, d_data_we;
   logic [BLK_SIZE-1:0]    i_data_wdata, d_data_wdata;
   logic [L2_NUM_WAY-1:0][BLK_SIZE-1:0] i_data_rdata, d_data_rdata;
 
   // =========================================================================
   // dp_bram instantiations (multi-bank, parametric)
   // Port A = I-pipe (+ flush writes), Port B = D-pipe
   // =========================================================================
 
   // Data arrays: L2_NUM_WAY x L2_NUM_BANKS
   for (genvar w = 0; w < L2_NUM_WAY; w++) begin : gen_data_way
     logic [BLK_SIZE-1:0] a_bank_rd [L2_NUM_BANKS];
     logic [BLK_SIZE-1:0] b_bank_rd [L2_NUM_BANKS];
     for (genvar b = 0; b < L2_NUM_BANKS; b++) begin : gen_data_bank
       dp_bram #(
         .DATA_WIDTH(BLK_SIZE),
         .NUM_SETS  (L2_BANK_SETS)
       ) i_data (
         .clk      (clk_i),
         .a_chip_en(i_bank_sel == BANK_SEL_W'(b)),
         .a_addr   (i_bank_addr),
         .a_wr_en  (i_data_we[w]),
         .a_wr_data(i_data_wdata),
         .a_rd_data(a_bank_rd[b]),
         .b_chip_en(d_bank_sel == BANK_SEL_W'(b)),
         .b_addr   (d_bank_addr),
         .b_wr_en  (d_data_we[w]),
         .b_wr_data(d_data_wdata),
         .b_rd_data(b_bank_rd[b])
       );
     end
     assign i_data_rdata[w] = a_bank_rd[i_bank_sel_q];
     assign d_data_rdata[w] = b_bank_rd[d_bank_sel_q];
   end
 
   // Tag arrays: L2_NUM_WAY x L2_NUM_BANKS
   for (genvar w = 0; w < L2_NUM_WAY; w++) begin : gen_tag_way
     logic [L2_TAG_BITS:0] a_bank_rd [L2_NUM_BANKS];
     logic [L2_TAG_BITS:0] b_bank_rd [L2_NUM_BANKS];
     for (genvar b = 0; b < L2_NUM_BANKS; b++) begin : gen_tag_bank
       dp_bram #(
         .DATA_WIDTH(L2_TAG_BITS + 1),
         .NUM_SETS  (L2_BANK_SETS)
       ) i_tag (
         .clk      (clk_i),
         .a_chip_en(i_bank_sel == BANK_SEL_W'(b)),
         .a_addr   (i_bank_addr),
         .a_wr_en  (i_tag_we[w]),
         .a_wr_data(i_tag_wdata),
         .a_rd_data(a_bank_rd[b]),
         .b_chip_en(d_bank_sel == BANK_SEL_W'(b)),
         .b_addr   (d_bank_addr),
         .b_wr_en  (d_tag_we[w]),
         .b_wr_data(d_tag_wdata),
         .b_rd_data(b_bank_rd[b])
       );
     end
     assign i_tag_rdata[w] = a_bank_rd[i_bank_sel_q];
     assign d_tag_rdata[w] = b_bank_rd[d_bank_sel_q];
   end
 
   // =========================================================================
   // PLRU — register-based (dual read, merged update)
   // =========================================================================
   logic [L2_LRU_W-1:0] plru_reg [L2_NUM_SETS];
 
   logic                 i_plru_wr, d_plru_wr;
   logic [L2_LRU_W-1:0] i_plru_wdata, d_plru_wdata;
 
   always_ff @(posedge clk_i) begin
     if (!rst_ni) begin
       for (int s = 0; s < L2_NUM_SETS; s++) plru_reg[s] <= '0;
     end else if (flush_active) begin
       plru_reg[flush_cnt] <= '0;
     end else begin
       if (i_plru_wr && d_plru_wr && i_req_set == d_req_set) begin
         plru_reg[i_req_set] <= update_node(i_plru_wdata, d_plru_hit_way());
       end else begin
         if (i_plru_wr) plru_reg[i_req_set] <= i_plru_wdata;
         if (d_plru_wr) plru_reg[d_req_set] <= d_plru_wdata;
       end
     end
   end
 
   logic [L2_LRU_W-1:0] i_plru_rdata;
   logic [L2_LRU_W-1:0] d_plru_rdata;
   assign i_plru_rdata = plru_reg[i_req_set];
   assign d_plru_rdata = plru_reg[d_req_set];
 
   // =========================================================================
   // Dirty array — register-based (dual read, merged update)
   // =========================================================================
   logic [L2_NUM_WAY-1:0] dirty_reg [L2_NUM_SETS];
 
   logic                     i_dirty_wr, d_dirty_wr;
   logic [L2_INDEX_BITS-1:0] i_dirty_idx, d_dirty_idx;
   logic [L2_NUM_WAY-1:0]    i_dirty_way, d_dirty_way;
   logic                     i_dirty_val, d_dirty_val;
 
   always_ff @(posedge clk_i) begin
     if (!rst_ni) begin
       for (int s = 0; s < L2_NUM_SETS; s++) dirty_reg[s] <= '0;
     end else if (flush_active) begin
       dirty_reg[flush_cnt] <= '0;
     end else begin
       if (i_dirty_wr && d_dirty_wr && i_dirty_idx == d_dirty_idx) begin
         for (int w = 0; w < L2_NUM_WAY; w++) begin
           if (i_dirty_way[w]) dirty_reg[i_dirty_idx][w] <= i_dirty_val;
           if (d_dirty_way[w]) dirty_reg[d_dirty_idx][w] <= d_dirty_val;
         end
       end else begin
         if (i_dirty_wr)
           for (int w = 0; w < L2_NUM_WAY; w++)
             if (i_dirty_way[w]) dirty_reg[i_dirty_idx][w] <= i_dirty_val;
         if (d_dirty_wr)
           for (int w = 0; w < L2_NUM_WAY; w++)
             if (d_dirty_way[w]) dirty_reg[d_dirty_idx][w] <= d_dirty_val;
       end
     end
   end
 
   logic [L2_NUM_WAY-1:0] i_dirty_read;
   logic [L2_NUM_WAY-1:0] d_dirty_read;
   assign i_dirty_read = dirty_reg[i_req_set];
   assign d_dirty_read = dirty_reg[d_req_set];
 
   // =========================================================================
   // Per-pipe hit/miss detection
   // =========================================================================
   logic [L2_NUM_WAY-1:0] i_valid_vec, i_hit_vec, i_hit_way_oh;
   logic                  i_hit_any;
   logic [BLK_SIZE-1:0]   i_select_data;
 
   always_comb begin
     for (int w = 0; w < L2_NUM_WAY; w++) begin
       i_valid_vec[w] = i_tag_rdata[w][L2_TAG_BITS];
       i_hit_vec[w]   = i_tag_rdata[w][L2_TAG_BITS-1:0] == i_req_tag;
     end
     i_hit_way_oh = i_valid_vec & i_hit_vec;
     i_hit_any    = |i_hit_way_oh;
     i_select_data = '0;
     for (int w = 0; w < L2_NUM_WAY; w++)
       if (i_hit_way_oh[w]) i_select_data = i_data_rdata[w];
   end
 
   logic [L2_NUM_WAY-1:0] d_valid_vec, d_hit_vec, d_hit_way_oh;
   logic                  d_hit_any;
   logic [L2_WAY_W-1:0]   d_hit_way_bin;
   logic [BLK_SIZE-1:0]   d_select_data;
 
   always_comb begin
     for (int w = 0; w < L2_NUM_WAY; w++) begin
       d_valid_vec[w] = d_tag_rdata[w][L2_TAG_BITS];
       d_hit_vec[w]   = d_tag_rdata[w][L2_TAG_BITS-1:0] == d_req_tag;
     end
     d_hit_way_oh = d_valid_vec & d_hit_vec;
     d_hit_any    = |d_hit_way_oh;
     d_hit_way_bin = '0;
     for (int w = L2_NUM_WAY - 1; w >= 0; w--)
       if (d_hit_way_oh[w]) d_hit_way_bin = L2_WAY_W'(w);
     d_select_data = '0;
     for (int w = 0; w < L2_NUM_WAY; w++)
       if (d_hit_way_oh[w]) d_select_data = d_data_rdata[w];
   end
 
   // =========================================================================
   // Per-pipe PLRU eviction
   // =========================================================================
   /* verilator lint_off UNOPTFLAT */
   logic [L2_NUM_WAY-1:0] i_evict_way, d_evict_way;
   logic [L2_NUM_WAY-2:0] i_updated_node, d_updated_node;
 
   always_comb begin
     i_updated_node = update_node(i_plru_rdata, i_hit_way_oh);
     i_evict_way    = compute_evict_way(i_plru_rdata);
   end
 
   always_comb begin
     d_updated_node = update_node(d_plru_rdata, d_hit_way_oh);
     d_evict_way    = compute_evict_way(d_plru_rdata);
   end
 
   // =========================================================================
   // Per-pipe eviction data
   // =========================================================================
   logic                   i_evict_dirty;
   logic [L2_TAG_BITS-1:0] i_evict_tag;
   logic [XLEN-1:0]        i_evict_addr;
   logic [BLK_SIZE-1:0]    i_evict_data;
 
   always_comb begin
     i_evict_dirty = 1'b0; i_evict_tag = '0; i_evict_data = '0;
     for (int w = 0; w < L2_NUM_WAY; w++) begin
       if (i_evict_way[w]) begin
         i_evict_dirty = i_dirty_read[w] && i_tag_rdata[w][L2_TAG_BITS];
         i_evict_tag   = i_tag_rdata[w][L2_TAG_BITS-1:0];
         i_evict_data  = i_data_rdata[w];
       end
     end
     i_evict_addr = {i_evict_tag, i_req_set, {L2_OFFSET_BITS{1'b0}}};
   end
 
   logic                   d_evict_dirty;
   logic [L2_TAG_BITS-1:0] d_evict_tag;
   logic [XLEN-1:0]        d_evict_addr;
   logic [BLK_SIZE-1:0]    d_evict_data;
 
   always_comb begin
     d_evict_dirty = 1'b0; d_evict_tag = '0; d_evict_data = '0;
     for (int w = 0; w < L2_NUM_WAY; w++) begin
       if (d_evict_way[w]) begin
         d_evict_dirty = d_dirty_read[w] && d_tag_rdata[w][L2_TAG_BITS];
         d_evict_tag   = d_tag_rdata[w][L2_TAG_BITS-1:0];
         d_evict_data  = d_data_rdata[w];
       end
     end
     d_evict_addr = {d_evict_tag, d_req_set, {L2_OFFSET_BITS{1'b0}}};
   end
 
   // =========================================================================
   // Write-merge for D-pipe hit writes
   // =========================================================================
   logic [BLK_SIZE-1:0] d_hit_wr_merged;
   always_comb begin
     d_hit_wr_merged = d_select_data;
     for (int b = 0; b < BLK_SIZE/8; b++)
       if (d_req_q.wstrb[b]) d_hit_wr_merged[b*8 +: 8] = d_req_q.wdata[b*8 +: 8];
   end
   /* verilator lint_on UNOPTFLAT */
 
   // =========================================================================
   // MSHR (inlined, shared between pipes)
   // =========================================================================
   l2_mshr_entry_t         mshr_entries [L2_MSHR_DEPTH];
 
   logic [L2_MSHR_DEPTH-1:0] i_mshr_line_match, d_mshr_line_match;
   logic                     i_mshr_any_match,   d_mshr_any_match;
   logic [L2_MSHR_DEPTH-1:0] mshr_free_vec;
   logic [L2_MSHR_PTR_W-1:0] mshr_free_idx;
   logic                     mshr_any_free;
   logic [L2_MSHR_DEPTH-1:0] mshr_pending_vec;
   logic [L2_MSHR_PTR_W-1:0] mshr_pending_idx;
   logic                     mshr_pending_valid;
   logic [L2_ADDR_WIDTH-1:0] mshr_pending_addr;
   logic                     mshr_pending_dport;
   logic [L2_MSHR_DEPTH-1:0] mshr_complete_vec;
   logic                     mshr_resp_valid;
   logic [L2_MSHR_DEPTH-1:0] mshr_wb_vec;
   logic                     mshr_wb_valid;
   logic                     i_mshr_alloc_req;
   logic                     d_mshr_alloc_req;
   logic                     i_mshr_full;
   logic                     d_mshr_full;
   logic i_mshr_do_alloc;
   logic d_mshr_do_alloc;
   logic i_fill_complete;
   logic d_fill_complete;
   // WB request from eit
   logic i_wb_req;
   logic d_wb_req;
 
   assign i_mshr_alloc_req = (i_pipe_state == PIPE_RESOLVE) && !i_hit_any && !i_resolve_stall;
   assign d_mshr_alloc_req = (d_pipe_state == PIPE_RESOLVE) && !d_hit_any && !d_resolve_stall;
 
   always_comb begin
     for (int i = 0; i < L2_MSHR_DEPTH; i++) begin
       i_mshr_line_match[i] = mshr_entries[i].valid &&
                               (mshr_entries[i].addr[L2_ADDR_WIDTH-1:L2_OFFSET_BITS] ==
                                i_req_q.addr[L2_ADDR_WIDTH-1:L2_OFFSET_BITS]);
       d_mshr_line_match[i] = mshr_entries[i].valid &&
                               (mshr_entries[i].addr[L2_ADDR_WIDTH-1:L2_OFFSET_BITS] ==
                                d_req_q.addr[L2_ADDR_WIDTH-1:L2_OFFSET_BITS]);
     end
     i_mshr_any_match = |i_mshr_line_match;
     d_mshr_any_match = |d_mshr_line_match;
   end
 
   always_comb begin
     for (int i = 0; i < L2_MSHR_DEPTH; i++)
       mshr_free_vec[i] = !mshr_entries[i].valid;
     mshr_any_free = |mshr_free_vec;
     mshr_free_idx = '0;
     for (int i = L2_MSHR_DEPTH - 1; i >= 0; i--)
       if (mshr_free_vec[i]) mshr_free_idx = L2_MSHR_PTR_W'(i);
   end
 
   assign i_mshr_full = !mshr_any_free && !i_mshr_any_match;
   assign d_mshr_full = !mshr_any_free && !d_mshr_any_match;
 
   // Pending MSHR for memory controller
   always_comb begin
     for (int i = 0; i < L2_MSHR_DEPTH; i++)
       mshr_pending_vec[i] = mshr_entries[i].valid && (mshr_entries[i].state == MSHR_PENDING);
     mshr_pending_valid = |mshr_pending_vec;
     mshr_pending_idx   = '0;
     for (int i = L2_MSHR_DEPTH - 1; i >= 0; i--)
       if (mshr_pending_vec[i]) mshr_pending_idx = L2_MSHR_PTR_W'(i);
     mshr_pending_addr  = mshr_entries[mshr_pending_idx].addr;
     mshr_pending_dport = mshr_entries[mshr_pending_idx].from_dport;
   end
 
   // Fill matching for MSHR completion
   logic [L2_MSHR_DEPTH-1:0] mshr_fill_match_vec;
   logic [L2_MSHR_PTR_W-1:0] mshr_fill_entry_idx;
   logic                     mshr_fill_from_dport;
 
   always_comb begin
     for (int i = 0; i < L2_MSHR_DEPTH; i++)
       mshr_fill_match_vec[i] = mshr_entries[i].valid &&
                                 (mshr_entries[i].state == MSHR_FILL_ACTIVE);
     mshr_fill_entry_idx = '0;
     for (int i = L2_MSHR_DEPTH - 1; i >= 0; i--)
       if (mshr_fill_match_vec[i]) mshr_fill_entry_idx = L2_MSHR_PTR_W'(i);
     mshr_fill_from_dport = mshr_entries[mshr_fill_entry_idx].from_dport;
   end
 
   always_comb begin
     for (int i = 0; i < L2_MSHR_DEPTH; i++)
       mshr_complete_vec[i] = mshr_entries[i].valid && (mshr_entries[i].state == MSHR_COMPLETE);
     mshr_resp_valid = |mshr_complete_vec;
   end
 
   always_comb begin
     for (int i = 0; i < L2_MSHR_DEPTH; i++)
       mshr_wb_vec[i] = mshr_entries[i].valid && (mshr_entries[i].state == MSHR_WB_PENDING);
     mshr_wb_valid = |mshr_wb_vec;
   end
 
   // MSHR allocator arbitration: if both pipes try to allocate, I-pipe wins
 
   assign i_mshr_do_alloc = i_mshr_alloc_req && !i_mshr_any_match && !i_mshr_full;
   assign d_mshr_do_alloc = d_mshr_alloc_req && !d_mshr_any_match && !d_mshr_full &&
                          !(i_mshr_do_alloc && mshr_free_vec == (1 << mshr_free_idx));
 
   // =========================================================================
   // Memory controller signals
   // =========================================================================
   logic                     fill_resp_valid;
   logic [BLK_SIZE-1:0]      fill_resp_data;
   logic                     fill_issued;
   logic                     wb_done;
   logic                     mem_busy;
   logic [L2_ADDR_WIDTH-1:0] mem_addr_q;
   logic [BLK_SIZE-1:0]      mem_data_q;
   mem_state_t               mem_state;
 
   // Which pipe requested the current writeback
   logic                     wb_from_dport;
 
   // Fill routing to pipes
   assign i_fill_complete = fill_resp_valid && !mshr_fill_from_dport;
   assign d_fill_complete = fill_resp_valid &&  mshr_fill_from_dport;
 
   // WB request from either pipe
   assign i_wb_req = (i_pipe_state == PIPE_WB_EVICT);
   assign d_wb_req = (d_pipe_state == PIPE_WB_EVICT);
 
   // Eviction data/addr for memory controller (latched per pipe)
   logic [XLEN-1:0]    wb_addr_latch;
   logic [BLK_SIZE-1:0] wb_data_latch;
 
   // Fill request from either pipe in MISS_WAIT
   assign i_miss_wait = (i_pipe_state == PIPE_MISS_WAIT);
   assign d_miss_wait = (d_pipe_state == PIPE_MISS_WAIT);
 
   assign fill_req_valid = (i_miss_wait || d_miss_wait) && mshr_pending_valid && !mem_busy;
   assign wb_req_valid   = (i_wb_req || d_wb_req) && !mem_busy;
 
   // =========================================================================
   // Set-conflict hazard detection
   // =========================================================================
   // Stall a pipe in RESOLVE if the other pipe is filling the same set
   // (prevents reading stale tags while the other pipe overwrites them)
   assign i_fill_writing = (i_pipe_state == PIPE_FILL_RESPOND);
   assign d_fill_writing = (d_pipe_state == PIPE_FILL_RESPOND);
 
   assign i_resolve_stall = (i_pipe_state == PIPE_RESOLVE) &&
                          (d_fill_writing && d_req_set == i_req_set);
   assign d_resolve_stall = (d_pipe_state == PIPE_RESOLVE) &&
                          (i_fill_writing && i_req_set == d_req_set);
 
   // If both pipes miss on the same set, D-pipe defers to I-pipe
   assign dual_miss_same_set = (i_pipe_state == PIPE_RESOLVE) && !i_hit_any &&
                             (d_pipe_state == PIPE_RESOLVE) && !d_hit_any &&
                             (i_req_set == d_req_set);
 
   // =========================================================================
   // MSHR state machine
   // =========================================================================
   logic i_mshr_resp_accepted, d_mshr_resp_accepted;
 
   always_ff @(posedge clk_i) begin
     if (!rst_ni) begin
       for (int i = 0; i < L2_MSHR_DEPTH; i++)
         mshr_entries[i] <= '0;
     end else begin
       // I-pipe allocation
       if (i_mshr_do_alloc) begin
         mshr_entries[mshr_free_idx].valid     <= 1'b1;
         mshr_entries[mshr_free_idx].state     <= MSHR_PENDING;
         mshr_entries[mshr_free_idx].addr      <= i_req_q.addr;
         mshr_entries[mshr_free_idx].is_write  <= 1'b0;
         mshr_entries[mshr_free_idx].wdata     <= '0;
         mshr_entries[mshr_free_idx].wstrb     <= '0;
         mshr_entries[mshr_free_idx].from_dport <= 1'b0;
       end
 
       // D-pipe allocation (uses next free after I-pipe if both allocate)
       if (d_mshr_do_alloc) begin
         automatic logic [L2_MSHR_PTR_W-1:0] d_idx;
         if (i_mshr_do_alloc) begin
           d_idx = '0;
           for (int i = L2_MSHR_DEPTH - 1; i >= 0; i--)
             if (mshr_free_vec[i] && L2_MSHR_PTR_W'(i) != mshr_free_idx) d_idx = L2_MSHR_PTR_W'(i);
         end else begin
           d_idx = mshr_free_idx;
         end
         mshr_entries[d_idx].valid     <= 1'b1;
         mshr_entries[d_idx].state     <= MSHR_PENDING;
         mshr_entries[d_idx].addr      <= d_req_q.addr;
         mshr_entries[d_idx].is_write  <= d_req_wr;
         mshr_entries[d_idx].wdata     <= d_req_q.wdata;
         mshr_entries[d_idx].wstrb     <= d_req_q.wstrb;
         mshr_entries[d_idx].from_dport <= 1'b1;
       end

       // Fill issued → PENDING → FILL_ACTIVE
       if (fill_issued) begin
         for (int i = 0; i < L2_MSHR_DEPTH; i++)
           if (mshr_entries[i].valid && mshr_entries[i].state == MSHR_PENDING) begin
             mshr_entries[i].state <= MSHR_FILL_ACTIVE;
             break;
           end
       end
 
       // Fill response → FILL_ACTIVE → COMPLETE
       if (fill_resp_valid && |mshr_fill_match_vec)
         mshr_entries[mshr_fill_entry_idx].state <= MSHR_COMPLETE;
 
       // Response accepted → clear entry
       if (i_mshr_resp_accepted) begin
         for (int i = 0; i < L2_MSHR_DEPTH; i++)
           if (mshr_entries[i].valid && mshr_entries[i].state == MSHR_COMPLETE &&
               !mshr_entries[i].from_dport) begin
             mshr_entries[i].valid <= 1'b0;
             mshr_entries[i].state <= MSHR_IDLE;
             break;
           end
       end
       if (d_mshr_resp_accepted) begin
         for (int i = 0; i < L2_MSHR_DEPTH; i++)
           if (mshr_entries[i].valid && mshr_entries[i].state == MSHR_COMPLETE &&
               mshr_entries[i].from_dport) begin
             mshr_entries[i].valid <= 1'b0;
             mshr_entries[i].state <= MSHR_IDLE;
             break;
           end
       end
 
       // WB done → WB_PENDING → PENDING
       if (mshr_wb_valid && wb_done) begin
         for (int i = 0; i < L2_MSHR_DEPTH; i++)
           if (mshr_entries[i].valid && mshr_entries[i].state == MSHR_WB_PENDING)
             mshr_entries[i].state <= MSHR_PENDING;
       end
     end
   end
 
   // =========================================================================
   // Memory controller FSM
   // =========================================================================
   assign mem_busy = (mem_state != MEM_IDLE);
 
   always_ff @(posedge clk_i) begin
     if (!rst_ni) begin
       mem_state       <= MEM_IDLE;
       mem_addr_q      <= '0;
       mem_data_q      <= '0;
       fill_resp_valid <= 1'b0;
       fill_resp_data  <= '0;
       fill_issued     <= 1'b0;
       wb_done         <= 1'b0;
       wb_from_dport   <= 1'b0;
       wb_addr_latch   <= '0;
       wb_data_latch   <= '0;
     end else begin
       fill_resp_valid <= 1'b0;
       fill_issued     <= 1'b0;
       wb_done         <= 1'b0;
 
       unique case (mem_state)
         MEM_IDLE: begin
           if (wb_req_valid) begin
             mem_state <= MEM_WB_SEND;
             if (d_wb_req && !i_wb_req) begin
               mem_addr_q    <= d_evict_addr;
               mem_data_q    <= d_evict_data;
               wb_from_dport <= 1'b1;
             end else begin
               mem_addr_q    <= i_evict_addr;
               mem_data_q    <= i_evict_data;
               wb_from_dport <= 1'b0;
             end
           end else if (fill_req_valid) begin
             mem_state   <= MEM_FILL_SEND;
             mem_addr_q  <= {mshr_pending_addr[L2_ADDR_WIDTH-1:L2_OFFSET_BITS], {L2_OFFSET_BITS{1'b0}}};
             fill_issued <= 1'b1;
           end
         end
 
         MEM_WB_SEND: begin
           if (mem_res_i.valid) begin
             wb_done <= 1'b1;
             if (fill_req_valid) begin
               mem_state   <= MEM_FILL_SEND;
               mem_addr_q  <= {mshr_pending_addr[L2_ADDR_WIDTH-1:L2_OFFSET_BITS], {L2_OFFSET_BITS{1'b0}}};
               fill_issued <= 1'b1;
             end else begin
               mem_state <= MEM_IDLE;
             end
           end
         end
 
         MEM_FILL_SEND: begin
           if (mem_res_i.valid) begin
             fill_resp_valid <= 1'b1;
             fill_resp_data  <= mem_res_i.data;
             mem_state       <= MEM_IDLE;
           end
         end
 
         default: mem_state <= MEM_IDLE;
       endcase
     end
   end
 
   // Memory controller output mux
   iomem_req_t cached_req;
   always_comb begin
     cached_req.valid    = 1'b0;
     cached_req.ready    = 1'b1;
     cached_req.addr     = mem_addr_q;
     cached_req.data     = mem_data_q;
     cached_req.rw       = '0;
     cached_req.uncached = 1'b0;
     unique case (mem_state)
       MEM_WB_SEND: begin
         cached_req.valid = 1'b1;
         cached_req.rw    = '1;
       end
       MEM_FILL_SEND: begin
         cached_req.valid = 1'b1;
         cached_req.rw    = '0;
       end
       default: ;
     endcase
   end
 
   // =========================================================================
   // Bypass mux — both pipes can bypass
   // =========================================================================
   logic i_bypass_active;
   logic d_bypass_active;
   assign i_bypass_active = (i_pipe_state == PIPE_BYPASS);
   assign d_bypass_active = (d_pipe_state == PIPE_BYPASS);
 
   always_comb begin
     if (i_bypass_active) begin
       mem_req_o.valid    = 1'b1;
       mem_req_o.ready    = 1'b1;
       mem_req_o.addr     = i_req_q.addr;
       mem_req_o.data     = '0;
       mem_req_o.rw       = '0;
       mem_req_o.uncached = 1'b1;
     end else if (d_bypass_active) begin
       mem_req_o.valid    = 1'b1;
       mem_req_o.ready    = 1'b1;
       mem_req_o.addr     = d_req_q.addr;
       mem_req_o.data     = d_req_q.wdata;
       mem_req_o.rw       = d_req_q.wstrb;
       mem_req_o.uncached = 1'b1;
     end else begin
       mem_req_o = cached_req;
     end
   end
 
   // =========================================================================
   // I-pipe SRAM control
   // =========================================================================
   always_comb begin
     i_tag_we    = '0;
     i_tag_wdata = '0;
     i_data_we   = '0;
     i_data_wdata = '0;
 
     if (flush_active) begin
       i_tag_we    = '1;
       i_tag_wdata = '0;
     end else if (i_fill_complete) begin
       i_tag_we    = i_evict_way;
       i_tag_wdata = {1'b1, i_req_tag};
       i_data_we   = i_evict_way;
       i_data_wdata = fill_resp_data;
     end
   end
 
   // =========================================================================
   // D-pipe SRAM control
   // =========================================================================
   always_comb begin
     d_tag_we    = '0;
     d_tag_wdata = '0;
     d_data_we   = '0;
     d_data_wdata = '0;
 
     if (d_pipe_state == PIPE_HIT_RESPOND && d_req_wr) begin
       d_data_we    = d_hit_way_oh;
       d_data_wdata = d_hit_wr_merged;
     end else if (d_fill_complete) begin
       d_tag_we    = d_evict_way;
       d_tag_wdata = {1'b1, d_req_tag};
       d_data_we   = d_evict_way;
       d_data_wdata = d_req_wr ? merge_fill_data(fill_resp_data, d_req_q.wdata, d_req_q.wstrb)
                                : fill_resp_data;
     end
   end
 
   // =========================================================================
   // PLRU update control
   // =========================================================================
   always_comb begin
     i_plru_wr    = 1'b0;
     i_plru_wdata = '0;
     if (i_pipe_state == PIPE_HIT_RESPOND) begin
       i_plru_wr    = 1'b1;
       i_plru_wdata = i_updated_node;
     end else if (i_pipe_state == PIPE_FILL_RESPOND) begin
       i_plru_wr    = 1'b1;
       i_plru_wdata = update_node(i_plru_rdata, i_evict_way);
     end
   end
 
   always_comb begin
     d_plru_wr    = 1'b0;
     d_plru_wdata = '0;
     if (d_pipe_state == PIPE_HIT_RESPOND) begin
       d_plru_wr    = 1'b1;
       d_plru_wdata = d_updated_node;
     end else if (d_pipe_state == PIPE_FILL_RESPOND) begin
       d_plru_wr    = 1'b1;
       d_plru_wdata = update_node(d_plru_rdata, d_evict_way);
     end
   end
 
   // Helper: extract D-pipe hit way for merged PLRU update
   function automatic [L2_NUM_WAY-1:0] d_plru_hit_way();
     if (d_pipe_state == PIPE_HIT_RESPOND)
       return d_hit_way_oh;
     else
       return d_evict_way;
   endfunction
 
   // =========================================================================
   // Dirty update control
   // =========================================================================
   always_comb begin
     i_dirty_wr  = 1'b0;
     i_dirty_idx = i_req_set;
     i_dirty_way = '0;
     i_dirty_val = 1'b0;
     if (i_fill_complete) begin
       i_dirty_wr  = 1'b1;
       i_dirty_way = i_evict_way;
       i_dirty_val = 1'b0;
     end
   end
 
   always_comb begin
     d_dirty_wr  = 1'b0;
     d_dirty_idx = d_req_set;
     d_dirty_way = '0;
     d_dirty_val = 1'b0;
     if (d_pipe_state == PIPE_HIT_RESPOND && d_req_wr) begin
       d_dirty_wr  = 1'b1;
       d_dirty_way = d_hit_way_oh;
       d_dirty_val = 1'b1;
     end else if (d_fill_complete) begin
       d_dirty_wr  = 1'b1;
       d_dirty_way = d_evict_way;
       d_dirty_val = d_req_wr;
     end
   end
 
   // =========================================================================
   // I-pipe FSM
   // =========================================================================
   logic i_pipe_accept;
   assign i_pipe_accept = (i_pipe_state == PIPE_IDLE) && !flush_active && icache_req_i.valid;
 
   always_ff @(posedge clk_i) begin
     if (!rst_ni) begin
       i_pipe_state        <= PIPE_IDLE;
       i_req_q             <= '0;
       i_mshr_resp_accepted <= 1'b0;
     end else begin
       i_mshr_resp_accepted <= 1'b0;
 
       unique case (i_pipe_state)
         PIPE_IDLE: begin
           if (i_pipe_accept) begin
             i_req_q.addr       <= icache_req_i.addr;
             i_req_q.is_write   <= 1'b0;
             i_req_q.rw_size    <= NO_SIZE;
             i_req_q.wdata      <= '0;
             i_req_q.wstrb      <= '0;
             i_req_q.uncached   <= icache_req_i.uncached;
             i_req_q.from_dport <= 1'b0;
             i_pipe_state       <= icache_req_i.uncached ? PIPE_BYPASS : PIPE_TAG_LOOKUP;
           end
         end
 
         PIPE_TAG_LOOKUP:
           i_pipe_state <= PIPE_RESOLVE;
 
         PIPE_RESOLVE: begin
           if (i_resolve_stall || (i_mshr_any_match && !i_hit_any)) begin
             i_pipe_state <= PIPE_TAG_LOOKUP;
           end else if (i_hit_any) begin
             i_pipe_state <= PIPE_HIT_RESPOND;
           end else if (i_evict_dirty) begin
             i_pipe_state <= PIPE_WB_EVICT;
           end else begin
             i_pipe_state <= PIPE_MISS_WAIT;
           end
         end
 
         PIPE_HIT_RESPOND:
           i_pipe_state <= PIPE_IDLE;
 
         PIPE_WB_EVICT:
           if (wb_done && !wb_from_dport) i_pipe_state <= PIPE_MISS_WAIT;
 
         PIPE_MISS_WAIT:
           if (i_fill_complete) i_pipe_state <= PIPE_FILL_RESPOND;
 
         PIPE_FILL_RESPOND: begin
           i_mshr_resp_accepted <= 1'b1;
           i_pipe_state <= PIPE_IDLE;
         end
 
         PIPE_BYPASS:
           if (mem_res_i.valid && !d_bypass_active) i_pipe_state <= PIPE_IDLE;
 
         default: i_pipe_state <= PIPE_IDLE;
       endcase
     end
   end
 
   // =========================================================================
   // D-pipe FSM
   // =========================================================================
   logic d_pipe_accept;
   assign d_pipe_accept = (d_pipe_state == PIPE_IDLE) && !flush_active && dcache_req_i.valid;
 
   always_ff @(posedge clk_i) begin
     if (!rst_ni) begin
       d_pipe_state        <= PIPE_IDLE;
       d_req_q             <= '0;
       d_mshr_resp_accepted <= 1'b0;
     end else begin
       d_mshr_resp_accepted <= 1'b0;
 
       unique case (d_pipe_state)
         PIPE_IDLE: begin
           if (d_pipe_accept) begin
             d_req_q.addr       <= dcache_req_i.addr;
             d_req_q.is_write   <= dcache_req_i.rw;
             d_req_q.rw_size    <= dcache_req_i.rw_size;
             d_req_q.wdata      <= dcache_req_i.data;
             d_req_q.uncached   <= dcache_req_i.uncached;
             d_req_q.from_dport <= 1'b1;
             d_pipe_state       <= dcache_req_i.uncached ? PIPE_BYPASS : PIPE_TAG_LOOKUP;
             if (dcache_req_i.rw) begin
               unique case (dcache_req_i.rw_size)
                 NO_SIZE: d_req_q.wstrb <= '0;
                 BYTE:    d_req_q.wstrb <= (BLK_SIZE/8)'(1'b1)   << dcache_req_i.addr[BOFFSET-1:0];
                 HALF:    d_req_q.wstrb <= (BLK_SIZE/8)'(2'b11)  << dcache_req_i.addr[BOFFSET-1:0];
                 default: d_req_q.wstrb <= dcache_req_i.uncached
                                         ? ((BLK_SIZE/8)'(4'b1111) << dcache_req_i.addr[BOFFSET-1:0])
                                         : '1;
               endcase
             end else begin
               d_req_q.wstrb <= '0;
             end
           end
         end
 
         PIPE_TAG_LOOKUP:
           d_pipe_state <= PIPE_RESOLVE;
 
         PIPE_RESOLVE: begin
           if (d_resolve_stall || dual_miss_same_set || (d_mshr_any_match && !d_hit_any)) begin
             d_pipe_state <= PIPE_TAG_LOOKUP;
           end else if (d_hit_any) begin
             d_pipe_state <= PIPE_HIT_RESPOND;
           end else if (d_evict_dirty) begin
             d_pipe_state <= PIPE_WB_EVICT;
           end else begin
             d_pipe_state <= PIPE_MISS_WAIT;
           end
         end
 
         PIPE_HIT_RESPOND:
           d_pipe_state <= PIPE_IDLE;
 
         PIPE_WB_EVICT:
           if (wb_done && wb_from_dport) d_pipe_state <= PIPE_MISS_WAIT;
 
         PIPE_MISS_WAIT:
           if (d_fill_complete) d_pipe_state <= PIPE_FILL_RESPOND;
 
         PIPE_FILL_RESPOND: begin
           d_mshr_resp_accepted <= 1'b1;
           d_pipe_state <= PIPE_IDLE;
         end
 
         PIPE_BYPASS: begin
           if (mem_res_i.valid && !i_bypass_active)
             d_pipe_state <= PIPE_IDLE;
         end
 
         default: d_pipe_state <= PIPE_IDLE;
       endcase
     end
   end
 
   // =========================================================================
   // Response output (per pipe)
   // =========================================================================
   logic                i_resp_valid, d_resp_valid;
   logic [BLK_SIZE-1:0] i_resp_data,  d_resp_data;
 
   always_comb begin
     i_resp_valid = 1'b0;
     i_resp_data  = '0;
     if (i_pipe_state == PIPE_HIT_RESPOND) begin
       i_resp_valid = 1'b1;
       i_resp_data  = i_select_data;
     end else if (i_pipe_state == PIPE_FILL_RESPOND) begin
       i_resp_valid = 1'b1;
       i_resp_data  = fill_resp_data;
     end else if (i_bypass_active && mem_res_i.valid && !d_bypass_active) begin
       i_resp_valid = 1'b1;
       i_resp_data  = mem_res_i.data;
     end
   end
 
   always_comb begin
     d_resp_valid = 1'b0;
     d_resp_data  = '0;
     if (d_pipe_state == PIPE_HIT_RESPOND) begin
       d_resp_valid = 1'b1;
       d_resp_data  = d_req_wr ? d_req_q.wdata : d_select_data;
     end else if (d_pipe_state == PIPE_FILL_RESPOND) begin
       d_resp_valid = 1'b1;
       d_resp_data  = fill_resp_data;
     end else if (d_bypass_active && mem_res_i.valid && !i_bypass_active) begin
       d_resp_valid = 1'b1;
       d_resp_data  = mem_res_i.data;
     end
   end
 
   assign icache_res_o.valid = i_resp_valid;
   assign icache_res_o.ready = (i_pipe_state == PIPE_IDLE) && !flush_active;
   assign icache_res_o.blk   = i_resp_data;
 
   assign dcache_res_o.valid = d_resp_valid;
   assign dcache_res_o.ready = (d_pipe_state == PIPE_IDLE) && !flush_active;
   assign dcache_res_o.data  = d_resp_data;
 
   // =========================================================================
   // Performance counters
   // =========================================================================
   logic [31:0] cnt_hit, cnt_miss, cnt_wb, cnt_stall;
 
   logic ev_hit;
   logic ev_miss;
   logic ev_wb;
   assign ev_hit  = (i_pipe_state == PIPE_HIT_RESPOND) || (d_pipe_state == PIPE_HIT_RESPOND);
   assign ev_miss = ((i_pipe_state == PIPE_RESOLVE) && !i_hit_any && !i_resolve_stall) ||
                    ((d_pipe_state == PIPE_RESOLVE) && !d_hit_any && !d_resolve_stall);
   assign ev_wb   = wb_done;
 
   always_ff @(posedge clk_i) begin
     if (!rst_ni) begin
       cnt_hit   <= '0;
       cnt_miss  <= '0;
       cnt_wb    <= '0;
       cnt_stall <= '0;
     end else begin
       if (ev_hit)  cnt_hit  <= cnt_hit  + 1;
       if (ev_miss) cnt_miss <= cnt_miss + 1;
       if (ev_wb)   cnt_wb   <= cnt_wb   + 1;
     end
   end
 
   // =========================================================================
   // Helper functions
   // =========================================================================
   function automatic logic [BLK_SIZE-1:0] merge_fill_data(
     input logic [BLK_SIZE-1:0]   fill,
     input logic [BLK_SIZE-1:0]   wdata,
     input logic [BLK_SIZE/8-1:0] wstrb
   );
     logic [BLK_SIZE-1:0] merged;
     merged = fill;
     for (int b = 0; b < BLK_SIZE/8; b++)
       if (wstrb[b]) merged[b*8 +: 8] = wdata[b*8 +: 8];
     return merged;
   endfunction
 
   function automatic [L2_NUM_WAY-2:0] update_node(
     input logic [L2_NUM_WAY-2:0] node_in,
     input logic [L2_NUM_WAY-1:0] hit_vec
   );
     logic [L2_NUM_WAY-2:0] node_tmp;
     int unsigned idx_base, shift;
     node_tmp = node_in;
     for (int unsigned i = 0; i < L2_NUM_WAY; i++) begin
       if (hit_vec[i]) begin
         for (int unsigned lvl = 0; lvl < $clog2(L2_NUM_WAY); lvl++) begin
           idx_base = (2 ** lvl) - 1;
           shift = $clog2(L2_NUM_WAY) - lvl;
           node_tmp[idx_base+(i>>shift)] = ((i >> (shift - 1)) & 1) == 0;
         end
       end
     end
     return node_tmp;
   endfunction
 
   function automatic [L2_NUM_WAY-1:0] compute_evict_way(
     input logic [L2_NUM_WAY-2:0] node_in
   );
     logic [L2_NUM_WAY-1:0] way;
     int unsigned idx_base, shift;
     for (int unsigned i = 0; i < L2_NUM_WAY; i++) begin
       logic en;
       en = 1'b1;
       for (int unsigned lvl = 0; lvl < $clog2(L2_NUM_WAY); lvl++) begin
         idx_base = (2 ** lvl) - 1;
         shift = $clog2(L2_NUM_WAY) - lvl;
         if (((i >> (shift - 1)) & 32'b1) == 32'b1) en &= node_in[idx_base+(i>>shift)];
         else en &= ~node_in[idx_base+(i>>shift)];
       end
       way[i] = en;
     end
     return way;
   endfunction
 
 endmodule
 