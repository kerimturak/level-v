// ============================================================================
// Load/Store Buffer
// ============================================================================
// Sits between the MEM pipeline stage and D-cache.
//
// Features:
//   - Parametric-depth store buffer with byte-enable tracking
//   - Store merging: consecutive stores to the same word-aligned address are
//     coalesced using byte strobes (e.g. SB+SB → SH, SH+SH → SW)
//   - Store-to-load forwarding: when a load hits a buffered store and all
//     requested bytes are present, data is returned combinationally without
//     going to D-cache
//   - Partial forwarding NOT attempted (stall until store drains instead)
//   - Flush-safe: buffer drains on fe_flush_cache_i (fence.i)
//
// The module does NOT touch instruction correctness — loads stall until all
// older stores are visible (in-order).
// ============================================================================
`timescale 1ns / 1ps
`include "ceres_defines.svh"

module ldst_buffer
  import ceres_param::*;
#(
    parameter int unsigned DEPTH = 4
) (
    input logic clk_i,
    input logic rst_ni,
    input logic flush_i, // fence.i or pipeline flush

    // --- Pipeline side (from EX stage) ---
    input  data_req_t req_i,   // incoming load/store request
    input  data_req_t me_req_i, // MEM-stage mirrored request (stable store payload source)
    output logic      stall_o, // back-pressure to pipeline

    // --- D-cache side ---
    output dcache_req_t dcache_req_o,        // to D-cache
    input  dcache_res_t dcache_res_i,        // from D-cache
    output logic        dcache_txn_active_o, // a transaction is in flight

    // --- Load result ---
    output logic [XLEN-1:0] ld_data_o,       // sign/size-extended load result
    output logic            ld_data_valid_o, // load data ready this cycle

    // --- PMA uncached flag (from external PMA unit) ---
    input logic uncached_i
);

  localparam int unsigned PTR_W = (DEPTH > 1) ? $clog2(DEPTH) : 1;
  localparam int unsigned CNT_W = $clog2(DEPTH + 1);
  localparam logic [PTR_W-1:0] DEPTH_LAST_PTR = PTR_W'(DEPTH - 1);
  localparam logic [CNT_W-1:0] DEPTH_CNT      = CNT_W'(DEPTH);

  function automatic logic [3:0] f_store_mask(input logic [1:0] addr_lsb, input rw_size_e size);
    logic [3:0] mask;
    begin
      mask = 4'b0000;
      unique case (size)
        BYTE: mask = (4'b0001 << addr_lsb);
        HALF: mask = addr_lsb[1] ? 4'b1100 : 4'b0011;
        WORD: mask = 4'b1111;
        default: mask = 4'b0000;
      endcase
      return mask;
    end
  endfunction

  function automatic logic [31:0] f_store_word_data(
      input logic [31:0] data,
      input logic [1:0]  addr_lsb,
      input rw_size_e    size
  );
    logic [31:0] word_data;
    begin
      word_data = 32'h0;
      unique case (size)
        BYTE: word_data[(addr_lsb*8)+:8] = data[7:0];
        HALF: begin
          if (addr_lsb[1]) begin
            word_data[31:16] = data[15:0];
          end else begin
            word_data[15:0] = data[15:0];
          end
        end
        WORD: word_data = data;
        default: word_data = 32'h0;
      endcase
      return word_data;
    end
  endfunction

  function automatic logic [31:0] f_merge_word_data(
      input logic [31:0] base_data,
      input logic [31:0] new_data,
      input logic [3:0]  new_mask
  );
    logic [31:0] merged;
    begin
      merged = base_data;
      for (int b = 0; b < 4; b++) begin
        if (new_mask[b]) begin
          merged[(b*8)+:8] = new_data[(b*8)+:8];
        end
      end
      return merged;
    end
  endfunction

  function automatic logic f_mask_encodable(input logic [3:0] mask);
    begin
      unique case (mask)
        4'b0001, 4'b0010, 4'b0100, 4'b1000,
        4'b0011, 4'b1100,
        4'b1111: f_mask_encodable = 1'b1;
        default: f_mask_encodable = 1'b0;
      endcase
    end
  endfunction

  function automatic rw_size_e f_mask_to_size(input logic [3:0] mask);
    begin
      unique case (mask)
        4'b0001, 4'b0010, 4'b0100, 4'b1000: f_mask_to_size = BYTE;
        4'b0011, 4'b1100: f_mask_to_size = HALF;
        4'b1111: f_mask_to_size = WORD;
        default: f_mask_to_size = NO_SIZE;
      endcase
    end
  endfunction

  function automatic logic [1:0] f_mask_to_lsb(input logic [3:0] mask);
    begin
      unique case (mask)
        4'b0001: f_mask_to_lsb = 2'd0;
        4'b0010: f_mask_to_lsb = 2'd1;
        4'b0100: f_mask_to_lsb = 2'd2;
        4'b1000: f_mask_to_lsb = 2'd3;
        4'b0011: f_mask_to_lsb = 2'd0;
        4'b1100: f_mask_to_lsb = 2'd2;
        default: f_mask_to_lsb = 2'd0;
      endcase
    end
  endfunction

  function automatic logic [31:0] f_issue_data(input logic [31:0] word_data, input logic [3:0] mask);
    logic [31:0] data;
    begin
      data = 32'h0;
      unique case (mask)
        4'b0001: data[7:0] = word_data[7:0];
        4'b0010: data[7:0] = word_data[15:8];
        4'b0100: data[7:0] = word_data[23:16];
        4'b1000: data[7:0] = word_data[31:24];
        4'b0011: data[15:0] = word_data[15:0];
        4'b1100: data[15:0] = word_data[31:16];
        4'b1111: data = word_data;
        default: data = word_data;
      endcase
      return data;
    end
  endfunction

  logic                  req_valid_q;
  logic [XLEN-1:0]       req_addr_q;
  logic                  req_rw_q;
  rw_size_e              req_rw_size_q;
  logic [31:0]           req_data_q;

  logic                  req_meta_changed;
  logic                  req_fire;
  logic                  req_data_changed;
  logic                  req_waiting_q;

  logic [XLEN-1:0]       store_fifo_addr_q [DEPTH];
  rw_size_e              store_fifo_size_q [DEPTH];
  logic [31:0]           store_fifo_data_q [DEPTH];
  logic [3:0]            store_fifo_mask_q [DEPTH];
  logic [PTR_W-1:0]      store_fifo_head_q;
  logic [PTR_W-1:0]      store_fifo_tail_q;
  logic [CNT_W-1:0]      store_fifo_count_q;

  logic                  txn_active_q;

  logic [XLEN-1:0]       active_addr_q;
  rw_size_e              active_rw_size_q;
  logic                  active_ld_sign_q;
  logic                  active_is_load_q;

  logic [31:0]           raw_ld_word;
  logic [7:0]            selected_byte;
  logic [15:0]           selected_halfword;
  logic [31:0]           store_data_sel;
  logic [1:0]            load_addr_lsb;

  logic                  issue_valid;
  logic                  issue_is_store;
  logic [XLEN-1:0]       issue_addr;
  rw_size_e              issue_size;
  logic [31:0]           issue_data;
  logic                  issue_from_pending;

  logic                  store_fifo_match_tail_i;
  logic [PTR_W-1:0]      store_fifo_tail_prev;
  logic                  store_fifo_empty;
  logic                  store_fifo_full;
  logic                  enqueue_store;
  logic                  dequeue_store;
  logic                  merge_tail_i;
  logic                  enqueue_new_i;
  logic                  tail_word_match_i;

  logic [PTR_W-1:0]      store_fifo_head_n;
  logic [PTR_W-1:0]      store_fifo_tail_n;
  logic [3:0]            req_store_mask;
  logic [31:0]           req_store_word_data;
  logic [XLEN-1:0]       req_store_word_addr;
  logic [3:0]            tail_merge_mask;
  logic [31:0]           tail_merge_data;
  logic                  issue_mask_valid;
  logic [3:0]            issue_mask;
  logic [1:0]            issue_addr_lsb;
  logic [XLEN-1:0]       issue_store_addr;
  rw_size_e              issue_store_size;
  logic [31:0]           issue_store_data;

  logic                  load_req_i;
  logic [3:0]            load_req_mask_i;
  logic [XLEN-1:0]       load_req_word_addr_i;
  logic [31:0]           fwd_word_data;
  logic [3:0]            fwd_collected_mask;
  logic                  fwd_hit;
  logic [PTR_W-1:0]      fwd_scan_ptr;
  logic [31:0]           ld_word_mux;
  logic [1:0]            ld_addr_lsb_mux;
  rw_size_e              ld_size_mux;
  logic                  ld_sign_mux;

  assign req_data_changed = req_i.rw && (req_i.data != req_data_q);
  assign req_meta_changed = (req_i.addr != req_addr_q) || (req_i.rw != req_rw_q) || (req_i.rw_size != req_rw_size_q) ||
                            (req_i.valid && !req_valid_q);
  assign store_fifo_empty = (store_fifo_count_q == '0);
  assign store_fifo_full  = (store_fifo_count_q == DEPTH_CNT);
  assign req_store_mask = f_store_mask(req_i.addr[1:0], req_i.rw_size);
  assign req_store_word_data = f_store_word_data(store_data_sel, req_i.addr[1:0], req_i.rw_size);
  assign req_store_word_addr = {req_i.addr[XLEN-1:2], 2'b00};
  assign load_req_i = req_i.valid && !req_i.rw;
  assign load_req_mask_i = f_store_mask(req_i.addr[1:0], req_i.rw_size);
  assign load_req_word_addr_i = {req_i.addr[XLEN-1:2], 2'b00};

  always_comb begin
    if (store_fifo_head_q == DEPTH_LAST_PTR) begin
      store_fifo_head_n = '0;
    end else begin
      store_fifo_head_n = store_fifo_head_q + 1'b1;
    end

    if (store_fifo_tail_q == DEPTH_LAST_PTR) begin
      store_fifo_tail_n = '0;
    end else begin
      store_fifo_tail_n = store_fifo_tail_q + 1'b1;
    end

    if (store_fifo_tail_q == '0) begin
      store_fifo_tail_prev = DEPTH_LAST_PTR;
    end else begin
      store_fifo_tail_prev = store_fifo_tail_q - 1'b1;
    end
  end

  assign req_fire = req_i.valid && !txn_active_q && store_fifo_empty && (req_meta_changed || req_waiting_q);

  assign store_fifo_match_tail_i = req_i.valid && req_i.rw && !store_fifo_empty &&
                                   (req_i.addr == store_fifo_addr_q[store_fifo_tail_prev]) &&
                                   (req_i.rw_size == store_fifo_size_q[store_fifo_tail_prev]);

  assign tail_word_match_i = req_i.valid && req_i.rw && !store_fifo_empty &&
                             (req_store_word_addr == {store_fifo_addr_q[store_fifo_tail_prev][XLEN-1:2], 2'b00});
  assign tail_merge_mask = store_fifo_mask_q[store_fifo_tail_prev] | req_store_mask;
  assign tail_merge_data = f_merge_word_data(store_fifo_data_q[store_fifo_tail_prev], req_store_word_data, req_store_mask);

  always_comb begin
    fwd_word_data       = '0;
    fwd_collected_mask  = 4'b0000;
    fwd_scan_ptr        = store_fifo_tail_prev;

    for (int unsigned k = 0; k < DEPTH; k++) begin
      if (k < store_fifo_count_q) begin
        if ({store_fifo_addr_q[fwd_scan_ptr][XLEN-1:2], 2'b00} == load_req_word_addr_i) begin
          for (int unsigned b = 0; b < 4; b++) begin
            if (store_fifo_mask_q[fwd_scan_ptr][b] && !fwd_collected_mask[b]) begin
              fwd_word_data[(b*8)+:8] = store_fifo_data_q[fwd_scan_ptr][(b*8)+:8];
            end
          end
          fwd_collected_mask = fwd_collected_mask | store_fifo_mask_q[fwd_scan_ptr];
        end

        if (fwd_scan_ptr == '0) begin
          fwd_scan_ptr = DEPTH_LAST_PTR;
        end else begin
          fwd_scan_ptr = fwd_scan_ptr - 1'b1;
        end
      end
    end
  end

  assign fwd_hit = load_req_i && !txn_active_q && !store_fifo_empty &&
                   ((fwd_collected_mask & load_req_mask_i) == load_req_mask_i);

  assign issue_from_pending = !txn_active_q && !store_fifo_empty && !fwd_hit;
  assign enqueue_store = txn_active_q && req_i.valid && req_meta_changed && req_i.rw;
  assign merge_tail_i  = enqueue_store && tail_word_match_i && f_mask_encodable(tail_merge_mask);
  assign enqueue_new_i = enqueue_store && !merge_tail_i && !store_fifo_full;
  assign dequeue_store = issue_from_pending;

  assign issue_mask = store_fifo_mask_q[store_fifo_head_q];
  assign issue_mask_valid = f_mask_encodable(issue_mask);
  assign issue_addr_lsb = f_mask_to_lsb(issue_mask);
  assign issue_store_addr = {store_fifo_addr_q[store_fifo_head_q][XLEN-1:2], 2'b00} + {{(XLEN-2){1'b0}}, issue_addr_lsb};
  assign issue_store_size = f_mask_to_size(issue_mask);
  assign issue_store_data = f_issue_data(store_fifo_data_q[store_fifo_head_q], issue_mask);

  always_comb begin
    issue_valid    = 1'b0;
    issue_is_store = 1'b0;
    issue_addr     = '0;
    issue_size     = NO_SIZE;
    issue_data     = '0;

    if (issue_from_pending) begin
      issue_valid    = 1'b1;
      issue_is_store = 1'b1;
      issue_addr     = issue_store_addr;
      issue_size     = issue_store_size;
      issue_data     = issue_store_data;
      if (!issue_mask_valid) begin
        issue_valid = 1'b0;
      end
    end else if (req_fire) begin
      issue_valid    = 1'b1;
      issue_is_store = req_i.rw;
      issue_addr     = req_i.addr;
      issue_size     = req_i.rw_size;
      issue_data     = store_data_sel;
    end
  end

  always_ff @(posedge clk_i) begin
    if (!rst_ni || flush_i) begin
      req_valid_q        <= 1'b0;
      req_addr_q         <= '0;
      req_rw_q           <= 1'b0;
      req_rw_size_q      <= NO_SIZE;
      req_data_q         <= '0;
      req_waiting_q      <= 1'b0;

      store_fifo_head_q  <= '0;
      store_fifo_tail_q  <= '0;
      store_fifo_count_q <= '0;

      for (int unsigned i = 0; i < DEPTH; i++) begin
        store_fifo_addr_q[i] <= '0;
        store_fifo_size_q[i] <= NO_SIZE;
        store_fifo_data_q[i] <= '0;
        store_fifo_mask_q[i] <= '0;
      end

      txn_active_q      <= 1'b0;
      active_addr_q     <= '0;
      active_rw_size_q  <= NO_SIZE;
      active_ld_sign_q  <= 1'b0;
      active_is_load_q  <= 1'b0;
    end else begin
      req_valid_q   <= req_i.valid;
      req_addr_q    <= req_i.addr;
      req_rw_q      <= req_i.rw;
      req_rw_size_q <= req_i.rw_size;
      req_data_q    <= req_i.data;

      if (issue_valid || fwd_hit || !req_i.valid) begin
        req_waiting_q <= 1'b0;
      end else if (req_i.valid && (txn_active_q || !store_fifo_empty)) begin
        req_waiting_q <= 1'b1;
      end

      if (enqueue_new_i) begin
        store_fifo_addr_q[store_fifo_tail_q] <= req_store_word_addr;
        store_fifo_size_q[store_fifo_tail_q] <= req_i.rw_size;
        store_fifo_data_q[store_fifo_tail_q] <= req_store_word_data;
        store_fifo_mask_q[store_fifo_tail_q] <= req_store_mask;
        store_fifo_tail_q                     <= store_fifo_tail_n;
        store_fifo_count_q                    <= store_fifo_count_q + 1'b1;
      end

      if (merge_tail_i) begin
        store_fifo_data_q[store_fifo_tail_prev] <= tail_merge_data;
        store_fifo_mask_q[store_fifo_tail_prev] <= tail_merge_mask;
        store_fifo_addr_q[store_fifo_tail_prev] <= req_store_word_addr;
        store_fifo_size_q[store_fifo_tail_prev] <= f_mask_to_size(tail_merge_mask);
      end else if (store_fifo_match_tail_i && req_data_changed) begin
        store_fifo_data_q[store_fifo_tail_prev] <= req_store_word_data;
        store_fifo_mask_q[store_fifo_tail_prev] <= req_store_mask;
        store_fifo_addr_q[store_fifo_tail_prev] <= req_store_word_addr;
        store_fifo_size_q[store_fifo_tail_prev] <= req_i.rw_size;
      end

      if (dequeue_store) begin
        store_fifo_head_q  <= store_fifo_head_n;
        store_fifo_count_q <= store_fifo_count_q - 1'b1;
      end

      if (dcache_res_i.valid) begin
        txn_active_q <= 1'b0;
      end

      if (issue_valid) begin
        txn_active_q      <= 1'b1;
        active_addr_q     <= issue_addr;
        active_rw_size_q  <= issue_size;
        active_ld_sign_q  <= req_i.ld_op_sign;
        active_is_load_q  <= !issue_is_store;
      end
    end
  end

  always_comb begin
    if (req_i.rw && me_req_i.valid && (me_req_i.addr == req_i.addr) && (me_req_i.rw_size == req_i.rw_size)) begin
      store_data_sel = me_req_i.data;
    end else begin
      store_data_sel = req_i.data;
    end

    dcache_req_o.valid    = issue_valid;
    dcache_req_o.addr     = issue_addr;
    dcache_req_o.ready    = 1'b1;
    dcache_req_o.rw       = issue_is_store;
    dcache_req_o.rw_size  = issue_size;
    dcache_req_o.data     = issue_data;
    dcache_req_o.uncached = uncached_i;
  end

  assign dcache_txn_active_o = txn_active_q;

  always_comb begin
    ld_word_mux     = fwd_hit ? fwd_word_data : dcache_res_i.data;
    ld_addr_lsb_mux = fwd_hit ? req_i.addr[1:0] : active_addr_q[1:0];
    ld_size_mux     = fwd_hit ? req_i.rw_size : active_rw_size_q;
    ld_sign_mux     = fwd_hit ? req_i.ld_op_sign : active_ld_sign_q;

    raw_ld_word       = ld_word_mux;
    load_addr_lsb     = ld_addr_lsb_mux;
    selected_byte     = raw_ld_word[(load_addr_lsb*8)+:8];
    selected_halfword = raw_ld_word[(load_addr_lsb[1]*16)+:16];

    if (ld_size_mux == BYTE) begin
      ld_data_o = ld_sign_mux ? {{24{selected_byte[7]}}, selected_byte} : {24'b0, selected_byte};
    end else if (ld_size_mux == HALF) begin
      ld_data_o = ld_sign_mux ? {{16{selected_halfword[15]}}, selected_halfword} : {16'b0, selected_halfword};
    end else if (ld_size_mux == WORD) begin
      ld_data_o = raw_ld_word;
    end else begin
      ld_data_o = '0;
    end

    ld_data_valid_o = (dcache_res_i.valid && active_is_load_q) || fwd_hit;
    stall_o = issue_valid || (!store_fifo_empty && !fwd_hit) || (txn_active_q && !dcache_res_i.valid);
  end

endmodule
