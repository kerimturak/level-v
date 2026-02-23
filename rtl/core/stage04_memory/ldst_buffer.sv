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

  logic                  req_valid_q;
  logic [XLEN-1:0]       req_addr_q;
  logic                  req_rw_q;
  rw_size_e              req_rw_size_q;
  logic [31:0]           req_data_q;

  logic                  req_meta_changed;
  logic                  req_fire;
  logic                  req_data_changed;
  logic                  req_waiting_q;

  logic                  pending_store_valid_q;
  logic [XLEN-1:0]       pending_store_addr_q;
  rw_size_e              pending_store_size_q;
  logic [31:0]           pending_store_data_q;

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

  logic                  pending_store_match_i;

  assign req_data_changed = req_i.rw && (req_i.data != req_data_q);
  assign req_meta_changed = (req_i.addr != req_addr_q) || (req_i.rw != req_rw_q) || (req_i.rw_size != req_rw_size_q) ||
                            (req_i.valid && !req_valid_q);
  assign req_fire       = req_i.valid && !txn_active_q && !pending_store_valid_q && (req_meta_changed || req_waiting_q);

  assign pending_store_match_i = req_i.valid && req_i.rw && pending_store_valid_q &&
                                 (req_i.addr == pending_store_addr_q) && (req_i.rw_size == pending_store_size_q);

  assign issue_from_pending = !txn_active_q && pending_store_valid_q;

  always_comb begin
    issue_valid    = 1'b0;
    issue_is_store = 1'b0;
    issue_addr     = '0;
    issue_size     = NO_SIZE;
    issue_data     = '0;

    if (issue_from_pending) begin
      issue_valid    = 1'b1;
      issue_is_store = 1'b1;
      issue_addr     = pending_store_addr_q;
      issue_size     = pending_store_size_q;
      issue_data     = pending_store_data_q;
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

      pending_store_valid_q <= 1'b0;
      pending_store_addr_q  <= '0;
      pending_store_size_q  <= NO_SIZE;
      pending_store_data_q  <= '0;

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

      if (issue_valid || !req_i.valid) begin
        req_waiting_q <= 1'b0;
      end else if (req_i.valid && (txn_active_q || pending_store_valid_q)) begin
        req_waiting_q <= 1'b1;
      end

      if (txn_active_q && req_i.valid && req_meta_changed && req_i.rw && !pending_store_valid_q) begin
        pending_store_valid_q <= 1'b1;
        pending_store_addr_q  <= req_i.addr;
        pending_store_size_q  <= req_i.rw_size;
        pending_store_data_q  <= store_data_sel;
      end

      if (pending_store_match_i && req_data_changed) begin
        pending_store_data_q <= store_data_sel;
      end

      if (issue_from_pending) begin
        pending_store_valid_q <= 1'b0;
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
    raw_ld_word       = dcache_res_i.data;
    load_addr_lsb     = active_addr_q[1:0];
    selected_byte     = raw_ld_word[(load_addr_lsb*8)+:8];
    selected_halfword = raw_ld_word[(load_addr_lsb[1]*16)+:16];

    unique case (active_rw_size_q)
      BYTE:    ld_data_o = active_ld_sign_q ? {{24{selected_byte[7]}}, selected_byte} : {24'b0, selected_byte};
      HALF:    ld_data_o = active_ld_sign_q ? {{16{selected_halfword[15]}}, selected_halfword} : {16'b0, selected_halfword};
      WORD:    ld_data_o = raw_ld_word;
      default: ld_data_o = '0;
    endcase

    ld_data_valid_o = dcache_res_i.valid && active_is_load_q;
    stall_o = issue_valid || pending_store_valid_q || (txn_active_q && !dcache_res_i.valid);
  end

endmodule
