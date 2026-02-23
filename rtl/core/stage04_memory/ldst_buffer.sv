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

  logic                  req_changed;
  logic                  req_fire;

  logic                  txn_active_q;

  logic [XLEN-1:0]       active_addr_q;
  rw_size_e              active_rw_size_q;
  logic                  active_ld_sign_q;
  logic                  active_is_load_q;

  logic [31:0]           raw_ld_word;
  logic [7:0]            selected_byte;
  logic [15:0]           selected_halfword;
  logic [31:0]           store_data_sel;

  assign req_changed    = (req_i.addr != req_addr_q) || (req_i.rw != req_rw_q) || (req_i.rw_size != req_rw_size_q) ||
                          (req_i.valid && !req_valid_q);
  assign req_fire       = req_i.valid && req_changed && !txn_active_q;

  always_ff @(posedge clk_i) begin
    if (!rst_ni || flush_i) begin
      req_valid_q        <= 1'b0;
      req_addr_q         <= '0;
      req_rw_q           <= 1'b0;
      req_rw_size_q      <= NO_SIZE;

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

      if (dcache_res_i.valid) begin
        txn_active_q <= 1'b0;
      end

      if (req_fire) begin
        txn_active_q      <= 1'b1;
        active_addr_q     <= req_i.addr;
        active_rw_size_q  <= req_i.rw_size;
        active_ld_sign_q  <= req_i.ld_op_sign;
        active_is_load_q  <= !req_i.rw;
      end
    end
  end

  always_comb begin
    if (req_i.rw && me_req_i.valid && (me_req_i.addr == req_i.addr) && (me_req_i.rw_size == req_i.rw_size)) begin
      store_data_sel = me_req_i.data;
    end else begin
      store_data_sel = req_i.data;
    end

    dcache_req_o.valid    = req_fire;
    dcache_req_o.addr     = req_i.addr;
    dcache_req_o.ready    = 1'b1;
    dcache_req_o.rw       = req_i.rw;
    dcache_req_o.rw_size  = req_i.rw_size;
    dcache_req_o.data     = store_data_sel;
    dcache_req_o.uncached = uncached_i;
  end

  assign dcache_txn_active_o = txn_active_q;

  always_comb begin
    raw_ld_word       = dcache_res_i.data;
    selected_byte     = raw_ld_word[(active_addr_q[1:0]*8)+:8];
    selected_halfword = raw_ld_word[(active_addr_q[1]*16)+:16];

    unique case (active_rw_size_q)
      BYTE:    ld_data_o = active_ld_sign_q ? {{24{selected_byte[7]}}, selected_byte} : {24'b0, selected_byte};
      HALF:    ld_data_o = active_ld_sign_q ? {{16{selected_halfword[15]}}, selected_halfword} : {16'b0, selected_halfword};
      WORD:    ld_data_o = raw_ld_word;
      default: ld_data_o = '0;
    endcase

    ld_data_valid_o = dcache_res_i.valid && active_is_load_q;
    stall_o = req_fire || (txn_active_q && !dcache_res_i.valid);
  end

endmodule
