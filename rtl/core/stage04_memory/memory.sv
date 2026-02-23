// ============================================================================
// Memory Stage — top-level wrapper
// ============================================================================
// Instantiates the separate ldst_buffer module and the D-cache, wiring them
// together with PMA and the load-data size/sign extension path.
// ============================================================================
`timescale 1ns / 1ps
`include "ceres_defines.svh"

module memory
  import ceres_param::*;
(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  stall_e                stall_i,
    input  logic                  fe_flush_cache_i,
    input  dlowX_res_t            lx_dres_i,
    output dlowX_req_t            lx_dreq_o,
    output logic       [XLEN-1:0] me_data_o,
    output logic                  dmiss_stall_o,
    output logic                  fencei_stall_o,    // Dcache dirty writeback stall for fence.i
    // MEM stage view (pipe3) — kept for interface compatibility
    input  data_req_t             me_data_req_i,
    // EX stage view (pipe2)
    input  data_req_t             ex_data_req_i
);

  // -------------------------------------------------------------------------
  // Internal wires
  // -------------------------------------------------------------------------
  dcache_req_t dcache_req;
  dcache_res_t dcache_res;
  logic        uncached;

  // -------------------------------------------------------------------------
  // PMA — determine if address is uncacheable
  // -------------------------------------------------------------------------
  pma i_dpma (
      .addr_i     (ex_data_req_i.addr),
      .uncached_o (uncached),
      .memregion_o(),                    // Not used
      .grand_o    ()                     // Not used
  );

  // -------------------------------------------------------------------------
  // Load / Store Buffer  (store merging + store-to-load forwarding)
  // -------------------------------------------------------------------------
  ldst_buffer #(
      .DEPTH(4)
  ) i_ldst_buffer (
      .clk_i  (clk_i),
      .rst_ni (rst_ni),
      .flush_i(fe_flush_cache_i),

      // Pipeline side
      .req_i  (ex_data_req_i),
      .me_req_i(me_data_req_i),
      .stall_o(dmiss_stall_o),

      // D-cache side
      .dcache_req_o       (dcache_req),
      .dcache_res_i       (dcache_res),
      .dcache_txn_active_o(),            // informational

      // Load data result
      .ld_data_o      (me_data_o),
      .ld_data_valid_o(),           // stall_o covers this

      // PMA
      .uncached_i(uncached)
  );

  // -------------------------------------------------------------------------
  // D-cache
  // -------------------------------------------------------------------------
  dcache #(
      .cache_req_t(dcache_req_t),
      .cache_res_t(dcache_res_t),
      .lowX_req_t (dlowX_req_t),
      .lowX_res_t (dlowX_res_t),
      .CACHE_SIZE (DC_CAPACITY),
      .BLK_SIZE   (BLK_SIZE),
      .XLEN       (XLEN),
      .NUM_WAY    (DC_WAY)
  ) i_dcache (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .flush_i       (fe_flush_cache_i),
      .cache_req_i   (dcache_req),
      .cache_res_o   (dcache_res),
      .lowX_res_i    (lx_dres_i),
      .lowX_req_o    (lx_dreq_o),
      .fencei_stall_o(fencei_stall_o)
  );

  // -------------------------------------------------------------------------
  // Cache Logger (optional)
  // -------------------------------------------------------------------------
  cache_logger i_cache_logger (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .cache_req_i(dcache_req),
      .cache_res_i(dcache_res)
  );

endmodule
