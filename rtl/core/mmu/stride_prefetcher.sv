/*
 * Stride Data Prefetcher for L1 D-Cache
 *
 * Architecture:
 *   Observes committed load PCs and their effective addresses.
 *   Maintains a Reference Prediction Table (RPT) indexed by load PC.
 *   When a stable stride is detected (confidence ≥ threshold),
 *   issues prefetch requests to the dcache LD port.
 *
 *   Prefetch requests are regular cached reads — on hit they are
 *   no-ops (data already present), on miss they trigger a fill that
 *   warms the cache for the upcoming demand access.
 *
 *   Integrates into memory.sv: observes ex_data_req, issues requests
 *   to dcache LD port when idle and no demand load is pending.
 */
`timescale 1ns / 1ps
`include "level_defines.svh"

module stride_prefetcher
  import level_param::*;
#(
    parameter int RPT_SIZE  = STRIDE_TABLE_SIZE,  // 64 entries
    parameter int STRIDE_W  = STRIDE_BITS,        // 12-bit signed stride
    parameter int CONF_MAX  = 3,                  // 2-bit saturating counter max
    parameter int PF_DEGREE = 4                   // prefetch N strides ahead (4 → next cache line for word stride)
) (
    input logic clk_i,
    input logic rst_ni,
    input logic flush_i,

    // Observation port — from pipeline load in EX/MEM stage
    input logic        train_valid_i,  // a load committed (valid && !rw)
    input logic [31:0] train_pc_i,     // load instruction PC
    input logic [31:0] train_addr_i,   // load effective address

    // Prefetch issue port — to dcache LD port
    input  logic        pf_ready_i,  // dcache LD port is idle & can accept
    output logic        pf_valid_o,  // prefetch request valid
    output logic [31:0] pf_addr_o    // prefetch address (line-aligned)
);

  // =========================================================================
  // Local parameters
  // =========================================================================
  localparam int RPT_IDX_W = $clog2(RPT_SIZE);
  localparam int CONF_W = $clog2(CONF_MAX + 1);
  localparam int LINE_BYTES = BLK_SIZE / 8;  // 16 bytes
  localparam int LINE_OFF = $clog2(LINE_BYTES);  // 4 bits

  // =========================================================================
  // RPT entry
  // =========================================================================
  typedef struct packed {
    logic                       valid;
    logic [31:0]                tag;        // full PC for disambiguation
    logic [31:0]                last_addr;  // last observed address
    logic signed [STRIDE_W-1:0] stride;     // detected stride
    logic [CONF_W-1:0]          conf;       // confidence counter
  } rpt_entry_t;

  rpt_entry_t                 rpt       [RPT_SIZE];

  // =========================================================================
  // Index into RPT by hashing load PC
  // =========================================================================
  logic       [RPT_IDX_W-1:0] train_idx;
  assign train_idx = train_pc_i[RPT_IDX_W+1:2];  // skip bit[1:0] (compressed alignment)

  // =========================================================================
  // Training logic
  // =========================================================================
  rpt_entry_t entry_r;
  assign entry_r = rpt[train_idx];

  logic signed [STRIDE_W-1:0] new_stride;
  assign new_stride = STRIDE_W'(signed'(train_addr_i) - signed'(entry_r.last_addr));

  logic tag_match;
  assign tag_match = entry_r.valid && (entry_r.tag == train_pc_i);

  logic stride_match;
  assign stride_match = tag_match && (new_stride == entry_r.stride);

  // =========================================================================
  // Prefetch candidate (registered for timing)
  // =========================================================================
  logic        pf_pending_q;
  logic [31:0] pf_addr_q;

  // Generate prefetch when confidence is high, stride is non-zero, and target is a different line
  logic        pf_trigger;
  assign pf_trigger = train_valid_i && tag_match && stride_match && (entry_r.conf >= CONF_W'(CONF_MAX - 1)) && (entry_r.stride != '0) && pf_cross_line;

  // Prefetch target: PF_DEGREE strides ahead, line-aligned
  logic [31:0] pf_target;
  assign pf_target = {(train_addr_i + 32'(signed'(entry_r.stride)) * PF_DEGREE) >> LINE_OFF, {LINE_OFF{1'b0}}};

  // Skip prefetch if target is in the same cache line (no benefit)
  logic pf_cross_line;
  assign pf_cross_line = (pf_target[31:LINE_OFF] != train_addr_i[31:LINE_OFF]);

  // =========================================================================
  // Debug counters (inside functional always_ff — cannot be DCE'd)
  // =========================================================================
  int unsigned dbg_cyc, dbg_train_cnt, dbg_pf_issued, dbg_pf_filtered;

  // =========================================================================
  // RPT update
  // =========================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni || flush_i) begin
      for (int i = 0; i < RPT_SIZE; i++) rpt[i].valid <= 1'b0;
      pf_pending_q    <= 1'b0;
      pf_addr_q       <= '0;
      dbg_cyc         <= 0;
      dbg_train_cnt   <= 0;
      dbg_pf_issued   <= 0;
      dbg_pf_filtered <= 0;
    end else begin
      dbg_cyc <= dbg_cyc + 1;

      // --- Prefetch issue tracking ---
      if (pf_pending_q && pf_ready_i) begin
        pf_pending_q  <= 1'b0;
        dbg_pf_issued <= dbg_pf_issued + 1;
      end

      // --- Training ---
      if (train_valid_i) begin
        dbg_train_cnt <= dbg_train_cnt + 1;
        if (!entry_r.valid || !tag_match) begin
          // Allocate / replace entry
          rpt[train_idx].valid     <= 1'b1;
          rpt[train_idx].tag       <= train_pc_i;
          rpt[train_idx].last_addr <= train_addr_i;
          rpt[train_idx].stride    <= '0;
          rpt[train_idx].conf      <= '0;
        end else begin
          // Tag matches — update stride and confidence
          rpt[train_idx].last_addr <= train_addr_i;

          if (new_stride == entry_r.stride) begin
            // Stride confirmed — increment confidence
            if (entry_r.conf < CONF_W'(CONF_MAX)) rpt[train_idx].conf <= entry_r.conf + 1'b1;
          end else begin
            // Stride changed — update stride, reset confidence
            rpt[train_idx].stride <= new_stride;
            rpt[train_idx].conf   <= '0;
          end
        end

        // --- Prefetch generation ---
        if (pf_trigger) begin
          pf_pending_q <= 1'b1;
          pf_addr_q    <= pf_target;
        end

        // Count same-line suppressed triggers (stride match + conf ok but same line)
        if (train_valid_i && tag_match && stride_match && (entry_r.conf >= CONF_W'(CONF_MAX - 1)) && (entry_r.stride != '0) && !pf_cross_line) dbg_pf_filtered <= dbg_pf_filtered + 1;
      end
    end
  end

  // =========================================================================
  // Output
  // =========================================================================
  assign pf_valid_o = pf_pending_q;
  assign pf_addr_o  = pf_addr_q;

  // Simulation-only summary
  final begin
    $display("[STRIDE_PF] cyc=%0d trains=%0d pf_issued=%0d same_line_filtered=%0d", dbg_cyc, dbg_train_cnt, dbg_pf_issued, dbg_pf_filtered);
  end

endmodule
