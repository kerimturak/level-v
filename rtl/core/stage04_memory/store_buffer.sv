`timescale 1ns / 1ps
`include "ceres_defines.svh"

module store_buffer
  import ceres_param::*;
#(
    parameter int DEPTH = SB_DEPTH
) (
    input  logic            clk_i,
    input  logic            rst_ni,

    // Store write port (from EX stage)
    input  logic            wr_valid_i,
    input  logic [XLEN-1:0] wr_addr_i,
    input  logic [XLEN-1:0] wr_data_i,
    input  rw_size_e        wr_size_i,
    input  logic            wr_uncached_i,

    // Load forwarding check (combinational)
    input  logic [XLEN-1:0] fwd_addr_i,
    input  rw_size_e        fwd_size_i,
    output logic            fwd_hit_o,
    output logic [XLEN-1:0] fwd_data_o,
    output logic            fwd_conflict_o,

    // Drain port (to dcache via memory module)
    output logic            drain_valid_o,
    output logic [XLEN-1:0] drain_addr_o,
    output logic [XLEN-1:0] drain_data_o,
    output rw_size_e        drain_size_o,
    output logic            drain_uncached_o,
    input  logic            drain_ack_i,

    // Status
    output logic            full_o,
    output logic            empty_o
);

  localparam int PTR_W = $clog2(DEPTH);

  logic [XLEN-1:0] buf_addr  [DEPTH];
  logic [XLEN-1:0] buf_data  [DEPTH];
  rw_size_e        buf_size  [DEPTH];
  logic            buf_uncached [DEPTH];
  logic [DEPTH-1:0] buf_valid;

  logic [PTR_W:0] head_ptr, tail_ptr;

  assign empty_o = (head_ptr == tail_ptr);
  assign full_o  = (head_ptr[PTR_W-1:0] == tail_ptr[PTR_W-1:0]) &&
                   (head_ptr[PTR_W] != tail_ptr[PTR_W]);

  // -------------------------------------------------------------------
  // Drain port: present oldest entry
  // -------------------------------------------------------------------
  logic [PTR_W-1:0] head_idx;
  assign head_idx = head_ptr[PTR_W-1:0];

  assign drain_valid_o    = !empty_o;
  assign drain_addr_o     = buf_addr[head_idx];
  assign drain_data_o     = buf_data[head_idx];
  assign drain_size_o     = buf_size[head_idx];
  assign drain_uncached_o = buf_uncached[head_idx];

  // -------------------------------------------------------------------
  // FIFO write / drain
  // -------------------------------------------------------------------
  logic [PTR_W-1:0] tail_idx;
  assign tail_idx = tail_ptr[PTR_W-1:0];

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      head_ptr  <= '0;
      tail_ptr  <= '0;
      buf_valid <= '0;
    end else begin
      if (drain_ack_i && !empty_o) begin
        buf_valid[head_idx] <= 1'b0;
        head_ptr <= head_ptr + 1'b1;
      end

      if (wr_valid_i && !full_o) begin
        buf_valid[tail_idx]    <= 1'b1;
        buf_addr[tail_idx]     <= wr_addr_i;
        buf_data[tail_idx]     <= wr_data_i;
        buf_size[tail_idx]     <= wr_size_i;
        buf_uncached[tail_idx] <= wr_uncached_i;
        tail_ptr <= tail_ptr + 1'b1;
      end
    end
  end

  // -------------------------------------------------------------------
  // Store-to-load forwarding with conflict detection
  //
  // WORD stores use word-aligned matching (addr[31:2]) and can forward
  // to any load within the same word. HALF/BYTE stores require exact
  // address match and the store size must cover the load size.
  //
  // A conflict is flagged when a store overlaps the load's word but
  // cannot provide the needed data. The memory module must stall and
  // wait for the conflicting entry to drain before issuing the load.
  //
  // Newest match wins (scan head→tail, later iterations overwrite).
  // -------------------------------------------------------------------
  always_comb begin
    fwd_hit_o      = 1'b0;
    fwd_data_o     = '0;
    fwd_conflict_o = 1'b0;

    for (int i = 0; i < DEPTH; i++) begin
      logic [PTR_W-1:0] idx;
      logic word_match, exact_match, can_fwd, has_conflict;

      idx = PTR_W'(head_ptr[PTR_W-1:0] + i[PTR_W-1:0]);

      word_match  = buf_valid[idx] && (buf_addr[idx][31:2] == fwd_addr_i[31:2]);
      exact_match = buf_valid[idx] && (buf_addr[idx] == fwd_addr_i);

      can_fwd = (buf_size[idx] == WORD && word_match) ||
                (buf_size[idx] != WORD && exact_match && buf_size[idx] >= fwd_size_i);

      has_conflict = word_match && !can_fwd;

      if (can_fwd) begin
        fwd_hit_o      = 1'b1;
        fwd_conflict_o = 1'b0;
        if (buf_size[idx] == WORD)
          fwd_data_o = buf_data[idx];
        else
          fwd_data_o = buf_data[idx] << (buf_addr[idx][1:0] * 8);
      end else if (has_conflict) begin
        fwd_conflict_o = 1'b1;
        fwd_hit_o      = 1'b0;
        fwd_data_o     = '0;
      end
    end
  end

endmodule
