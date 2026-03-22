/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
Next-Line Prefetcher
================================================================================
On a new demand miss (cached region), arms prefetch of the following cache line.
Issues the prefetch only after the demand miss clears so the single lowX port
stays well-defined.

States: IDLE → WAIT_MISS_END (miss active) → REQ (prefetch_valid until ack)
================================================================================
*/
`timescale 1ns / 1ps

module next_line_prefetcher
  import level_param::*;
#(
    parameter int XLEN     = level_param::XLEN,
    parameter int BLK_SIZE = level_param::BLK_SIZE
) (
    input  logic            clk_i,
    input  logic            rst_ni,
    input  logic            flush_i,
    input  logic            cache_miss_i,
    input  logic            miss_uncached_i,
    input  logic [XLEN-1:0] miss_addr_i,
    input  logic            prefetch_ack_i,
    output logic            prefetch_valid_o,
    output logic [XLEN-1:0] prefetch_addr_o
);

  localparam int LINE_BYTES = BLK_SIZE / 8;
  localparam int OFFSET_BITS = $clog2(LINE_BYTES);

  typedef enum logic [1:0] {
    ST_IDLE,
    ST_WAIT_MISS_END,
    ST_REQ
  } state_e;

  state_e state_q, state_d;

  logic [XLEN-1:0] pf_line_q;
  logic [XLEN-1:0] last_miss_line_q;

  logic [XLEN-1:0] miss_line;
  assign miss_line = {miss_addr_i[XLEN-1:OFFSET_BITS], {OFFSET_BITS{1'b0}}};

  logic [XLEN-1:0] next_line_addr;
  assign next_line_addr = miss_line + XLEN'(unsigned'(LINE_BYTES));

  logic is_new_miss_line;
  assign is_new_miss_line = (miss_line != last_miss_line_q);

  assign prefetch_addr_o  = pf_line_q;
  assign prefetch_valid_o = (state_q == ST_REQ);

  always_comb begin
    state_d = state_q;
    case (state_q)
      ST_IDLE: begin
        if (flush_i) state_d = ST_IDLE;
        else if (cache_miss_i && !miss_uncached_i && is_new_miss_line) state_d = ST_WAIT_MISS_END;
      end
      ST_WAIT_MISS_END: begin
        if (flush_i) state_d = ST_IDLE;
        else if (!cache_miss_i) state_d = ST_REQ;
      end
      ST_REQ: begin
        if (flush_i) state_d = ST_IDLE;
        else if (prefetch_ack_i) state_d = ST_IDLE;
      end
      default: state_d = ST_IDLE;
    endcase
  end

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      state_q          <= ST_IDLE;
      pf_line_q        <= '0;
      last_miss_line_q <= '0;
    end else if (flush_i) begin
      state_q <= ST_IDLE;
    end else begin
      state_q <= state_d;

      if (state_q == ST_IDLE && cache_miss_i && !miss_uncached_i && is_new_miss_line) begin
        pf_line_q        <= next_line_addr;
        last_miss_line_q <= miss_line;
      end
    end
  end

`ifndef SYNTHESIS
  assert property (@(posedge clk_i) disable iff (!rst_ni) prefetch_valid_o |-> (prefetch_addr_o[OFFSET_BITS-1:0] == '0))
  else $error("Prefetch address not cache-line aligned!");
`endif

endmodule
