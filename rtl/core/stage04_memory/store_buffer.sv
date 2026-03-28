`timescale 1ns / 1ps
`include "level_defines.svh"

module store_buffer
  import level_param::*;
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
  // Merge pending stores that target the same 32-bit word as the load,
  // youngest-to-oldest (tail side first): each byte comes from the newest
  // store that still occupies the buffer and writes that byte.
  //
  // Stale head->tail scan + false "has_conflict" from a younger byte/half
  // store could cancel an older word forward and break CoreMark under
  // pressure (small D$ / more SB occupancy).
  //
  // conflict: the load needs byte(s) this merge does not cover, but some
  // pending store touches the word — we cannot supply the full value from
  // SB alone and do not merge SB partial + dcache; stall until drains.
  // -------------------------------------------------------------------
  always_comb begin
    logic [3:0] need_m, covered_m, wr_mask;
    logic [31:0] merged;
    logic        word_pending;
    int          j, i, bi;

    fwd_hit_o      = 1'b0;
    fwd_conflict_o = 1'b0;
    fwd_data_o     = '0;

    need_m = '0;
    unique case (fwd_size_i)
      BYTE: need_m = 4'b1 << fwd_addr_i[1:0];
      HALF: need_m = fwd_addr_i[1] ? 4'b1100 : 4'b0011;
      WORD: need_m = 4'b1111;
      default: need_m = '0;
    endcase

    covered_m    = '0;
    merged       = '0;
    word_pending = 1'b0;

    for (j = 0; j < DEPTH; j++) begin
      logic [PTR_W-1:0] idx;

      i   = DEPTH - 1 - j;
      idx = PTR_W'(head_ptr[PTR_W-1:0] + i[PTR_W-1:0]);

      if (!buf_valid[idx] || buf_addr[idx][31:2] != fwd_addr_i[31:2]) begin
      end else begin
        word_pending = 1'b1;

        unique case (buf_size[idx])
          WORD: wr_mask = 4'b1111;
          HALF: wr_mask = buf_addr[idx][1] ? 4'b1100 : 4'b0011;
          BYTE: wr_mask = 4'b1 << buf_addr[idx][1:0];
          default: wr_mask = '0;
        endcase

        for (bi = 0; bi < 4; bi++) begin
          if (wr_mask[bi] && !covered_m[bi]) begin
            unique case (buf_size[idx])
              WORD: merged[bi*8+:8] = buf_data[idx][bi*8+:8];
              HALF: begin
                if (!buf_addr[idx][1]) begin
                  unique case (bi)
                    0: merged[7:0]   = buf_data[idx][7:0];
                    1: merged[15:8]  = buf_data[idx][15:8];
                    default: ;
                  endcase
                end else begin
                  unique case (bi)
                    2: merged[23:16] = buf_data[idx][7:0];
                    3: merged[31:24] = buf_data[idx][15:8];
                    default: ;
                  endcase
                end
              end
              BYTE: merged[bi*8+:8] = buf_data[idx][7:0];
              default: ;
            endcase
            covered_m[bi] = 1'b1;
          end
        end
      end
    end

    if (|need_m && ((covered_m & need_m) == need_m)) begin
      fwd_hit_o  = 1'b1;
      fwd_data_o = merged;
    end else if (|need_m && word_pending && ((covered_m & need_m) != need_m)) begin
      fwd_conflict_o = 1'b1;
    end
  end

endmodule
