/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"
module pma
  import ceres_param::*;
(
    input logic [XLEN-1:0] addr_i,
    output logic uncached_o,
    output logic memregion_o,
    output logic grand_o
);

  typedef struct packed {
    logic [XLEN-1:0] addr;
    logic [XLEN-1:0] mask;
    logic uncached;
    logic memregion;
    logic x;
    logic w;
    logic r;
  } pma_t;

  logic [2:0] region_match;

  localparam pma_t [2:0] pma_map = '{
      '{addr : 32'h8000_0000, mask: 32'h000F_FFFF, uncached: 1'b0, memregion: 1'b1, x : 1'b1, w : 1'b1, r : 1'b1},  // Memregion
      '{addr : 32'h2000_0000, mask: 32'h0000_000F, uncached: 1'b0, memregion: 1'b0, x : 1'b0, w : 1'b1, r : 1'b1},  // Uart
      '{addr : 32'h3000_0000, mask: 32'h0000_0007, uncached: 1'b1, memregion: 1'b1, x : 1'b0, w : 1'b0, r : 1'b1}  // Timer
  };

  for (genvar i = 0; i < 3; i++) begin
    assign region_match[i] = pma_map[i].addr == (addr_i & ~pma_map[i].mask);
  end

  always_comb begin
    memregion_o = '0;
    uncached_o  = '0;
    grand_o     = '0;
    if (region_match[0]) begin
      uncached_o  = pma_map[0].uncached;
      memregion_o = pma_map[0].memregion;
      grand_o     = pma_map[0].x;
    end else if (region_match[1]) begin
      uncached_o  = pma_map[1].uncached;
      memregion_o = pma_map[1].memregion;
      grand_o     = pma_map[1].x;
    end else if (region_match[2]) begin
      uncached_o  = pma_map[2].uncached;
      memregion_o = pma_map[2].memregion;
      grand_o     = pma_map[2].x;
    end

  end

endmodule
