// Dual-Port Block RAM — single scheduled block for deterministic cross-port behavior.
// Two independent always_ff blocks leave same-addr Rd/Wr or Wr/Rd on the same cycle
// simulation-order dependent; L2 (I-port fill vs D-port tag/data read) can then diverge
// under pressure (e.g. small L1 + CoreMark).
`timescale 1ns / 1ps
module dp_bram #(
    parameter DATA_WIDTH = 32,
    parameter NUM_SETS   = 1024
) (
    input  logic                        clk,
    // Port A
    input  logic                        a_chip_en,
    input  logic [$clog2(NUM_SETS)-1:0] a_addr,
    input  logic                        a_wr_en,
    input  logic [DATA_WIDTH-1:0]       a_wr_data,
    output logic [DATA_WIDTH-1:0]       a_rd_data,
    // Port B
    input  logic                        b_chip_en,
    input  logic [$clog2(NUM_SETS)-1:0] b_addr,
    input  logic                        b_wr_en,
    input  logic [DATA_WIDTH-1:0]       b_wr_data,
    output logic [DATA_WIDTH-1:0]       b_rd_data
);

  logic [DATA_WIDTH-1:0] bram[NUM_SETS-1:0];

  always_ff @(posedge clk) begin
    if (a_chip_en && a_wr_en)
      bram[a_addr] <= a_wr_data;
    if (b_chip_en && b_wr_en) begin
      // If both write same address same cycle, both receive write-first rd_data below;
      // BRAM last write wins (B after A here). Avoid in upstream RTL.
      bram[b_addr] <= b_wr_data;
    end

    if (a_chip_en) begin
      if (a_wr_en)
        a_rd_data <= a_wr_data;
      else if (b_chip_en && b_wr_en && b_addr == a_addr)
        a_rd_data <= b_wr_data;
      else
        a_rd_data <= bram[a_addr];
    end

    if (b_chip_en) begin
      if (b_wr_en)
        b_rd_data <= b_wr_data;
      else if (a_chip_en && a_wr_en && a_addr == b_addr)
        b_rd_data <= a_wr_data;
      else
        b_rd_data <= bram[b_addr];
    end
  end

endmodule
