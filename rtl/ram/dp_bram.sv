// True dual-port Block RAM — Xilinx UG-style TDP template (e.g. rams_tdp_rf_rf).
// One clock: both ports use the same clk (clka/clkb tied). One always_ff per port
// so Vivado can infer RAMB18/36 TDP instead of dissolving into registers.
//
// Do not read and write the same address on both ports in the same cycle; behavior
// is device-dependent. Cross-port bypass is not modeled — avoid collisions upstream.
//
// Note: On a write cycle, inferred BRAM uses write-first read on that port; Verilog
// sim of `rd <= ram[addr]` after `ram[addr] <= din` may differ — use gate-level
// or constrained tests if you need cycle-accurate write-first visibility.
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

  // Port A (posedge clka → clk)
  always_ff @(posedge clk) begin
    if (a_chip_en) begin
      if (a_wr_en)
        bram[a_addr] <= a_wr_data;
      a_rd_data <= bram[a_addr];
    end
  end

  // Port B (posedge clkb → clk)
  always_ff @(posedge clk) begin
    if (b_chip_en) begin
      if (b_wr_en)
        bram[b_addr] <= b_wr_data;
      b_rd_data <= bram[b_addr];
    end
  end

endmodule
