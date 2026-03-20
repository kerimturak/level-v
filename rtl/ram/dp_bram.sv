// Dual-Port Block RAM Write-First Mode
// Port A and Port B can independently read/write to different addresses.
// Same-address simultaneous write from both ports is undefined behavior.
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

  logic [DATA_WIDTH-1:0] bram [NUM_SETS-1:0];

  always_ff @(posedge clk) begin
    if (a_chip_en) begin
      if (a_wr_en) begin
        bram[a_addr] <= a_wr_data;
        a_rd_data    <= a_wr_data;
      end else begin
        a_rd_data <= bram[a_addr];
      end
    end
  end

  always_ff @(posedge clk) begin
    if (b_chip_en) begin
      if (b_wr_en) begin
        bram[b_addr] <= b_wr_data;
        b_rd_data    <= b_wr_data;
      end else begin
        b_rd_data <= bram[b_addr];
      end
    end
  end

endmodule
