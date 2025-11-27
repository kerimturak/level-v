// Single-Port Block RAM Write-First Mode (recommended template)
// https://docs.xilinx.com/r/en-US/ug901-vivado-synthesis/Creating-Pipeline-Example-1-8K-x-72
`timescale 1ns / 1ps
module sp_bram #(
    parameter DATA_WIDTH = 32,   // Veri genişliği
    parameter NUM_SETS   = 1024  // Set sayısı
) (
    input  logic                        clk,      // Clock sinyali
    input  logic                        chip_en,
    input  logic [$clog2(NUM_SETS)-1:0] addr,     // Adres sinyali
    input  logic                        wr_en,    // Yazma işlemi enable sinyali
    input  logic [      DATA_WIDTH-1:0] wr_data,  // Yazılacak veri
    output logic [      DATA_WIDTH-1:0] rd_data   // Okunan veri
);

  logic [DATA_WIDTH-1:0] bram[NUM_SETS-1:0];

  always @(posedge clk) begin
    if (chip_en) begin
      if (wr_en) begin
        bram[addr] <= wr_data;
        rd_data    <= wr_data;
      end else begin
        rd_data <= bram[addr];
      end
    end
  end

endmodule
