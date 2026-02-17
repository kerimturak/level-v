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

`ifdef CERES_OPENLANE
  localparam int BANK_WIDTH = 32;
  localparam int BANK_COUNT = (DATA_WIDTH + BANK_WIDTH - 1) / BANK_WIDTH;
  localparam int PADDED_WIDTH = BANK_COUNT * BANK_WIDTH;
  localparam int ADDR_WIDTH = $clog2(NUM_SETS);

  logic [PADDED_WIDTH-1:0] wr_data_padded;
  logic [PADDED_WIDTH-1:0] rd_data_padded;

  always_comb begin
    wr_data_padded = '0;
    wr_data_padded[DATA_WIDTH-1:0] = wr_data;
  end

  if (NUM_SETS <= 256) begin : g_macro
    for (genvar i = 0; i < BANK_COUNT; i++) begin : g_bank
      logic [31:0] dout0_bank;
      sky130_sram_1kbyte_1rw1r_32x256_8 i_sram (
          .clk0  (clk),
          .csb0  (~chip_en),
          .web0  (~wr_en),
          .wmask0(4'b1111),
          .addr0 ({{(8 - ADDR_WIDTH) {1'b0}}, addr}),
          .din0  (wr_data_padded[i*BANK_WIDTH+:BANK_WIDTH]),
          .dout0 (dout0_bank),
          .clk1  (clk),
          .csb1  (1'b1),
          .addr1 ('0),
          .dout1 ()
      );

      assign rd_data_padded[i*BANK_WIDTH+:BANK_WIDTH] = dout0_bank;
    end

    always_ff @(posedge clk) begin
      if (chip_en) begin
        if (wr_en) rd_data <= wr_data;
        else rd_data <= rd_data_padded[DATA_WIDTH-1:0];
      end
    end
  end else begin : g_fallback_large_depth
    logic [DATA_WIDTH-1:0] bram[NUM_SETS-1:0];

    always_ff @(posedge clk) begin
      if (chip_en) begin
        if (wr_en) begin
          bram[addr] <= wr_data;
          rd_data <= wr_data;
        end else begin
          rd_data <= bram[addr];
        end
      end
    end
  end
`else
  logic [DATA_WIDTH-1:0] bram[NUM_SETS-1:0];

  always_ff @(posedge clk) begin
    if (chip_en) begin
      if (wr_en) begin
        bram[addr] <= wr_data;
        rd_data    <= wr_data;
      end else begin
        rd_data <= bram[addr];
      end
    end
  end
`endif

endmodule
