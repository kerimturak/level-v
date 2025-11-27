/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
module ceres_wrapper
  import ceres_param::*;
(
    input  logic clk_i,
    input  logic rst_ni,
    input  logic program_rx_i,
    output logic prog_mode_led_o,
    output logic uart_tx_o,
    input  logic uart_rx_i
);

  // 50 MHz clocking wizard ip
  //logic locked;
  logic clk_o;
  //clk_wiz_0 dutclk (
  //  .clk_out1 (clk_o    ),
  //  .clk_in1  (clk_i    ),
  //  .reset    (!rst_ni  ),
  //  .locked   (locked   )
  //);

  assign clk_o = clk_i;


  localparam WRAP_BLOCK_SIZE = 128;
  localparam WRAP_NUMS_BYTE = WRAP_BLOCK_SIZE / 8;
  localparam BYTE_OFFSET = $clog2(WRAP_NUMS_BYTE);
  localparam RAM_DELAY = 16;
  parameter integer MEM_WORDS = 4096;
  parameter [31:0] PROGADDR_RESET = 32'h8000_0000;
  parameter [31:0] STACKADDR = PROGADDR_RESET + (4 * MEM_WORDS);
  parameter [31:0] PROGADDR_IRQ = 32'h0000_0000;
  parameter [31:0] UART_BASE_ADDR = 32'h2000_0000;
  parameter [31:0] UART_MASK_ADDR = 32'h0000_000f;
  parameter [31:0] SPI_BASE_ADDR = 32'h2001_0000;
  parameter [31:0] SPI_MASK_ADDR = 32'h0000_00ff;
  parameter [31:0] RAM_BASE_ADDR = 32'h8000_0000;
  parameter [31:0] RAM_MASK_ADDR = 32'h000f_ffff;
  parameter [31:0] CHIP_IO_BASE_ADDR = SPI_BASE_ADDR + SPI_MASK_ADDR;
  parameter [31:0] CHIP_IO_MASK_ADDR = RAM_BASE_ADDR + RAM_MASK_ADDR;
  parameter RAM_DEPTH = 8 * 1024;  //131072; // 32 kb

  iomem_req_t                         iomem_req;
  iomem_res_t                         iomem_res;
  logic       [  WRAP_BLOCK_SIZE-1:0] ram_rdata;
  logic       [  WRAP_NUMS_BYTE -1:0] ram_wr_en;
  logic                               ram_rd_en;
  logic                               req_waited_q;
  logic       [                 63:0] timer;
  logic                               prog_system_reset;
  logic                               rst_n;
  logic       [$clog2(RAM_DEPTH)-1:0] idx;
  logic       [        RAM_DELAY-1:0] ram_shift_q;
  logic                               req_responsed;
  logic                               req_waited;

  cpu soc (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .iomem_req_o(iomem_req),
      .iomem_res_i(iomem_res),
      .uart_tx_o  (uart_tx_o),
      .uart_rx_i  (uart_rx_i)
  );

  wrapper_ram #(
      .NB_COL          (WRAP_NUMS_BYTE),
      .COL_WIDTH       (8),
      .RAM_DEPTH       (RAM_DEPTH),
      .CPU_CLK         (CPU_CLK),
      .PROG_BAUD_RATE  (PROG_BAUD_RATE),
      .PROGRAM_SEQUENCE(PROGRAM_SEQUENCE)
  ) main_memory (
      .clk_i          (clk_o),
      .rst_ni         (rst_ni),
      .wr_addr        (idx),
      .rd_addr        (idx),
      .wr_data        (iomem_req.data),
      .wr_en          (ram_wr_en),
      .rd_data        (ram_rdata),
      .rd_en          (ram_rd_en),
      .ram_prog_rx_i  (program_rx_i),
      .system_reset_o (prog_system_reset),
      .prog_mode_led_o(prog_mode_led_o)
  );

  always_comb begin
    rst_n = prog_system_reset & rst_ni;

    iomem_res.valid = ram_shift_q[RAM_DELAY-1] | (iomem_req.valid & (iomem_req.addr == 32'h3000_0000 || iomem_req.addr == 32'h3000_0004));
    iomem_res.ready = 1'b1;
    iomem_res.data = (iomem_req.valid & ((iomem_req.addr & 32'hFFFF_FFFF << 4) == 32'h3000_0000)) ? ({64'b0, timer} >> iomem_req.addr[3:2] * 32) : ram_rdata;

    idx = iomem_req.addr[$clog2(RAM_DEPTH*WRAP_NUMS_BYTE)-1:BYTE_OFFSET];
    req_responsed = iomem_req.valid & iomem_res.valid & ((iomem_req.addr & ~RAM_MASK_ADDR) == RAM_BASE_ADDR);
    req_waited = iomem_req.valid & !iomem_res.valid & ((iomem_req.addr & ~RAM_MASK_ADDR) == RAM_BASE_ADDR);
    ram_wr_en = iomem_req.valid & ((iomem_req.addr & ~RAM_MASK_ADDR) == RAM_BASE_ADDR) ? iomem_req.rw : {WRAP_NUMS_BYTE{1'b0}};
    ram_rd_en = iomem_req.valid & ((iomem_req.addr & ~RAM_MASK_ADDR) == RAM_BASE_ADDR) & ~(|iomem_req.rw);
  end

  always_ff @(posedge clk_o) begin
    if (!rst_ni) begin
      ram_shift_q <= '0;
    end else begin
      if (req_responsed) ram_shift_q <= '0;
      else ram_shift_q <= {ram_shift_q[RAM_DELAY-2:0], req_waited_q};
    end

    if (!rst_n) begin
      req_waited_q <= 1'b0;
      timer <= 64'h0;
    end else begin
      req_waited_q <= req_waited;
      timer <= timer + 64'h1;
    end
  end

endmodule
