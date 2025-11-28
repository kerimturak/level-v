/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  Top-level wrapper using word-based RAM with burst support.
  This version uses 32-bit word memory organization, supporting
  standard .mem file formats while still providing cache-line
  width data transfers.
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

  logic clk_o;
  assign clk_o = clk_i;

  // Memory parameters - 32-bit word based
  localparam WORD_WIDTH       = 32;                        // 32-bit words
  localparam CACHE_LINE_WIDTH = BLK_SIZE;                  // From ceres_param (128-bit)
  localparam WORDS_PER_LINE   = CACHE_LINE_WIDTH / WORD_WIDTH;  // 4 words per cache line
  localparam RAM_DEPTH        = 32 * 1024;                 // 32K words = 128KB
  localparam BYTE_OFFSET      = $clog2(WORD_WIDTH / 8);    // 2 bits for word offset
  localparam LINE_OFFSET      = $clog2(WORDS_PER_LINE);    // 2 bits for word-in-line
  localparam RAM_DELAY        = 16;

  // Address parameters
  parameter [31:0] RAM_BASE_ADDR  = 32'h8000_0000;
  parameter [31:0] RAM_MASK_ADDR  = 32'h000f_ffff;
  parameter [31:0] TIMER_BASE     = 32'h3000_0000;

  // Internal signals
  iomem_req_t                         iomem_req;
  iomem_res_t                         iomem_res;
  logic [CACHE_LINE_WIDTH-1:0]        ram_rdata;
  logic [CACHE_LINE_WIDTH/8-1:0]      ram_wstrb;
  logic                               ram_rd_en;
  logic                               req_waited_q;
  logic [63:0]                        timer;
  logic                               prog_system_reset;
  logic                               rst_n;
  logic [$clog2(RAM_DEPTH)-1:0]       word_addr;
  logic [RAM_DELAY-1:0]               ram_shift_q;
  logic                               req_responsed;
  logic                               req_waited;
  logic                               is_ram_access;
  logic                               is_timer_access;

  // CPU instance
  cpu soc (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .iomem_req_o(iomem_req),
      .iomem_res_i(iomem_res),
      .uart_tx_o  (uart_tx_o),
      .uart_rx_i  (uart_rx_i)
  );

  // Word-based RAM with burst support
  wrapper_ram #(
      .WORD_WIDTH      (WORD_WIDTH),
      .RAM_DEPTH       (RAM_DEPTH),
      .CACHE_LINE_WIDTH(CACHE_LINE_WIDTH),
      .CPU_CLK         (CPU_CLK),
      .PROG_BAUD_RATE  (PROG_BAUD_RATE),
      .PROGRAM_SEQUENCE(PROGRAM_SEQUENCE)
  ) main_memory (
      .clk_i          (clk_o),
      .rst_ni         (rst_ni),
      .addr_i         (word_addr),
      .wdata_i        (iomem_req.data),
      .wstrb_i        (ram_wstrb),
      .rdata_o        (ram_rdata),
      .rd_en_i        (ram_rd_en),
      .ram_prog_rx_i  (program_rx_i),
      .system_reset_o (prog_system_reset),
      .prog_mode_led_o(prog_mode_led_o)
  );

  // Address decode
  assign is_ram_access   = (iomem_req.addr & ~RAM_MASK_ADDR) == RAM_BASE_ADDR;
  assign is_timer_access = (iomem_req.addr & 32'hFFFF_FFF0) == TIMER_BASE;

  // Word address extraction
  // iomem_req.addr[1:0] = byte offset within word (ignored, handled by strobes)
  // iomem_req.addr[3:2] = word offset within cache line (for 128-bit lines)
  // iomem_req.addr[...] = word address in RAM
  assign word_addr = iomem_req.addr[BYTE_OFFSET + $clog2(RAM_DEPTH) - 1 : BYTE_OFFSET];

  // Combinational logic
  always_comb begin
    rst_n = prog_system_reset & rst_ni;

    // Response valid when RAM delay complete or timer access
    iomem_res.valid = ram_shift_q[RAM_DELAY-1] | (iomem_req.valid & is_timer_access);
    iomem_res.ready = 1'b1;
    
    // Data mux: timer or RAM
    if (iomem_req.valid & is_timer_access)
      iomem_res.data = {64'b0, timer} >> (iomem_req.addr[3:2] * 32);
    else
      iomem_res.data = ram_rdata;

    // RAM control signals
    req_responsed = iomem_req.valid & iomem_res.valid & is_ram_access;
    req_waited    = iomem_req.valid & !iomem_res.valid & is_ram_access;
    
    // Write strobes - pass through from request
    ram_wstrb = (iomem_req.valid & is_ram_access) ? iomem_req.rw : '0;
    
    // Read enable
    ram_rd_en = iomem_req.valid & is_ram_access & ~(|iomem_req.rw);
  end

  // Sequential logic
  always_ff @(posedge clk_o) begin
    if (!rst_ni) begin
      ram_shift_q <= '0;
    end else begin
      if (req_responsed) 
        ram_shift_q <= '0;
      else 
        ram_shift_q <= {ram_shift_q[RAM_DELAY-2:0], req_waited_q};
    end

    if (!rst_n) begin
      req_waited_q <= 1'b0;
      timer        <= 64'h0;
    end else begin
      req_waited_q <= req_waited;
      timer        <= timer + 64'h1;
    end
  end

endmodule
