/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  Word-based (32-bit) RAM with cache line burst support.
  
  Features:
    - 32-bit word organization (standard .mem file compatible)
    - Cache line width read/write (128-bit default)
    - UART programming interface via separate module
    - Configurable depth and timing
  
  Memory Organization:
    - Words are 32-bit aligned
    - Cache lines span WORDS_PER_LINE consecutive words
    - Byte strobes enable fine-grained writes
*/
`timescale 1ns / 1ps

module wrapper_ram
  import ceres_param::*;
#(
    // Memory Configuration
    parameter int unsigned WORD_WIDTH       = 32,
    parameter int unsigned RAM_DEPTH        = 32768,
    parameter int unsigned CACHE_LINE_WIDTH = BLK_SIZE,

    // Programming Configuration  
    parameter int unsigned                              CPU_CLK          = ceres_param::CPU_CLK,
    parameter int unsigned                              PROG_BAUD_RATE   = ceres_param::PROG_BAUD_RATE,
    parameter logic        [8*PROGRAM_SEQUENCE_LEN-1:0] PROGRAM_SEQUENCE = ceres_param::PROGRAM_SEQUENCE
) (
    input logic clk_i,
    input logic rst_ni,

    // Memory Interface (cache line width)
    input  logic [ $clog2(RAM_DEPTH)-1:0] addr_i,
    input  logic [  CACHE_LINE_WIDTH-1:0] wdata_i,
    input  logic [CACHE_LINE_WIDTH/8-1:0] wstrb_i,
    output logic [  CACHE_LINE_WIDTH-1:0] rdata_o,
    input  logic                          rd_en_i,

    // Programming Interface
    input  logic ram_prog_rx_i,
    output logic system_reset_o,
    output logic prog_mode_led_o
);

  // ==========================================================================
  // Derived Parameters
  // ==========================================================================
  localparam int WORDS_PER_LINE = CACHE_LINE_WIDTH / WORD_WIDTH;
  localparam int BYTES_PER_WORD = WORD_WIDTH / 8;
  localparam int LINE_ADDR_BITS = $clog2(WORDS_PER_LINE);

  // ==========================================================================
  // Memory Array - Separate BRAMs for each word position
  // ==========================================================================
  // Split into individual BRAMs for proper inference
  logic [WORD_WIDTH-1:0] ram0[RAM_DEPTH/WORDS_PER_LINE-1:0];
  logic [WORD_WIDTH-1:0] ram1[RAM_DEPTH/WORDS_PER_LINE-1:0];
  logic [WORD_WIDTH-1:0] ram2[RAM_DEPTH/WORDS_PER_LINE-1:0];
  logic [WORD_WIDTH-1:0] ram3[RAM_DEPTH/WORDS_PER_LINE-1:0];

  // ==========================================================================
  // Internal Signals
  // ==========================================================================

  // Address calculation
  logic [$clog2(RAM_DEPTH/WORDS_PER_LINE)-1:0] word_addr;

  // Read data register
  logic [                CACHE_LINE_WIDTH-1:0] rdata_q;

  // Programming interface
  logic [                                31:0] prog_addr;
  logic [                                31:0] prog_data;
  logic                                        prog_valid;
  logic                                        prog_mode;
  logic                                        prog_sys_rst;

  // ==========================================================================
  // Memory Initialization
  // ==========================================================================
  localparam int INIT_FILE_LEN = 256;
  reg     [8*INIT_FILE_LEN-1:0] init_file = {INIT_FILE_LEN{8'h00}};
  integer                       fd = 0;
  logic   [     WORD_WIDTH-1:0] temp_ram  [0:RAM_DEPTH-1];

  initial begin
`ifndef SYNTHESIS
    if ($value$plusargs("INIT_FILE=%s", init_file)) begin
      fd = $fopen(init_file, "r");
      if (fd == 0) begin
        $display("[ERROR] Cannot open memory file: %s", init_file);
        $finish;
      end
      $fclose(fd);
      $readmemh(init_file, temp_ram, 0, RAM_DEPTH - 1);
      // Distribute to separate BRAMs
      for (int i = 0; i < RAM_DEPTH; i += 4) begin
        ram0[i/4] = temp_ram[i];
        ram1[i/4] = temp_ram[i+1];
        ram2[i/4] = temp_ram[i+2];
        ram3[i/4] = temp_ram[i+3];
      end
`ifdef LOG_RAM
      $display("[INFO] Memory loaded successfully.");
`endif
    end else begin
`ifdef LOG_RAM
      $display("[INFO] No INIT_FILE -> RAM initialized to zero");
`endif
    end
`else
    // During synthesis, initialize to zero (BRAM will be initialized via .coe or programming interface)
    for (int i = 0; i < RAM_DEPTH/WORDS_PER_LINE; i++) begin
      ram0[i] = '0;
      ram1[i] = '0;
      ram2[i] = '0;
      ram3[i] = '0;
    end
`endif
  end

  // ==========================================================================
  // Address Calculation
  // ==========================================================================
  assign word_addr = addr_i[$clog2(RAM_DEPTH)-1:LINE_ADDR_BITS];

  // ==========================================================================
  // Read/Write Logic - Write-First Mode (Vivado BRAM Template)
  // ==========================================================================
  // Reference: UG901 - Recommended Single-Port BRAM Template
  // Write-first mode: Write data appears on output in same cycle as write

  // RAM Bank 0 - Write-first BRAM
  always_ff @(posedge clk_i) begin
    if (prog_mode && prog_valid && prog_addr[LINE_ADDR_BITS-1:0] == 2'd0) begin
      ram0[prog_addr[$clog2(RAM_DEPTH)-1:LINE_ADDR_BITS]] <= prog_data;
      rdata_q[0*WORD_WIDTH+:WORD_WIDTH] <= prog_data;
    end else if (!prog_mode && |wstrb_i[0*BYTES_PER_WORD+:BYTES_PER_WORD]) begin
      ram0[word_addr] <= wdata_i[0*WORD_WIDTH+:WORD_WIDTH];
      rdata_q[0*WORD_WIDTH+:WORD_WIDTH] <= wdata_i[0*WORD_WIDTH+:WORD_WIDTH];
    end else if (!prog_mode && rd_en_i) begin
      rdata_q[0*WORD_WIDTH+:WORD_WIDTH] <= ram0[word_addr];
    end
  end

  // RAM Bank 1 - Write-first BRAM
  always_ff @(posedge clk_i) begin
    if (prog_mode && prog_valid && prog_addr[LINE_ADDR_BITS-1:0] == 2'd1) begin
      ram1[prog_addr[$clog2(RAM_DEPTH)-1:LINE_ADDR_BITS]] <= prog_data;
      rdata_q[1*WORD_WIDTH+:WORD_WIDTH] <= prog_data;
    end else if (!prog_mode && |wstrb_i[1*BYTES_PER_WORD+:BYTES_PER_WORD]) begin
      ram1[word_addr] <= wdata_i[1*WORD_WIDTH+:WORD_WIDTH];
      rdata_q[1*WORD_WIDTH+:WORD_WIDTH] <= wdata_i[1*WORD_WIDTH+:WORD_WIDTH];
    end else if (!prog_mode && rd_en_i) begin
      rdata_q[1*WORD_WIDTH+:WORD_WIDTH] <= ram1[word_addr];
    end
  end

  // RAM Bank 2 - Write-first BRAM
  always_ff @(posedge clk_i) begin
    if (prog_mode && prog_valid && prog_addr[LINE_ADDR_BITS-1:0] == 2'd2) begin
      ram2[prog_addr[$clog2(RAM_DEPTH)-1:LINE_ADDR_BITS]] <= prog_data;
      rdata_q[2*WORD_WIDTH+:WORD_WIDTH] <= prog_data;
    end else if (!prog_mode && |wstrb_i[2*BYTES_PER_WORD+:BYTES_PER_WORD]) begin
      ram2[word_addr] <= wdata_i[2*WORD_WIDTH+:WORD_WIDTH];
      rdata_q[2*WORD_WIDTH+:WORD_WIDTH] <= wdata_i[2*WORD_WIDTH+:WORD_WIDTH];
    end else if (!prog_mode && rd_en_i) begin
      rdata_q[2*WORD_WIDTH+:WORD_WIDTH] <= ram2[word_addr];
    end
  end

  // RAM Bank 3 - Write-first BRAM
  always_ff @(posedge clk_i) begin
    if (prog_mode && prog_valid && prog_addr[LINE_ADDR_BITS-1:0] == 2'd3) begin
      ram3[prog_addr[$clog2(RAM_DEPTH)-1:LINE_ADDR_BITS]] <= prog_data;
      rdata_q[3*WORD_WIDTH+:WORD_WIDTH] <= prog_data;
    end else if (!prog_mode && |wstrb_i[3*BYTES_PER_WORD+:BYTES_PER_WORD]) begin
      ram3[word_addr] <= wdata_i[3*WORD_WIDTH+:WORD_WIDTH];
      rdata_q[3*WORD_WIDTH+:WORD_WIDTH] <= wdata_i[3*WORD_WIDTH+:WORD_WIDTH];
    end else if (!prog_mode && rd_en_i) begin
      rdata_q[3*WORD_WIDTH+:WORD_WIDTH] <= ram3[word_addr];
    end
  end

  assign rdata_o = rdata_q;

  // ==========================================================================
  // Programming Module Instance
  // ==========================================================================
  ram_programmer #(
      .CLK_FREQ    (CPU_CLK),
      .BAUD_RATE   (PROG_BAUD_RATE),
      .MAGIC_SEQ   (PROGRAM_SEQUENCE),
      .SEQ_LENGTH  (PROGRAM_SEQUENCE_LEN),
      .BREAK_CYCLES(1_000_000)
  ) i_programmer (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .uart_rx_i     (ram_prog_rx_i),
      .prog_addr_o   (prog_addr),
      .prog_data_o   (prog_data),
      .prog_valid_o  (prog_valid),
      .prog_mode_o   (prog_mode),
      .system_reset_o(prog_sys_rst)
  );

  // ==========================================================================
  // Output Assignments
  // ==========================================================================
  assign system_reset_o  = prog_sys_rst;
  assign prog_mode_led_o = prog_mode;

endmodule
