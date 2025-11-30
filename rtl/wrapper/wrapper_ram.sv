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
    parameter int unsigned CPU_CLK          = ceres_param::CPU_CLK,
    parameter int unsigned PROG_BAUD_RATE   = ceres_param::PROG_BAUD_RATE,
    parameter              PROGRAM_SEQUENCE = ceres_param::PROGRAM_SEQUENCE
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
  // Memory Array
  // ==========================================================================
  logic   [       WORD_WIDTH-1:0] ram            [0:RAM_DEPTH-1];

  // ==========================================================================
  // Internal Signals
  // ==========================================================================

  // Address calculation
  logic   [$clog2(RAM_DEPTH)-1:0] line_base_addr;

  // Read data register
  logic   [ CACHE_LINE_WIDTH-1:0] rdata_q;

  // Programming interface
  logic   [                 31:0] prog_addr;
  logic   [                 31:0] prog_data;
  logic                           prog_valid;
  logic                           prog_mode;
  logic                           prog_sys_rst;

  // ==========================================================================
  // Memory Initialization
  // ==========================================================================
  string                          init_file;
  integer                         fd;

  initial begin
    if ($value$plusargs("INIT_FILE=%s", init_file)) begin
`ifdef LOG_RAM
      $display("┌────────────────────────────────────────────────────┐");
      $display("│            RAM INITIALIZATION                      │");
      $display("├────────────────────────────────────────────────────┤");
      $display("│ File  : %s", init_file);
      $display("│ Width : %0d-bit words", WORD_WIDTH);
      $display("│ Depth : %0d words (%0d KB)", RAM_DEPTH, (RAM_DEPTH * 4) / 1024);
      $display("└────────────────────────────────────────────────────┘");
`endif
      fd = $fopen(init_file, "r");
      if (fd == 0) begin
        $display("[ERROR] Cannot open memory file: %s", init_file);
        $finish;
      end
      $fclose(fd);
      $readmemh(init_file, ram, 0, RAM_DEPTH - 1);
`ifdef LOG_RAM
      $display("[INFO] Memory loaded successfully.");
`endif
    end else begin
`ifdef LOG_RAM
      $display("[INFO] No INIT_FILE -> RAM initialized to zero");
`endif
      ram = '{default: '0};
    end
  end

  // ==========================================================================
  // Address Calculation
  // ==========================================================================
  // Align to cache line boundary
  assign line_base_addr = {addr_i[$clog2(RAM_DEPTH)-1:LINE_ADDR_BITS], {LINE_ADDR_BITS{1'b0}}};

  // ==========================================================================
  // Read Logic - Burst read for cache line
  // ==========================================================================
  always_ff @(posedge clk_i) begin
    if (rd_en_i) begin
      for (int i = 0; i < WORDS_PER_LINE; i++) begin
        rdata_q[i*WORD_WIDTH+:WORD_WIDTH] <= ram[line_base_addr+i[$clog2(RAM_DEPTH)-1:0]];
      end
    end
  end

  assign rdata_o = rdata_q;

  // ==========================================================================
  // Write Logic - Byte-granular with programming support
  // ==========================================================================
  generate
    for (genvar w = 0; w < WORDS_PER_LINE; w++) begin : gen_word
      for (genvar b = 0; b < BYTES_PER_WORD; b++) begin : gen_byte
        localparam int STROBE_IDX = w * BYTES_PER_WORD + b;

        always_ff @(posedge clk_i) begin
          // Normal write via strobes
          if (wstrb_i[STROBE_IDX]) begin
            ram[line_base_addr+w[$clog2(RAM_DEPTH)-1:0]][b*8+:8] <= wdata_i[w*WORD_WIDTH+b*8+:8];
          end  // Programming write (only to word 0 position)
          else if (prog_mode && prog_valid && w == 0) begin
            ram[prog_addr[$clog2(RAM_DEPTH)-1:0]][b*8+:8] <= prog_data[b*8+:8];
          end
        end
      end
    end
  endgenerate

  // ==========================================================================
  // Programming Module Instance
  // ==========================================================================
  ram_programmer #(
      .CLK_FREQ    (CPU_CLK),
      .BAUD_RATE   (PROG_BAUD_RATE),
      .MAGIC_SEQ   (PROGRAM_SEQUENCE),
      .SEQ_LENGTH  (9),
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
