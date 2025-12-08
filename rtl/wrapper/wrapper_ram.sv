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
    // Completion pulses (one-cycle) to indicate serialized operations finished

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
  // Request Xilinx block RAM implementation where possible
  (* ram_style = "block" *)
  logic [            WORD_WIDTH-1:0] ram            [0:RAM_DEPTH-1];

  // ==========================================================================
  // Internal Signals
  // ==========================================================================

  // Address calculation
  logic [     $clog2(RAM_DEPTH)-1:0] line_base_addr;

  // Read data register
  logic [      CACHE_LINE_WIDTH-1:0] rdata_q;

  // Programming interface
  logic [                      31:0] prog_addr;
  logic [                      31:0] prog_data;
  logic                              prog_valid;
  logic                              prog_mode;
  logic                              prog_sys_rst;
  logic                              read_active;
  // Read FSM indices/base address
  logic [$clog2(WORDS_PER_LINE)-1:0] read_idx;
  logic [     $clog2(RAM_DEPTH)-1:0] read_base_addr;
  // Completion pulses (registered)
  logic                              rd_done_q;
  logic                              wr_done_q;

  // ==========================================================================
  // Memory Initialization
  // ==========================================================================
  localparam int INIT_FILE_LEN = 256;
  reg     [8*INIT_FILE_LEN-1:0] init_file;
  integer                       fd;

  initial begin
`ifndef SYNTHESIS
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
`else
    // In synthesis, initialize RAM to zero
    init_file = "coremark.mem";
    $readmemh(init_file, ram, 0, RAM_DEPTH - 1);
`endif
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
    if (!rst_ni) begin
      read_active    <= 1'b0;
      read_idx       <= '0;
      read_base_addr <= '0;
      rdata_q        <= '0;
      rd_done_q      <= 1'b0;
    end else begin
      if (rd_en_i && !read_active) begin
        read_active    <= 1'b1;
        read_idx       <= '0;
        read_base_addr <= line_base_addr;
      end else if (read_active) begin
        rdata_q[read_idx*WORD_WIDTH+:WORD_WIDTH] <= ram[read_base_addr+read_idx];
        if (read_idx == WORDS_PER_LINE - 1) begin
          read_active <= 1'b0;
          rd_done_q   <= 1'b1;
        end else begin
          rd_done_q <= 1'b0;
        end
        read_idx <= read_idx + 1;
      end
    end
  end

  assign rdata_o = rdata_q;

  // ==========================================================================
  // Write Logic - Byte-granular with programming support
  // ==========================================================================
  // Serialized write: buffer write request and perform one word write per cycle
  logic                              write_active;
  logic [$clog2(WORDS_PER_LINE)-1:0] write_idx;
  logic [     $clog2(RAM_DEPTH)-1:0] write_base_addr;
  logic [      CACHE_LINE_WIDTH-1:0] write_wdata_buf;
  logic [    CACHE_LINE_WIDTH/8-1:0] write_wstrb_buf;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      write_active    <= 1'b0;
      write_idx       <= '0;
      write_base_addr <= '0;
      write_wdata_buf <= '0;
      write_wstrb_buf <= '0;
      wr_done_q       <= 1'b0;
    end else begin
      if (|wstrb_i && !write_active) begin
        write_active    <= 1'b1;
        write_idx       <= '0;
        write_base_addr <= line_base_addr;
        write_wdata_buf <= wdata_i;
        write_wstrb_buf <= wstrb_i;
      end else if (write_active) begin
        logic   [WORD_WIDTH-1:0] prev_word;
        logic   [WORD_WIDTH-1:0] next_word;
        integer                  b;
        prev_word = ram[write_base_addr+write_idx];
        next_word = prev_word;
        for (b = 0; b < BYTES_PER_WORD; b++) begin
          automatic int strobe_idx = write_idx * BYTES_PER_WORD + b;
          if (write_wstrb_buf[strobe_idx]) begin
            next_word[b*8+:8] = write_wdata_buf[write_idx*WORD_WIDTH+b*8+:8];
          end
        end
        if (|write_wstrb_buf[write_idx*BYTES_PER_WORD+:BYTES_PER_WORD]) begin
          ram[write_base_addr+write_idx] <= next_word;
        end
        if (prog_mode && prog_valid && write_idx == 0) begin
          ram[prog_addr[$clog2(RAM_DEPTH)-1:0]] <= prog_data;
        end

        if (write_idx == WORDS_PER_LINE - 1) begin
          write_active <= 1'b0;
          wr_done_q    <= 1'b1;
        end else begin
          wr_done_q <= 1'b0;
        end
        write_idx <= write_idx + 1;
      end
    end
  end

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
