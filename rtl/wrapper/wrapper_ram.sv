/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  Word-based (32-bit) RAM with cache line burst support - BRAM optimized version.
  
  Features:
    - 32-bit word organization (standard .mem file compatible)
    - Cache line width read/write (128-bit default)
    - UART programming interface via separate module
    - Configurable depth and timing
    - TRUE DUAL-PORT or SIMPLE DUAL-PORT BRAM inference
    - Read data valid signal
  
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
    output logic                          rdata_valid_o,  // NEW: Read data valid signal
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
  // Memory Array - BRAM Inference
  // ==========================================================================
  (* ram_style = "block" *)
  logic [       WORD_WIDTH-1:0] ram            [0:RAM_DEPTH-1];

  // ==========================================================================
  // Internal Signals
  // ==========================================================================
  logic [$clog2(RAM_DEPTH)-1:0] line_base_addr;
  logic [ CACHE_LINE_WIDTH-1:0] rdata_q;
  logic                         rdata_valid_q;

  // Programming interface
  logic [                 31:0] prog_addr;
  logic [                 31:0] prog_data;
  logic                         prog_valid;
  logic                         prog_mode;

  // FSM states
  typedef enum logic [1:0] {
    IDLE,
    READING,
    WRITING
  } state_t;
  state_t                              state;

  logic   [$clog2(WORDS_PER_LINE)-1:0] access_idx;
  logic   [     $clog2(RAM_DEPTH)-1:0] access_base_addr;
  logic   [      CACHE_LINE_WIDTH-1:0] write_wdata_buf;
  logic   [    CACHE_LINE_WIDTH/8-1:0] write_wstrb_buf;

  // BRAM Port Signals
  logic                                ram_we;
  logic   [     $clog2(RAM_DEPTH)-1:0] ram_addr;
  logic   [            WORD_WIDTH-1:0] ram_wdata;
  logic   [            WORD_WIDTH-1:0] ram_rdata;
  logic   [        BYTES_PER_WORD-1:0] ram_we_bytes;

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
  assign line_base_addr = {addr_i[$clog2(RAM_DEPTH)-1:LINE_ADDR_BITS], {LINE_ADDR_BITS{1'b0}}};

  // ==========================================================================
  // BRAM Access Block - Single Always Block for Optimal Inference
  // ==========================================================================
  always_ff @(posedge clk_i) begin
    // Default: no write
    ram_we <= 1'b0;

    // BRAM read/write with byte enables
    if (ram_we) begin
      for (int b = 0; b < BYTES_PER_WORD; b++) begin
        if (ram_we_bytes[b]) begin
          ram[ram_addr][b*8+:8] <= ram_wdata[b*8+:8];
        end
      end
    end

    // Always perform read (BRAM behavior)
    ram_rdata <= ram[ram_addr];
  end

  // ==========================================================================
  // Control Logic - FSM and Data Path
  // ==========================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      state            <= IDLE;
      access_idx       <= '0;
      access_base_addr <= '0;
      rdata_q          <= '0;
      rdata_valid_q    <= 1'b0;
      write_wdata_buf  <= '0;
      write_wstrb_buf  <= '0;
      ram_addr         <= '0;
      ram_wdata        <= '0;
      ram_we_bytes     <= '0;
    end else begin
      // Default: clear valid signal
      rdata_valid_q <= 1'b0;

      case (state)
        IDLE: begin
          if (rd_en_i) begin
            // Start read operation
            state            <= READING;
            access_idx       <= '0;
            access_base_addr <= line_base_addr;
            ram_addr         <= line_base_addr;
          end else if (|wstrb_i) begin
            // Start write operation
            state            <= WRITING;
            access_idx       <= '0;
            access_base_addr <= line_base_addr;
            write_wdata_buf  <= wdata_i;
            write_wstrb_buf  <= wstrb_i;
            ram_addr         <= line_base_addr;
          end else if (prog_mode && prog_valid) begin
            // Programming mode write
            ram_addr     <= prog_addr[$clog2(RAM_DEPTH)-1:0];
            ram_wdata    <= prog_data;
            ram_we       <= 1'b1;
            ram_we_bytes <= '1;  // Write all bytes
          end
        end

        READING: begin
          // Capture read data (first word available after 1 cycle latency)
          if (access_idx > 0) begin
            rdata_q[(access_idx-1)*WORD_WIDTH+:WORD_WIDTH] <= ram_rdata;
          end

          // Setup next read or finish
          if (access_idx < WORDS_PER_LINE) begin
            access_idx <= access_idx + 1;
            if (access_idx < WORDS_PER_LINE - 1) begin
              ram_addr <= access_base_addr + access_idx + 1;
            end
          end else begin
            // Last word captured - assert valid and return to IDLE
            rdata_q[(WORDS_PER_LINE-1)*WORD_WIDTH+:WORD_WIDTH] <= ram_rdata;
            rdata_valid_q                                       <= 1'b1;
            state                                               <= IDLE;
          end
        end

        WRITING: begin
          // Extract byte enables and data for current word
          logic [BYTES_PER_WORD-1:0] current_wstrb;
          logic [    WORD_WIDTH-1:0] current_wdata;

          current_wstrb = write_wstrb_buf[access_idx*BYTES_PER_WORD+:BYTES_PER_WORD];
          current_wdata = write_wdata_buf[access_idx*WORD_WIDTH+:WORD_WIDTH];

          // Perform write if any byte enables are active
          if (|current_wstrb) begin
            ram_addr     <= access_base_addr + access_idx;
            ram_wdata    <= current_wdata;
            ram_we       <= 1'b1;
            ram_we_bytes <= current_wstrb;
          end

          // Move to next word or finish
          if (access_idx < WORDS_PER_LINE - 1) begin
            access_idx <= access_idx + 1;
          end else begin
            state <= IDLE;
          end
        end

        default: state <= IDLE;
      endcase
    end
  end

  // Output assignments
  assign rdata_o       = rdata_q;
  assign rdata_valid_o = rdata_valid_q;

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
      .system_reset_o(system_reset_o)
  );

  assign prog_mode_led_o = prog_mode;

endmodule
