/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  Single wide BRAM with cache line width data bus.

  Features:
    - Direct cache line width organization (128-bit default)
    - Byte-enable support for fine-grained writes
    - UART programming interface via separate module
    - Optimized for BRAM inference

  Memory Organization:
    - Single wide RAM array matching cache line width
    - Byte strobes for partial line writes
    - Compatible with standard .mem file loading
*/
`timescale 1ns / 1ps

module wrapper_ram
  import ceres_param::*;
#(
    // Memory Configuration
    parameter int unsigned CACHE_LINE_WIDTH = BLK_SIZE,
    parameter int unsigned RAM_DEPTH        = 32768,     // Total words (32-bit)

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
  localparam int WORD_WIDTH = 32;
  localparam int WORDS_PER_LINE = CACHE_LINE_WIDTH / WORD_WIDTH;
  localparam int BYTES_PER_LINE = CACHE_LINE_WIDTH / 8;
  localparam int LINE_DEPTH = RAM_DEPTH / WORDS_PER_LINE;
  localparam int LINE_ADDR_BITS = $clog2(WORDS_PER_LINE);

  // ==========================================================================
  // Memory Array - Single Wide BRAM (fallback)
  // ==========================================================================
`ifndef CERES_OPENLANE
  (* ram_style = "block" *) logic [CACHE_LINE_WIDTH-1:0] ram [LINE_DEPTH-1:0];
`endif

  // ==========================================================================
  // Internal Signals
  // ==========================================================================
  logic [$clog2(LINE_DEPTH)-1:0] line_addr;
  logic [  CACHE_LINE_WIDTH-1:0] rdata_q;

`ifdef CERES_OPENLANE
  logic [CACHE_LINE_WIDTH-1:0] sram_rdata_line;
  logic [                31:0] sram_bank_rdata [0:WORDS_PER_LINE-1];
  logic [                 3:0] sram_bank_wmask [0:WORDS_PER_LINE-1];
  logic [                31:0] sram_bank_wdata [0:WORDS_PER_LINE-1];
  logic                        sram_bank_we    [0:WORDS_PER_LINE-1];
`endif

  // Programming interface
  logic [                  31:0] prog_addr;
  logic [                  31:0] prog_data;
  logic                          prog_valid;
  logic                          prog_mode;
  logic                          prog_sys_rst;

  // Write control signals
  logic [$clog2(LINE_DEPTH)-1:0] wr_addr;
  logic [  CACHE_LINE_WIDTH-1:0] wr_data;
  logic [CACHE_LINE_WIDTH/8-1:0] wr_strb;

  // ==========================================================================
  // Memory Initialization
  // ==========================================================================
`ifndef CERES_OPENLANE
  localparam int INIT_FILE_LEN = 256;
  reg     [8*INIT_FILE_LEN-1:0] init_file = {INIT_FILE_LEN{8'h00}};
  integer                       fd = 0;
  logic   [     WORD_WIDTH-1:0] temp_ram                           [0:RAM_DEPTH-1];

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
      // Pack words into cache lines
      for (int i = 0; i < LINE_DEPTH; i++) begin
        for (int j = 0; j < WORDS_PER_LINE; j++) begin
          ram[i][j*WORD_WIDTH+:WORD_WIDTH] = temp_ram[i*WORDS_PER_LINE+j];
        end
      end
`ifdef LOG_RAM
      $display("[INFO] Memory loaded successfully: %0d cache lines", LINE_DEPTH);
`endif
    end else begin
`ifdef LOG_RAM
      $display("[INFO] No INIT_FILE -> RAM initialized to zero");
`endif
      ram = '{default: '0};
    end
`else
    // During synthesis, initialize RAM to zero (no external mem file dependency)
`ifndef CERES_OPENLANE
    $readmemh("/home/kerim/level-v/coremark_128.mem", ram);
`else
    for (int i = 0; i < LINE_DEPTH; i++) begin
      ram[i] = '0;
    end
`endif
`endif
  end
`endif

  // ==========================================================================
  // Address Calculation
  // ==========================================================================
  assign line_addr = addr_i[$clog2(RAM_DEPTH)-1:LINE_ADDR_BITS];

  // ==========================================================================
  // Write Control Muxing
  // ==========================================================================
  always_comb begin
    if (prog_mode && prog_valid) begin
      // Programming mode: write single word to specific position
      wr_addr = prog_addr[$clog2(RAM_DEPTH)-1:LINE_ADDR_BITS];
      wr_data = {WORDS_PER_LINE{prog_data}};  // Replicate to all positions
      // Enable only the target word position (little-endian byte order)
      case (prog_addr[LINE_ADDR_BITS-1:0])
        2'd0:    wr_strb = 16'b0000_0000_0000_1111;  // Bytes [3:0]   -> Bits [31:0]
        2'd1:    wr_strb = 16'b0000_0000_1111_0000;  // Bytes [7:4]   -> Bits [63:32]
        2'd2:    wr_strb = 16'b0000_1111_0000_0000;  // Bytes [11:8]  -> Bits [95:64]
        2'd3:    wr_strb = 16'b1111_0000_0000_0000;  // Bytes [15:12] -> Bits [127:96]
        default: wr_strb = '0;
      endcase
    end else begin
      // Normal mode: use cache line interface
      wr_addr = line_addr;
      wr_data = wdata_i;
      wr_strb = wstrb_i;
    end
  end

  // ==========================================================================
  // RAM Read/Write Logic
  // ==========================================================================
`ifdef CERES_OPENLANE
  if ((WORDS_PER_LINE == 4) && (LINE_DEPTH <= 256)) begin : g_sram_main_mem
    logic [7:0] sram_wr_addr;
    logic [7:0] sram_rd_addr;

    assign sram_wr_addr = wr_addr[7:0];
    assign sram_rd_addr = line_addr[7:0];

    always_comb begin
      for (int w = 0; w < WORDS_PER_LINE; w++) begin
        sram_bank_wdata[w] = wr_data[w*32+:32];
        sram_bank_wmask[w] = wr_strb[w*4+:4];
        sram_bank_we[w] = |wr_strb[w*4+:4];
        sram_rdata_line[w*32+:32] = sram_bank_rdata[w];
      end
    end

    for (genvar w = 0; w < WORDS_PER_LINE; w++) begin : g_word_bank
      sky130_sram_1kbyte_1rw1r_32x256_8 i_main_sram_bank (
          .clk0  (clk_i),
          .csb0  (~sram_bank_we[w]),
          .web0  (1'b0),
          .wmask0(sram_bank_wmask[w]),
          .addr0 (sram_wr_addr),
          .din0  (sram_bank_wdata[w]),
          .dout0 (),
          .clk1  (clk_i),
          .csb1  (~rd_en_i),
          .addr1 (sram_rd_addr),
          .dout1 (sram_bank_rdata[w])
      );
    end

    assign rdata_o = sram_rdata_line;
  end else begin : g_sram_fallback_regmem
    (* ram_style = "block" *) logic [CACHE_LINE_WIDTH-1:0] ram [LINE_DEPTH-1:0];

    genvar i;
    for (i = 0; i < BYTES_PER_LINE; i++) begin : byte_write
      always_ff @(posedge clk_i) begin
        if (wr_strb[i]) ram[wr_addr][i*8+:8] <= wr_data[i*8+:8];
      end
    end

    always_ff @(posedge clk_i) begin
      if (rd_en_i) rdata_q <= ram[line_addr];
    end

    assign rdata_o = rdata_q;
  end
`else
  genvar i;
  generate
    for (i = 0; i < BYTES_PER_LINE; i++) begin : byte_write
      always_ff @(posedge clk_i) begin
        if (wr_strb[i]) ram[wr_addr][i*8+:8] <= wr_data[i*8+:8];
      end
    end
  endgenerate

  // Read logic with output register
  always_ff @(posedge clk_i) begin
    if (rd_en_i) rdata_q <= ram[line_addr];
  end

  assign rdata_o = rdata_q;
`endif

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
