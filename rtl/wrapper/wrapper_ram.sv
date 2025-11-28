/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  Word-based (32-bit) RAM with burst support for cache line transfers.
  Memory is organized as 32-bit words, but supports reading/writing
  full cache lines (e.g., 128-bit) through burst operations.
  
  This allows using standard 32-bit .mem files while still supporting
  cache line width transfers.
*/
`timescale 1ns / 1ps

module wrapper_ram #(
    parameter WORD_WIDTH       = 32,          // Word genişliği (bit)
    parameter RAM_DEPTH        = 32768,       // Word sayısı (32K words = 128KB)
    parameter CACHE_LINE_WIDTH = 128,         // Cache line genişliği (bit)
    parameter CPU_CLK          = 50_000_000,
    parameter PROG_BAUD_RATE   = 115200,
    parameter PROGRAM_SEQUENCE = "ceresTEST"
) (
    input  logic                              clk_i,
    input  logic                              rst_ni,
    
    // Cache/Memory Interface (cache line width)
    input  logic [$clog2(RAM_DEPTH)-1:0]      addr_i,         // Word address
    input  logic [CACHE_LINE_WIDTH-1:0]       wdata_i,        // Write data (full cache line)
    input  logic [CACHE_LINE_WIDTH/8-1:0]     wstrb_i,        // Byte write strobes
    output logic [CACHE_LINE_WIDTH-1:0]       rdata_o,        // Read data (full cache line)
    input  logic                              rd_en_i,
    
    // Programming interface
    input  logic                              ram_prog_rx_i,
    output logic                              system_reset_o,
    output logic                              prog_mode_led_o
);

  // Derived parameters
  localparam WORDS_PER_LINE = CACHE_LINE_WIDTH / WORD_WIDTH;  // 4 for 128-bit line
  localparam BYTES_PER_WORD = WORD_WIDTH / 8;                 // 4 bytes
  localparam LINE_ADDR_BITS = $clog2(WORDS_PER_LINE);         // 2 bits for 4 words
  
  // Word-based memory array (32-bit words)
  logic [WORD_WIDTH-1:0] ram [0:RAM_DEPTH-1];
  
  // Internal signals
  logic [$clog2(RAM_DEPTH)-1:0] base_addr;
  logic [CACHE_LINE_WIDTH-1:0]  rdata_reg;
  
  // Programming FSM signals
  localparam PROG_SEQ_LENGTH = 9;
  localparam SEQ_BREAK_THRESHOLD = 32'd1000000;
  
  logic [31:0]                   prog_uart_do;
  logic [PROG_SEQ_LENGTH*8-1:0]  received_sequence;
  logic [3:0]                    rcv_seq_ctr;
  logic [31:0]                   sequence_break_ctr;
  logic                          sequence_break;
  logic [$clog2(RAM_DEPTH)-1:0]  prog_addr;
  logic [WORD_WIDTH-1:0]         prog_word;
  logic                          prog_word_valid;
  logic [1:0]                    prog_byte_ctr;
  logic [31:0]                   prog_word_number;
  logic [31:0]                   prog_word_ctr;
  logic                          prog_sys_rst_n;
  logic                          ram_prog_rd_en;

  // FSM states
  typedef enum logic [2:0] {
    SequenceWait       = 3'b000,
    SequenceReceive    = 3'b001,
    SequenceCheck      = 3'b011,
    SequenceLengthCalc = 3'b010,
    SequenceProgram    = 3'b110,
    SequenceFinish     = 3'b100
  } fsm_t;

  fsm_t state_prog, state_prog_next;

  // ============================================
  // Memory Initialization
  // ============================================
  string  init_file;
  integer fd;
  string  line;
  int     line_num;

  initial begin
    if ($value$plusargs("INIT_FILE=%s", init_file)) begin
      $display("------------------------------------------------------");
      $display("[INFO] Loading memory from file: %s", init_file);
      $display("[INFO] Memory organization: %0d-bit words, %0d depth", WORD_WIDTH, RAM_DEPTH);
      $display("------------------------------------------------------");

      fd = $fopen(init_file, "r");
      if (fd == 0) begin
        $display("[ERROR] Cannot open memory file: %s", init_file);
        $finish;
      end

      line_num = 0;
      while (!$feof(fd) && line_num < 8) begin
        line_num++;
        void'($fgets(line, fd));
        line = line.tolower();
        $display("  [%0d] %s", line_num, line);
      end
      $fclose(fd);

      $readmemh(init_file, ram, 0, RAM_DEPTH - 1);
      $display("[INFO] Memory file successfully loaded into RAM.");
      $display("------------------------------------------------------");
    end else begin
      $display("[INFO] No INIT_FILE provided -> initializing RAM to zero");
      ram = '{default: '0};
    end
  end

  // ============================================
  // Cache Line Address Calculation
  // ============================================
  // addr_i is word-aligned, we need to get the base address of the cache line
  assign base_addr = {addr_i[$clog2(RAM_DEPTH)-1:LINE_ADDR_BITS], {LINE_ADDR_BITS{1'b0}}};

  // ============================================
  // Read Operation - Burst read for cache line
  // ============================================
  always_ff @(posedge clk_i) begin
    if (rd_en_i) begin
      // Read WORDS_PER_LINE consecutive words
      for (int i = 0; i < WORDS_PER_LINE; i++) begin
        rdata_reg[i*WORD_WIDTH +: WORD_WIDTH] <= ram[base_addr + i[$clog2(RAM_DEPTH)-1:0]];
      end
    end
  end
  
  assign rdata_o = rdata_reg;

  // ============================================
  // Write Operation - Byte-wise write with strobes
  // ============================================
  // Handle both normal writes and programming writes
  generate
    for (genvar word_idx = 0; word_idx < WORDS_PER_LINE; word_idx++) begin : gen_word_write
      for (genvar byte_idx = 0; byte_idx < BYTES_PER_WORD; byte_idx++) begin : gen_byte_write
        localparam int strobe_idx = word_idx * BYTES_PER_WORD + byte_idx;
        
        always_ff @(posedge clk_i) begin
          // Normal cache line write
          if (wstrb_i[strobe_idx]) begin
            ram[base_addr + word_idx[$clog2(RAM_DEPTH)-1:0]][byte_idx*8 +: 8] <= 
              wdata_i[word_idx*WORD_WIDTH + byte_idx*8 +: 8];
          end
          // Programming write (word at a time)
          else if (prog_mode_led_o && prog_word_valid && (word_idx == 0)) begin
            ram[prog_addr][byte_idx*8 +: 8] <= prog_word[byte_idx*8 +: 8];
          end
        end
      end
    end
  endgenerate

  // ============================================
  // Programming Address Counter
  // ============================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni || !system_reset_o) begin
      prog_addr <= '0;
    end else if (prog_mode_led_o && prog_word_valid) begin
      prog_addr <= prog_addr + 1'b1;
    end
  end

  // ============================================
  // Control Signals
  // ============================================
  assign system_reset_o  = prog_sys_rst_n;
  assign ram_prog_rd_en  = (state_prog != SequenceFinish);
  assign prog_mode_led_o = (state_prog == SequenceProgram);
  assign sequence_break  = (sequence_break_ctr == SEQ_BREAK_THRESHOLD);

  // ============================================
  // Programming FSM - State Register
  // ============================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) state_prog <= SequenceWait;
    else state_prog <= state_prog_next;
  end

  // ============================================
  // Programming FSM - Next State Logic
  // ============================================
  always_comb begin
    state_prog_next = state_prog;
    case (state_prog)
      SequenceWait: begin
        if (prog_uart_do != '1)
          state_prog_next = SequenceReceive;
      end

      SequenceReceive: begin
        if (prog_uart_do != '1) begin
          if (rcv_seq_ctr == PROG_SEQ_LENGTH - 1) 
            state_prog_next = SequenceCheck;
        end else if (sequence_break) begin
          state_prog_next = SequenceWait;
        end
      end

      SequenceCheck: begin
        if (received_sequence == PROGRAM_SEQUENCE) 
          state_prog_next = SequenceLengthCalc;
        else 
          state_prog_next = SequenceWait;
      end

      SequenceLengthCalc: begin
        if ((prog_uart_do != '1) && &prog_byte_ctr) 
          state_prog_next = SequenceProgram;
      end

      SequenceProgram: begin
        if ((prog_word_ctr == prog_word_number) && ~&prog_byte_ctr) 
          state_prog_next = SequenceFinish;
      end

      SequenceFinish: begin
        state_prog_next = SequenceWait;
      end

      default: state_prog_next = SequenceWait;
    endcase
  end

  // ============================================
  // Programming FSM - Output Logic
  // ============================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      prog_byte_ctr      <= '0;
      prog_word          <= '0;
      prog_word_number   <= '0;
      prog_word_ctr      <= '0;
      sequence_break_ctr <= '0;
      received_sequence  <= '0;
      rcv_seq_ctr        <= '0;
      prog_word_valid    <= 1'b0;
      prog_sys_rst_n     <= 1'b1;
    end else begin
      case (state_prog)
        SequenceWait: begin
          prog_byte_ctr      <= '0;
          prog_word          <= '0;
          prog_word_number   <= '0;
          prog_word_ctr      <= '0;
          sequence_break_ctr <= '0;
          received_sequence  <= '0;
          rcv_seq_ctr        <= '0;
          prog_word_valid    <= 1'b0;
          prog_sys_rst_n     <= 1'b1;
          if (prog_uart_do != '1) begin
            rcv_seq_ctr       <= rcv_seq_ctr + 1;
            received_sequence <= {received_sequence[PROG_SEQ_LENGTH*8-9:0], prog_uart_do[7:0]};
          end
        end

        SequenceReceive: begin
          if (prog_uart_do != '1) begin
            received_sequence <= {received_sequence[PROG_SEQ_LENGTH*8-9:0], prog_uart_do[7:0]};
            if (rcv_seq_ctr == PROG_SEQ_LENGTH - 1) 
              rcv_seq_ctr <= 0;
            else 
              rcv_seq_ctr <= rcv_seq_ctr + 1;
          end else begin
            if (sequence_break) 
              sequence_break_ctr <= 0;
            else 
              sequence_break_ctr <= sequence_break_ctr + 1;
          end
        end

        SequenceCheck: begin
          prog_byte_ctr <= 0;
        end

        SequenceLengthCalc: begin
          prog_word_ctr <= 0;
          if (prog_uart_do != '1) begin
            // Receive 4 bytes for word count (big-endian)
            prog_word_number <= {prog_word_number[23:0], prog_uart_do[7:0]};
            prog_byte_ctr <= prog_byte_ctr + 1;
          end
        end

        SequenceProgram: begin
          if (prog_uart_do != '1) begin
            // Receive bytes and form 32-bit words (little-endian for RISC-V)
            prog_word <= {prog_uart_do[7:0], prog_word[31:8]};
            
            if (&prog_byte_ctr) begin
              // Complete word received
              prog_byte_ctr   <= 0;
              prog_word_valid <= 1'b1;
              prog_word_ctr   <= prog_word_ctr + 1;
            end else begin
              prog_byte_ctr   <= prog_byte_ctr + 1;
              prog_word_valid <= 1'b0;
            end
          end else begin
            prog_word_valid <= 1'b0;
          end
        end

        SequenceFinish: begin
          prog_sys_rst_n <= 1'b0;
        end

        default: begin
          // No action
        end
      endcase
    end
  end

  // ============================================
  // UART for Programming
  // ============================================
  simpleuart #(
      .DEFAULT_DIV(CPU_CLK / PROG_BAUD_RATE)
  ) simpleuart_inst (
      .clk       (clk_i),
      .resetn    (rst_ni),
      .ser_tx    (),
      .ser_rx    (ram_prog_rx_i),
      .reg_div_we(4'h0),
      .reg_div_di(32'h0),
      .reg_div_do(),
      .reg_dat_we(1'b0),
      .reg_dat_re(ram_prog_rd_en),
      .reg_dat_di(32'h0),
      .reg_dat_do(prog_uart_do)
  );

endmodule
