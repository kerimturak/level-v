/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  UART-based RAM Programmer Module
  
  Receives a magic sequence via UART, then programs RAM with incoming data.
  Protocol:
    1. Wait for magic sequence (e.g., "ceresTEST")
    2. Receive 4-byte word count (big-endian)
    3. Receive words (little-endian for RISC-V)
    4. Assert system reset when done
*/
`timescale 1ns / 1ps

module ram_programmer
  import ceres_param::*;
#(
  parameter int unsigned CLK_FREQ     = CPU_CLK,
  parameter int unsigned BAUD_RATE    = PROG_BAUD_RATE,
  parameter int unsigned SEQ_LENGTH   = PROGRAM_SEQUENCE_LEN,
  parameter logic [SEQ_LENGTH*8-1:0]  MAGIC_SEQ    = PROGRAM_SEQUENCE,
  parameter int unsigned BREAK_CYCLES = 1_000_000
) (
    input logic clk_i,
    input logic rst_ni,

    // UART RX
    input logic uart_rx_i,

    // RAM Write Interface
    output logic [31:0] prog_addr_o,
    output logic [31:0] prog_data_o,
    output logic        prog_valid_o,

    // Control
    output logic prog_mode_o,
    output logic system_reset_o
);

  // ==========================================================================
  // FSM States
  // ==========================================================================
  typedef enum logic [2:0] {
    ST_IDLE        = 3'b000,
    ST_SEQ_RECEIVE = 3'b001,
    ST_SEQ_CHECK   = 3'b010,
    ST_LEN_RECEIVE = 3'b011,
    ST_PROGRAM     = 3'b100,
    ST_FINISH      = 3'b101
  } state_t;

  state_t state_q, state_next;

  // ==========================================================================
  // Internal Signals
  // ==========================================================================

  // UART
  logic [            31:0] uart_data;
  logic                    uart_rd_en;
  logic                    uart_byte_valid;

  // Sequence detection
  logic [SEQ_LENGTH*8-1:0] seq_shift_q;
  logic [             3:0] seq_cnt_q;
  logic [            31:0] break_cnt_q;
  logic                    seq_timeout;
  logic                    seq_match;

  // Programming
  logic [            31:0] word_count_q;
  logic [            31:0] word_idx_q;
  logic [            31:0] prog_addr_q;
  logic [            31:0] prog_word_q;
  logic [             1:0] byte_cnt_q;
  logic                    prog_valid_q;
  logic                    sys_rst_q;

  // ==========================================================================
  // UART Instance
  // ==========================================================================
  simpleuart #(
      .DEFAULT_DIV(CLK_FREQ / BAUD_RATE)
  ) u_uart (
      .clk       (clk_i),
      .resetn    (rst_ni),
      .ser_tx    (),
      .ser_rx    (uart_rx_i),
      .reg_div_we(4'h0),
      .reg_div_di(32'h0),
      .reg_div_do(),
      .reg_dat_we(1'b0),
      .reg_dat_re(uart_rd_en),
      .reg_dat_di(32'h0),
      .reg_dat_do(uart_data)
  );

  assign uart_byte_valid = (uart_data != 32'hFFFF_FFFF);
  assign uart_rd_en      = (state_q != ST_FINISH);

  // ==========================================================================
  // Control Signals
  // ==========================================================================
  assign seq_timeout     = (break_cnt_q >= BREAK_CYCLES);
  assign seq_match       = (seq_shift_q == MAGIC_SEQ);

  // ==========================================================================
  // FSM - State Register
  // ==========================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) state_q <= ST_IDLE;
    else state_q <= state_next;
  end

  // ==========================================================================
  // FSM - Next State Logic
  // ==========================================================================
  always_comb begin
    state_next = state_q;

    case (state_q)
      ST_IDLE: begin
        if (uart_byte_valid) state_next = ST_SEQ_RECEIVE;
      end

      ST_SEQ_RECEIVE: begin
        if (uart_byte_valid && seq_cnt_q == SEQ_LENGTH - 1) state_next = ST_SEQ_CHECK;
        else if (seq_timeout) state_next = ST_IDLE;
      end

      ST_SEQ_CHECK: begin
        state_next = seq_match ? ST_LEN_RECEIVE : ST_IDLE;
      end

      ST_LEN_RECEIVE: begin
        if (uart_byte_valid && &byte_cnt_q) state_next = ST_PROGRAM;
      end

      ST_PROGRAM: begin
        if (word_idx_q >= word_count_q && ~&byte_cnt_q) state_next = ST_FINISH;
      end

      ST_FINISH: begin
        state_next = ST_IDLE;
      end

      default: state_next = ST_IDLE;
    endcase
  end

  // ==========================================================================
  // FSM - Datapath
  // ==========================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      seq_shift_q  <= '0;
      seq_cnt_q    <= '0;
      break_cnt_q  <= '0;
      word_count_q <= '0;
      word_idx_q   <= '0;
      prog_addr_q  <= '0;
      prog_word_q  <= '0;
      byte_cnt_q   <= '0;
      prog_valid_q <= 1'b0;
      sys_rst_q    <= 1'b1;
    end else begin
      // Default
      prog_valid_q <= 1'b0;

      case (state_q)
        ST_IDLE: begin
          seq_shift_q  <= '0;
          seq_cnt_q    <= '0;
          break_cnt_q  <= '0;
          word_count_q <= '0;
          word_idx_q   <= '0;
          prog_addr_q  <= '0;
          byte_cnt_q   <= '0;
          sys_rst_q    <= 1'b1;

          if (uart_byte_valid) begin
            seq_shift_q <= {seq_shift_q[SEQ_LENGTH*8-9:0], uart_data[7:0]};
            seq_cnt_q   <= seq_cnt_q + 1;
          end
        end

        ST_SEQ_RECEIVE: begin
          if (uart_byte_valid) begin
            seq_shift_q <= {seq_shift_q[SEQ_LENGTH*8-9:0], uart_data[7:0]};
            seq_cnt_q   <= (seq_cnt_q == SEQ_LENGTH - 1) ? '0 : seq_cnt_q + 1;
            break_cnt_q <= '0;
          end else begin
            break_cnt_q <= break_cnt_q + 1;
          end
        end

        ST_SEQ_CHECK: begin
          byte_cnt_q <= '0;
        end

        ST_LEN_RECEIVE: begin
          if (uart_byte_valid) begin
            // Big-endian word count
            word_count_q <= {word_count_q[23:0], uart_data[7:0]};
            byte_cnt_q   <= byte_cnt_q + 1;
          end
        end

        ST_PROGRAM: begin
          if (uart_byte_valid) begin
            // Little-endian word assembly
            prog_word_q <= {uart_data[7:0], prog_word_q[31:8]};

            if (&byte_cnt_q) begin
              // Complete word received
              byte_cnt_q   <= '0;
              prog_valid_q <= 1'b1;
              prog_addr_q  <= prog_addr_q + 1;
              word_idx_q   <= word_idx_q + 1;
            end else begin
              byte_cnt_q <= byte_cnt_q + 1;
            end
          end
        end

        ST_FINISH: begin
          sys_rst_q <= 1'b0;
        end

        default: ;
      endcase
    end
  end

  // ==========================================================================
  // Outputs
  // ==========================================================================
  assign prog_addr_o    = prog_addr_q - 1;  // Address of completed word
  assign prog_data_o    = {uart_data[7:0], prog_word_q[31:8]};  // Current complete word
  assign prog_valid_o   = prog_valid_q;
  assign prog_mode_o    = (state_q == ST_PROGRAM);
  assign system_reset_o = sys_rst_q;

endmodule
