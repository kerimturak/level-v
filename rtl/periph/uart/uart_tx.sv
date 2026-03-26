/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
module uart_tx
  import level_param::*;
#(
    parameter DATA_WIDTH = level_param::UART_DATA_WIDTH,
    parameter FIFO_DEPTH = level_param::UART_TX_FIFO_DEPTH
) (
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic [15:0] baud_div_i,
    input  logic        tx_we_i,
    input  logic        tx_en_i,
    input  logic [ 7:0] din_i,
    output logic        full_o,
    output logic        empty_o,
    output logic        tx_bit_o
);

  logic [ 7:0] data;
  logic [ 9:0] frame;
  logic [ 3:0] bit_counter;
  logic [15:0] baud_counter;
  logic        baud_clk;
  logic        rd_en;

  enum logic [1:0] {
    IDLE,
    LOAD,
    SENDING
  }
      state, next_state;

  wbit_fifo #(
      .DATA_WIDTH(DATA_WIDTH),
      .FIFO_DEPTH(FIFO_DEPTH)
  ) i_tx_buffer (
      .clk       (clk_i),
      .rst       (!rst_ni),
      .write_en  (tx_we_i),
      .read_en   (rd_en),
      .write_data(din_i),
      .read_data (data),
      .full      (full_o),
      .empty     (empty_o)
  );

  always_comb begin
    next_state = state;
    case (state)
      IDLE:    if (!empty_o && tx_en_i) next_state = LOAD;
      LOAD:    next_state = SENDING;
      SENDING: if (bit_counter == 4'd9) next_state = (!empty_o && tx_en_i) ? LOAD : IDLE;
      default: next_state = IDLE;
    endcase
    frame = {1'b1, data, 1'b0};
    tx_bit_o = (state == SENDING) ? frame[bit_counter] : 1'b1;
    rd_en = (state == LOAD);
  end

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      state        <= IDLE;
      baud_clk     <= 1'b0;
      baud_counter <= 16'd0;
      bit_counter  <= 4'd0;
    end else begin
      // If beginning of packet look bit counter to go load state, else change state with baud clk
      if (baud_clk || (bit_counter == 4'b0)) state <= next_state;
      // Baud clk generator
      if (tx_en_i) begin
        if (baud_counter == baud_div_i - 16'b1) begin
          baud_counter <= 16'd0;
          baud_clk     <= 1'b1;
        end else begin
          baud_counter <= baud_counter + 16'b1;
          baud_clk     <= 1'b0;
        end
      end else begin
        baud_counter <= 16'd0;
        baud_clk <= 1'b0;
      end
      // Bit counter
      if (baud_clk) begin
        bit_counter <= (state == SENDING && bit_counter != 4'd9) ? bit_counter + 4'b1 : 4'd0;
      end
    end
  end

  // ============================================================================
  // UART OUTPUT FILE LOGGER
  // Logs each character written to UART TX to a file (uart_output.log)
  // Enable with: +define+LOG_UART
  // ============================================================================

`ifdef LOG_UART
  integer uart_fd;
  string  uart_log_path;

  initial begin
    // Path can be passed at runtime with +uart_log_path=<path>
    if (!$value$plusargs("uart_log_path=%s", uart_log_path)) begin
      uart_log_path = "uart_output.log";  // Default: current directory
    end
    uart_fd = $fopen(uart_log_path, "w");
    if (uart_fd == 0) begin
      $display("[UART_TX] Warning: Could not open %s for writing", uart_log_path);
    end else begin
      $display("[UART_TX] Logging UART output to: %s", uart_log_path);
    end
  end

  always_ff @(posedge clk_i) begin
    if (rst_ni && tx_we_i && !full_o && uart_fd != 0) begin
      // Write each character to the file (with flush)
      $fwrite(uart_fd, "%c", din_i);
      $fflush(uart_fd);
    end
  end

  final begin
    if (uart_fd != 0) begin
      $fclose(uart_fd);
    end
  end
`endif  // LOG_UART

  // ============================================================================
  // SIMULATION MONITORING BLOCK (Optional - UART substring → $finish)
  //
  // CoreMark `portable_fini` ends with an infinite loop, so without this the
  // testbench runs until MAX_CYCLES.  We stop after a configurable TX substring
  // match (default catches the final banner after all scores / CRC lines).
  //
  // Enable RTL: +define+SIM_UART_MONITOR
  // Optional:   +uart_finish_pattern=CoreMark Complete!
  //             (override if you want an earlier stop, e.g. after "Iterations/Sec")
  // ============================================================================

`ifdef SIM_UART_MONITOR
  localparam int unsigned UART_FINISH_BUF_MAX = 96;

  logic [7:0]               finish_buf[UART_FINISH_BUF_MAX];
  int unsigned              finish_len;
  int unsigned              finish_match_pos;

  initial begin
    string pat;
    int    k;
    finish_len       = 0;
    finish_match_pos = 0;
    if (!$value$plusargs("uart_finish_pattern=%s", pat) || pat.len() == 0) begin
      pat = "CoreMark Complete!";
    end
    if (pat.len() > UART_FINISH_BUF_MAX) begin
      $display("[UART_TX] SIM_UART_MONITOR: pattern too long (%0d), truncating to %0d", pat.len(),
               UART_FINISH_BUF_MAX);
      finish_len = UART_FINISH_BUF_MAX;
    end else begin
      finish_len = pat.len();
    end
    for (k = 0; k < finish_len; k++) begin
      finish_buf[k] = pat.getc(k);
    end
    $display("[UART_TX] SIM_UART_MONITOR: stop after TX sees %0d-byte pattern (first chars: %s...)",
             finish_len, pat.substr(0, (pat.len() > 8) ? 7 : pat.len() - 1));
  end

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      finish_match_pos <= 0;
    end else if (tx_we_i && !full_o && finish_len > 0) begin
      if (din_i == finish_buf[finish_match_pos]) begin
        finish_match_pos <= finish_match_pos + 1;
        if (finish_match_pos + 1 >= finish_len) begin
          $display("[UART_TX] SIM_UART_MONITOR: matched — $finish (simulation stopped after UART marker)");
          $finish(0);
        end
      end else begin
        finish_match_pos <= (din_i == finish_buf[0]) ? 1 : 0;
      end
    end
  end
`endif  // SIM_UART_MONITOR

endmodule
