/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
module uart_tx
  import ceres_param::*;
#(
    parameter DATA_WIDTH = ceres_param::UART_DATA_WIDTH,
    parameter FIFO_DEPTH = ceres_param::UART_TX_FIFO_DEPTH
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
    // Runtime'da +uart_log_path=<path> ile path geçilebilir
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
      // Her karakter geldiğinde dosyaya yaz (flush ile)
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
  // SIMULATION MONITORING BLOCK (Optional - for threshold-based termination)
  // Dumps UART TX buffer contents as ASCII and stops simulation when threshold met
  // Enable with: +define+SIM_UART_MONITOR
  // ============================================================================

endmodule
