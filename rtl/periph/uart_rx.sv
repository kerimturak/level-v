/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
module uart_rx #(  // counter
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 32
) (
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic [15:0] baud_div_i,
    input  logic        rx_re_i,
    input  logic        rx_en_i,
    output logic [ 7:0] dout_o,
    output logic        full_o,
    output logic        empty_o,
    input  logic        rx_bit_i
);

  logic        rx_bit_new;
  logic        rx_bit_old;
  logic [15:0] baud_counter;
  logic        baud_clk;
  logic [ 3:0] bit_counter;
  logic        rx_we;
  logic [ 7:0] data;

  enum logic {
    IDLE,
    SAMPLING
  }
      state, next_state;

  wbit_fifo #(
      .DATA_WIDTH(DATA_WIDTH),
      .FIFO_DEPTH(FIFO_DEPTH)
  ) i_rx_buffer (
      .clk       (clk_i),
      .rst       (!rst_ni),
      .write_en  (rx_we),
      .read_en   (rx_re_i),
      .write_data(data),
      .read_data (dout_o),
      .full      (full_o),
      .empty     (empty_o)
  );

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      state        <= IDLE;
      baud_clk     <= 1'b0;
      baud_counter <= 16'b0;
      bit_counter  <= 4'b0;
      rx_bit_old   <= 1'b1;
      rx_bit_new   <= 1'b1;
    end else begin
      if (baud_clk) begin
        if (state == SAMPLING || bit_counter == 4'b0) begin
          data[bit_counter[2:0]] <= rx_bit_i;
        end
        if (rx_en_i) begin
          rx_bit_old <= rx_bit_new;
          rx_bit_new <= rx_bit_i;
        end
      end
      if (baud_clk || (bit_counter == 4'b0)) state <= next_state;
      rx_we <= baud_clk && state == SAMPLING && bit_counter == 4'd7 ? 1'b1 : 1'b0;
      // Baud clk generator
      if (rx_en_i) begin
        if (baud_counter == baud_div_i - 16'b1) begin
          baud_counter <= 16'b0;
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
        bit_counter <= (state == SAMPLING && bit_counter != 4'd7) ? bit_counter + 4'b1 : 4'd0;
      end
    end
  end

  always_comb begin
    next_state = state;
    case (state)
      IDLE:     if (rx_bit_old && !rx_bit_new && !full_o) next_state = SAMPLING;
      SAMPLING: if (bit_counter == 4'd7) next_state = IDLE;
    endcase
  end

endmodule
