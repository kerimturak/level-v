/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
module uart
  import ceres_param::*;
(
    input  logic            clk_i,
    input  logic            rst_ni,
    input  logic            stb_i,
    input  logic [     1:0] adr_i,
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,
    input  logic            uart_rx_i,
    output logic            uart_tx_o
);

  logic [15:0] baud_div;
  logic        tx_en;
  logic        tx_full;
  logic        tx_empty;
  logic        tx_we;
  logic        rx_en;
  logic [ 7:0] dout;
  logic        rx_full;
  logic        rx_empty;
  logic        rx_re;
  logic [ 7:0] tx_data;

  // Select correct byte based on byte_sel
  // For UART, always use the lowest byte (dat_i[7:0]) regardless of byte_sel
  // This maintains compatibility with both byte and word writes
  assign tx_data = dat_i[7:0];

  uart_tx i_uart_tx (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .baud_div_i(baud_div),
      .tx_we_i   (tx_we),
      .tx_en_i   (tx_en),
      .din_i     (tx_data),
      .full_o    (tx_full),
      .empty_o   (tx_empty),
      .tx_bit_o  (uart_tx_o)
  );

  uart_rx i_uart_rx (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .baud_div_i(baud_div),
      .rx_re_i   (rx_re),
      .rx_en_i   (rx_en),
      .dout_o    (dout),
      .full_o    (rx_full),
      .empty_o   (rx_empty),
      .rx_bit_i  (uart_rx_i)
  );

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      tx_en    <= 1'b0;
      rx_en    <= 1'b0;
      baud_div <= 16'b0;
    end else if (stb_i && we_i && adr_i == '0) begin
      tx_en    <= byte_sel_i[0] ? dat_i[0] : tx_en;
      rx_en    <= byte_sel_i[0] ? dat_i[1] : rx_en;
      baud_div <= (&byte_sel_i[3:2]) ? dat_i[31:16] : baud_div;
    end
  end

  always_comb begin
    tx_we = 0;
    rx_re = 0;
    case (adr_i)
      2'b00: dat_o = {baud_div, 14'b0, rx_en, tx_en};
      2'b01: dat_o = {28'b0, rx_empty, rx_full, tx_empty, tx_full};
      2'b10: begin
        dat_o = {24'b0, dout};
        rx_re = stb_i && ~rx_empty && byte_sel_i[0];
      end
      2'b11: begin
        dat_o = {28'b0, rx_empty, rx_full, tx_empty, tx_full};
        tx_we = stb_i && ~tx_full && we_i && byte_sel_i[0];
      end
    endcase
  end

  always_ff @(posedge clk_i) begin
    if (stb_i && we_i && adr_i == 2'b11) begin
      $display("[%0t] UART_MODULE: stb=%b we=%b adr=%b byte_sel=%b tx_full=%b", $time, stb_i, we_i, adr_i, byte_sel_i, tx_full);
      $display("              dat_i=%h tx_data=%h (from byte_sel)", dat_i, tx_data);
      $display("              tx_we=%b (final enable)", tx_we);
      if (tx_we) begin
        $display("              ✓ TX FIFO WRITE: char='%c' (0x%h)", tx_data, tx_data);
      end else begin
        $display("              ✗ TX BLOCKED: tx_full=%b byte_sel[0]=%b", tx_full, byte_sel_i[0]);
      end
    end
  end

endmodule
