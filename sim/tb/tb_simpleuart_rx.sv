`timescale 1ns / 1ps
/* Minimal top: PicoRV32 simpleuart RX only — C++ drives ser_rx; byte reads via reg_dat_re */
module tb_simpleuart_rx (
    input wire         clk_i,
    input wire         rst_ni,
    input wire         ser_rx_i,
    input wire         reg_dat_re_i,
    output wire [31:0] reg_dat_do_o
);
  simpleuart #(
      .DEFAULT_DIV(25000000 / 115200)
  ) u (
      .clk      (clk_i),
      .resetn   (rst_ni),
      .ser_tx   (),
      .ser_rx   (ser_rx_i),
      .reg_div_we(4'h0),
      .reg_div_di(32'b0),
      .reg_div_do(),
      .reg_dat_we(1'b0),
      .reg_dat_re(reg_dat_re_i),
      .reg_dat_di(32'b0),
      .reg_dat_do(reg_dat_do_o)
  );
endmodule
