`timescale 1ns / 1ps
module tb_wrapper;
  logic clk_i = 0;
  logic rst_ni = 0;
  logic program_rx_i = 1;
  logic uart_rx_i = 1;
  logic prog_mode_led_o;
  logic uart_tx_o;

  ceres_wrapper ceres_wrapper (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .program_rx_i   (program_rx_i),
      .prog_mode_led_o(prog_mode_led_o),
      .uart_tx_o      (uart_tx_o),
      .uart_rx_i      (uart_rx_i)
  );

  initial begin
    rst_ni       <= 0;
    program_rx_i <= 1;
    uart_rx_i    <= 1;
    #10;
    rst_ni <= 1;
  end

  always #5 clk_i = !clk_i;


endmodule
