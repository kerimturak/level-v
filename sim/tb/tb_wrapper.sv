`timescale 1ns / 1ps
module tb_wrapper;
  logic        clk_i = 0;
  logic        rst_ni = 0;
  logic        program_rx_i = 1;
  logic        uart_rx_i = 1;
  logic        prog_mode_led_o;
  logic        uart_tx_o;
  logic        spi0_sclk_o;
  logic        spi0_mosi_o;
  logic        spi0_miso_i;
  logic [ 3:0] spi0_ss_o;
  wire         i2c0_sda_io;
  wire         i2c0_scl_io;
  // GPIO Interface (active when GPIO_EN=1)
  logic [31:0] gpio_i;
  logic [31:0] gpio_o;
  logic [31:0] gpio_oe_o;
  // External Interrupts
  logic [ 7:0] ext_irq_i;
  logic [ 3:0] status_led_o;

  ceres_wrapper ceres_wrapper (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .program_rx_i   (program_rx_i),
      .prog_mode_led_o(prog_mode_led_o),
      .uart_tx_o      (uart_tx_o),
      .uart_rx_i      (uart_rx_i),
      .spi0_sclk_o    (spi0_sclk_o),
      .spi0_mosi_o    (spi0_mosi_o),
      .spi0_miso_i    (spi0_miso_i),
      .spi0_ss_o      (spi0_ss_o),
      .i2c0_sda_io    (i2c0_sda_io),
      .i2c0_scl_io    (i2c0_scl_io),
      .gpio_i         (gpio_i),
      .gpio_o         (gpio_o),
      .gpio_oe_o      (gpio_oe_o),
      .ext_irq_i      (ext_irq_i),
      .status_led_o   (status_led_o)
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
