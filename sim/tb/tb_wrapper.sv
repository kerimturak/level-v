`timescale 1ns / 1ps
module tb_wrapper;
  logic        clk_i = 0;
  logic        rst_ni = 0;

  // Programming interface
  logic        prog_rx_i = 1;
  logic        prog_mode_o;

  // UARTs
  logic        uart0_tx_o;
  logic        uart0_rx_i = 1;
  logic        uart1_tx_o;
  logic        uart1_rx_i = 1;

  // SPI
  logic        spi0_sclk_o;
  logic        spi0_mosi_o;
  logic        spi0_miso_i;
  logic [ 3:0] spi0_ss_o;
  wire         i2c0_sda_io;
  wire         i2c0_scl_io;

  // PWM / Watchdog / VGA / CPU status
  logic [7:0]  pwm_o;
  logic [7:0]  pwm_n_o;
  logic        pwm_fault_i = 0;
  logic        wdt_reset_o;
  logic        vga_hsync_o;
  logic        vga_vsync_o;
  logic [3:0]  vga_r_o;
  logic [3:0]  vga_g_o;
  logic [3:0]  vga_b_o;
  logic        cpu_halt_o;
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
      .uart0_tx_o     (uart0_tx_o),
      .uart0_rx_i     (uart0_rx_i),
      .uart1_tx_o     (uart1_tx_o),
      .uart1_rx_i     (uart1_rx_i),
      .spi0_sclk_o    (spi0_sclk_o),
      .spi0_mosi_o    (spi0_mosi_o),
      .spi0_miso_i    (spi0_miso_i),
      .spi0_ss_o      (spi0_ss_o),
      .i2c0_sda_io    (i2c0_sda_io),
      .i2c0_scl_io    (i2c0_scl_io),
      .gpio_i         (gpio_i),
      .gpio_o         (gpio_o),
      .gpio_oe_o      (gpio_oe_o),
      .pwm_o          (pwm_o),
      .pwm_n_o        (pwm_n_o),
      .pwm_fault_i    (pwm_fault_i),
      .wdt_reset_o    (wdt_reset_o),
      .vga_hsync_o    (vga_hsync_o),
      .vga_vsync_o    (vga_vsync_o),
      .vga_r_o        (vga_r_o),
      .vga_g_o        (vga_g_o),
      .vga_b_o        (vga_b_o),
      .ext_irq_i      (ext_irq_i),
      .prog_rx_i      (prog_rx_i),
      .prog_mode_o    (prog_mode_o),
      .cpu_halt_o     (cpu_halt_o),
      .status_led_o   (status_led_o)
    );

  // SPI Loopback: Connect MOSI to MISO for testing
  assign spi0_miso_i = spi0_mosi_o;

  initial begin
    rst_ni       <= 0;
    prog_rx_i    <= 1;
    uart0_rx_i   <= 1;
    #10;
    rst_ni <= 1;
  end

  always #5 clk_i = !clk_i;


endmodule
