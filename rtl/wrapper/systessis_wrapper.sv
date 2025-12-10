`timescale 1ns / 1ps

module systessis_wrapper
  import ceres_param::*;
#(
    parameter int unsigned CLK_FREQ_HZ = CPU_CLK,
    parameter int unsigned BAUD_RATE   = 115200
) (
    // Clock / Reset
    input logic clk_i,
    input logic rst_ni,

    // UART
    output logic uart0_tx_o,
    input  logic uart0_rx_i,
    /*
    output logic uart1_tx_o,
    input  logic uart1_rx_i,

    // SPI
    output logic       spi0_sclk_o,
    output logic       spi0_mosi_o,
    input  logic       spi0_miso_i,
    output logic [3:0] spi0_ss_o,

    // I2C
    inout wire i2c0_sda_io,
    inout wire i2c0_scl_io,

    // GPIO
    input  logic [31:0] gpio_i,
    output logic [31:0] gpio_o,
    output logic [31:0] gpio_oe_o,

    // PWM
    output logic [7:0] pwm_o,
    output logic [7:0] pwm_n_o,
    input  logic       pwm_fault_i,

    // Watchdog
    output logic wdt_reset_o,

    // VGA
    output logic       vga_hsync_o,
    output logic       vga_vsync_o,
    output logic [3:0] vga_r_o,
    output logic [3:0] vga_g_o,
    output logic [3:0] vga_b_o,

    // External interrupts
    input logic [7:0] ext_irq_i,
*/
    // Programming
    input  logic prog_rx_i,
    output logic prog_mode_o

    // Debug / Status
    //output logic       cpu_halt_o,
    //output logic [3:0] status_led_o
);

  logic clk_out1;
  logic locked;

`ifdef SYNTHESIS
  clk_wiz_0 clk_generator (
      // Clock out ports  
      .clk_out1(clk_out1),
      // Status and control signals               
      .reset   (~rst_ni),
      .locked  (locked),
      // Clock in ports
      .clk_in1 (clk_i)
  );
`endif

  // Instantiate the real wrapper
  ceres_wrapper #(
      .CLK_FREQ_HZ(CLK_FREQ_HZ),
      .BAUD_RATE  (BAUD_RATE)
  ) u_ceres_wrapper (
      .clk_i (clk_out1),
      .rst_ni(rst_ni),

      .uart0_tx_o(uart0_tx_o),
      .uart0_rx_i(uart0_rx_i),
      .uart1_tx_o(uart1_tx_o),
      .uart1_rx_i(uart1_rx_i),

      .spi0_sclk_o(spi0_sclk_o),
      .spi0_mosi_o(spi0_mosi_o),
      .spi0_miso_i(spi0_miso_i),
      .spi0_ss_o  (spi0_ss_o),

      .i2c0_sda_io(i2c0_sda_io),
      .i2c0_scl_io(i2c0_scl_io),

      .gpio_i   (gpio_i),
      .gpio_o   (gpio_o),
      .gpio_oe_o(gpio_oe_o),

      .pwm_o      (pwm_o),
      .pwm_n_o    (pwm_n_o),
      .pwm_fault_i(pwm_fault_i),

      .wdt_reset_o(wdt_reset_o),

      .vga_hsync_o(vga_hsync_o),
      .vga_vsync_o(vga_vsync_o),
      .vga_r_o    (vga_r_o),
      .vga_g_o    (vga_g_o),
      .vga_b_o    (vga_b_o),

      .ext_irq_i(ext_irq_i),

      .prog_rx_i  (prog_rx_i),
      .prog_mode_o(prog_mode_o),

      .cpu_halt_o  (cpu_halt_o),
      .status_led_o(status_led_o)
  );

endmodule
