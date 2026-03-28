`timescale 1ns / 1ps

// FPGA top for Basys3 (and similar): clocks the SoC from clk_wiz in synthesis,
// passes through clk_i in simulation.
module systessis_wrapper
  import level_param::*;
#(
    parameter int unsigned CLK_FREQ_HZ = CPU_CLK,
    parameter int unsigned BAUD_RATE   = 115200,
    // Enable flags for synthesis (sim usually uses default wrapper params;
    // use Verilator -G… if needed).
    parameter bit          FPGA_GPIO_EN = 1'b1,
    parameter bit          FPGA_VGA_EN  = 1'b1,
    parameter bit          FPGA_TIMER_EN = 1'b1
) (
    input logic clk_i,
    input logic rst_ni,

    output logic uart0_tx_o,
    input  logic uart0_rx_i,

    // Switches SW15..SW1 (15 bits). SW0 (V17) is reserved for rst_ni / bringup.
    input logic [14:0] gpio_sw_i,
    // LEDs: gpio_o[15:5] -> led[15:5], gpio_o[3:0] -> led[3:0]. gpio_o[4] is
    // routed to gpio_led4_aux_o (e.g. Pmod) because W18 drives prog_mode_o.
    output logic [15:0] gpio_led_o,
    output logic        gpio_led4_aux_o,

    output logic       vga_hsync_o,
    output logic       vga_vsync_o,
    output logic [3:0] vga_r_o,
    output logic [3:0] vga_g_o,
    output logic [3:0] vga_b_o,

    // I2C pads (tie-offs inside level_wrapper when I2C_EN=0).
    inout wire i2c0_sda_io,
    inout wire i2c0_scl_io,

    input  logic prog_rx_i,
    output logic prog_mode_o
);

  logic clk_sys;

`ifdef SYNTHESIS
  logic locked;
  clk_wiz_0 clk_generator (
      .clk_out1(clk_sys),
      .reset   (~rst_ni),
      .locked  (locked),
      .clk_in1 (clk_i)
  );
`else
  assign clk_sys = clk_i;
`endif

  wire [31:0] gpio_i_w = {17'b0, gpio_sw_i};

  wire        uart1_tx_nc;
  wire        spi0_sclk_nc;
  wire        spi0_mosi_nc;
  wire [3:0]  spi0_ss_nc;
  wire        uart1_rx_hi = 1'b1;
  wire        spi0_miso_hi = 1'b1;
  wire        pwm_fault_lo = 1'b0;
  wire [7:0]  ext_irq_lo = 8'b0;

  wire [31:0] gpio_o_w;
  wire [31:0] gpio_oe_nc;
  wire [7:0]  pwm_o_nc;
  wire [7:0]  pwm_n_nc;
  wire        wdt_reset_nc;
  wire        cpu_halt_nc;
  wire [3:0]  status_led_nc;

  // LED[4] (W18) is used by prog_mode_o; gpio_o[4] is brought out on gpio_led4_aux_o.
  assign gpio_led_o = {gpio_o_w[15:5], 1'b0, gpio_o_w[3:0]};
  assign gpio_led4_aux_o = gpio_o_w[4];

  level_wrapper #(
      .CLK_FREQ_HZ(CLK_FREQ_HZ),
      .BAUD_RATE  (BAUD_RATE),
      .GPIO_EN    (FPGA_GPIO_EN),
      .VGA_EN     (FPGA_VGA_EN),
      .TIMER_EN   (FPGA_TIMER_EN)
  ) u_level_wrapper (
      .clk_i (clk_sys),
      .rst_ni(rst_ni),

      .uart0_tx_o(uart0_tx_o),
      .uart0_rx_i(uart0_rx_i),
      .uart1_tx_o(uart1_tx_nc),
      .uart1_rx_i(uart1_rx_hi),

      .spi0_sclk_o(spi0_sclk_nc),
      .spi0_mosi_o(spi0_mosi_nc),
      .spi0_miso_i(spi0_miso_hi),
      .spi0_ss_o  (spi0_ss_nc),

      .i2c0_sda_io(i2c0_sda_io),
      .i2c0_scl_io(i2c0_scl_io),

      .gpio_i   (gpio_i_w),
      .gpio_o   (gpio_o_w),
      .gpio_oe_o(gpio_oe_nc),

      .pwm_o      (pwm_o_nc),
      .pwm_n_o    (pwm_n_nc),
      .pwm_fault_i(pwm_fault_lo),

      .wdt_reset_o(wdt_reset_nc),

      .vga_hsync_o(vga_hsync_o),
      .vga_vsync_o(vga_vsync_o),
      .vga_r_o    (vga_r_o),
      .vga_g_o    (vga_g_o),
      .vga_b_o    (vga_b_o),

      .ext_irq_i(ext_irq_lo),

      .prog_rx_i  (prog_rx_i),
      .prog_mode_o(prog_mode_o),

      .cpu_halt_o  (cpu_halt_nc),
      .status_led_o(status_led_nc)
  );

endmodule
