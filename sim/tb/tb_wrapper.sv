`timescale 1ns / 1ps
`include "level_defines.svh"

module tb_wrapper;
  import level_param::*;
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

    level_wrapper level_wrapper (
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

  // Debug: make run_verilator RTL_PRINT_CFG=1  or  binary ... +print_rtl_cfg
  initial begin
    if ($test$plusargs("print_rtl_cfg")) begin
      $display("");
      $display("================================================================");
      $display(" RTL configuration (compiled-in rtl/cfg pack + defines)");
      $display("----------------------------------------------------------------");
      $display("  rtl/cfg profile : %0s", RTL_CFG_PROFILE_NAME);
      $display("  CPU_CLK_Hz      : %0d", CPU_CLK);
      `ifdef MINIMAL_SOC
      $display("  MINIMAL_SOC     : 1");
      `else
      $display("  MINIMAL_SOC     : 0");
      `endif
      `ifdef LEVEL_OPENLANE
      $display("  LEVEL_OPENLANE  : 1");
      `else
      $display("  LEVEL_OPENLANE  : 0");
      `endif
      `ifdef USE_L2_CACHE
      $display("  USE_L2_CACHE    : 1");
      `else
      $display("  USE_L2_CACHE    : 0");
      `endif
      `ifdef NO_L2_CACHE
      $display("  NO_L2_CACHE     : 1");
      `else
      $display("  NO_L2_CACHE     : 0");
      `endif
      $display("----------------------------------------------------------------");
      $display("  WRAPPER_RAM_KiB : %0d", WRAPPER_RAM_SIZE_KB);
      $display("  I$              : %0d-way, %0d KiB (blk %0d B)",
               IC_WAY, IC_CAPACITY / (8 * 1024), BLK_SIZE / 8);
      $display("  D$              : %0d-way, %0d KiB, MSHR %0d, banks %0d",
               DC_WAY, DC_CAPACITY / (8 * 1024), DC_MSHR_DEPTH, DC_NUM_BANK);
      $display("  L2              : %0d KiB, %0d-way, MSHR %0d, banks %0d",
               L2_CACHE_SIZE_KB, L2_NUM_WAY, L2_MSHR_DEPTH, L2_NUM_BANKS);
      $display("  BP              : PHT %0d, BTB %0d, GHR %0d, RAS %0d",
               PHT_SIZE, BTB_SIZE, GHR_SIZE, RAS_SIZE);
      $display("  UART FIFO       : TX %0d, RX %0d", UART_TX_FIFO_DEPTH,
               UART_RX_FIFO_DEPTH);
      $display("  align buffer    : size %0d, way %0d", ABUFF_SIZE, ABUFF_WAY);
      $display("  prefetch        : type %0d deg %0d | stride_tbl %0d bits %0d streams %0d",
               PREFETCH_TYPE, PREFETCH_DEGREE, STRIDE_TABLE_SIZE, STRIDE_BITS,
               NUM_STREAMS);
      $display("  store buffer    : depth %0d (PTR_W %0d)", SB_DEPTH, SB_PTR_W);
      $display("  BP log interval : %0d", BP_LOG_INTERVAL);
      $display("================================================================");
      $display("");
    end
  end

  initial begin
    rst_ni       <= 0;
    prog_rx_i    <= 1;
    uart0_rx_i   <= 1;
    #10;
    rst_ni <= 1;
  end

  always #5 clk_i = !clk_i;


endmodule
