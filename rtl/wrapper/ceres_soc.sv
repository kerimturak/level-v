/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  CERES RISC-V SoC Top-Level Wrapper
  
  This is a modular, extensible SoC wrapper designed for future expansion.
  It includes:
    - Standardized memory map
    - Peripheral bus infrastructure  
    - Interrupt controller integration points
    - Debug interface ready
    - Configurable peripherals via parameters

  Memory Map:
    0x2000_0000 : Peripherals (UART, SPI, I2C, GPIO, Timer, etc.)
    0x3000_0000 : CLINT (mtime, mtimecmp)
    0x8000_0000 : Main RAM

  Future Extensions:
    - PLIC (Platform-Level Interrupt Controller)
    - DMA controller
    - VGA/HDMI controller
    - Ethernet MAC
    - External memory controller (DDR, QSPI Flash)
*/
`timescale 1ns / 1ps

module ceres_soc
  import ceres_param::*;
#(
    // ========================================================================
    // System Configuration
    // ========================================================================
    parameter int unsigned CLK_FREQ_HZ = CPU_CLK,
    parameter int unsigned BAUD_RATE   = 115200,

    // ========================================================================
    // Memory Configuration
    // ========================================================================
    parameter int unsigned RAM_SIZE_KB     = 128,
    parameter int unsigned RAM_LATENCY     = 16,
    parameter bit          BOOTROM_EN      = 1'b0,
    parameter int unsigned BOOTROM_SIZE_KB = 4,

    // ========================================================================
    // Peripheral Configuration
    // ========================================================================
    parameter int unsigned NUM_UART = 1,
    parameter bit          SPI_EN   = 1'b0,
    parameter bit          I2C_EN   = 1'b0,
    parameter bit          GPIO_EN  = 1'b0,
    parameter bit          PWM_EN   = 1'b0,
    parameter bit          TIMER_EN = 1'b1,
    parameter bit          PLIC_EN  = 1'b0,

    // ========================================================================
    // Debug Configuration
    // ========================================================================
    parameter bit DEBUG_EN = 1'b0,
    parameter bit JTAG_EN  = 1'b0,

    // ========================================================================
    // Programming Interface
    // ========================================================================
    parameter string PROG_SEQUENCE = PROGRAM_SEQUENCE
) (
    // ========================================================================
    // Clock and Reset
    // ========================================================================
    input logic clk_i,
    input logic rst_ni,

    // ========================================================================
    // UART Interface
    // ========================================================================
    output logic uart0_tx_o,
    input  logic uart0_rx_i,
    output logic uart1_tx_o,
    input  logic uart1_rx_i,

    // ========================================================================
    // SPI Interface
    // ========================================================================
    output logic       spi0_sclk_o,
    output logic       spi0_mosi_o,
    input  logic       spi0_miso_i,
    output logic [3:0] spi0_ss_o,

    // ========================================================================
    // I2C Interface
    // ========================================================================
    inout wire i2c0_sda_io,
    inout wire i2c0_scl_io,

    // ========================================================================
    // GPIO Interface
    // ========================================================================
    input  logic [31:0] gpio_i,
    output logic [31:0] gpio_o,
    output logic [31:0] gpio_oe_o,

    // ========================================================================
    // External Interrupts
    // ========================================================================
    input logic [7:0] ext_irq_i,

    // ========================================================================
    // Programming Interface
    // ========================================================================
    input  logic prog_rx_i,
    output logic prog_mode_o,

    // ========================================================================
    // Debug/Status
    // ========================================================================
    output logic       cpu_halt_o,
    output logic [3:0] status_led_o
);

  // ==========================================================================
  // Local Parameters
  // ==========================================================================
  localparam int RAM_DEPTH = (RAM_SIZE_KB * 1024) / 4;
  localparam int CACHE_LINE_W = BLK_SIZE;
  localparam int WORDS_PER_LINE = CACHE_LINE_W / 32;

  // Address decode masks
  localparam logic [31:0] PERIPH_MASK = 32'hF000_0000;
  localparam logic [31:0] RAM_MASK = 32'h8000_0000;
  localparam logic [31:0] CLINT_MASK = 32'hF000_0000;

  // ==========================================================================
  // Internal Signals
  // ==========================================================================

  // CPU <-> Memory Interface
  iomem_req_t                         cpu_mem_req;
  iomem_res_t                         cpu_mem_res;

  // Address Decode Signals
  logic                               sel_ram;
  logic                               sel_clint;
  logic                               sel_periph;
  logic                               sel_uart0;
  logic                               sel_uart1;
  logic                               sel_spi0;
  logic                               sel_i2c0;
  logic                               sel_gpio;
  logic                               sel_pwm;
  logic                               sel_timer;
  logic                               sel_plic;

  // RAM Signals
  logic       [     CACHE_LINE_W-1:0] ram_rdata;
  logic       [   CACHE_LINE_W/8-1:0] ram_wstrb;
  logic                               ram_rd_en;
  logic       [$clog2(RAM_DEPTH)-1:0] ram_addr;
  logic       [      RAM_LATENCY-1:0] ram_delay_q;
  logic                               ram_valid;

  // CLINT Signals
  logic       [                 63:0] mtime;
  logic       [                 63:0] mtimecmp;
  logic                               timer_irq;
  logic                               sw_irq;

  // Reset Management
  logic                               prog_reset;
  logic                               sys_rst_n;

  // Response Mux
  iomem_res_t                         ram_res;
  iomem_res_t                         clint_res;
  iomem_res_t                         periph_res;

  // ==========================================================================
  // Reset Controller
  // ==========================================================================
  assign sys_rst_n = rst_ni & prog_reset;

  // ==========================================================================
  // CPU Core
  // ==========================================================================
  cpu u_cpu (
      .clk_i      (clk_i),
      .rst_ni     (sys_rst_n),
      .iomem_req_o(cpu_mem_req),
      .iomem_res_i(cpu_mem_res),
      .uart_tx_o  (uart0_tx_o),
      .uart_rx_i  (uart0_rx_i)
  );

  // ==========================================================================
  // Address Decoder
  // ==========================================================================
  always_comb begin
    // Default: nothing selected
    sel_ram    = 1'b0;
    sel_clint  = 1'b0;
    sel_periph = 1'b0;
    sel_uart0  = 1'b0;
    sel_uart1  = 1'b0;
    sel_spi0   = 1'b0;
    sel_i2c0   = 1'b0;
    sel_gpio   = 1'b0;
    sel_pwm    = 1'b0;
    sel_timer  = 1'b0;
    sel_plic   = 1'b0;

    if (cpu_mem_req.valid) begin
      // RAM: 0x8000_0000 - 0xFFFF_FFFF
      if ((cpu_mem_req.addr & RAM_MASK) == MMAP_RAM_BASE) begin
        sel_ram = 1'b1;
      end  // CLINT: 0x3000_0000 - 0x3FFF_FFFF
      else if ((cpu_mem_req.addr & CLINT_MASK) == MMAP_CLINT_BASE) begin
        sel_clint = 1'b1;
      end  // Peripherals: 0x2000_0000 - 0x2FFF_FFFF
      else if ((cpu_mem_req.addr & PERIPH_MASK) == MMAP_PERIPH_BASE) begin
        sel_periph = 1'b1;

        // Decode peripheral slot (12-bit offset, 4KB slots)
        case (cpu_mem_req.addr[15:12])
          4'h0:    sel_uart0 = (NUM_UART >= 1);
          4'h1:    sel_uart1 = (NUM_UART >= 2);
          4'h2:    sel_spi0 = SPI_EN;
          4'h3:    sel_i2c0 = I2C_EN;
          4'h4:    sel_gpio = GPIO_EN;
          4'h5:    sel_pwm = PWM_EN;
          4'h6:    sel_timer = TIMER_EN;
          4'h7:    sel_plic = PLIC_EN;
          default: ;  // No peripheral
        endcase
      end
    end
  end

  // ==========================================================================
  // Main RAM
  // ==========================================================================

  // Word address extraction
  assign ram_addr  = cpu_mem_req.addr[2+$clog2(RAM_DEPTH)-1 : 2];

  // Write strobes (only for RAM accesses)
  assign ram_wstrb = sel_ram ? cpu_mem_req.rw : '0;

  // Read enable
  assign ram_rd_en = sel_ram & ~(|cpu_mem_req.rw);

  wrapper_ram #(
      .WORD_WIDTH      (32),
      .RAM_DEPTH       (RAM_DEPTH),
      .CACHE_LINE_WIDTH(CACHE_LINE_W),
      .CPU_CLK         (CLK_FREQ_HZ),
      .PROG_BAUD_RATE  (BAUD_RATE),
      .PROGRAM_SEQUENCE(PROG_SEQUENCE)
  ) u_main_ram (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .addr_i         (ram_addr),
      .wdata_i        (cpu_mem_req.data),
      .wstrb_i        (ram_wstrb),
      .rdata_o        (ram_rdata),
      .rd_en_i        (ram_rd_en),
      .ram_prog_rx_i  (prog_rx_i),
      .system_reset_o (prog_reset),
      .prog_mode_led_o(prog_mode_o)
  );

  // RAM Response with latency
  logic ram_pending_q;
  logic ram_responded;

  assign ram_responded = sel_ram & ram_delay_q[RAM_LATENCY-1];

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ram_delay_q   <= '0;
      ram_pending_q <= 1'b0;
    end else begin
      if (ram_responded) begin
        ram_delay_q <= '0;
      end else begin
        ram_delay_q <= {ram_delay_q[RAM_LATENCY-2:0], ram_pending_q};
      end

      ram_pending_q <= sel_ram & ~ram_responded;
    end
  end

  assign ram_res.valid = ram_delay_q[RAM_LATENCY-1];
  assign ram_res.ready = 1'b1;
  assign ram_res.data  = ram_rdata;

  // ==========================================================================
  // CLINT (Core-Local Interruptor)
  // ==========================================================================
  // Provides mtime and mtimecmp registers for timer interrupts

  always_ff @(posedge clk_i or negedge sys_rst_n) begin
    if (!sys_rst_n) begin
      mtime    <= 64'h0;
      mtimecmp <= 64'hFFFF_FFFF_FFFF_FFFF;
      sw_irq   <= 1'b0;
    end else begin
      // Increment mtime every cycle
      mtime <= mtime + 64'h1;

      // CLINT register writes
      if (sel_clint && (|cpu_mem_req.rw)) begin
        case (cpu_mem_req.addr[15:0])
          CLINT_MSIP_OFF:         sw_irq <= cpu_mem_req.data[0];
          CLINT_MTIMECMP_OFF:     mtimecmp[31:0] <= cpu_mem_req.data[31:0];
          CLINT_MTIMECMP_OFF + 4: mtimecmp[63:32] <= cpu_mem_req.data[31:0];
          CLINT_MTIME_OFF:        mtime[31:0] <= cpu_mem_req.data[31:0];
          CLINT_MTIME_OFF + 4:    mtime[63:32] <= cpu_mem_req.data[31:0];
          default:                ;
        endcase
      end
    end
  end

  // Timer interrupt: fires when mtime >= mtimecmp
  assign timer_irq = (mtime >= mtimecmp);

  // CLINT Response (immediate, no latency)
  always_comb begin
    clint_res.valid = sel_clint;
    clint_res.ready = 1'b1;
    clint_res.data  = '0;

    if (sel_clint) begin
      case (cpu_mem_req.addr[15:0])
        CLINT_MSIP_OFF:         clint_res.data = {96'b0, 31'b0, sw_irq};
        CLINT_MTIMECMP_OFF:     clint_res.data = {96'b0, mtimecmp[31:0]};
        CLINT_MTIMECMP_OFF + 4: clint_res.data = {96'b0, mtimecmp[63:32]};
        CLINT_MTIME_OFF:        clint_res.data = {96'b0, mtime[31:0]};
        CLINT_MTIME_OFF + 4:    clint_res.data = {96'b0, mtime[63:32]};
        default:                clint_res.data = '0;
      endcase
    end
  end

  // ==========================================================================
  // Peripheral Response (placeholder for future peripherals)
  // ==========================================================================
  assign periph_res.valid = sel_periph;
  assign periph_res.ready = 1'b1;
  assign periph_res.data  = '0;

  // ==========================================================================
  // Response Multiplexer
  // ==========================================================================
  always_comb begin
    cpu_mem_res.valid = 1'b0;
    cpu_mem_res.ready = 1'b1;
    cpu_mem_res.data  = '0;

    if (sel_ram) begin
      cpu_mem_res = ram_res;
    end else if (sel_clint) begin
      cpu_mem_res = clint_res;
    end else if (sel_periph) begin
      cpu_mem_res = periph_res;
    end
  end

  // ==========================================================================
  // Unused Peripheral Outputs
  // ==========================================================================

  // UART1 - tied off if not enabled
  generate
    if (NUM_UART < 2) begin : gen_no_uart1
      assign uart1_tx_o = 1'b1;  // Idle high
    end
  endgenerate

  // SPI - disabled
  generate
    if (!SPI_EN) begin : gen_no_spi
      assign spi0_sclk_o = 1'b0;
      assign spi0_mosi_o = 1'b0;
      assign spi0_ss_o   = 4'hF;  // All slaves deselected
    end
  endgenerate

  // GPIO - disabled
  generate
    if (!GPIO_EN) begin : gen_no_gpio
      assign gpio_o    = 32'h0;
      assign gpio_oe_o = 32'h0;  // All inputs
    end
  endgenerate

  // Status outputs
  assign cpu_halt_o   = 1'b0;  // TODO: Connect to debug module
  assign status_led_o = {3'b0, prog_mode_o};

endmodule
