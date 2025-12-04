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
    // MINIMAL_SOC modunda sadece UART ve Timer aktif, diğerleri kapalı
`ifdef MINIMAL_SOC
    parameter int unsigned NUM_UART = 1,
    parameter bit          SPI_EN   = 1'b0,
    parameter bit          I2C_EN   = 1'b0,
    parameter bit          GPIO_EN  = 1'b0,
    parameter bit          PWM_EN   = 1'b0,
    parameter bit          TIMER_EN = 1'b1,
    parameter bit          PLIC_EN  = 1'b0,
    parameter bit          WDT_EN   = 1'b0,
    parameter bit          DMA_EN   = 1'b0,
    parameter bit          VGA_EN   = 1'b0,
`else
    parameter int unsigned NUM_UART = 1,
    parameter bit          SPI_EN   = 1'b0,
    parameter bit          I2C_EN   = 1'b0,
    parameter bit          GPIO_EN  = 1'b0,
    parameter bit          PWM_EN   = 1'b0,
    parameter bit          TIMER_EN = 1'b1,
    parameter bit          PLIC_EN  = 1'b0,
    parameter bit          WDT_EN   = 1'b0,
    parameter bit          DMA_EN   = 1'b0,
    parameter bit          VGA_EN   = 1'b0,
`endif

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
    // PWM Interface
    // ========================================================================
    output logic [7:0] pwm_o,
    output logic [7:0] pwm_n_o,
    input  logic       pwm_fault_i,

    // ========================================================================
    // Watchdog
    // ========================================================================
    output logic wdt_reset_o,

    // ========================================================================
    // VGA Interface
    // ========================================================================
    output logic       vga_hsync_o,
    output logic       vga_vsync_o,
    output logic [3:0] vga_r_o,
    output logic [3:0] vga_g_o,
    output logic [3:0] vga_b_o,

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
  logic                               sel_wdt;
  logic                               sel_dma;
  logic                               sel_vga;

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

  // GPIO Signals
  logic       [                 31:0] gpio_rdata;
  logic                               gpio_irq;

  // PLIC Signals
  logic       [                 31:0] plic_rdata;
  logic       [                 31:0] plic_irq_sources;  // Interrupt sources to PLIC
  logic                               plic_irq;  // External interrupt to CPU

  // Timer Signals
  logic       [                 31:0] timer_rdata;
  logic       [                  7:0] timer_pwm;  // 4 timers * 2 PWM outputs
  logic       [                  3:0] gptimer_irq;  // Per-timer interrupt
  logic                               gptimer_irq_combined;

  // Watchdog Signals
  logic       [                 31:0] wdt_rdata;
  logic                               wdt_irq;
  logic                               wdt_reset;

  // DMA Signals
  logic       [                 31:0] dma_rdata;
  logic       [                  3:0] dma_irq;
  logic                               dma_req;
  logic       [                 31:0] dma_addr;
  logic       [                 31:0] dma_wdata;
  logic       [                  3:0] dma_wstrb;
  logic                               dma_ack;

  // PWM Controller Signals
  logic       [                 31:0] pwm_rdata;
  logic       [                  7:0] pwm_out;
  logic       [                  7:0] pwm_n_out;
  logic                               pwm_irq;
  logic                               pwm_sync;

  // VGA Controller Signals
  logic       [                 31:0] vga_rdata;
  logic                               pixel_clk;
  logic                               pll_locked;

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
  cpu i_cpu (
      .clk_i      (clk_i),
      .rst_ni     (sys_rst_n),
      // Hardware interrupt inputs
      .timer_irq_i(timer_irq),    // CLINT timer interrupt
      .sw_irq_i   (sw_irq),       // CLINT software interrupt
      .ext_irq_i  (plic_irq),     // PLIC external interrupt
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
    sel_wdt    = 1'b0;
    sel_dma    = 1'b0;
    sel_vga    = 1'b0;

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
          4'h8:    sel_wdt = WDT_EN;
          4'h9:    sel_dma = DMA_EN;
          4'hD:    sel_vga = VGA_EN;
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
  // GPIO Controller
  // ==========================================================================
  generate
    if (GPIO_EN) begin : gen_gpio
      gpio #(
          .GPIO_WIDTH(32)
      ) i_gpio (
          .clk_i     (clk_i),
          .rst_ni    (sys_rst_n),
          .stb_i     (sel_gpio),
          .adr_i     (cpu_mem_req.addr[5:2]),   // Register address (word aligned)
          .byte_sel_i(cpu_mem_req.rw[3:0]),     // Byte enables
          .we_i      (|cpu_mem_req.rw),         // Write enable
          .dat_i     (cpu_mem_req.data[31:0]),
          .dat_o     (gpio_rdata),
          .gpio_i    (gpio_i),
          .gpio_o    (gpio_o),
          .gpio_oe_o (gpio_oe_o),
          .gpio_pue_o(),                        // Pull-up (connect to pads if needed)
          .gpio_pde_o(),                        // Pull-down (connect to pads if needed)
          .irq_o     (gpio_irq)
      );
    end else begin : gen_no_gpio_internal
      assign gpio_rdata = '0;
      assign gpio_irq   = 1'b0;
    end
  endgenerate

  // ==========================================================================
  // PLIC (Platform-Level Interrupt Controller)
  // ==========================================================================
  // Interrupt source mapping:
  //   Source 0     : Reserved (always 0)
  //   Source 1     : GPIO interrupt
  //   Source 2-9   : External interrupts (ext_irq_i[0-7])
  //   Source 10    : Timer combined interrupt
  //   Source 11-14 : Individual timer interrupts
  //   Source 15    : Watchdog early warning
  //   Source 16-19 : DMA channel interrupts
  //   Source 20    : PWM interrupt
  //   Source 21-31 : Reserved for future peripherals
  assign plic_irq_sources = {
    11'b0,  // Sources 21-31: Reserved
    pwm_irq,  // Source 20: PWM
    dma_irq,  // Sources 16-19: DMA channels
    wdt_irq,  // Source 15: Watchdog
    gptimer_irq,  // Sources 11-14: Individual timer IRQs
    gptimer_irq_combined,  // Source 10: Timer combined
    ext_irq_i,  // Sources 2-9: External interrupts
    gpio_irq,  // Source 1: GPIO
    1'b0  // Source 0: Reserved (always 0)
  };

  generate
    if (PLIC_EN) begin : gen_plic
      plic #(
          .NUM_SOURCES (32),
          .NUM_PRIORITY(8)
      ) i_plic (
          .clk_i        (clk_i),
          .rst_ni       (sys_rst_n),
          .stb_i        (sel_plic),
          .adr_i        (cpu_mem_req.addr[11:2]),  // 10-bit word address
          .byte_sel_i   (cpu_mem_req.rw[3:0]),
          .we_i         (|cpu_mem_req.rw),
          .dat_i        (cpu_mem_req.data[31:0]),
          .dat_o        (plic_rdata),
          .irq_sources_i(plic_irq_sources),
          .irq_o        (plic_irq)
      );
    end else begin : gen_no_plic
      assign plic_rdata = '0;
      assign plic_irq   = 1'b0;
    end
  endgenerate

  // ==========================================================================
  // General Purpose Timer
  // ==========================================================================
  generate
    if (TIMER_EN) begin : gen_timer
      gptimer #(
          .NUM_TIMERS(4)
      ) i_gptimer (
          .clk_i         (clk_i),
          .rst_ni        (sys_rst_n),
          .stb_i         (sel_timer),
          .adr_i         (cpu_mem_req.addr[9:2]),   // 8-bit word address
          .byte_sel_i    (cpu_mem_req.rw[3:0]),
          .we_i          (|cpu_mem_req.rw),
          .dat_i         (cpu_mem_req.data[31:0]),
          .dat_o         (timer_rdata),
          .pwm_o         (timer_pwm),
          .irq_o         (gptimer_irq),
          .irq_combined_o(gptimer_irq_combined)
      );
    end else begin : gen_no_timer
      assign timer_rdata          = '0;
      assign timer_pwm            = '0;
      assign gptimer_irq          = '0;
      assign gptimer_irq_combined = 1'b0;
    end
  endgenerate

  // ==========================================================================
  // Watchdog Timer
  // ==========================================================================
  generate
    if (WDT_EN) begin : gen_wdt
      watchdog #(
          .RESET_PULSE_WIDTH(16)
      ) i_watchdog (
          .clk_i      (clk_i),
          .rst_ni     (sys_rst_n),
          .stb_i      (sel_wdt),
          .adr_i      (cpu_mem_req.addr[5:2]),   // 4-bit word address
          .byte_sel_i (cpu_mem_req.rw[3:0]),
          .we_i       (|cpu_mem_req.rw),
          .dat_i      (cpu_mem_req.data[31:0]),
          .dat_o      (wdt_rdata),
          .dbg_halt_i (1'b0),                    // TODO: Connect to debug module
          .wdt_reset_o(wdt_reset),
          .irq_o      (wdt_irq)
      );
    end else begin : gen_no_wdt
      assign wdt_rdata = '0;
      assign wdt_reset = 1'b0;
      assign wdt_irq   = 1'b0;
    end
  endgenerate

  assign wdt_reset_o = wdt_reset;

  // ==========================================================================
  // DMA Controller
  // ==========================================================================
  generate
    if (DMA_EN) begin : gen_dma
      dma #(
          .NUM_CHANNELS(4),
          .MAX_BURST   (16)
      ) i_dma (
          .clk_i      (clk_i),
          .rst_ni     (sys_rst_n),
          .stb_i      (sel_dma),
          .adr_i      (cpu_mem_req.addr[7:2]),   // 6-bit word address
          .byte_sel_i (cpu_mem_req.rw[3:0]),
          .we_i       (|cpu_mem_req.rw),
          .dat_i      (cpu_mem_req.data[31:0]),
          .dat_o      (dma_rdata),
          .dma_req_o  (dma_req),
          .dma_addr_o (dma_addr),
          .dma_wdata_o(dma_wdata),
          .dma_wstrb_o(dma_wstrb),
          .dma_rdata_i(32'h0),                   // TODO: Connect DMA master port
          .dma_ack_i  (1'b0),
          .dreq_i     (4'b0),                    // TODO: Connect peripheral DMA requests
          .irq_o      (dma_irq)
      );
    end else begin : gen_no_dma
      assign dma_rdata = '0;
      assign dma_req   = 1'b0;
      assign dma_addr  = '0;
      assign dma_wdata = '0;
      assign dma_wstrb = '0;
      assign dma_irq   = '0;
    end
  endgenerate

  // ==========================================================================
  // PWM Controller
  // ==========================================================================
  generate
    if (PWM_EN) begin : gen_pwm
      pwm #(
          .NUM_CHANNELS(8),
          .PWM_WIDTH   (16)
      ) i_pwm (
          .clk_i     (clk_i),
          .rst_ni    (sys_rst_n),
          .stb_i     (sel_pwm),
          .adr_i     (cpu_mem_req.addr[7:2]),   // 6-bit word address
          .byte_sel_i(cpu_mem_req.rw[3:0]),
          .we_i      (|cpu_mem_req.rw),
          .dat_i     (cpu_mem_req.data[31:0]),
          .dat_o     (pwm_rdata),
          .fault_i   (pwm_fault_i),
          .pwm_o     (pwm_out),
          .pwm_n_o   (pwm_n_out),
          .sync_o    (pwm_sync),
          .drq_o     (),                        // DMA request (connect if needed)
          .irq_o     (pwm_irq)
      );
    end else begin : gen_no_pwm
      assign pwm_rdata = '0;
      assign pwm_out   = '0;
      assign pwm_n_out = '0;
      assign pwm_sync  = 1'b0;
      assign pwm_irq   = 1'b0;
    end
  endgenerate

  assign pwm_o   = pwm_out;
  assign pwm_n_o = pwm_n_out;

  // ==========================================================================
  // VGA Controller
  // ==========================================================================
  generate
    if (VGA_EN) begin : gen_vga
      // Pixel clock generator
      vga_clk_gen #(
          .SYS_CLK_FREQ  (CLK_FREQ_HZ),
          .PIXEL_CLK_FREQ(25_175_000)
      ) i_vga_clk (
          .clk_i      (clk_i),
          .rst_ni     (sys_rst_n),
          .pixel_clk_o(pixel_clk),
          .locked_o   (pll_locked)
      );

      // VGA controller
      vga_controller #(
          .H_VISIBLE  (640),
          .H_FRONT    (16),
          .H_SYNC     (96),
          .H_BACK     (48),
          .V_VISIBLE  (480),
          .V_FRONT    (10),
          .V_SYNC     (2),
          .V_BACK     (33),
          .TEXT_COLS  (80),
          .TEXT_ROWS  (30),
          .CHAR_WIDTH (8),
          .CHAR_HEIGHT(16)
      ) i_vga (
          .clk_i      (clk_i),
          .rst_ni     (sys_rst_n),
          .pixel_clk_i(pixel_clk),
          .stb_i      (sel_vga),
          .adr_i      (cpu_mem_req.addr[11:2]),  // 10-bit word address (4KB)
          .byte_sel_i (cpu_mem_req.rw[3:0]),
          .we_i       (|cpu_mem_req.rw),
          .dat_i      (cpu_mem_req.data[31:0]),
          .dat_o      (vga_rdata),
          .hsync_o    (vga_hsync_o),
          .vsync_o    (vga_vsync_o),
          .r_o        (vga_r_o),
          .g_o        (vga_g_o),
          .b_o        (vga_b_o)
      );
    end else begin : gen_no_vga
      assign vga_rdata   = '0;
      assign pixel_clk   = 1'b0;
      assign pll_locked  = 1'b0;
      assign vga_hsync_o = 1'b1;
      assign vga_vsync_o = 1'b1;
      assign vga_r_o     = '0;
      assign vga_g_o     = '0;
      assign vga_b_o     = '0;
    end
  endgenerate

  // ==========================================================================
  // Peripheral Response Multiplexer
  // ==========================================================================
  always_comb begin
    periph_res.valid = sel_periph;
    periph_res.ready = 1'b1;
    periph_res.data  = '0;

    if (sel_gpio) begin
      periph_res.data = {96'b0, gpio_rdata};
    end else if (sel_plic) begin
      periph_res.data = {96'b0, plic_rdata};
    end else if (sel_timer) begin
      periph_res.data = {96'b0, timer_rdata};
    end else if (sel_wdt) begin
      periph_res.data = {96'b0, wdt_rdata};
    end else if (sel_dma) begin
      periph_res.data = {96'b0, dma_rdata};
    end else if (sel_pwm) begin
      periph_res.data = {96'b0, pwm_rdata};
    end else if (sel_vga) begin
      periph_res.data = {96'b0, vga_rdata};
    end
    // Add more peripherals here as they are implemented:
    // else if (sel_uart0) begin
    //   periph_res.data = {96'b0, uart0_rdata};
    // end
  end

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

  // GPIO outputs - directly driven by gpio module when enabled
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
