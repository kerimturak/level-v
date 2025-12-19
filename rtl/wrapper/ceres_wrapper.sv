/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  CERES RISC-V SoC Top-Level Wrapper with Wishbone B4 Bus
  
  Full Wishbone B4 pipelined bus architecture for peripheral interconnect.
  
  Bus Topology:
    CPU -> iomem -> wb_master_bridge -> wb_interconnect -> slaves
    
  Memory Map:
    0x8000_0000 : Main RAM (via Wishbone)
    0x3000_0000 : CLINT (via Wishbone)
    0x2000_0000 : Peripherals (via Wishbone)
      0x2000_0xxx : UART0
*/
`timescale 1ns / 1ps

module ceres_wrapper
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
`ifndef SYNTHESIS
    parameter int unsigned RAM_SIZE_KB = ceres_param::WRAPPER_RAM_SIZE_KB,
`else
    parameter int unsigned RAM_SIZE_KB = 48,
`endif

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
    parameter logic [8*PROGRAM_SEQUENCE_LEN-1:0] PROG_SEQUENCE = PROGRAM_SEQUENCE
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
  localparam int BYTE_OFFSET = $clog2(CACHE_LINE_W / 8);  // 4 for 128-bit cache line (16 bytes)

  // Wishbone Slave IDs
  localparam int SLV_RAM = 0;
  localparam int SLV_CLINT = 1;
  localparam int SLV_PBUS = 2;
  localparam int WB_NUM_SLAVES_LOCAL = 3;

  // ==========================================================================
  // Internal Signals
  // ==========================================================================

  // CPU Interface
  iomem_req_t                         cpu_mem_req;
  iomem_res_t                         cpu_mem_res;

  // Wishbone Bus
  wb_master_t                         wb_cpu_m;
  wb_slave_t                          wb_cpu_s;
  wb_master_t                         wb_slave_m           [WB_NUM_SLAVES_LOCAL];
  wb_slave_t                          wb_slave_s           [WB_NUM_SLAVES_LOCAL];

  // Reset
  logic                               prog_reset;
  logic                               sys_rst_n;

  // RAM signals
  logic       [     CACHE_LINE_W-1:0] ram_rdata;
  logic       [   CACHE_LINE_W/8-1:0] ram_wstrb;
  logic                               ram_rd_en;
  logic       [$clog2(RAM_DEPTH)-1:0] ram_addr;
  logic       [      RAM_LATENCY-1:0] ram_delay_q;
  logic                               ram_pending_q;

  // RAM Wishbone adapter signals
  logic                               ram_wb_req;
  logic                               ram_wb_we;
  logic       [                 31:0] ram_wb_addr;
  logic       [                 31:0] ram_wb_wdata;
  logic       [                  3:0] ram_wb_sel;
  logic       [                 31:0] ram_wb_rdata;
  logic                               ram_wb_ack;

  // RAM Burst handling
  logic                               ram_burst_active;
  logic       [                  1:0] ram_burst_cnt;
  logic       [                 31:0] ram_burst_base_addr;
  logic       [     CACHE_LINE_W-1:0] ram_burst_data_q;
  logic                               ram_burst_data_valid;

  // Timer/SW interrupt from CLINT
  logic                               timer_irq;
  logic                               sw_irq;

  // Peripheral bus signals
  logic       [                 31:0] pbus_addr;
  logic       [                 31:0] pbus_wdata;
  logic       [                  3:0] pbus_wstrb;
  logic                               pbus_valid;
  logic                               pbus_we;
  logic       [                 31:0] pbus_rdata;
  logic                               pbus_ready;

  // Peripheral select signals
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

  // UART
  logic       [                 31:0] uart0_rdata;
  logic       [                 31:0] uart1_rdata;

  // SPI
  logic       [                 31:0] spi0_rdata;

  // I2C (currently not instantiated, default to 0)
  logic       [                 31:0] i2c0_rdata;
  logic                               i2c0_scl_o;
  logic                               i2c0_scl_oe;
  logic                               i2c0_scl_i;
  logic                               i2c0_sda_o;
  logic                               i2c0_sda_oe;
  logic                               i2c0_sda_i;
  logic                               i2c0_irq;

  // Default unused I2C signals to 0 (no I2C module instantiated)
  assign i2c0_rdata  = 32'h0;
  assign i2c0_scl_o  = 1'b0;
  assign i2c0_scl_oe = 1'b0;
  assign i2c0_scl_i  = 1'b0;
  assign i2c0_sda_o  = 1'b0;
  assign i2c0_sda_oe = 1'b0;
  assign i2c0_sda_i  = 1'b0;
  assign i2c0_irq    = 1'b0;

  // Default unused UART1 signals to 0 (no UART1 module instantiated)
  assign uart1_rdata = 32'h0;

  // GPIO
  logic       [31:0] gpio_rdata;
  logic              gpio_irq;

  // PWM
  logic       [31:0] pwm_rdata;
  logic       [ 7:0] pwm_out;
  logic       [ 7:0] pwm_n_out;
  logic              pwm_irq;
  logic              pwm_sync;

  // Timer
  logic       [31:0] timer_rdata;
  logic       [ 7:0] timer_pwm;
  logic       [ 3:0] gptimer_irq;
  logic              gptimer_irq_combined;

  // PLIC
  logic       [31:0] plic_rdata;
  logic       [31:0] plic_irq_sources;
  logic              plic_irq;

  // Watchdog
  logic       [31:0] wdt_rdata;
  logic              wdt_irq;
  logic              wdt_reset;

  // DMA
  logic       [31:0] dma_rdata;
  logic       [ 3:0] dma_irq;
  logic              dma_req;
  logic       [31:0] dma_addr;
  logic       [31:0] dma_wdata;
  logic       [ 3:0] dma_wstrb;
  logic              dma_ack;

  // VGA
  logic       [31:0] vga_rdata;
  logic              pixel_clk;
  logic              pll_locked;

  // Response signals for multiplexer
  iomem_res_t        ram_res;
  iomem_res_t        clint_res;
  iomem_res_t        periph_res;

  logic              uart_sel;
  logic              spi_sel;
  logic              i2c_sel;
  logic              i2c_scl_i;
  logic              i2c_sda_i;
  logic              i2c_irq;
  // ==========================================================================
  // Reset
  // ==========================================================================
`ifdef VERILATOR
  assign sys_rst_n = rst_ni;
`else
  assign sys_rst_n = rst_ni & prog_reset;
`endif

  // ==========================================================================
  // CPU Core
  // ==========================================================================
  cpu i_soc (
      .clk_i      (clk_i),
      .rst_ni     (sys_rst_n),
      // Hardware interrupt inputs
      .timer_irq_i(timer_irq),    // CLINT timer interrupt
      .sw_irq_i   (sw_irq),       // CLINT software interrupt  
      .ext_irq_i  (|ext_irq_i),   // External interrupt (directly from external pins)
      .iomem_req_o(cpu_mem_req),
      .iomem_res_i(cpu_mem_res)
  );

  // ==========================================================================
  // WISHBONE MASTER BRIDGE (iomem -> Wishbone B4)
  // ==========================================================================
  wb_master_bridge i_wb_master (
      .clk_i      (clk_i),
      .rst_ni     (sys_rst_n),
      .iomem_req_i(cpu_mem_req),
      .iomem_res_o(cpu_mem_res),
      .wb_m_o     (wb_cpu_m),
      .wb_s_i     (wb_cpu_s)
  );

  // ==========================================================================
  // WISHBONE INTERCONNECT (1-to-N Switch)
  // ==========================================================================
  wb_interconnect #(
      .NUM_SLAVES(WB_NUM_SLAVES_LOCAL)
  ) i_wb_interconnect (
      .clk_i (clk_i),
      .rst_ni(sys_rst_n),
      .wb_m_i(wb_cpu_m),
      .wb_s_o(wb_cpu_s),
      .wb_m_o(wb_slave_m),
      .wb_s_i(wb_slave_s)
  );

  // ==========================================================================
  // SLAVE 0: RAM (Wishbone -> Cache-line RAM adapter with Burst Support)
  // ==========================================================================
  assign ram_wb_req   = wb_slave_m[SLV_RAM].cyc && wb_slave_m[SLV_RAM].stb;
  assign ram_wb_we    = wb_slave_m[SLV_RAM].we;
  assign ram_wb_addr  = wb_slave_m[SLV_RAM].adr;
  assign ram_wb_wdata = wb_slave_m[SLV_RAM].dat;
  assign ram_wb_sel   = wb_slave_m[SLV_RAM].sel;

  // Detect burst mode from CTI
  wire ram_is_burst = (wb_slave_m[SLV_RAM].cti == WB_CTI_INCR) || (wb_slave_m[SLV_RAM].cti == WB_CTI_EOB);
  wire ram_is_burst_start = ram_wb_req && !ram_wb_we && (wb_slave_m[SLV_RAM].cti == WB_CTI_INCR) && !ram_burst_active;
  wire ram_is_burst_end = ram_burst_active && (wb_slave_m[SLV_RAM].cti == WB_CTI_EOB);

  // Convert byte address to RAM word address (divide by 4)
  // RAM module internally aligns to cache line boundary
  assign ram_addr = ram_wb_addr[2+$clog2(RAM_DEPTH)-1 : 2];

  // Expand word data to cache line width with proper byte strobes
  logic [  CACHE_LINE_W-1:0] ram_wdata_expanded;
  logic [CACHE_LINE_W/8-1:0] ram_wstrb_expanded;
  logic [               1:0] ram_word_offset;

  always_comb begin
    ram_wdata_expanded = '0;
    ram_wstrb_expanded = '0;
    ram_word_offset = ram_wb_addr[3:2];  // Select word within 16-byte cache line

    // Replicate write data across all word positions
    for (int i = 0; i < CACHE_LINE_W / 32; i++) begin
      ram_wdata_expanded[i*32+:32] = ram_wb_wdata;
    end

    // Set byte strobes for correct word position
    if (ram_wb_req && ram_wb_we) begin
      ram_wstrb_expanded[ram_word_offset*4+:4] = ram_wb_sel;
    end
  end

  assign ram_wstrb = ram_wstrb_expanded;

  // Only issue RAM read for first beat of burst OR single access
  assign ram_rd_en = ram_wb_req && !ram_wb_we && !ram_burst_data_valid;

  wrapper_ram #(
      .RAM_DEPTH       (RAM_DEPTH),
      .CACHE_LINE_WIDTH(CACHE_LINE_W),
      .CPU_CLK         (CLK_FREQ_HZ),
      .PROG_BAUD_RATE  (BAUD_RATE),
      .PROGRAM_SEQUENCE(PROG_SEQUENCE)
  ) i_main_ram (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .addr_i         (ram_addr),
      .wdata_i        (ram_wdata_expanded),
      .wstrb_i        (ram_wstrb),
      .rdata_o        (ram_rdata),
      .rd_en_i        (ram_rd_en),
      .ram_prog_rx_i  (prog_rx_i),
      .system_reset_o (prog_reset),
      .prog_mode_led_o(prog_mode_o)
  );

  // Burst state machine
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      ram_burst_active     <= 1'b0;
      ram_burst_cnt        <= '0;
      ram_burst_base_addr  <= '0;
      ram_burst_data_q     <= '0;
      ram_burst_data_valid <= 1'b0;
    end else begin
      // First beat of burst - wait for RAM latency then capture data
      if (ram_delay_q[RAM_LATENCY-1] && !ram_burst_data_valid) begin
        ram_burst_data_q     <= ram_rdata;
        ram_burst_data_valid <= 1'b1;
        ram_burst_active     <= ram_is_burst;
        ram_burst_cnt        <= '0;
`ifdef WB_INTC
        $display("[%0t] WB_RAM: BURST_CAPTURE addr=%h rdata=%h is_burst=%b", $time, ram_wb_addr, ram_rdata, ram_is_burst);
`endif
      end  // Subsequent beats - increment counter
      else if (ram_burst_active && ram_wb_req && ram_burst_data_valid) begin
        ram_burst_cnt <= ram_burst_cnt + 1;
`ifdef WB_INTC
        $display("[%0t] WB_RAM: BURST_BEAT[%0d] addr=%h data=%h cti=%b", $time, ram_burst_cnt, ram_wb_addr, ram_wb_rdata, wb_slave_m[SLV_RAM].cti);
`endif
        if (ram_is_burst_end) begin
          ram_burst_active     <= 1'b0;
          ram_burst_data_valid <= 1'b0;
`ifdef WB_INTC
          $display("[%0t] WB_RAM: BURST_END", $time);
`endif
        end
      end  // Non-burst read complete - clear valid
      else if (ram_delay_q[RAM_LATENCY-1] && !ram_is_burst) begin
        ram_burst_data_valid <= 1'b0;
      end  // Single access complete
      else if (!ram_wb_req && !ram_burst_active) begin
        ram_burst_data_valid <= 1'b0;
      end
    end
  end

  // Extract correct word from cache line for read (use burst data when valid)
  always_comb begin
    logic [1:0] word_offset;
    if (ram_burst_data_valid) begin
      word_offset  = ram_wb_addr[3:2];
      ram_wb_rdata = ram_burst_data_q[word_offset*32+:32];
    end else begin
      word_offset  = ram_wb_addr[3:2];
      ram_wb_rdata = ram_rdata[word_offset*32+:32];
    end
  end

  // RAM Latency Pipeline for Wishbone ACK
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      ram_delay_q   <= '0;
      ram_pending_q <= 1'b0;
    end else begin
      // Clear delay pipeline on ACK
      if (ram_wb_ack) begin
        ram_delay_q   <= '0;
        ram_pending_q <= 1'b0;
      end else begin
        ram_delay_q   <= {ram_delay_q[RAM_LATENCY-2:0], ram_pending_q};
        // Only set pending for first beat of burst or single access
        ram_pending_q <= ram_rd_en;
      end
    end
  end

  // RAM Wishbone response
  // - Writes ACK immediately
  // - First read beat: ACK after RAM latency
  // - Subsequent burst beats: ACK immediately (data already in buffer)
  assign ram_wb_ack = (ram_wb_req && ram_wb_we) || ram_delay_q[RAM_LATENCY-1] || (ram_burst_active && ram_wb_req && ram_burst_data_valid);

  assign wb_slave_s[SLV_RAM].dat = ram_wb_rdata;
  assign wb_slave_s[SLV_RAM].ack = ram_wb_ack;
  assign wb_slave_s[SLV_RAM].err = 1'b0;
  assign wb_slave_s[SLV_RAM].rty = 1'b0;
  assign wb_slave_s[SLV_RAM].stall = 1'b0;

  // ==========================================================================
  // SLAVE 1: CLINT (Core-Local Interruptor)
  // ==========================================================================
  wb_clint_slave i_wb_clint (
      .clk_i      (clk_i),
      .rst_ni     (sys_rst_n),
      .wb_m_i     (wb_slave_m[SLV_CLINT]),
      .wb_s_o     (wb_slave_s[SLV_CLINT]),
      .timer_irq_o(timer_irq),
      .sw_irq_o   (sw_irq)
  );

  // ==========================================================================
  // SLAVE 2: Peripheral Bus (UART, etc.)
  // ==========================================================================
  wb_pbus_slave i_wb_pbus (
      .clk_i       (clk_i),
      .rst_ni      (sys_rst_n),
      .wb_m_i      (wb_slave_m[SLV_PBUS]),
      .wb_s_o      (wb_slave_s[SLV_PBUS]),
      .pbus_addr_o (pbus_addr),
      .pbus_wdata_o(pbus_wdata),
      .pbus_wstrb_o(pbus_wstrb),
      .pbus_valid_o(pbus_valid),
      .pbus_we_o   (pbus_we),
      .pbus_rdata_i(pbus_rdata),
      .pbus_ready_i(pbus_ready)
  );

`ifdef WB_INTC
  // Debug: PBUS transactions
  always_ff @(posedge clk_i) begin
    if (pbus_valid && pbus_we) begin
      $display("[%0t] PBUS_WRITE: addr=%h data=%h wstrb=%b ready=%b", $time, pbus_addr, pbus_wdata, pbus_wstrb, pbus_ready);
    end
    if (wb_slave_m[SLV_PBUS].cyc && wb_slave_m[SLV_PBUS].stb) begin
      $display("[%0t] WB_PBUS: cyc=%b stb=%b we=%b addr=%h sel=%b ack=%b", $time, wb_slave_m[SLV_PBUS].cyc, wb_slave_m[SLV_PBUS].stb, wb_slave_m[SLV_PBUS].we, wb_slave_m[SLV_PBUS].adr,
               wb_slave_m[SLV_PBUS].sel, wb_slave_s[SLV_PBUS].ack);
    end
  end
`endif

  // ==========================================================================
  // Peripheral Bus Address Decoding
  // Memory Map:
  //   0x2000_0xxx : UART0 (addr[19:16] == 0x0)
  //   0x2001_0xxx : SPI0  (addr[19:16] == 0x1)
  //   0x2002_0xxx : I2C0  (addr[19:16] == 0x2)
  //   0x2003_0xxx : UART1 (addr[19:16] == 0x3)
  // ==========================================================================
  assign uart_sel  = (pbus_addr[19:16] == 4'h0);  // 0x2000_0xxx
  assign spi_sel   = (pbus_addr[19:16] == 4'h1);  // 0x2001_0xxx
  assign i2c_sel   = (pbus_addr[19:16] == 4'h2);  // 0x2002_0xxx

  assign sel_uart0 = uart_sel;  // UART0 at 0x2000_0xxx
  assign sel_uart1 = (pbus_addr[19:16] == 4'h3);  // UART1 at 0x2003_0xxx
  assign sel_spi0  = spi_sel;  // SPI0 at 0x2001_0xxx
  assign sel_i2c0  = i2c_sel;  // I2C0 at 0x2002_0xxx

  // Additional peripheral selects (currently unused/disabled)
  assign sel_gpio  = 1'b0;
  assign sel_pwm   = 1'b0;
  assign sel_timer = 1'b0;
  assign sel_plic  = 1'b0;
  assign sel_wdt   = 1'b0;
  assign sel_dma   = 1'b0;
  assign sel_vga   = 1'b0;

  // ==========================================================================
  // UART (Connected via Peripheral Bus)
  // ==========================================================================
  // UART0
  uart i_uart (
      .clk_i     (clk_i),
      .rst_ni    (sys_rst_n),
      .stb_i     (pbus_valid && uart_sel),
      .adr_i     (pbus_addr[3:2]),
      .byte_sel_i(pbus_wstrb),
      .we_i      (pbus_we),
      .dat_i     (pbus_wdata),
      .dat_o     (uart0_rdata),
      .uart_rx_i (uart0_rx_i),
      .uart_tx_o (uart0_tx_o)
  );

  // ==========================================================================
  // SPI Master (Connected via Peripheral Bus)
  // ==========================================================================
  // SPI Master (instantiated only when enabled)
  generate
    if (SPI_EN) begin : gen_spi
      spi_master i_spi (
          .clk_i     (clk_i),
          .rst_ni    (sys_rst_n),
          .stb_i     (pbus_valid && spi_sel),
          .adr_i     (pbus_addr[3:2]),
          .byte_sel_i(pbus_wstrb),
          .we_i      (pbus_we),
          .dat_i     (pbus_wdata),
          .dat_o     (spi0_rdata),
          .spi_sck_o (spi0_sclk_o),
          .spi_mosi_o(spi0_mosi_o),
          .spi_miso_i(spi0_miso_i),
          .spi_cs_n_o(spi0_ss_o[0])
      );
    end
  endgenerate

  // ==========================================================================
  // I2C Master (Connected via Peripheral Bus)
  // ==========================================================================
  // I2C Master (instantiated only when enabled)
  generate
    if (I2C_EN) begin : gen_i2c
      i2c_master i_i2c (
          .clk_i       (clk_i),
          .rst_ni      (sys_rst_n),
          .stb_i       (pbus_valid && i2c_sel),
          .adr_i       (pbus_addr[4:2]),
          .byte_sel_i  (pbus_wstrb),
          .we_i        (pbus_we),
          .dat_i       (pbus_wdata),
          .dat_o       (i2c0_rdata),
          .i2c_scl_o   (i2c0_scl_o),
          .i2c_scl_oe_o(i2c0_scl_oe),
          .i2c_scl_i   (i2c_scl_i),
          .i2c_sda_o   (i2c0_sda_o),
          .i2c_sda_oe_o(i2c0_sda_oe),
          .i2c_sda_i   (i2c_sda_i),
          .irq_o       (i2c_irq)
      );
    end
  endgenerate

  // I2C Tri-state buffers and simulation slave
`ifdef VERILATOR
  // For simulation: I2C slave model
  logic i2c_slave_sda_o;
  logic i2c_slave_sda_oe;

  i2c_slave_sim #(
      .SLAVE_ADDR(7'h50),
      .MEM_SIZE  (256)
  ) i_i2c_slave (
      .clk_i   (clk_i),
      .rst_ni  (sys_rst_n),
      .scl_i   (i2c0_scl_oe ? i2c0_scl_o : 1'b1),
      .sda_i   (i2c0_sda_oe ? i2c0_sda_o : 1'b1),
      .sda_o   (i2c_slave_sda_o),
      .sda_oe_o(i2c_slave_sda_oe)
  );

  // Wired-AND for I2C bus (open-drain simulation)
`else
  // For FPGA: external tri-state buffers
  assign i2c0_scl_io = i2c0_scl_oe ? (i2c0_scl_o ? 1'bz : 1'b0) : 1'bz;
  assign i2c0_sda_io = i2c0_sda_oe ? (i2c0_sda_o ? 1'bz : 1'b0) : 1'bz;
  assign i2c_scl_i   = i2c0_scl_io;
  assign i2c_sda_i   = i2c0_sda_io;
`endif

  // Peripheral read data mux
  always_comb begin
    pbus_rdata = 32'h0;
    pbus_ready = 1'b1;
    if (sel_uart0) begin
      pbus_rdata = uart0_rdata;
    end else if (sel_uart1) begin
      pbus_rdata = uart1_rdata;
    end else if (sel_spi0) begin
      pbus_rdata = spi0_rdata;
    end else if (sel_i2c0) begin
      pbus_rdata = i2c0_rdata;
    end else if (sel_gpio) begin
      pbus_rdata = gpio_rdata;
    end else if (sel_pwm) begin
      pbus_rdata = pwm_rdata;
    end else if (sel_timer) begin
      pbus_rdata = timer_rdata;
    end else if (sel_plic) begin
      pbus_rdata = plic_rdata;
    end else if (sel_wdt) begin
      pbus_rdata = wdt_rdata;
    end else if (sel_dma) begin
      pbus_rdata = dma_rdata;
    end else if (sel_vga) begin
      pbus_rdata = vga_rdata;
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
          .fb_req_o   (),                        // Framebuffer interface not connected
          .fb_addr_o  (),
          .fb_data_i  (32'h0),
          .fb_ack_i   (1'b0),
          .char_addr_o(),                        // Character ROM interface not connected
          .char_data_i(8'h0),
          .vga_hsync_o(vga_hsync_o),
          .vga_vsync_o(vga_vsync_o),
          .vga_r_o    (vga_r_o),
          .vga_g_o    (vga_g_o),
          .vga_b_o    (vga_b_o),
          .vga_de_o   (),                        // Data enable not connected
          .vsync_irq_o()                         // VSync interrupt not connected
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
  // NOTE: `cpu_mem_res` is driven by the `wb_master_bridge` instance
  // (connected to `.iomem_res_o`) and therefore must not be driven
  // procedurally here. The bridge handles packing responses from
  // Wishbone slaves and presenting them to the CPU.

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
