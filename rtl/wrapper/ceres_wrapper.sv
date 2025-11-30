/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  CERES RISC-V SoC Top-Level Wrapper
  
  Modular, extensible SoC wrapper designed for future expansion.
  
  Memory Map:
    0x8000_0000 : Main RAM (128KB default)
    0x3000_0000 : CLINT (mtime, mtimecmp, msip)
    0x2000_0000 : Peripherals
      0x2000_0xxx : UART0
      0x2000_1xxx : UART1
      0x2000_2xxx : SPI0
      0x2000_3xxx : I2C0
      0x2000_4xxx : GPIO
      0x2000_5xxx : PWM
      0x2000_6xxx : Timer
      0x2000_7xxx : PLIC
*/
`timescale 1ns / 1ps

module ceres_wrapper
  import ceres_param::*;
#(
    // System Configuration
    parameter int unsigned CLK_FREQ_HZ = CPU_CLK,
    parameter int unsigned BAUD_RATE   = 115200,

    // Memory Configuration
    parameter int unsigned RAM_SIZE_KB = 1024,
    parameter int unsigned RAM_LATENCY = 16,

    // Peripheral Configuration
    parameter int unsigned NUM_UART = 1,
    parameter bit          SPI_EN   = 1'b0,
    parameter bit          I2C_EN   = 1'b0,
    parameter bit          GPIO_EN  = 1'b0,
    parameter bit          PWM_EN   = 1'b0,
    parameter bit          TIMER_EN = 1'b1,
    parameter bit          PLIC_EN  = 1'b0,

    // Programming Interface
    parameter string PROG_SEQUENCE = PROGRAM_SEQUENCE
) (
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    // UART Interface
    output logic uart_tx_o,
    input  logic uart_rx_i,

    // SPI Interface (active when SPI_EN=1)
    output logic       spi0_sclk_o,
    output logic       spi0_mosi_o,
    input  logic       spi0_miso_i,
    output logic [3:0] spi0_ss_o,

    // I2C Interface (active when I2C_EN=1)
    inout wire i2c0_sda_io,
    inout wire i2c0_scl_io,

    // GPIO Interface (active when GPIO_EN=1)
    input  logic [31:0] gpio_i,
    output logic [31:0] gpio_o,
    output logic [31:0] gpio_oe_o,

    // External Interrupts
    input logic [7:0] ext_irq_i,

    // Programming Interface
    input  logic program_rx_i,
    output logic prog_mode_led_o,

    // Debug/Status
    output logic [3:0] status_led_o
);

  // ==========================================================================
  // Local Parameters
  // ==========================================================================
  localparam int RAM_DEPTH = (RAM_SIZE_KB * 1024) / 4;
  localparam int CACHE_LINE_W = BLK_SIZE;
  localparam int BYTE_OFFSET = 2;

  // Address Regions
  localparam logic [31:0] RAM_BASE = 32'h8000_0000;
  localparam logic [31:0] RAM_MASK = 32'h000F_FFFF;
  localparam logic [31:0] CLINT_BASE = 32'h3000_0000;
  localparam logic [31:0] CLINT_MASK = 32'h0000_FFFF;
  localparam logic [31:0] PBUS_BASE = 32'h2000_0000;
  localparam logic [31:0] PBUS_MASK = 32'h00FF_FFFF;

  // CLINT Offsets
  localparam logic [15:0] CLINT_MSIP = 16'h0000;
  localparam logic [15:0] CLINT_MTIMECMP = 16'h4000;
  localparam logic [15:0] CLINT_MTIME = 16'hBFF8;

  // ==========================================================================
  // Internal Signals
  // ==========================================================================

  // CPU Interface
  iomem_req_t cpu_mem_req;
  iomem_res_t cpu_mem_res;

  // Reset
  logic       prog_reset;
  logic       sys_rst_n;

  // Address Decode
  logic sel_ram, sel_clint, sel_pbus;
  logic [                 15:0] clint_off;

  // RAM
  logic [     CACHE_LINE_W-1:0] ram_rdata;
  logic [   CACHE_LINE_W/8-1:0] ram_wstrb;
  logic                         ram_rd_en;
  logic [$clog2(RAM_DEPTH)-1:0] ram_addr;
  logic [      RAM_LATENCY-1:0] ram_delay_q;
  logic                         ram_pending_q;

  // CLINT
  logic [                 63:0] mtime_q;
  logic [                 63:0] mtimecmp_q;
  logic                         msip_q;
  logic                         timer_irq;

  // ==========================================================================
  // Reset
  // ==========================================================================
  // In Verilator simulation, bypass prog_reset to prevent floating UART issues
`ifdef VERILATOR
  assign sys_rst_n = rst_ni;  // Programming reset bypass for simulation
`else
  assign sys_rst_n = rst_ni & prog_reset;
`endif

  // ==========================================================================
  // Address Decoder
  // ==========================================================================
  assign sel_ram   = (cpu_mem_req.addr & ~RAM_MASK) == RAM_BASE;
  assign sel_clint = (cpu_mem_req.addr & ~CLINT_MASK) == CLINT_BASE;
  assign sel_pbus  = (cpu_mem_req.addr & ~PBUS_MASK) == PBUS_BASE;
  assign clint_off = cpu_mem_req.addr[15:0];

  // ==========================================================================
  // CPU Core (instance name 'soc' for tracer compatibility)
  // ==========================================================================
  cpu i_soc (
      .clk_i      (clk_i),
      .rst_ni     (sys_rst_n),
      .iomem_req_o(cpu_mem_req),
      .iomem_res_i(cpu_mem_res),
      .uart_tx_o  (uart_tx_o),
      .uart_rx_i  (uart_rx_i)
  );

  // ==========================================================================
  // Main RAM
  // ==========================================================================
  assign ram_addr  = cpu_mem_req.addr[BYTE_OFFSET+$clog2(RAM_DEPTH)-1 : BYTE_OFFSET];
  assign ram_wstrb = (cpu_mem_req.valid & sel_ram) ? cpu_mem_req.rw : '0;
  assign ram_rd_en = cpu_mem_req.valid & sel_ram & ~(|cpu_mem_req.rw);

  wrapper_ram #(
      .WORD_WIDTH      (32),
      .RAM_DEPTH       (RAM_DEPTH),
      .CACHE_LINE_WIDTH(CACHE_LINE_W),
      .CPU_CLK         (CLK_FREQ_HZ),
      .PROG_BAUD_RATE  (BAUD_RATE),
      .PROGRAM_SEQUENCE(PROG_SEQUENCE)
  ) i_main_ram (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .addr_i         (ram_addr),
      .wdata_i        (cpu_mem_req.data),
      .wstrb_i        (ram_wstrb),
      .rdata_o        (ram_rdata),
      .rd_en_i        (ram_rd_en),
      .ram_prog_rx_i  (program_rx_i),
      .system_reset_o (prog_reset),
      .prog_mode_led_o(prog_mode_led_o)
  );

  // RAM Latency Pipeline
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ram_delay_q   <= '0;
      ram_pending_q <= 1'b0;
    end else begin
      if (cpu_mem_req.valid & cpu_mem_res.valid & sel_ram) ram_delay_q <= '0;
      else ram_delay_q <= {ram_delay_q[RAM_LATENCY-2:0], ram_pending_q};

      ram_pending_q <= cpu_mem_req.valid & ~cpu_mem_res.valid & sel_ram;
    end
  end

  // ==========================================================================
  // CLINT (Core-Local Interruptor)
  // ==========================================================================
  assign timer_irq = (mtime_q >= mtimecmp_q);

  always_ff @(posedge clk_i or negedge sys_rst_n) begin
    if (!sys_rst_n) begin
      mtime_q    <= 64'h0;
      mtimecmp_q <= 64'hFFFF_FFFF_FFFF_FFFF;
      msip_q     <= 1'b0;
    end else begin
      mtime_q <= mtime_q + 64'h1;

      if (cpu_mem_req.valid & sel_clint & (|cpu_mem_req.rw)) begin
        case (clint_off)
          CLINT_MSIP:         msip_q <= cpu_mem_req.data[0];
          CLINT_MTIMECMP:     mtimecmp_q[31:0] <= cpu_mem_req.data[31:0];
          CLINT_MTIMECMP + 4: mtimecmp_q[63:32] <= cpu_mem_req.data[31:0];
          CLINT_MTIME:        mtime_q[31:0] <= cpu_mem_req.data[31:0];
          CLINT_MTIME + 4:    mtime_q[63:32] <= cpu_mem_req.data[31:0];
          default:            ;
        endcase
      end
    end
  end

  // ==========================================================================
  // Response Mux
  // ==========================================================================
  always_comb begin
    cpu_mem_res.ready = 1'b1;
    cpu_mem_res.valid = 1'b0;
    cpu_mem_res.data  = '0;

    if (cpu_mem_req.valid) begin
      if (sel_ram) begin
        cpu_mem_res.valid = ram_delay_q[RAM_LATENCY-1];
        cpu_mem_res.data  = ram_rdata;
      end else if (sel_clint) begin
        cpu_mem_res.valid = 1'b1;
        case (clint_off)
          CLINT_MSIP:         cpu_mem_res.data = {96'b0, 31'b0, msip_q};
          CLINT_MTIMECMP:     cpu_mem_res.data = {96'b0, mtimecmp_q[31:0]};
          CLINT_MTIMECMP + 4: cpu_mem_res.data = {96'b0, mtimecmp_q[63:32]};
          CLINT_MTIME:        cpu_mem_res.data = {96'b0, mtime_q[31:0]};
          CLINT_MTIME + 4:    cpu_mem_res.data = {96'b0, mtime_q[63:32]};
          default:            cpu_mem_res.data = '0;
        endcase
      end else if (sel_pbus) begin
        cpu_mem_res.valid = 1'b1;
        cpu_mem_res.data  = '0;  // Placeholder for peripherals
      end else begin
        cpu_mem_res.valid = 1'b1;
        cpu_mem_res.data  = '0;  // Unmapped
      end
    end
  end

  // ==========================================================================
  // Unused Peripheral Tie-offs
  // ==========================================================================
  generate
    if (!SPI_EN) begin : gen_no_spi
      assign spi0_sclk_o = 1'b0;
      assign spi0_mosi_o = 1'b0;
      assign spi0_ss_o   = 4'hF;
    end
    if (!GPIO_EN) begin : gen_no_gpio
      assign gpio_o    = 32'h0;
      assign gpio_oe_o = 32'h0;
    end
  endgenerate

  assign status_led_o = {3'b0, prog_mode_led_o};

endmodule
