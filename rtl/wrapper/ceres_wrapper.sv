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
    parameter logic [8*PROGRAM_SEQUENCE_LEN-1:0] PROG_SEQUENCE = PROGRAM_SEQUENCE
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
  logic                               uart_sel;
  logic                               spi_sel;
  logic                               i2c_sel;

  // UART
  logic       [                 31:0] uart_rdata;

  // I2C
  logic       [                 31:0] i2c_rdata;
  logic                               i2c_scl_o;
  logic                               i2c_scl_oe;
  logic                               i2c_scl_i;
  logic                               i2c_sda_o;
  logic                               i2c_sda_oe;
  logic                               i2c_sda_i;
  logic                               i2c_irq;

  // SPI
  logic       [                 31:0] spi_rdata;

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

  always_comb begin
    ram_wdata_expanded = '0;
    ram_wstrb_expanded = '0;

    // Replicate write data across all word positions
    for (int i = 0; i < CACHE_LINE_W / 32; i++) begin
      ram_wdata_expanded[i*32+:32] = ram_wb_wdata;
    end

    // Set byte strobes for correct word position
    if (ram_wb_req && ram_wb_we) begin
      logic [1:0] word_offset;
      word_offset = ram_wb_addr[3:2];  // Select word within 16-byte cache line
      ram_wstrb_expanded[word_offset*4+:4] = ram_wb_sel;
    end
  end

  assign ram_wstrb = ram_wstrb_expanded;

  // Only issue RAM read for first beat of burst OR single access
  assign ram_rd_en = ram_wb_req && !ram_wb_we && !ram_burst_data_valid;

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
      .wdata_i        (ram_wdata_expanded),
      .wstrb_i        (ram_wstrb),
      .rdata_o        (ram_rdata),
      .rd_en_i        (ram_rd_en),
      .ram_prog_rx_i  (program_rx_i),
      .system_reset_o (prog_reset),
      .prog_mode_led_o(prog_mode_led_o)
  );

  // Burst state machine
  always_ff @(posedge clk_i or negedge rst_ni) begin
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
  always_ff @(posedge clk_i or negedge rst_ni) begin
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
  //   0x2000_0xxx : UART (addr[19:16] == 0x0)
  //   0x2001_0xxx : SPI  (addr[19:16] == 0x1)
  //   0x2002_0xxx : I2C  (addr[19:16] == 0x2)
  // ==========================================================================
  assign uart_sel = (pbus_addr[19:16] == 4'h0);  // 0x2000_0xxx
  assign spi_sel  = (pbus_addr[19:16] == 4'h1);  // 0x2001_0xxx
  assign i2c_sel  = (pbus_addr[19:16] == 4'h2);  // 0x2002_0xxx

  // ==========================================================================
  // UART (Connected via Peripheral Bus)
  // ==========================================================================
  uart i_uart (
      .clk_i     (clk_i),
      .rst_ni    (sys_rst_n),
      .stb_i     (pbus_valid && uart_sel),
      .adr_i     (pbus_addr[3:2]),
      .byte_sel_i(pbus_wstrb),
      .we_i      (pbus_we),
      .dat_i     (pbus_wdata),
      .dat_o     (uart_rdata),
      .uart_rx_i (uart_rx_i),
      .uart_tx_o (uart_tx_o)
  );

  // ==========================================================================
  // SPI Master (Connected via Peripheral Bus)
  // ==========================================================================
  spi_master i_spi (
      .clk_i     (clk_i),
      .rst_ni    (sys_rst_n),
      .stb_i     (pbus_valid && spi_sel),
      .adr_i     (pbus_addr[3:2]),
      .byte_sel_i(pbus_wstrb),
      .we_i      (pbus_we),
      .dat_i     (pbus_wdata),
      .dat_o     (spi_rdata),
      .spi_sck_o (spi0_sclk_o),
      .spi_mosi_o(spi0_mosi_o),
      .spi_miso_i(spi0_miso_i),
      .spi_cs_n_o(spi0_ss_o[0])
  );

  // ==========================================================================
  // I2C Master (Connected via Peripheral Bus)
  // ==========================================================================
  i2c_master i_i2c (
      .clk_i       (clk_i),
      .rst_ni      (sys_rst_n),
      .stb_i       (pbus_valid && i2c_sel),
      .adr_i       (pbus_addr[4:2]),
      .byte_sel_i  (pbus_wstrb),
      .we_i        (pbus_we),
      .dat_i       (pbus_wdata),
      .dat_o       (i2c_rdata),
      .i2c_scl_o   (i2c_scl_o),
      .i2c_scl_oe_o(i2c_scl_oe),
      .i2c_scl_i   (i2c_scl_i),
      .i2c_sda_o   (i2c_sda_o),
      .i2c_sda_oe_o(i2c_sda_oe),
      .i2c_sda_i   (i2c_sda_i),
      .irq_o       (i2c_irq)
  );

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
      .scl_i   (i2c_scl_oe ? i2c_scl_o : 1'b1),
      .sda_i   (i2c_sda_oe ? i2c_sda_o : 1'b1),
      .sda_o   (i2c_slave_sda_o),
      .sda_oe_o(i2c_slave_sda_oe)
  );

  // Wired-AND for I2C bus (open-drain simulation)
  assign i2c_scl_i = i2c_scl_oe ? i2c_scl_o : 1'b1;
  assign i2c_sda_i = (i2c_sda_oe ? i2c_sda_o : 1'b1) & (i2c_slave_sda_oe ? i2c_slave_sda_o : 1'b1);
`else
  // For FPGA: external tri-state buffers
  assign i2c0_scl_io = i2c_scl_oe ? (i2c_scl_o ? 1'bz : 1'b0) : 1'bz;
  assign i2c0_sda_io = i2c_sda_oe ? (i2c_sda_o ? 1'bz : 1'b0) : 1'bz;
  assign i2c_scl_i   = i2c0_scl_io;
  assign i2c_sda_i   = i2c0_sda_io;
`endif

  // Peripheral read data mux
  assign pbus_rdata = uart_sel ? uart_rdata : spi_sel ? spi_rdata : i2c_sel ? i2c_rdata : 32'h0;
  assign pbus_ready = 1'b1;  // All peripherals always ready

  // ==========================================================================
  // Unused Peripheral Tie-offs
  // ==========================================================================
  generate
    if (!GPIO_EN) begin : gen_no_gpio
      assign gpio_o    = 32'h0;
      assign gpio_oe_o = 32'h0;
    end
  endgenerate

  // SPI slave selects - directly controlled via register for now
  assign spi0_ss_o[3:1] = 3'b111;  // Other slaves inactive

  assign status_led_o   = {3'b0, prog_mode_led_o};

endmodule
