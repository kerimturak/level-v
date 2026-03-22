# Level SoC Wrapper - Technical Documentation

## Contents

1. [Overview](#overview)
2. [Module Interface](#module-interface)
3. [Wishbone Bus Architecture](#wishbone-bus-architecture)
4. [Memory Map](#memory-map)
5. [Peripheral Integration](#peripheral-integration)
6. [RAM and Burst Transfer](#ram-and-burst-transfer)
7. [CLINT and Interrupts](#clint-and-interrupts)
8. [Programming Interface](#programming-interface)

---

## Overview

### Purpose

The `level_wrapper` module is the top-level wrapper integrating the Level RISC-V core into the SoC using the **Wishbone B4** bus. It manages connections among the CPU, memory, CLINT, and peripherals.

### File Location

```
rtl/wrapper/level_wrapper.sv
```

### Bus Topology

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          LEVEL SOC WRAPPER                                       │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌───────────┐     ┌──────────────┐     ┌──────────────────┐                   │
│   │           │     │              │     │                  │                   │
│   │    CPU    │────►│  WB Master   │────►│  WB Interconnect │                   │
│   │  (iomem)  │     │   Bridge     │     │    (1-to-N)      │                   │
│   │           │     │              │     │                  │                   │
│   └───────────┘     └──────────────┘     └────────┬─────────┘                   │
│                                                   │                              │
│                           ┌───────────────────────┼───────────────────┐         │
│                           │                       │                   │         │
│                           ▼                       ▼                   ▼         │
│                    ┌────────────┐          ┌────────────┐      ┌────────────┐   │
│                    │   RAM      │          │   CLINT    │      │   PBUS     │   │
│                    │  Slave     │          │   Slave    │      │   Slave    │   │
│                    │ (0x8xxx)   │          │ (0x3xxx)   │      │ (0x2xxx)   │   │
│                    └─────┬──────┘          └─────┬──────┘      └─────┬──────┘   │
│                          │                       │                   │          │
│                          ▼                       ▼                   ▼          │
│                    ┌────────────┐          ┌────────────┐      ┌────────────┐   │
│                    │  wrapper   │          │   mtime    │      │   UART     │   │
│                    │    RAM     │          │  mtimecmp  │      │   SPI      │   │
│                    │            │          │   msip     │      │   I2C      │   │
│                    └────────────┘          └────────────┘      └────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Module Interface

### Parametreler

```systemverilog
module level_wrapper
  import level_param::*;
#(
    // System Configuration
    parameter int unsigned CLK_FREQ_HZ = CPU_CLK,      // 50 MHz
    parameter int unsigned BAUD_RATE   = 115200,

    // Memory Configuration
    parameter int unsigned RAM_SIZE_KB = 1024,         // 1 MB
    parameter int unsigned RAM_LATENCY = 16,           // cycles

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
)
```

### Port Definitions

```systemverilog
(
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    // UART Interface
    output logic uart_tx_o,
    input  logic uart_rx_i,

    // SPI Interface
    output logic       spi0_sclk_o,
    output logic       spi0_mosi_o,
    input  logic       spi0_miso_i,
    output logic [3:0] spi0_ss_o,

    // I2C Interface
    inout wire i2c0_sda_io,
    inout wire i2c0_scl_io,

    // GPIO Interface
    input  logic [31:0] gpio_i,
    output logic [31:0] gpio_o,
    output logic [31:0] gpio_oe_o,

    // External Interrupts
    input logic [7:0] ext_irq_i,

    // Programming Interface
    input  logic program_rx_i,
    output logic prog_mode_led_o,

    // Status
    output logic [3:0] status_led_o
);
```

---

## Wishbone Bus Architecture

### Slave Definitions

```systemverilog
// Wishbone Slave IDs
localparam int SLV_RAM   = 0;  // 0x8000_0000
localparam int SLV_CLINT = 1;  // 0x3000_0000
localparam int SLV_PBUS  = 2;  // 0x2000_0000
localparam int WB_NUM_SLAVES_LOCAL = 3;
```

### Bus Signals

```systemverilog
// CPU → Wishbone Master Bridge
iomem_req_t cpu_mem_req;
iomem_res_t cpu_mem_res;

// Wishbone Master
wb_master_t wb_cpu_m;
wb_slave_t  wb_cpu_s;

// Wishbone Slave array
wb_master_t wb_slave_m[WB_NUM_SLAVES_LOCAL];
wb_slave_t  wb_slave_s[WB_NUM_SLAVES_LOCAL];
```

### Interconnect

```systemverilog
wb_interconnect #(
    .NUM_SLAVES(WB_NUM_SLAVES_LOCAL)
) i_wb_interconnect (
    .clk_i (clk_i),
    .rst_ni(sys_rst_n),
    .wb_m_i(wb_cpu_m),        // Master input
    .wb_s_o(wb_cpu_s),        // Master response
    .wb_m_o(wb_slave_m),      // Slave requests
    .wb_s_i(wb_slave_s)       // Slave responses
);
```

---

## Memory Map

### Address Decode

```systemverilog
// Interconnect internal decode
// 0x8xxx_xxxx → SLV_RAM
// 0x3xxx_xxxx → SLV_CLINT
// 0x2xxx_xxxx → SLV_PBUS
```

### Peripheral Bus Decode

```systemverilog
// PBUS internal decode (addr[19:16])
assign uart_sel = (pbus_addr[19:16] == 4'h0);  // 0x2000_0xxx
assign spi_sel  = (pbus_addr[19:16] == 4'h1);  // 0x2001_0xxx
assign i2c_sel  = (pbus_addr[19:16] == 4'h2);  // 0x2002_0xxx
```

---

## Peripheral Integration

### UART

```systemverilog
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
```

### SPI Master

```systemverilog
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
```

### I2C Master

```systemverilog
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
```

---

## RAM and Burst Transfer

### Burst State Machine

The RAM module supports cache-line burst transfers:

```systemverilog
// Burst detection
wire ram_is_burst = (wb_slave_m[SLV_RAM].cti == WB_CTI_INCR) ||
                    (wb_slave_m[SLV_RAM].cti == WB_CTI_EOB);
wire ram_is_burst_start = ram_wb_req && !ram_wb_we &&
                          (wb_slave_m[SLV_RAM].cti == WB_CTI_INCR) &&
                          !ram_burst_active;
wire ram_is_burst_end = ram_burst_active &&
                        (wb_slave_m[SLV_RAM].cti == WB_CTI_EOB);
```

### Burst Data Capture

```systemverilog
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        ram_burst_data_valid <= 1'b0;
    end else begin
        // First beat: capture data after RAM latency
        if (ram_delay_q[RAM_LATENCY-1] && !ram_burst_data_valid) begin
            ram_burst_data_q     <= ram_rdata;  // Full cache line
            ram_burst_data_valid <= 1'b1;
            ram_burst_active     <= ram_is_burst;
            ram_burst_cnt        <= '0;
        end
        // Subsequent beats: immediate ACK
        else if (ram_burst_active && ram_wb_req && ram_burst_data_valid) begin
            ram_burst_cnt <= ram_burst_cnt + 1;
            if (ram_is_burst_end) begin
                ram_burst_active     <= 1'b0;
                ram_burst_data_valid <= 1'b0;
            end
        end
    end
end
```

### Word Extraction

```systemverilog
// Extract the correct word from the cache line
always_comb begin
    logic [1:0] word_offset;
    word_offset  = ram_wb_addr[3:2];  // Word select within the 16-byte line
    if (ram_burst_data_valid) begin
        ram_wb_rdata = ram_burst_data_q[word_offset*32+:32];
    end else begin
        ram_wb_rdata = ram_rdata[word_offset*32+:32];
    end
end
```

---

## CLINT and Interrupts

### CLINT Slave

```systemverilog
wb_clint_slave i_wb_clint (
    .clk_i      (clk_i),
    .rst_ni     (sys_rst_n),
    .wb_m_i     (wb_slave_m[SLV_CLINT]),
    .wb_s_o     (wb_slave_s[SLV_CLINT]),
    .timer_irq_o(timer_irq),
    .sw_irq_o   (sw_irq)
);
```

### CPU Interrupt Connection

```systemverilog
cpu i_soc (
    .clk_i      (clk_i),
    .rst_ni     (sys_rst_n),
    .timer_irq_i(timer_irq),    // CLINT timer
    .sw_irq_i   (sw_irq),       // CLINT software
    .ext_irq_i  (|ext_irq_i),   // External
    .iomem_req_o(cpu_mem_req),
    .iomem_res_i(cpu_mem_res)
);
```

---

## Programming Interface

### Reset Management

```systemverilog
// Verilator'da program reset bypass
`ifdef VERILATOR
    assign sys_rst_n = rst_ni;
`else
    assign sys_rst_n = rst_ni & prog_reset;
`endif
```

### RAM Programmer

```systemverilog
wrapper_ram #(
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
```

---

## Summary

The `level_wrapper` module:

1. **Wishbone B4 bus**: CPU ↔ peripheral communication
2. **3 Slave**: RAM, CLINT, PBUS
3. **Burst Support**: Cache line transfer
4. **Peripherals**: UART, SPI, I2C
5. **Interrupts**: Timer, SW, External
6. **Programming**: RAM programming over UART

This module is the main integration point of the Level SoC.
