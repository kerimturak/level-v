# Wishbone RAM Slave - Technical Documentation

## Contents

1. [Overview](#overview)
2. [Module Interface](#module-interface)
3. [Latency Pipeline](#latency-pipeline)
4. [Byte-Enable Writes](#byte-enable-yazma)
5. [Burst Support](#burst-support)

---

## Overview

### Purpose

The `wb_ram_slave` module, interfaces the Wishbone bus to a RAM module. supports configurable latency and byte-granular writes.

### File Location

```
rtl/wrapper/wb_ram_slave.sv
```

### RAM Slave Architecture

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          WB_RAM_SLAVE                                            │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│    Wishbone Interface              Latency Pipeline         RAM Interface       │
│                                                                                  │
│    ┌────────────┐               ┌─────────────────┐      ┌────────────────┐    │
│    │  cyc/stb   │──────────────►│                 │      │                │    │
│    │  we        │               │   Delay Shift   │─────►│   ram_we_o     │    │
│    │  addr      │──────────────►│   Register      │─────►│   ram_addr_o   │    │
│    │  wdata     │──────────────►│   (LATENCY)     │─────►│   ram_wdata_o  │    │
│    │  sel       │──────────────►│                 │─────►│   ram_wstrb_o  │    │
│    └────────────┘               └────────┬────────┘      └───────┬────────┘    │
│                                          │                       │             │
│    ┌────────────┐                        │                       │             │
│    │  ack       │◄───────────────────────┘                       │             │
│    │  rdata     │◄───────────────────────────────────────────────┘             │
│    │  err       │◄─── (1'b0)             │   ram_rdata_i                       │
│    └────────────┘                        │                                     │
│                                          │                                     │
│                     Latency: LATENCY cycles from req to ack                    │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Module Interface

### Parametreler

```systemverilog
module wb_ram_slave
  import level_param::*;
#(
    parameter int LATENCY = 1  // RAM access latency (cycles)
)
```

### Port Definitions

```systemverilog
(
    input  logic clk_i,
    input  logic rst_ni,

    // Wishbone Slave Interface
    input  wb_master_t wb_m_i,    // Master request
    output wb_slave_t  wb_s_o,    // Slave response

    // RAM Interface
    output logic        ram_we_o,     // Write enable
    output logic [31:0] ram_addr_o,   // Address
    output logic [31:0] ram_wdata_o,  // Write data
    output logic [3:0]  ram_wstrb_o,  // Byte strobes
    input  logic [31:0] ram_rdata_i   // Read data
);
```

---

## Latency Pipeline

### Delay Shift Register

```systemverilog
// Shift register for request tracking
logic [LATENCY-1:0] req_delay_q;
logic [LATENCY-1:0] we_delay_q;

wire wb_req = wb_m_i.cyc && wb_m_i.stb;

always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        req_delay_q <= '0;
        we_delay_q  <= '0;
    end else begin
        // Shift request through pipeline
        req_delay_q <= {req_delay_q[LATENCY-2:0], wb_req};
        we_delay_q  <= {we_delay_q[LATENCY-2:0], wb_req && wb_m_i.we};
    end
end
```

### ACK Generation

```systemverilog
// ACK arrives LATENCY cycles after request
assign wb_s_o.ack = req_delay_q[LATENCY-1];
```

### Timing Diagram (LATENCY=2)

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └───

wb_req         ┌───────┐
           ────┘       └───────────────────

req_delay[0]       ┌───────┐
           ────────┘       └───────────────

req_delay[1]           ┌───────┐
(= ack)    ────────────┘       └───────────

           ├─T0─┼─T1─┼─T2─┤
           req  delay ack
```

---

## Byte-Enable Writes

### Write Strobe Handling

```systemverilog
// Direct passthrough of byte enables
assign ram_we_o    = wb_req && wb_m_i.we;
assign ram_addr_o  = wb_m_i.adr;
assign ram_wdata_o = wb_m_i.dat;
assign ram_wstrb_o = wb_m_i.sel;
```

### RAM Implementation Requirements

```systemverilog
// RAM module should support byte enables:
always_ff @(posedge clk) begin
    if (we) begin
        if (wstrb[0]) mem[addr][7:0]   <= wdata[7:0];
        if (wstrb[1]) mem[addr][15:8]  <= wdata[15:8];
        if (wstrb[2]) mem[addr][23:16] <= wdata[23:16];
        if (wstrb[3]) mem[addr][31:24] <= wdata[31:24];
    end
end
```

### Store Instructions Mapping

| Instruction | sel | Bytes Written |
|-------------|-----|---------------|
| SW | 4'b1111 | All 4 bytes |
| SH (addr[1:0]=0) | 4'b0011 | Bytes 0,1 |
| SH (addr[1:0]=2) | 4'b1100 | Bytes 2,3 |
| SB (addr[1:0]=0) | 4'b0001 | Byte 0 |
| SB (addr[1:0]=1) | 4'b0010 | Byte 1 |
| SB (addr[1:0]=2) | 4'b0100 | Byte 2 |
| SB (addr[1:0]=3) | 4'b1000 | Byte 3 |

---

## Burst Support

### Burst Detection

```systemverilog
wire is_burst = (wb_m_i.cti == WB_CTI_INCR) ||
                (wb_m_i.cti == WB_CTI_EOB);
wire is_burst_end = (wb_m_i.cti == WB_CTI_EOB);
```

### Burst State Machine

```systemverilog
logic burst_active;
logic [1:0] burst_cnt;

always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        burst_active <= 1'b0;
        burst_cnt    <= '0;
    end else begin
        if (wb_req && !burst_active && (wb_m_i.cti == WB_CTI_INCR)) begin
            // Start of burst
            burst_active <= 1'b1;
            burst_cnt    <= '0;
        end else if (burst_active && wb_req) begin
            burst_cnt <= burst_cnt + 1;
            if (is_burst_end) begin
                burst_active <= 1'b0;
            end
        end
    end
end
```

### Burst Timing (4-beat)

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └───

wb_m_i.cyc     ┌───────────────────────────┐
           ────┘                           └───

wb_m_i.stb     ┌───┐   ┌───┐   ┌───┐   ┌───┐
           ────┘   └───┘   └───┘   └───┘   └───

wb_m_i.cti ────┤INCR├───┤INCR├───┤INCR├───┤EOB├───

wb_m_i.adr ────┤ A0 ├───┤ A1 ├───┤ A2 ├───┤ A3 ├───

wb_s_o.ack         ┌───┐   ┌───┐   ┌───┐   ┌───┐
           ────────┘   └───┘   └───┘   └───┘   └───

wb_s_o.dat     ────┤ D0├───┤ D1├───┤ D2├───┤ D3├───
```

---

## Response Signals

```systemverilog
// Read data from RAM (combinational or pipelined)
assign wb_s_o.dat = ram_rdata_i;

// No error or retry
assign wb_s_o.err = 1'b0;
assign wb_s_o.rty = 1'b0;
```

---

## Configuration Examples

### Single-Cycle RAM

```systemverilog
wb_ram_slave #(
    .LATENCY(1)
) i_ram_slave (
    .clk_i     (clk),
    .rst_ni    (rst_n),
    .wb_m_i    (wb_m),
    .wb_s_o    (wb_s),
    .ram_we_o  (ram_we),
    .ram_addr_o(ram_addr),
    .ram_wdata_o(ram_wdata),
    .ram_wstrb_o(ram_wstrb),
    .ram_rdata_i(ram_rdata)
);
```

### Multi-Cycle RAM (External Memory)

```systemverilog
wb_ram_slave #(
    .LATENCY(16)  // Slow external memory
) i_ext_ram_slave (
    .clk_i     (clk),
    .rst_ni    (rst_n),
    .wb_m_i    (wb_m),
    .wb_s_o    (wb_s),
    .ram_we_o  (ram_we),
    .ram_addr_o(ram_addr),
    .ram_wdata_o(ram_wdata),
    .ram_wstrb_o(ram_wstrb),
    .ram_rdata_i(ram_rdata)
);
```

---

## Summary

The `wb_ram_slave` module:

1. **Configurable Latency**: LATENCY parametresi
2. **Byte Enable**: Full sel/wstrb support
3. **Burst Support**: CTI/BTE handling
4. **Simple Interface**: Direct RAM connection

This module connects the Wishbone bus to RAM modules.
