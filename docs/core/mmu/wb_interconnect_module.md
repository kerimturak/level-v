# Wishbone Interconnect Module — Technical Documentation

## Contents

1. [Overview](#overview)
2. [Module Interface](#module-interface)
3. [Address Decoding](#address-decoding)
4. [Slave Map](#slave-map)
5. [Request/Response Routing](#requestresponse-routing)
6. [Error Handling](#error-handling)
7. [Timing Diagrams](#timing-diagrams)
8. [Verification and Testing](#verification-and-testing)

---

## Overview

### Purpose

`wb_interconnect` is a **Wishbone B4**-compatible **1-to-N crossbar interconnect**. It routes memory requests from the CPU to the appropriate slave based on address.

### Key Features

| Feature | Value |
|---------|-------|
| **Bus standard** | Wishbone B4 pipelined |
| **Topology** | 1 master → N slaves |
| **Address decode** | Single-cycle combinational |
| **Slave count** | 3 (RAM, CLINT, PBUS) |
| **Burst support** | Yes (CTI/BTE) |
| **Error handling** | Unmapped address error |

### Wishbone Interconnect Block Diagram

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                           WISHBONE INTERCONNECT                                  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────────────┐                                                           │
│   │   CPU Master    │                                                           │
│   │   (wb_m_i)      │                                                           │
│   └────────┬────────┘                                                           │
│            │                                                                     │
│            ▼                                                                     │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                        ADDRESS DECODER                                   │   │
│   │                                                                          │   │
│   │   addr[31:28] ────┬─────────────────────────────────────────────────────│   │
│   │                   │                                                      │   │
│   │         ┌─────────┴─────────┬──────────────┬──────────────┐             │   │
│   │         │                   │              │              │             │   │
│   │     0x8 (RAM)          0x3 (CLINT)    0x2 (PBUS)     Other            │   │
│   │         │                   │              │              │             │   │
│   │         ▼                   ▼              ▼              ▼             │   │
│   │   slave_sel[0]        slave_sel[1]   slave_sel[2]   addr_valid=0      │   │
│   │                                                      → ERROR           │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                     SLAVE INTERFACES                                     │   │
│   │                                                                          │   │
│   │   ┌──────────┐         ┌──────────┐         ┌──────────┐                │   │
│   │   │   RAM    │         │  CLINT   │         │   PBUS   │                │   │
│   │   │ Slave 0  │         │ Slave 1  │         │ Slave 2  │                │   │
│   │   │0x8xxxxxxx│         │0x3xxxxxxx│         │0x2xxxxxxx│                │   │
│   │   └──────────┘         └──────────┘         └──────────┘                │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Module Interface

### Port Definitions

```systemverilog
module wb_interconnect #(
    parameter int NUM_SLAVES = 3
) (
    input  logic       clk_i,           // System clock
    input  logic       rst_ni,          // Active-low reset

    // Wishbone Master interface (from CPU)
    input  wb_master_t wb_m_i,          // Request from master
    output wb_slave_t  wb_s_o,          // Response to master

    // Wishbone Slave interfaces
    output wb_master_t wb_m_o[NUM_SLAVES],  // Request to slaves
    input  wb_slave_t  wb_s_i[NUM_SLAVES]   // Response from slaves
);
```

### Wishbone Master Signals

```systemverilog
typedef struct packed {
    logic [WB_ADDR_WIDTH-1:0] adr;  // Address
    logic [WB_DATA_WIDTH-1:0] dat;  // Write data
    logic [WB_SEL_WIDTH-1:0]  sel;  // Byte select
    logic                     we;   // Write enable
    logic                     stb;  // Strobe
    logic                     cyc;  // Cycle
    logic [2:0]               cti;  // Cycle Type Identifier
    logic [1:0]               bte;  // Burst Type Extension
} wb_master_t;
```

### Wishbone Slave Signals

```systemverilog
typedef struct packed {
    logic [WB_DATA_WIDTH-1:0] dat;    // Read data
    logic                     ack;    // Acknowledge
    logic                     err;    // Error
    logic                     rty;    // Retry
    logic                     stall;  // Stall
} wb_slave_t;
```

---

## Address Decoding

### Address Decode Logic

```systemverilog
// Slave indices
localparam SLAVE_RAM   = 0;
localparam SLAVE_CLINT = 1;
localparam SLAVE_PBUS  = 2;

logic [NUM_SLAVES-1:0] slave_sel;
logic                  addr_valid;

// Combinational address decode
always_comb begin
    slave_sel  = '0;
    addr_valid = 1'b0;

    case (wb_m_i.adr[31:28])
        4'h8: begin  // RAM
            slave_sel[SLAVE_RAM] = 1'b1;
            addr_valid = 1'b1;
        end
        4'h3: begin  // CLINT
            slave_sel[SLAVE_CLINT] = 1'b1;
            addr_valid = 1'b1;
        end
        4'h2: begin  // Peripheral Bus
            slave_sel[SLAVE_PBUS] = 1'b1;
            addr_valid = 1'b1;
        end
        default: begin
            addr_valid = 1'b0;  // Invalid address → error
        end
    endcase
end
```

### Address Ranges

| Slave | Address range | Size | Description |
|-------|---------------|------|-------------|
| RAM | 0x8000_0000 - 0xFFFF_FFFF | 2GB | Main memory |
| CLINT | 0x3000_0000 - 0x3FFF_FFFF | 256MB | Core-local interruptor |
| PBUS | 0x2000_0000 - 0x2FFF_FFFF | 256MB | Peripheral bus |

---

## Slave Map

### Slave 0: RAM (Main Memory)

```
Address range: 0x8000_0000 - 0xFFFF_FFFF
Size: 2GB (typical use: 128KB - 1MB)

Attributes:
- Cacheable
- Executable
- Read/Write

Usage:
- Program code
- Data
- Stack/heap
```

### Slave 1: CLINT (Core Local Interruptor)

```
Address range: 0x3000_0000 - 0x3000_FFFF
Size: 64KB

Attributes:
- Uncacheable
- Non-executable
- Read/Write

Register Map:
- msip     @ 0x0000: Machine Software Interrupt Pending
- mtimecmp @ 0x4000: Machine Timer Compare
- mtime    @ 0xBFF8: Machine Timer
```

### Slave 2: PBUS (Peripheral Bus)

```
Address range: 0x2000_0000 - 0x2FFF_FFFF
Size: 256MB

Attributes:
- Uncacheable
- Non-executable
- Read/Write

Peripheral Offsets:
0x0000: UART0
0x1000: UART1
0x2000: SPI0
0x3000: I2C0
0x4000: GPIO
0x5000: PWM
0x6000: Timer
0x7000: PLIC
0x8000: Watchdog
0x9000: DMA
0xD000: VGA Control
```

---

## Request/Response Routing

### Request Tracking

Tracks which slave owns the active request:

```systemverilog
logic [1:0] active_slave_q;
logic       req_pending_q;

always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        active_slave_q <= '0;
        req_pending_q  <= 1'b0;
    end else begin
        if (wb_m_i.cyc && wb_m_i.stb && !wb_s_o.stall) begin
            // New request accepted
            for (int i = 0; i < NUM_SLAVES; i++) begin
                if (slave_sel[i]) begin
                    active_slave_q <= i[1:0];
                end
            end
            req_pending_q <= 1'b1;
        end else if (wb_s_o.ack || wb_s_o.err) begin
            // Request completed
            if (wb_m_i.cti == WB_CTI_CLASSIC || wb_m_i.cti == WB_CTI_EOB) begin
                req_pending_q <= 1'b0;
            end
        end
    end
end
```

### Master → Slave Routing

```systemverilog
always_comb begin
    for (int i = 0; i < NUM_SLAVES; i++) begin
        // Broadcast all signals
        wb_m_o[i].adr = wb_m_i.adr;
        wb_m_o[i].dat = wb_m_i.dat;
        wb_m_o[i].sel = wb_m_i.sel;
        wb_m_o[i].we  = wb_m_i.we;
        wb_m_o[i].cti = wb_m_i.cti;
        wb_m_o[i].bte = wb_m_i.bte;

        // Gate strobe and cycle from slave select
        wb_m_o[i].stb = wb_m_i.stb && slave_sel[i];
        wb_m_o[i].cyc = wb_m_i.cyc && 
                        (slave_sel[i] || (req_pending_q && active_slave_q == i[1:0]));
    end
end
```

### Slave → Master Routing

```systemverilog
always_comb begin
    // Default: no response
    wb_s_o.dat   = '0;
    wb_s_o.ack   = 1'b0;
    wb_s_o.err   = 1'b0;
    wb_s_o.rty   = 1'b0;
    wb_s_o.stall = 1'b0;

    if (!addr_valid && wb_m_i.cyc && wb_m_i.stb) begin
        // Invalid address — assert error
        wb_s_o.err = 1'b1;
    end else begin
        // Forward response from selected slave
        for (int i = 0; i < NUM_SLAVES; i++) begin
            if (slave_sel[i] || (req_pending_q && active_slave_q == i[1:0])) begin
                wb_s_o.dat   = wb_s_i[i].dat;
                wb_s_o.ack   = wb_s_i[i].ack;
                wb_s_o.err   = wb_s_i[i].err;
                wb_s_o.rty   = wb_s_i[i].rty;
                wb_s_o.stall = wb_s_i[i].stall;
            end
        end
    end
end
```

---

## Error Handling

### Unmapped Address Error

On access to an invalid address the interconnect automatically asserts error:

```systemverilog
if (!addr_valid && wb_m_i.cyc && wb_m_i.stb) begin
    wb_s_o.err = 1'b1;  // Error response
end
```

### Error Scenarios

| Address | Result | Description |
|---------|--------|-------------|
| 0x0xxx_xxxx | ERROR | Debug module (not implemented) |
| 0x1xxx_xxxx | ERROR | Boot ROM (not implemented) |
| 0x4xxx_xxxx | ERROR | External memory (not implemented) |
| 0x5xxx_xxxx | ERROR | Reserved |
| 0x6xxx_xxxx | ERROR | Reserved |
| 0x7xxx_xxxx | ERROR | Reserved |

---

## Timing Diagrams

### Successful RAM Read

```
clk      ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

wb_m_i   ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────
.cyc

wb_m_i   ────/‾‾‾‾\──────────────────────────────────
.stb

wb_m_i   ────┤0x8000_0000├───────────────────────────
.adr

slave_sel────┤RAM (sel[0]=1)├────────────────────────

wb_s_o   ────────────────────────────────/‾‾‾‾\──────
.ack                                     RAM ack

wb_s_o   ────────────────────────────────┤DATA├──────
.dat
```

### Burst Transfer (Cache Line)

```
clk      ____/‾\____/‾\____/‾\____/‾\____/‾\____

wb_m_i   ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────
.cyc

wb_m_i   ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────
.stb

wb_m_i   ────┤INCR├┤INCR├┤INCR├┤EOB ├──────────────
.cti

wb_m_i   ────┤ +0 ├┤ +4 ├┤ +8 ├┤ +C ├──────────────
.adr

wb_s_o   ────────/‾‾‾‾\────/‾‾‾‾\────/‾‾‾‾\────/‾‾‾‾\
.ack

wb_s_o   ────────┤ W0 ├────┤ W1 ├────┤ W2 ├────┤ W3 ├
.dat
```

### Invalid Address Error

```
clk      ____/‾‾‾‾\____/‾‾‾‾\____

wb_m_i   ────/‾‾‾‾\──────────────
.stb

wb_m_i   ────┤0x0000_0000├───────
.adr        (invalid!)

addr_valid───┤ 0 ├───────────────

wb_s_o   ────/‾‾‾‾\──────────────
.err            │
             Error!
```

---

## Verification and Testing

### Assertions

```systemverilog
// Exactly one slave must be selected
assert property (@(posedge clk_i) disable iff (!rst_ni)
    addr_valid |-> $onehot(slave_sel)
) else $error("Only one slave should be selected");

// Invalid address must assert error
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (!addr_valid && wb_m_i.cyc && wb_m_i.stb) |-> wb_s_o.err
) else $error("Invalid address should generate error");

// ACK and ERR must not be active together
assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(wb_s_o.ack && wb_s_o.err)
) else $error("ACK and ERR cannot be active simultaneously");
```

### Test Scenarios

1. **Address decode**
   - Access each slave range
   - Boundary address tests

2. **Error generation**
   - Invalid address access
   - Access to reserved regions

3. **Burst transfer**
   - Cache-line burst
   - CTI/BTE combinations

4. **Stall handling**
   - Slave stall
   - Master wait

---

## Summary

The `wb_interconnect` module:

1. **Simple 1-to-N routing**: One master, multiple slaves
2. **Address-based selection**: Upper 4-bit address decode
3. **Wishbone B4 compliant**: Pipelined, burst-capable
4. **Error handling**: Unmapped-address protection
5. **Low latency**: Combinational decode

It connects the CPU to memory and peripherals in the Level SoC.
