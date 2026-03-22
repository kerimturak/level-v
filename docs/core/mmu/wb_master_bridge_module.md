# Wishbone Master Bridge Module — Technical Documentation

## Contents

1. [Overview](#overview)
2. [Module Interface](#module-interface)
3. [State Machine](#state-machine)
4. [Transfer Modes](#transfer-modes)
5. [Burst Operations](#burst-operations)
6. [Stall and Error Handling](#stall-and-error-handling)
7. [Timing and Latency](#timing-and-latency)
8. [Verification and Debug](#verification-and-debug)

---

## Overview

### Purpose

`wb_master_bridge` bridges the CPU’s internal memory interface (`iomem`) and the **Wishbone B4** bus protocol. It converts a simple ready/valid request–response interface into Wishbone pipelined transactions.

### Key Features

| Feature | Value |
|---------|-------|
| **Input protocol** | iomem (ready/valid) |
| **Output protocol** | Wishbone B4 pipelined |
| **Burst support** | Incrementing (4-beat) |
| **Address alignment** | 4-byte (word aligned) |
| **Byte enable** | 4-bit select |
| **Error handling** | Pass-through |

### Block Diagram

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          WISHBONE MASTER BRIDGE                                  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────────────┐                              ┌─────────────────┐          │
│   │   iomem_i       │                              │   wb_m_o        │          │
│   │   (CPU side)    │                              │   (Bus side)    │          │
│   │                 │                              │                 │          │
│   │  .valid    ────┼──────────────────────────────┼──→ .stb         │          │
│   │  .addr     ────┼──────────────────────────────┼──→ .adr         │          │
│   │  .wdata    ────┼──────────────────────────────┼──→ .dat         │          │
│   │  .we       ────┼──────────────────────────────┼──→ .we          │          │
│   │  .sel      ────┼──────────────────────────────┼──→ .sel         │          │
│   │  .burst    ────┼──────────────────────────────┼──→ .cti/.bte    │          │
│   │                 │                              │                 │          │
│   │  .ready   ◄────┼──────────────────────────────┼─── .ack/.stall  │          │
│   │  .rdata   ◄────┼──────────────────────────────┼─── .dat         │          │
│   │  .err     ◄────┼──────────────────────────────┼─── .err         │          │
│   └─────────────────┘                              └─────────────────┘          │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                          STATE MACHINE                                   │   │
│   │                                                                          │   │
│   │                    ┌─────────────────┐                                   │   │
│   │         ┌─────────►│      IDLE       │◄──────────────┐                  │   │
│   │         │          └────────┬────────┘               │                  │   │
│   │         │                   │ valid                  │                  │   │
│   │         │                   ▼                        │                  │   │
│   │         │          ┌─────────────────┐               │                  │   │
│   │     ack │          │     REQUEST     │               │                  │   │
│   │  (single)          └────────┬────────┘               │                  │   │
│   │         │                   │ burst?                 │ last + ack       │   │
│   │         │         ┌─────────┴─────────┐              │                  │   │
│   │         │         │                   │              │                  │   │
│   │         │         ▼                   ▼              │                  │   │
│   │    ┌────┴────┐         ┌─────────────────┐           │                  │   │
│   │    │ WAIT_   │         │     BURST       │───────────┘                  │   │
│   │    │ ACK     │         │ (count beats)   │                              │   │
│   │    └─────────┘         └─────────────────┘                              │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Module Interface

### Port Definitions

```systemverilog
module wb_master_bridge
  import level_param::*;
(
    input  logic       clk_i,        // System clock
    input  logic       rst_ni,       // Active-low reset

    // iomem interface (CPU side)
    input  iomem_req_t iomem_i,      // Request
    output iomem_rsp_t iomem_o,      // Response

    // Wishbone master interface
    output wb_master_t wb_m_o,       // Signals to bus
    input  wb_slave_t  wb_s_i        // Signals from bus
);
```

### iomem Request Structure

```systemverilog
typedef struct packed {
    logic                     valid;   // Request valid
    logic [XLEN-1:0]          addr;    // Address
    logic [XLEN-1:0]          wdata;   // Write data
    logic                     we;      // Write enable
    logic [WB_SEL_WIDTH-1:0]  sel;     // Byte select
    logic                     burst;   // Burst mode
    logic [1:0]               burst_cnt; // Burst counter (0-3)
} iomem_req_t;
```

### iomem Response Structure

```systemverilog
typedef struct packed {
    logic                ready;   // Transfer complete
    logic [XLEN-1:0]     rdata;   // Read data
    logic                err;     // Error
} iomem_rsp_t;
```

---

## State Machine

### State Definitions

```systemverilog
typedef enum logic [1:0] {
    IDLE,       // Idle, waiting for request
    REQUEST,    // Request sent, waiting for response
    BURST,      // Burst mode, counting beats
    WAIT_ACK    // Waiting for final ACK
} state_e;

state_e state_q, state_d;
```

### State Transitions

```systemverilog
always_comb begin
    state_d = state_q;

    case (state_q)
        IDLE: begin
            if (iomem_i.valid) begin
                if (iomem_i.burst) begin
                    state_d = BURST;
                end else begin
                    state_d = REQUEST;
                end
            end
        end

        REQUEST: begin
            if (wb_s_i.ack || wb_s_i.err) begin
                state_d = IDLE;
            end
        end

        BURST: begin
            if (wb_s_i.ack || wb_s_i.err) begin
                if (burst_cnt_q == WB_BURST_LEN - 1) begin
                    state_d = IDLE;  // Last beat
                end
                // Else: burst continues
            end
        end

        WAIT_ACK: begin
            if (wb_s_i.ack || wb_s_i.err) begin
                state_d = IDLE;
            end
        end
    endcase
end
```

### State Machine Diagram

```
                    ┌─────────────────────────────────────────────┐
                    │                                             │
                    ▼                                             │
             ┌──────────┐                                         │
    ──reset──►   IDLE   │                                         │
             └────┬─────┘                                         │
                  │                                               │
                  │ valid                                         │
                  ▼                                               │
          ┌───────────────┐                                       │
          │  burst mode?  │                                       │
          └───────┬───────┘                                       │
                  │                                               │
         ┌────────┴────────┐                                      │
         │ yes             │ no                                   │
         ▼                 ▼                                      │
   ┌──────────┐      ┌──────────┐                                │
   │  BURST   │      │ REQUEST  │                                │
   └────┬─────┘      └────┬─────┘                                │
        │                 │                                       │
        │                 │ ack/err ───────────────────────────────►
        │                 │
        │ count beats     │
        │                 │
        ▼                 │
   ┌──────────┐          │
   │  last    │──────────┘
   │  beat?   │
   └──────────┘
```

---

## Transfer Modes

### Single Transfer (Classic)

Single-word read or write:

```systemverilog
// CTI = Classic (single transfer)
wb_m_o.cti = WB_CTI_CLASSIC;  // 3'b000
wb_m_o.bte = 2'b00;           // Linear (don't care)
```

**Timing:**

```
clk    ____/‾\____/‾\____/‾\____

iomem  ────/‾‾‾‾\────────────────
.valid

wb_m   ────/‾‾‾‾‾‾‾‾\────────────
.cyc

wb_m   ────/‾‾‾‾\────────────────
.stb

wb_s   ────────────/‾\───────────
.ack

iomem  ────────────/‾\───────────
.ready
```

### Burst Transfer (Incrementing)

Four-beat burst for cache-line fetch:

```systemverilog
// CTI encoding during burst
case (burst_cnt_q)
    2'b00, 2'b01, 2'b10: begin
        wb_m_o.cti = WB_CTI_INCR;  // 3'b010 - Incrementing
    end
    2'b11: begin
        wb_m_o.cti = WB_CTI_EOB;   // 3'b111 - End of Burst
    end
endcase

wb_m_o.bte = 2'b00;  // Linear burst
```

**Timing:**

```
clk      ____/‾\____/‾\____/‾\____/‾\____/‾\____

iomem    ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────────
.valid

wb_m.cyc ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──────

wb_m.stb ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──────

wb_m.cti ────┤INCR├┤INCR├┤INCR├┤EOB ├───────────

wb_m.adr ────┤ +0 ├┤ +4 ├┤ +8 ├┤ +C ├───────────

wb_s.ack ────────/‾\────/‾\────/‾\────/‾\────────

burst_cnt────┤ 0  ├┤ 1  ├┤ 2  ├┤ 3  ├───────────

iomem    ────────/‾\────/‾\────/‾\────/‾\────────
.ready          W0    W1    W2    W3
```

---

## Burst Operations

### Burst Counter

```systemverilog
logic [1:0] burst_cnt_q, burst_cnt_d;
logic [XLEN-1:0] burst_addr_q, burst_addr_d;

// Burst counter update
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        burst_cnt_q  <= '0;
        burst_addr_q <= '0;
    end else begin
        burst_cnt_q  <= burst_cnt_d;
        burst_addr_q <= burst_addr_d;
    end
end

always_comb begin
    burst_cnt_d  = burst_cnt_q;
    burst_addr_d = burst_addr_q;

    case (state_q)
        IDLE: begin
            if (iomem_i.valid && iomem_i.burst) begin
                burst_cnt_d  = '0;
                burst_addr_d = iomem_i.addr;
            end
        end

        BURST: begin
            if (wb_s_i.ack && !wb_s_i.stall) begin
                burst_cnt_d  = burst_cnt_q + 1'b1;
                burst_addr_d = burst_addr_q + 4;  // Word increment
            end
        end
    endcase
end
```

### Address Computation

```systemverilog
// Address auto-increments in burst mode
always_comb begin
    if (state_q == BURST) begin
        wb_m_o.adr = burst_addr_q;
    end else begin
        wb_m_o.adr = iomem_i.addr;
    end
end
```

### Burst Length

```systemverilog
// Cache line size: 128 bit = 4 × 32-bit words
localparam WB_BURST_LEN = 4;

// Burst complete when:
logic burst_done;
assign burst_done = (burst_cnt_q == WB_BURST_LEN - 1) && wb_s_i.ack;
```

---

## Stall and Error Handling

### Stall Handling

In Wishbone B4 pipelined mode the slave can use `stall` for flow control:

```systemverilog
// Hold request while stalled
logic stalled_q;

always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        stalled_q <= 1'b0;
    end else begin
        stalled_q <= wb_s_i.stall && wb_m_o.cyc;
    end
end

// Strobe only when not stalled
assign wb_m_o.stb = (state_q == REQUEST || state_q == BURST) && !stalled_q;
```

**Stall timing:**

```
clk      ____/‾\____/‾\____/‾\____/‾\____

wb_m.stb ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────────

wb_s.stall────────/‾‾‾‾\────────────────
                    │
                  Hold

wb_s.ack ────────────────────/‾\────────
```

### Error Handling

```systemverilog
// Error signal passed through
assign iomem_o.err = wb_s_i.err;

// On error, transaction ends
always_comb begin
    if (wb_s_i.err) begin
        state_d = IDLE;
        // Abort entire transaction including burst
    end
end
```

---

## Timing and Latency

### Latency Values

| Operation | Latency (cycles) | Description |
|-----------|------------------|-------------|
| Single read | 2-3 | Request + ACK |
| Single write | 2-3 | Request + ACK |
| Burst read (4) | 5-8 | Four beats + overhead |
| Burst write (4) | 5-8 | Four beats + overhead |
| Stalled request | +N | Additional stall cycles |

### Throughput

**In burst mode:**
- Best case: 1 word/cycle (back-to-back ACK)
- Typical: 0.8 word/cycle (occasional stall)

**In single mode:**
- 0.33-0.5 word/cycle (overhead)

### Pipeline Diagram

```
Cycle:    0     1     2     3     4     5     6
          │     │     │     │     │     │     │
          ▼     ▼     ▼     ▼     ▼     ▼     ▼

Burst:   REQ0──REQ1──REQ2──REQ3
              │     │     │     │
         ACK0──ACK1──ACK2──ACK3
              │     │     │     │
         DAT0  DAT1  DAT2  DAT3


Single:  REQ0────────ACK0
                     │
                    DAT0

              REQ1────────ACK1
                          │
                         DAT1
```

---

## Verification and Debug

### Wishbone Protocol Assertions

```systemverilog
// STB must only be asserted when CYC is active
assert property (@(posedge clk_i) disable iff (!rst_ni)
    wb_m_o.stb |-> wb_m_o.cyc
) else $error("STB requires CYC");

// After ACK, STB must deassert (single mode)
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (wb_s_i.ack && wb_m_o.cti == WB_CTI_CLASSIC) |=> !wb_m_o.stb
) else $error("STB should deassert after ACK in classic mode");

// Burst CTI transitions must be legal
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (wb_m_o.cti == WB_CTI_EOB && wb_s_i.ack) |=> !wb_m_o.cyc
) else $error("CYC should deassert after EOB+ACK");

// Error and ACK must not be active together
assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(wb_s_i.ack && wb_s_i.err)
) else $error("ACK and ERR conflict");
```

### Debug Signals

```systemverilog
`ifdef DEBUG_WB_BRIDGE
    // State machine debug output
    always_ff @(posedge clk_i) begin
        if (state_q != state_d) begin
            $display("[WB_BRIDGE] State: %s -> %s @ %0t",
                     state_q.name(), state_d.name(), $time);
        end

        if (wb_s_i.ack) begin
            $display("[WB_BRIDGE] ACK addr=0x%08x data=0x%08x @ %0t",
                     wb_m_o.adr, wb_s_i.dat, $time);
        end

        if (wb_s_i.err) begin
            $display("[WB_BRIDGE] ERROR addr=0x%08x @ %0t",
                     wb_m_o.adr, $time);
        end
    end
`endif
```

### Test Scenarios

1. **Single transfer**
   - Read/write with all byte-enable combinations
   - Back-to-back single transfers

2. **Burst transfer**
   - 4-beat burst read
   - 4-beat burst write
   - Stalled burst

3. **Error conditions**
   - Error during single transfer
   - Error during burst (mid-burst abort)

4. **Stall scenarios**
   - Continuous stall
   - Intermittent stall
   - Stall at burst boundary

---

## Summary

The `wb_master_bridge` module:

1. **Protocol conversion**: iomem ↔ Wishbone B4
2. **Burst support**: 4-beat incrementing burst
3. **Pipelined operation**: Low-latency transfers
4. **Error handling**: Pass-through error signaling
5. **Flow control**: Stall signal support

It is the key block connecting the CPU core to the Wishbone-based SoC bus.
