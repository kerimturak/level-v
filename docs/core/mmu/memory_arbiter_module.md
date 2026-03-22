# Memory Arbiter Module — Technical Documentation

## Contents

1. [Overview](#overview)
2. [Module Interface](#module-interface)
3. [Arbitration Logic](#arbitration-logic)
4. [State Machine](#state-machine)
5. [Data Paths](#data-paths)
6. [Timing Diagrams](#timing-diagrams)
7. [Performance Analysis](#performance-analysis)
8. [Verification and Testing](#verification-and-testing)

---

## Overview

### Purpose

The `memory_arbiter` module arbitrates memory access between the I-Cache and D-Cache. In a Von Neumann organization it multiplexes both caches onto a single memory interface.

### Key Features

| Feature | Value |
|---------|-------|
| **Arbitration type** | Round-robin |
| **Priority** | Equal (fair scheduling) |
| **Latching** | Requests are registered |
| **Pipeline** | Single-stage |
| **Burst support** | Yes (cache line) |

### Memory Arbiter Block Diagram

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              MEMORY ARBITER                                      │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────────┐                                   ┌─────────────┐             │
│   │   I-Cache   │                                   │   D-Cache   │             │
│   │   Request   │                                   │   Request   │             │
│   └──────┬──────┘                                   └──────┬──────┘             │
│          │                                                 │                     │
│          ▼                                                 ▼                     │
│   ┌─────────────┐                                   ┌─────────────┐             │
│   │   icache_   │                                   │   dcache_   │             │
│   │   req_reg   │                                   │   req_reg   │             │
│   │  (latch)    │                                   │  (latch)    │             │
│   └──────┬──────┘                                   └──────┬──────┘             │
│          │                                                 │                     │
│          └──────────────────┬──────────────────────────────┘                     │
│                             │                                                    │
│                             ▼                                                    │
│                    ┌─────────────────┐                                          │
│                    │   ROUND-ROBIN   │                                          │
│                    │   STATE MACHINE │                                          │
│                    │  ┌───────────┐  │                                          │
│                    │  │   IDLE    │──┼──▶ Wait for request                      │
│                    │  │   ICACHE  │──┼──▶ I-Cache service                       │
│                    │  │   DCACHE  │──┼──▶ D-Cache service                       │
│                    │  └───────────┘  │                                          │
│                    └────────┬────────┘                                          │
│                             │                                                    │
│                             ▼                                                    │
│                    ┌─────────────────┐                                          │
│                    │    iomem_req    │                                          │
│                    │      (out)      │                                          │
│                    └────────┬────────┘                                          │
│                             │                                                    │
│                             ▼                                                    │
│                    ┌─────────────────┐                                          │
│                    │   Wishbone Bus  │                                          │
│                    │   (to memory)   │                                          │
│                    └─────────────────┘                                          │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Module Interface

### Port Definitions

```systemverilog
module memory_arbiter (
    input  logic       clk_i,           // System clock
    input  logic       rst_ni,          // Active-low reset
    
    // I-Cache interface
    input  ilowX_req_t icache_req_i,    // I-Cache request
    output ilowX_res_t icache_res_o,    // I-Cache response
    
    // D-Cache interface
    input  dlowX_req_t dcache_req_i,    // D-Cache request
    output dlowX_res_t dcache_res_o,    // D-Cache response
    
    // Memory interface
    input  iomem_res_t iomem_res_i,     // Memory response
    output iomem_req_t iomem_req_o      // Memory request
);
```

### Port Descriptions

| Port | Direction | Type | Description |
|------|-----------|------|-------------|
| `clk_i` | Input | logic | System clock |
| `rst_ni` | Input | logic | Active-low reset |
| `icache_req_i` | Input | ilowX_req_t | I-Cache memory request |
| `icache_res_o` | Output | ilowX_res_t | I-Cache memory response |
| `dcache_req_i` | Input | dlowX_req_t | D-Cache memory request |
| `dcache_res_o` | Output | dlowX_res_t | D-Cache memory response |
| `iomem_res_i` | Input | iomem_res_t | Lower-level memory response |
| `iomem_req_o` | Output | iomem_req_t | Lower-level memory request |

### Request/Response Structures

```systemverilog
// I-Cache request structure
typedef struct packed {
    logic [XLEN-1:0] addr;      // Memory address
    logic            valid;     // Request valid
    logic            ready;     // Cache ready
    logic            uncached;  // Uncached access
} ilowX_req_t;

// I-Cache response structure
typedef struct packed {
    logic [BLK_SIZE-1:0] blk;   // Cache line data
    logic                valid; // Response valid
    logic                ready; // Arbiter ready
} ilowX_res_t;

// D-Cache request structure
typedef struct packed {
    logic [XLEN-1:0]    addr;      // Memory address
    logic [BLK_SIZE-1:0] data;     // Write data
    logic               valid;     // Request valid
    logic               rw;        // 0: Read, 1: Write
    logic [1:0]         rw_size;   // 01:byte, 10:half, 11:word
    logic               uncached;  // Uncached access
} dlowX_req_t;

// D-Cache response structure
typedef struct packed {
    logic [BLK_SIZE-1:0] data;  // Read data
    logic                valid; // Response valid
    logic                ready; // Arbiter ready
} dlowX_res_t;
```

---

## Arbitration Logic

### Round-Robin State Machine

```systemverilog
typedef enum logic [1:0] {
    IDLE,     // Idle, waiting for request
    ICACHE,   // I-Cache being serviced
    DCACHE    // D-Cache being serviced
} round_e;

round_e round;
```

### Request Latching

Requests are registered so single-cycle pulses are not lost:

```systemverilog
// Latching registers
ilowX_req_t icache_req_reg;
dlowX_req_t dcache_req_reg;

always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
        icache_req_reg <= '{default: 0};
        dcache_req_reg <= '{default: 0};
    end else begin
        // Latch new requests when present
        if (!icache_req_reg.valid && icache_req_i.valid) 
            icache_req_reg <= icache_req_i;
        if (!dcache_req_reg.valid && dcache_req_i.valid) 
            dcache_req_reg <= dcache_req_i;
    end
end
```

### State Transitions

```systemverilog
always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
        round <= IDLE;
    end else begin
        if (iomem_res_i.valid || round == IDLE) begin
            case (round)
                ICACHE: begin
                    icache_req_reg.valid <= 1'b0;  // Request completed
                    round <= dcache_req_reg.valid ? DCACHE : 
                             icache_req_reg.valid && !iomem_res_i.valid ? ICACHE : 
                             IDLE;
                end
                
                DCACHE: begin
                    dcache_req_reg.valid <= 1'b0;  // Request completed
                    round <= icache_req_reg.valid ? ICACHE : 
                             dcache_req_reg.valid && !iomem_res_i.valid ? DCACHE : 
                             IDLE;
                end
                
                IDLE: begin
                    if (icache_req_reg.valid) 
                        round <= ICACHE;
                    else if (dcache_req_reg.valid) 
                        round <= DCACHE;
                    else 
                        round <= IDLE;
                end
            endcase
        end
    end
end
```

---

## State Machine

### State Diagram

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                         ROUND-ROBIN STATE MACHINE                                │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│                          ┌──────────────────────┐                               │
│                          │                      │                               │
│                          │        IDLE          │                               │
│                          │ (Waiting for request)│                               │
│                          │                      │                               │
│                          └───────────┬──────────┘                               │
│                                      │                                          │
│                        ┌─────────────┼─────────────┐                            │
│                        │             │             │                            │
│            icache_valid│             │             │dcache_valid                │
│        (icache first)  │             │             │ (dcache first)             │
│                        ▼             │             ▼                            │
│              ┌──────────────┐        │        ┌──────────────┐                  │
│              │              │        │        │              │                  │
│              │   ICACHE     │        │        │   DCACHE     │                  │
│              │  Service     │◀───────┴───────▶│  Service     │                  │
│              │              │  dcache_valid   │              │                  │
│              └──────┬───────┘  icache_valid   └───────┬──────┘                  │
│                     │                                 │                          │
│         iomem_valid │                                 │ iomem_valid              │
│                     │                                 │                          │
│                     └─────────────────────────────────┘                          │
│                                      │                                          │
│                                      ▼                                          │
│                             If other request pending                             │
│                             → Round switch                                       │
│                             Else → IDLE                                          │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### State Descriptions

| State | Description |
|-------|-------------|
| **IDLE** | Waiting; transition to ICACHE or DCACHE when a new request arrives |
| **ICACHE** | I-Cache request in service; on completion go to DCACHE or IDLE |
| **DCACHE** | D-Cache request in service; on completion go to ICACHE or IDLE |

---

## Data Paths

### Request Routing

```systemverilog
always_comb begin
    if (round == DCACHE) begin
        iomem_req_o.addr  = dcache_req_reg.addr;
        iomem_req_o.valid = dcache_req_reg.valid;
    end else begin
        // In ICACHE or IDLE, I-Cache takes priority on the mux
        iomem_req_o.addr  = icache_req_reg.addr;
        iomem_req_o.valid = icache_req_reg.valid;
    end
    
    iomem_req_o.data = dcache_req_reg.data;  // D-Cache write data
end
```

### Write Mask (D-Cache)

```systemverilog
always_comb begin
    iomem_req_o.rw = '0;
    
    if (round == DCACHE && dcache_req_reg.valid && dcache_req_reg.rw) begin
        if (dcache_req_reg.uncached) begin
            // Uncached write: byte enable from rw_size
            case (dcache_req_reg.rw_size)
                2'b01:   iomem_req_o.rw = 'b1    << dcache_req_reg.addr[BOFFSET-1:0]; // Byte
                2'b10:   iomem_req_o.rw = 'b11   << dcache_req_reg.addr[BOFFSET-1:0]; // Halfword
                default: iomem_req_o.rw = 'b1111 << dcache_req_reg.addr[BOFFSET-1:0]; // Word
            endcase
        end else begin
            // Cached write: full cache line
            case (dcache_req_reg.rw_size)
                2'b01:   iomem_req_o.rw = 'b1    << dcache_req_reg.addr[BOFFSET-1:0];
                2'b10:   iomem_req_o.rw = 'b11   << dcache_req_reg.addr[BOFFSET-1:0];
                default: iomem_req_o.rw = '1;  // Full line
            endcase
        end
    end
end
```

### Response Routing

```systemverilog
always_comb begin
    // I-Cache response
    icache_res_o.valid = (round == ICACHE) && iomem_res_i.valid;
    icache_res_o.ready = 1'b1;
    icache_res_o.blk   = iomem_res_i.data;

    // D-Cache response
    dcache_res_o.valid = (round == DCACHE) && iomem_res_i.valid;
    dcache_res_o.ready = 1'b1;
    dcache_res_o.data  = iomem_res_i.data;
end
```

---

## Timing Diagrams

### Single I-Cache Request

```
clk      ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____ ... ____/‾‾‾‾\____

icache   ────/‾‾‾‾\─────────────────────────────────────────────
req.valid

round    ────┤IDLE ├────┤ICACHE├──────────────────┤IDLE ├──────

iomem    ────────────────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\─────────────────────
req.valid                Memory access

iomem    ─────────────────────────────────────────/‾‾‾‾\────────
res.valid                                         Done!

icache   ─────────────────────────────────────────/‾‾‾‾\────────
res.valid
```

### I-Cache and D-Cache Contention

```
clk      ____/‾\____/‾\____/‾\____ ... ____/‾\____ ... ____/‾\____

icache   ────/‾‾‾‾\───────────────────────────────────────────────
req.valid

dcache   ──────────/‾‾‾‾\─────────────────────────────────────────
req.valid

round    ────┤IDLE├┤ICACHE├────────────────┤DCACHE├───────┤IDLE├──

iomem_req────────────/‾‾‾‾‾‾‾‾‾‾\────────────/‾‾‾‾‾‾‾‾‾‾\─────────
             icache addr        dcache addr

icache   ──────────────────────────────────/‾‾‾‾\─────────────────
res.valid                                   I done

dcache   ────────────────────────────────────────────────/‾‾‾‾\───
res.valid                                                D done
```

### Round-Robin Fairness

```
clk      ____/‾\____/‾\____/‾\____/‾\____/‾\____ ... 

         Continuous icache and dcache requests

round    ──┤IC├────┤DC├────┤IC├────┤DC├────┤IC├── ...
           ↑       ↑       ↑       ↑       ↑
           │       │       │       │       │
        icache  dcache  icache  dcache  icache
       service service service service service

         Fair scheduling: alternating access
```

---

## Performance Analysis

### Latency Analysis

| Scenario | Latency |
|----------|---------|
| Single request (IDLE → service) | 0-cycle overhead |
| Contending requests | First: 0, second: +memory_latency |
| Sustained contention | Average 2× memory latency |

### Bandwidth

```
Peak Bandwidth (no contention):
    BW = BLK_SIZE / memory_latency
    BW = 128 bit / 10 cycle = 12.8 bits/cycle @ 50MHz

Effective Bandwidth (with contention):
    BW_eff = BW / 2 (worst case: 50% utilization per cache)
```

### Fairness

- Round-robin avoids starvation
- Any request waits for at most one other request
- Long-term equal opportunity for both sides

---

## Verification and Testing

### Assertions

```systemverilog
// Only one cache may be serviced at a time
assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(icache_res_o.valid && dcache_res_o.valid)
) else $error("Both caches cannot have valid response simultaneously");

// Must leave IDLE when a request is pending
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (round == IDLE && (icache_req_reg.valid || dcache_req_reg.valid)) |=> 
    (round != IDLE)
) else $error("Should transition from IDLE when request pending");

// Round-robin fairness: alternate service under continuous requests
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (round == ICACHE && iomem_res_i.valid && dcache_req_reg.valid) |=> 
    (round == DCACHE)
) else $error("Should switch to DCACHE after ICACHE when DCACHE pending");
```

### Test Scenarios

1. **Single-cache access**
   - I-Cache requests only
   - D-Cache requests only

2. **Contending requests**
   - Both requests in the same cycle
   - Alternating requests

3. **Starvation test**
   - One cache always requesting, the other occasional
   - Both must still get service

4. **Uncached write**
   - D-Cache uncached write
   - Byte/halfword/word write

---

## Summary

The `memory_arbiter` module:

1. **Fair scheduling**: Round-robin avoids starvation
2. **Request latching**: Prevents lost pulses
3. **Flexible writes**: Byte/halfword/word support
4. **Simple design**: Low complexity, easy to debug
5. **Low latency**: No extra delay when there is no contention

It provides efficient memory sharing between I-Cache and D-Cache in a Von Neumann memory system.
