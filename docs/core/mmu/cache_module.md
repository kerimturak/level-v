# Cache Module — Technical Documentation

## Contents

1. [Overview](#overview)
2. [Module Interface](#module-interface)
3. [Cache Architecture](#cache-architecture)
4. [PLRU Eviction Algorithm](#plru-eviction-algorithm)
5. [I-Cache Behavior](#i-cache-behavior)
6. [D-Cache Behavior](#d-cache-behavior)
7. [FENCE.I Dirty Writeback](#fencei-dirty-writeback)
8. [Memory Structures](#memory-structures)
9. [Timing Diagrams](#timing-diagrams)
10. [Performance Analysis](#performance-analysis)
11. [Verification and Testing](#verification-and-testing)

---

## Overview

### Purpose

The `cache` module is a **parametric**, **set-associative** cache implementation for the Level RISC-V processor. A single module instance can be configured as either an **I-Cache** (instruction cache) or a **D-Cache** (data cache).

### Key Features

| Feature | Value |
|---------|-------|
| **Associativity** | Parametric (default 8-way) |
| **Capacity** | Parametric (default 8KB) |
| **Block Size** | 128-bit (4 × 32-bit words) |
| **Eviction Policy** | Pseudo-LRU (tree-based PLRU) |
| **Write Policy** | Write-back, write-allocate (D-Cache) |
| **Unified/Split** | Split (separate I-Cache and D-Cache) |
| **FENCE.I Support** | Dirty writeback state machine |

### Cache Block Diagram

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                                    CACHE                                         │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌──────────────────────────────────────────────────────────────────────────┐  │
│   │                           ADDRESS DECODE                                  │  │
│   │   ┌────────────┬────────────┬────────────┐                               │  │
│   │   │    TAG     │   INDEX    │   OFFSET   │                               │  │
│   │   │  [31:IDX+B]│[IDX+B-1:B] │  [B-1:0]   │                               │  │
│   │   └────────────┴────────────┴────────────┘                               │  │
│   └──────────────────────────────────────────────────────────────────────────┘  │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                         MEMORY ARRAYS                                    │   │
│   │                                                                          │   │
│   │   ┌─────────────┐   ┌─────────────┐   ┌─────────────┐   ┌───────────┐   │   │
│   │   │  Tag Array  │   │ Data Array  │   │ Valid Array │   │PLRU Array │   │   │
│   │   │  (NUM_WAY)  │   │  (NUM_WAY)  │   │  (NUM_WAY)  │   │(NUM_WAY-1)│   │   │
│   │   └──────┬──────┘   └──────┬──────┘   └──────┬──────┘   └─────┬─────┘   │   │
│   │          │                 │                 │                │          │   │
│   │          ▼                 ▼                 ▼                ▼          │   │
│   │   ┌─────────────────────────────────────────────────────────────────┐   │   │
│   │   │                    HIT/MISS DETECTION                            │   │   │
│   │   │   Tag Match && Valid → Hit                                       │   │   │
│   │   │   !Match || !Valid  → Miss                                       │   │   │
│   │   └─────────────────────────────────────────────────────────────────┘   │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                    D-CACHE SPECIFIC (IS_ICACHE=0)                        │   │
│   │   ┌─────────────┐   ┌─────────────────────────────────────────────────┐ │   │
│   │   │ Dirty Array │   │         FENCE.I Writeback FSM                   │ │   │
│   │   │  (NUM_WAY)  │   │  IDLE → SCAN → CHECK → WRITEBACK → MARK_CLEAN   │ │   │
│   │   └─────────────┘   └─────────────────────────────────────────────────┘ │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Module Interface

### Port Definitions

```systemverilog
module cache
  import level_param::*;
#(
    parameter      IS_ICACHE   = 1,           // 1: I-Cache, 0: D-Cache
    parameter type cache_req_t = logic,       // Cache request type
    parameter type cache_res_t = logic,       // Cache response type
    parameter type lowX_res_t  = logic,       // Lower-level response type
    parameter type lowX_req_t  = logic,       // Lower-level request type
    parameter      CACHE_SIZE  = 1024,        // Cache size (bytes)
    parameter      BLK_SIZE    = level_param::BLK_SIZE, // Block size (bits)
    parameter      XLEN        = level_param::XLEN,     // Data width
    parameter      NUM_WAY     = 4            // Associativity
) (
    input  logic       clk_i,          // System clock
    input  logic       rst_ni,         // Active-low reset
    input  logic       flush_i,        // Cache flush signal
    input  cache_req_t cache_req_i,    // Cache request
    output cache_res_t cache_res_o,    // Cache response
    input  lowX_res_t  lowX_res_i,     // Lower-level (memory) response
    output lowX_req_t  lowX_req_o,     // Lower-level (memory) request
    output logic       fencei_stall_o  // FENCE.I stall signal
);
```

### Port Descriptions

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk_i` | Input | 1 bit | System clock |
| `rst_ni` | Input | 1 bit | Active-low asynchronous reset |
| `flush_i` | Input | 1 bit | Cache flush trigger (FENCE.I) |
| `cache_req_i` | Input | Struct | Cache access request |
| `cache_res_o` | Output | Struct | Cache response |
| `lowX_res_i` | Input | Struct | Memory response |
| `lowX_req_o` | Output | Struct | Memory request |
| `fencei_stall_o` | Output | 1 bit | FENCE.I dirty writeback stall |

### Local Parameters

```systemverilog
localparam NUM_SET    = (CACHE_SIZE / BLK_SIZE) / NUM_WAY;  // Number of sets
localparam IDX_WIDTH  = $clog2(NUM_SET);                     // Index bit width
localparam BOFFSET    = $clog2(BLK_SIZE / 8);                // Block offset bits
localparam WOFFSET    = $clog2(BLK_SIZE / 32);               // Word offset bits
localparam TAG_SIZE   = XLEN - IDX_WIDTH - BOFFSET;          // Tag bit width
```

### Default Configuration (8KB, 8-way)

| Parameter | Value | Calculation |
|-----------|-------|-----------|
| CACHE_SIZE | 8192 byte | 8KB |
| BLK_SIZE | 128 bit | 16 byte cache line |
| NUM_WAY | 8 | 8-way set associative |
| NUM_SET | 64 | 8192 / 16 / 8 |
| IDX_WIDTH | 6 bit | log2(64) |
| BOFFSET | 4 bit | log2(128/8) |
| TAG_SIZE | 22 bit | 32 - 6 - 4 |

---

## Cache Architecture

### Address Decoding

```
32-bit address layout:
┌─────────────────────────────────────────────────────────────────┐
│  31        31-IDX_WIDTH   IDX_WIDTH+BOFFSET-1   BOFFSET-1    0  │
│  ┌──────────────────────┬────────────────────┬───────────────┐  │
│  │         TAG          │       INDEX        │    OFFSET     │  │
│  │      (22 bit)        │      (6 bit)       │   (4 bit)     │  │
│  └──────────────────────┴────────────────────┴───────────────┘  │
└─────────────────────────────────────────────────────────────────┘

Example: address 0x8000_1234
- TAG:    0x200004  (bits [31:10])
- INDEX:  0x12      (bits [9:4])
- OFFSET: 0x4       (bits [3:0])
```

### Set-Associative Organization

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                           8-WAY SET ASSOCIATIVE CACHE                            │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│         Way 0      Way 1      Way 2      Way 3      Way 4      Way 5      ...   │
│       ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐        │
│ Set 0 │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│        │
│       ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤        │
│ Set 1 │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│        │
│       ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤        │
│ Set 2 │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│        │
│       ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤        │
│  ...  │  ...   │ │  ...   │ │  ...   │ │  ...   │ │  ...   │ │  ...   │        │
│       ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤        │
│Set 63 │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│        │
│       └────────┘ └────────┘ └────────┘ └────────┘ └────────┘ └────────┘        │
│                                                                                  │
│   V = Valid bit (1 bit)                                                          │
│   T = Tag (22 bit)                                                               │
│   Data = Cache line (128 bit = 4 words)                                          │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Cache Line Layout

```
128-bit Cache Line (4 x 32-bit words):
┌────────────────┬────────────────┬────────────────┬────────────────┐
│    Word 3      │    Word 2      │    Word 1      │    Word 0      │
│   [127:96]     │   [95:64]      │   [63:32]      │   [31:0]       │
├────────────────┴────────────────┴────────────────┴────────────────┤
│                      Offset [3:0]                                  │
│   0x0 → Word 0    0x4 → Word 1    0x8 → Word 2    0xC → Word 3    │
└───────────────────────────────────────────────────────────────────┘
```

---

## PLRU Eviction Algorithm

### Tree-based Pseudo-LRU

PLRU (Pseudo Least Recently Used) approximates LRU at lower hardware cost. An 8-way cache uses a 7-bit tree structure.

```
                    PLRU tree (8-way)
                    ─────────────────
                    
                           [0]
                          /    \
                        /        \
                      /            \
                    [1]            [2]
                   /   \          /   \
                  /     \        /     \
                [3]     [4]    [5]     [6]
               / \     / \    / \     / \
              W0  W1  W2  W3 W4  W5  W6  W7

    Node value:
    - 0 = go left (LRU candidate on the left)
    - 1 = go right (LRU candidate on the right)
    
    After an access:
    - All nodes on the path to the accessed way flip to the opposite direction
```

### PLRU Node Update Function

```systemverilog
function automatic [NUM_WAY-2:0] update_node(
    input logic [NUM_WAY-2:0] node_in, 
    input logic [NUM_WAY-1:0] hit_vec
);
    logic [NUM_WAY-2:0] node_tmp;
    int idx_base, shift;
    node_tmp = node_in;
    
    for (int unsigned i = 0; i < NUM_WAY; i++) begin
        if (hit_vec[i]) begin
            for (int unsigned lvl = 0; lvl < $clog2(NUM_WAY); lvl++) begin
                idx_base = (2 ** lvl) - 1;
                shift = $clog2(NUM_WAY) - lvl;
                // Flip path to accessed way to opposite direction
                node_tmp[idx_base + (i >> shift)] = ((i >> (shift - 1)) & 1) == 0;
            end
        end
    end
    return node_tmp;
endfunction
```

### PLRU Evict-Way Computation

```systemverilog
function automatic [NUM_WAY-1:0] compute_evict_way(
    input logic [NUM_WAY-2:0] node_in
);
    logic [NUM_WAY-1:0] way;
    int idx_base, shift;
    
    for (int unsigned i = 0; i < NUM_WAY; i++) begin
        logic en;
        en = 1'b1;
        for (int unsigned lvl = 0; lvl < $clog2(NUM_WAY); lvl++) begin
            idx_base = (2 ** lvl) - 1;
            shift = $clog2(NUM_WAY) - lvl;
            // Follow tree to find LRU way
            if (((i >> (shift - 1)) & 32'b1) == 32'b1) 
                en &= node_in[idx_base + (i >> shift)];
            else 
                en &= ~node_in[idx_base + (i >> shift)];
        end
        way[i] = en;
    end
    return way;
endfunction
```

### PLRU Example

```
Initial: node = 7'b0000000 (all directions left)
         Evict way = way 0

Access way 5:
- Path: Root(0) → Right(2) → Left(5) → way 5
- Update: node[0]=0, node[2]=0, node[5]=1
- New node = 7'b0100000
- New evict way = way 0 (unchanged)

Access way 0:
- Path: Root(0) → Left(1) → Left(3) → way 0
- Update: node[0]=1, node[1]=1, node[3]=1
- New node = 7'b0101011
- New evict way = way 4
```

---

## I-Cache Behavior

### I-Cache Features

| Feature | Value |
|---------|-------|
| IS_ICACHE | 1 |
| Write support | No (read-only) |
| Dirty bit | None |
| Writeback | None |
| FENCE.I stall | Always 0 |

### I-Cache Logic

```systemverilog
if (IS_ICACHE) begin : icache_impl
    // No dirty writeback in I-Cache
    assign fencei_stall_o = 1'b0;

    always_comb begin
        // Node array update (on hit or refill)
        nsram.rw_en = cache_wr_en || cache_hit;
        nsram.wnode = flush ? '0 : updated_node;
        nsram.idx   = cache_idx;

        // Tag array update (on miss + refill)
        tsram.way   = '0;
        tsram.idx   = cache_idx;
        tsram.wtag  = flush ? '0 : {1'b1, cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET]};
        for (int i = 0; i < NUM_WAY; i++) 
            tsram.way[i] = flush ? '1 : cache_wr_way[i] && cache_wr_en;

        // Data array update (on refill)
        dsram.way   = '0;
        dsram.idx   = cache_idx;
        dsram.wdata = lowX_res_i.blk;
        for (int i = 0; i < NUM_WAY; i++) 
            dsram.way[i] = cache_wr_way[i] && cache_wr_en;
    end

    // LowX interface and cache response
    always_comb begin
        lowX_req_o.valid    = !lookup_ack && cache_miss;
        lowX_req_o.ready    = !flush;
        lowX_req_o.addr     = cache_req_q.addr;
        lowX_req_o.uncached = cache_req_q.uncached;
        
        cache_res_o.miss  = cache_miss;
        cache_res_o.valid = cache_req_i.ready && 
                           (cache_hit || (cache_miss && lowX_req_o.ready && lowX_res_i.valid));
        cache_res_o.ready = (!cache_miss || lowX_res_i.valid) && !flush;
        cache_res_o.blk   = (cache_miss && lowX_res_i.valid) ? lowX_res_i.blk : cache_select_data;
    end
end
```

### I-Cache Hit/Miss Flow

```
I-Cache Hit (1 cycle):
┌────────┐    ┌────────┐    ┌────────┐
│  Req   │───▶│Tag Cmp │───▶│  Data  │
│ (addr) │    │  Hit!  │    │ Return │
└────────┘    └────────┘    └────────┘

I-Cache Miss (~10 cycles):
┌────────┐    ┌────────┐    ┌─────────────┐    ┌────────┐    ┌────────┐
│  Req   │───▶│Tag Cmp │───▶│   Memory    │───▶│ Refill │───▶│  Data  │
│ (addr) │    │ Miss!  │    │   Fetch     │    │  Cache │    │ Return │
└────────┘    └────────┘    └─────────────┘    └────────┘    └────────┘
                                  ↑
                           ~10 cycle latency
```

---

## D-Cache Behavior

### D-Cache Features

| Feature | Value |
|---------|-------|
| IS_ICACHE | 0 |
| Write support | Yes (read/write) |
| Write policy | Write-back, write-allocate |
| Dirty bit | Yes (per way) |
| Writeback | On eviction and FENCE.I |
| FENCE.I stall | Active when dirty lines exist |

### D-Cache Dirty Array

```systemverilog
// Register-based dirty array (not SRAM)
// FENCE.I needs visibility of all dirty bits in a single cycle
logic [NUM_WAY-1:0] dirty_reg[NUM_SET];

always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
        for (int i = 0; i < NUM_SET; i++) 
            dirty_reg[i] <= '0;
    end else begin
        for (int w = 0; w < NUM_WAY; w++) begin
            if (drsram.way[w]) begin
                dirty_reg[drsram.idx][w] <= drsram.wdirty;
            end
        end
    end
end

// Combinational read (immediate visibility)
always_comb begin
    for (int w = 0; w < NUM_WAY; w++) begin
        drsram.rdirty[w] = dirty_reg[drsram.idx][w];
    end
end
```

### D-Cache Write Operation

```systemverilog
// Data masking (byte/halfword/word write)
always_comb begin
    mask_data   = cache_hit ? cache_select_data : lowX_res_i.data;
    data_wr_pre = mask_data;
    
    case (cache_req_q.rw_size)
        2'b11: data_wr_pre[cache_req_q.addr[BOFFSET-1:2]*32+:32] = cache_req_q.data; // Word
        2'b10: data_wr_pre[cache_req_q.addr[BOFFSET-1:1]*16+:16] = cache_req_q.data[15:0]; // Halfword
        2'b01: data_wr_pre[cache_req_q.addr[BOFFSET-1:0]*8+:8]   = cache_req_q.data[7:0];  // Byte
        2'b00: data_wr_pre = '0;
    endcase
end
```

### D-Cache Writeback Logic

```systemverilog
// Dirty line writeback on eviction
write_back = cache_miss && (|(drsram.rdirty & evict_way & cache_valid_vec));

// Writeback address and data
always_comb begin
    evict_tag  = '0;
    evict_data = '0;
    for (int i = 0; i < NUM_WAY; i++) begin
        if (evict_way[i]) begin
            evict_tag  = tsram.rtag[i][TAG_SIZE-1:0];
            evict_data = dsram.rdata[i];
        end
    end
end
```

---

## FENCE.I Dirty Writeback

### FENCE.I State Machine

When a FENCE.I executes, all dirty lines in the D-Cache must be written to memory. A state machine performs this.

```systemverilog
typedef enum logic [2:0] {
    FI_IDLE,            // Normal operation
    FI_SCAN,            // Scan sets
    FI_CHECK_WAY,       // Check each way
    FI_WRITEBACK_REQ,   // Issue writeback request
    FI_WRITEBACK_WAIT,  // Wait for writeback to complete
    FI_MARK_CLEAN,      // Mark line clean
    FI_NEXT_WAY,        // Advance to next way
    FI_DONE             // Writeback complete
} fencei_state_e;
```

### FENCE.I Flow Diagram

```
┌──────────────────────────────────────────────────────────────────────────────────┐
│                         FENCE.I DIRTY WRITEBACK FSM                              │
├──────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│                              ┌──────────┐                                        │
│              flush_i ───────▶│  FI_IDLE │                                        │
│              rising edge     └────┬─────┘                                        │
│                                   │                                              │
│                                   ▼                                              │
│                              ┌──────────┐                                        │
│                              │ FI_SCAN  │◀─────────────────────────┐            │
│                              │(BRAM lat)│                          │            │
│                              └────┬─────┘                          │            │
│                                   │                                │            │
│                                   ▼                                │            │
│                           ┌─────────────┐                          │            │
│                           │FI_CHECK_WAY │                          │            │
│                           │ dirty[way]? │                          │            │
│                           └──────┬──────┘                          │            │
│                          ┌───────┴───────┐                         │            │
│                          │               │                         │            │
│                     dirty=1         dirty=0                        │            │
│                          │               │                         │            │
│                          ▼               │                         │            │
│                   ┌─────────────┐        │                         │            │
│                   │FI_WRITEBACK │        │                         │            │
│                   │    _REQ     │        │                         │            │
│                   └──────┬──────┘        │                         │            │
│                          │               │                         │            │
│                          ▼               │                         │            │
│                   ┌─────────────┐        │                         │            │
│                   │FI_WRITEBACK │        │                         │            │
│                   │   _WAIT     │        │                         │            │
│                   └──────┬──────┘        │                         │            │
│                          │               │                         │            │
│                          ▼               │                         │            │
│                   ┌─────────────┐        │                         │            │
│                   │FI_MARK_CLEAN│        │                         │            │
│                   └──────┬──────┘        │                         │            │
│                          │               │                         │            │
│                          └───────┬───────┘                         │            │
│                                  │                                 │            │
│                                  ▼                                 │            │
│                           ┌─────────────┐                          │            │
│                           │ FI_NEXT_WAY │                          │            │
│                           └──────┬──────┘                          │            │
│                          ┌───────┴───────┐                         │            │
│                          │               │                         │            │
│                     way<NUM_WAY-1   way=NUM_WAY-1                  │            │
│                          │               │                         │            │
│                          │        ┌──────┴──────┐                  │            │
│                          │        │             │                  │            │
│                          │   set<NUM_SET-1  set=NUM_SET-1          │            │
│                          │        │             │                  │            │
│                          │        │             ▼                  │            │
│                          │        │       ┌──────────┐             │            │
│                          │        │       │ FI_DONE  │────▶ flush_i=0 ──▶ IDLE  │
│                          │        │       └──────────┘             │            │
│                          │        │                                │            │
│                          ▼        └────────────────────────────────┘            │
│                     CHECK_WAY                                                    │
│                     (next way)                                                   │
│                                                                                  │
└──────────────────────────────────────────────────────────────────────────────────┘
```

### FENCE.I State Machine Code

```systemverilog
always_comb begin
    fi_state_d       = fi_state_q;
    fi_set_idx_d     = fi_set_idx_q;
    fi_way_idx_d     = fi_way_idx_q;
    fi_active        = 1'b0;
    fi_writeback_req = 1'b0;
    fi_mark_clean    = 1'b0;

    unique case (fi_state_q)
        FI_IDLE: begin
            if (fi_start) begin
                fi_state_d   = FI_SCAN;
                fi_set_idx_d = '0;
                fi_way_idx_d = '0;
                fi_active    = 1'b1;
            end
        end

        FI_SCAN: begin
            fi_active  = 1'b1;
            fi_state_d = FI_CHECK_WAY;  // Wait for BRAM latency
        end

        FI_CHECK_WAY: begin
            fi_active = 1'b1;
            if (fi_has_dirty) begin
                fi_state_d = FI_WRITEBACK_REQ;
            end else begin
                fi_state_d = FI_NEXT_WAY;
            end
        end

        FI_WRITEBACK_REQ: begin
            fi_active = 1'b1;
            fi_writeback_req = 1'b1;
            if (lowX_res_i.ready) begin
                fi_state_d = FI_WRITEBACK_WAIT;
            end
        end

        FI_WRITEBACK_WAIT: begin
            fi_active = 1'b1;
            fi_writeback_req = 1'b1;
            if (lowX_res_i.valid) begin
                fi_state_d = FI_MARK_CLEAN;
            end
        end

        FI_MARK_CLEAN: begin
            fi_active = 1'b1;
            fi_mark_clean = 1'b1;
            fi_state_d = FI_NEXT_WAY;
        end

        FI_NEXT_WAY: begin
            fi_active = 1'b1;
            if (fi_way_idx_q == NUM_WAY - 1) begin
                if (fi_set_idx_q == NUM_SET - 1) begin
                    fi_state_d = FI_DONE;
                end else begin
                    fi_set_idx_d = fi_set_idx_q + 1'b1;
                    fi_way_idx_d = '0;
                    fi_state_d   = FI_SCAN;
                end
            end else begin
                fi_way_idx_d = fi_way_idx_q + 1'b1;
                fi_state_d   = FI_CHECK_WAY;
            end
        end

        FI_DONE: begin
            fi_active = 1'b0;  // Release stall
            if (!flush_i) begin
                fi_state_d = FI_IDLE;
            end
        end
    endcase
end

assign fencei_stall_o = fi_active;
```

### FENCE.I Notes

1. **No tag invalidation**: FENCE.I only performs dirty writeback; it does not invalidate cache lines.
2. **Stall duration**: Depends on the number of dirty lines (worst case: NUM_SET × NUM_WAY × memory_latency).
3. **Pipeline impact**: While `fencei_stall_o` is active, the whole pipeline stalls.

---

## Memory Structures

### Tag Array

```systemverilog
typedef struct packed {
    logic [IDX_WIDTH-1:0]           idx;    // Index
    logic [NUM_WAY-1:0]             way;    // Way select
    logic [TAG_SIZE:0]              wtag;   // Tag + valid to write
    logic [NUM_WAY-1:0][TAG_SIZE:0] rtag;   // Read tags
} tsram_t;
```

### Data Array

```systemverilog
typedef struct packed {
    logic [IDX_WIDTH-1:0]             idx;    // Index
    logic [NUM_WAY-1:0]               way;    // Way select
    logic [BLK_SIZE-1:0]              wdata;  // Write data
    logic [NUM_WAY-1:0][BLK_SIZE-1:0] rdata;  // Read data
} dsram_t;
```

### Node Array (PLRU)

```systemverilog
typedef struct packed {
    logic [IDX_WIDTH-1:0] idx;    // Index
    logic                 rw_en;  // R/W enable
    logic [NUM_WAY-2:0]   wnode;  // PLRU state to write
    logic [NUM_WAY-2:0]   rnode;  // Read PLRU state
} nsram_t;
```

### Dirty Array (D-Cache Only)

```systemverilog
typedef struct packed {
    logic [IDX_WIDTH-1:0] idx;      // Index
    logic [NUM_WAY-1:0]   way;      // Way select
    logic                 rw_en;    // R/W enable
    logic                 wdirty;   // Dirty bit to write
    logic [NUM_WAY-1:0]   rdirty;   // Read dirty bits
} drsram_t;
```

---

## Timing Diagrams

### Cache Hit (1 Cycle)

```
clk     ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

req     ────/‾‾‾‾‾‾‾‾‾\──────────────────
valid

hit     ─────────────/‾‾‾‾‾‾‾‾‾\─────────

data    ─────────────┤ VALID  ├──────────
                      │ DATA   │

res     ─────────────/‾‾‾‾‾‾‾‾‾\─────────
valid
```

### Cache Miss + Refill (~10 Cycles)

```
clk     ____/‾\____/‾\____/‾\____ ... ____/‾\____/‾\____

req     ────/‾‾‾‾\───────────────────────────────────────
valid

miss    ─────────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──────────────

lowX    ─────────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──────────────
req            Memory fetch in progress...

lowX    ───────────────────────────────────/‾‾‾‾\────────
valid                                      │data│

res     ───────────────────────────────────/‾‾‾‾\────────
valid                                      │hit!│
```

### D-Cache Write-back Eviction

```
clk     ____/‾\____/‾\____/‾\____/‾\____ ... ____/‾\____

miss    ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──────

evict   ────/‾‾‾‾‾‾‾‾‾‾‾\────────────────────────────────
dirty        │writeback │

lowX    ────/‾‾‾‾‾‾‾‾‾‾‾\────────────────────────────────
wr_req       │evict data│

lowX    ─────────────────/‾‾‾‾\──────────────────────────
wr_ack               │done│

lowX    ─────────────────────/‾‾‾‾‾‾‾‾‾‾‾\───────────────
rd_req                   │fetch new│

lowX    ───────────────────────────────────/‾‾‾‾\────────
rd_ack                                 │data│
```

### FENCE.I Dirty Writeback

```
clk     ____/‾\____/‾\____/‾\____/‾\____ ... ____/‾\____

flush_i ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──

stall   ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────────

state   IDLE│SCAN│CHK│WB_REQ│WB_WAIT│MARK│NEXT│...│DONE│

        ↑    ↑    ↑    ↑      ↑       ↑    ↑        ↑
        │    │    │    │      │       │    │        │
     start  bram  dirty? request wait  clear next  all
             lat   yes          mem    bit  set/   done
                                            way
```

---

## Performance Analysis

### Cache Hit Rate

| Workload | Typical I-Cache Hit Rate | Typical D-Cache Hit Rate |
|----------|------------------------|------------------------|
| Coremark | >95% | >90% |
| Dhrystone | >98% | >95% |
| General | >90% | >85% |

### Latency Analysis

| Operation | Latency (cycles) | Description |
|-----------|------------------|-------------|
| Cache hit | 1 | Single-cycle read |
| Cache miss (clean) | ~10 | Memory latency |
| Cache miss (dirty) | ~20 | Writeback + refill |
| FENCE.I (best) | 2 | No dirty lines |
| FENCE.I (worst) | NUM_SET × NUM_WAY × 10 | All lines dirty |

### Area (8KB, 8-way)

| Component | Size | Calculation |
|-----------|------|-------------|
| Data array | 8KB × 8 way = 64Kb | BLK_SIZE × NUM_SET × NUM_WAY |
| Tag array | (22+1) × 64 × 8 = 11776 bit | (TAG_SIZE+1) × NUM_SET × NUM_WAY |
| Node array | 7 × 64 = 448 bit | (NUM_WAY-1) × NUM_SET |
| Dirty array | 8 × 64 = 512 bit | NUM_WAY × NUM_SET |
| **Total** | ~76KB | Data + tag + node + dirty |

---

## Verification and Testing

### Assertions

```systemverilog
// Hit and miss cannot both be active
assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(cache_hit && cache_miss)
) else $error("Hit and miss cannot be active simultaneously");

// PLRU evict way must be one-hot
assert property (@(posedge clk_i) disable iff (!rst_ni)
    $onehot(evict_way)
) else $error("Evict way must be one-hot encoded");

// D-Cache: normal access disabled during FENCE.I
assert property (@(posedge clk_i) disable iff (!rst_ni)
    fi_active |-> !cache_res_o.valid
) else $error("Cache should not respond during FENCE.I");

// lowX request must be active on miss
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (cache_miss && !lookup_ack) |-> lowX_req_o.valid
) else $error("Memory request should be active on cache miss");
```

### Test Scenarios

1. **Basic hit/miss**
   - Back-to-back access to the same address (hit)
   - Access to different sets (cold miss)
   - Nine distinct addresses in the same set (capacity miss)

2. **PLRU eviction**
   - Fill all eight ways in order
   - On the 9th access, verify PLRU eviction
   - After an access pattern, check evict way

3. **D-Cache write-back**
   - Write miss → allocate → write
   - Dirty writeback during eviction
   - Clean line eviction (no writeback)

4. **FENCE.I**
   - No dirty lines → fast completion
   - Single dirty line → writeback
   - All lines dirty → full writeback

5. **Uncached access**
   - Peripheral addresses (uncached)
   - RAM addresses (cached)

### Coverage Points

```systemverilog
covergroup cache_cg @(posedge clk_i);
    // Hit/Miss coverage
    hit_miss: coverpoint {cache_hit, cache_miss} {
        bins hit  = {2'b10};
        bins miss = {2'b01};
        bins idle = {2'b00};
    }
    
    // Way selection coverage
    way_sel: coverpoint cache_wr_way {
        bins way[] = {[0:NUM_WAY-1]};
    }
    
    // D-Cache write size coverage
    write_size: coverpoint cache_req_i.rw_size iff (cache_req_i.rw) {
        bins byte_wr = {2'b01};
        bins half_wr = {2'b10};
        bins word_wr = {2'b11};
    }
    
    // FENCE.I state coverage
    fencei_state: coverpoint fi_state_q {
        bins all_states[] = {[FI_IDLE:FI_DONE]};
    }
endgroup
```

---

## Summary

The `cache` module is a key performance component for the Level RISC-V processor:

1. **Parametric design**: Capacity, associativity, and block size are configurable.
2. **Single module**: One RTL block serves as either I-Cache or D-Cache.
3. **PLRU eviction**: Low-cost, effective replacement policy.
4. **Write-back policy**: Minimizes memory traffic for the D-Cache.
5. **FENCE.I support**: Dirty writeback state machine.
6. **Uncached bypass**: Cache bypass for peripheral accesses.

This design targets >90% hit rate on typical embedded workloads while optimizing FPGA resource use.
