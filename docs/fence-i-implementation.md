# Fence.i Instruction Implementation for Dcache

## Overview

This document explains how the RISC-V `fence.i` instruction is implemented on the dcache side. The `fence.i` instruction is used to maintain consistency between the instruction cache and the data cache.

## Problem statement

The RISC-V architecture supports self-modifying code. A program can write new instructions to memory and then execute them. For that to work:

1. New instructions written to the data cache must be flushed to memory
2. The instruction cache must be invalidated
3. The pipeline must be cleaned up

## Implementation details

### 1. Dirty array register structure

**Previous state:** Dirty bits lived inside SRAM, making it impossible to see all dirty states in a single cycle.

**Solution:** Hold the dirty array in registers:

```systemverilog
// Dirty bits as register array for instant access
logic [NUM_WAY-1:0] dirty_reg_q [NUM_SET];
logic [NUM_WAY-1:0] dirty_reg_d [NUM_SET];
```

This allows:
- Reading any set’s dirty state in one cycle
- Fast dirty scanning for the fence.i state machine

### 2. Fence.i state machine

We implemented an 8-state FSM for the dcache:

```
FI_IDLE → FI_SCAN → FI_CHECK_WAY → FI_WRITEBACK_REQ → FI_WRITEBACK_WAIT → FI_MARK_CLEAN → FI_NEXT_WAY → FI_DONE
    ↑                     ↓                                                                              ↓
    └─────────────────────┴──────────────────────────────────────────────────────────────────────────────┘
```

| State | Description |
|-------|-------------|
| `FI_IDLE` | Idle; wait for fence.i |
| `FI_SCAN` | Set index; send address to SRAM |
| `FI_CHECK_WAY` | Check if current set has a dirty way |
| `FI_WRITEBACK_REQ` | Issue write to memory via LowX interface |
| `FI_WRITEBACK_WAIT` | Wait for memory write to complete |
| `FI_MARK_CLEAN` | Clear dirty bit |
| `FI_NEXT_WAY` | Advance to next way or next set |
| `FI_DONE` | Done; deassert stall |

### 3. Pipeline stall mechanism

We added a new stall type to stop the pipeline during fence.i:

```systemverilog
// level_param.sv
typedef enum logic [2:0] {
    NO_STALL      = 0,
    DMEM_STALL    = 1,
    IMEM_STALL    = 2,
    MUL_STALL     = 3,
    DIV_STALL     = 4,
    FENCEI_STALL  = 5  // New
} stall_e;
```

**Stall priority:** `FENCEI_STALL` has highest priority (checked before other stalls).

### 4. Flush signal management

**Problem:** When fence.i arrives, both icache flush and dcache dirty writeback are needed. But a shared `flush` signal affected both caches and cleared dcache tags immediately — before dirty writeback finished.

**Solution:** Block flush writes to the dcache tag array while fence.i is active:

```systemverilog
// Tag array write — block flush writes during fence.i
for (int i = 0; i < NUM_WAY; i++) 
    tsram.way[i] = (flush && !fi_active) ? '1 : (cache_wr_way[i] && tag_array_wr_en);
```

### 5. Fence.i start condition

We detect fence.i reliably with rising-edge detection:

```systemverilog
logic flush_i_prev;
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) flush_i_prev <= 1'b0;
    else         flush_i_prev <= flush_i;
end

wire fencei_rising_edge = flush_i && !flush_i_prev;
```

### 6. Pipe2 flush condition

**Problem:** While the fence.i instruction was in pipe2, `fencei_flush` flushed pipe2, which dropped fence.i itself.

**Solution:** Removed `fencei_flush` from the pipe2 flush condition:

```systemverilog
// Before (buggy):
if (!rst_ni || ex_flush_en || priority_flush == 3 || priority_flush == 2 || fencei_flush)

// After (fixed):
if (!rst_ni || ex_flush_en || priority_flush == 3 || priority_flush == 2)
```

## Test used

### rv32ui-p-fence_i

This test checks that fence.i behaves correctly:

1. Fetches an instruction from memory (e.g. from `0x80002000`)
2. Stores a new instruction to the same address
3. Executes `fence.i`
4. Jumps to the newly written address
5. Checks that the new instruction executes correctly

**Test flow:**
```
PC=0x80000144: sh x13, 0x80002004  # Write new instruction (0x8693)
PC=0x8000014c: sh x11, 0x80002006  # Write new instruction (0x14d6)
PC=0x80000150: fence.i             # Dcache flush + Icache invalidate
PC=0x8000015c: jalr x6, x15        # Jump to 0x80002004
PC=0x80002004: addi x13, x13, 0x14d6  # Execute newly written instruction
```

## Unused / alternative approaches

### 1. SRAM-based dirty array (not used)

**Reason:** SRAM read has 1-cycle latency. Scanning all sets during fence.i would take too many cycles.

**Preferred:** Register-based dirty array — O(1) access time.

### 2. Blocking cache during fence.i (partially used)

We block the cache with a pipeline stall but ensured the normal cache state machine is not corrupted.

### 3. Write-through cache (not used)

**Reason:** Every store goes straight to memory, simplifying fence.i but hurting performance.

**Preferred:** Write-back cache — better performance; fence.i requires dirty writeback.

### 4. Invalidate-only approach (not used)

**Reason:** Invalidating alone loses data. Dirty lines would be dropped without writeback to memory.

**Preferred:** Dirty writeback + invalidate.

## File changes

| File | Change |
|------|--------|
| `rtl/core/mmu/cache.sv` | Fence.i FSM, dirty register array, `fencei_stall_o` port |
| `rtl/core/stage04_memory/memory.sv` | `fencei_stall_o` passthrough |
| `rtl/core/cpu.sv` | `FENCEI_STALL` integration, pipe2 flush fix |
| `rtl/pkg/level_param.sv` | `FENCEI_STALL` enum value |
| `rtl/include/writeback_log.svh` | `FENCEI_STALL` logging condition |

## Test result

```
✅ MATCH | PC=0x80002004 INST=0x14d68693 x13 0x000001bc | PC=0x80002004 INST=0x14d68693 x13 0x000001bc
```

The test passed. The dcache wrote dirty data to memory and the icache fetched the new instruction correctly.

## Future improvements

1. **Parallel dirty scan:** Scan dirty bits across sets in parallel for faster writeback
2. **Priority encoder:** Ordering when multiple dirty ways exist
3. **Writeback buffer:** Buffer back-to-back writebacks to optimize memory bandwidth
