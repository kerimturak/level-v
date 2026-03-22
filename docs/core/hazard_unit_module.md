# Hazard Unit Module — Technical Documentation

## Contents

1. [Overview](#overview)
2. [Module Interface](#module-interface)
3. [Data Hazard Types](#data-hazard-types)
4. [Forwarding Mechanism](#forwarding-mechanism)
5. [Stall Mechanism](#stall-mechanism)
6. [Flush Mechanism](#flush-mechanism)
7. [Decision Matrix](#decision-matrix)
8. [Timing Diagrams](#timing-diagrams)
9. [Performance Analysis](#performance-analysis)
10. [Verification and Test](#verification-and-test)

---

## Overview

### Purpose

The `hazard_unit` module detects and resolves **data hazards** in the five-stage pipeline. It controls **forwarding** and **stall** (pipeline hold) so the processor produces correct results.

### Key features

| Feature | Value |
|---------|-------|
| **Hazard types** | RAW (read after write), control |
| **Forwarding paths** | MEM→EX, WB→EX, WB→DE |
| **Stall support** | Load-use hazard |
| **Flush support** | Branch misprediction |
| **Combinational design** | Fully combinational (no registers) |

### Hazard unit block diagram

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                               HAZARD UNIT                                        │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌───────────────────────────────────────────────────────────────────────┐     │
│   │                    REGISTER ADDRESSES                                  │     │
│   │                                                                        │     │
│   │   Decode Stage     Execute Stage     Memory Stage    Writeback Stage  │     │
│   │   ┌─────────┐      ┌─────────┐       ┌─────────┐     ┌─────────┐      │     │
│   │   │r1_addr  │      │r1_addr  │       │rd_addr  │     │rd_addr  │      │     │
│   │   │r2_addr  │      │r2_addr  │       │rf_rw    │     │rf_rw    │      │     │
│   │   └────┬────┘      │rd_addr  │       └────┬────┘     └────┬────┘      │     │
│   │        │           └────┬────┘            │               │           │     │
│   └────────┼────────────────┼─────────────────┼───────────────┼───────────┘     │
│            │                │                 │               │                  │
│            ▼                ▼                 ▼               ▼                  │
│   ┌────────────────────────────────────────────────────────────────────────┐    │
│   │                        COMPARATOR MATRIX                                │    │
│   │                                                                         │    │
│   │   ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐        │    │
│   │   │  EX vs MEM      │  │  EX vs WB       │  │  DE vs WB       │        │    │
│   │   │  Forwarding     │  │  Forwarding     │  │  Forwarding     │        │    │
│   │   └────────┬────────┘  └────────┬────────┘  └────────┬────────┘        │    │
│   │            │                    │                    │                  │    │
│   └────────────┼────────────────────┼────────────────────┼──────────────────┘    │
│                │                    │                    │                       │
│                ▼                    ▼                    ▼                       │
│   ┌────────────────────────────────────────────────────────────────────────┐    │
│   │                         OUTPUT GENERATION                               │    │
│   │                                                                         │    │
│   │   fwd_a_ex[1:0]    fwd_b_ex[1:0]    fwd_a_de    fwd_b_de               │    │
│   │   stall_fe         stall_de         flush_de    flush_ex                │    │
│   │                                                                         │    │
│   └────────────────────────────────────────────────────────────────────────┘    │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Module Interface

### Port definitions

```systemverilog
module hazard_unit (
    // Decode stage register addresses
    input  logic [4:0] r1_addr_de_i,    // Decode rs1 address
    input  logic [4:0] r2_addr_de_i,    // Decode rs2 address
    
    // Execute stage register addresses
    input  logic [4:0] r1_addr_ex_i,    // Execute rs1 address
    input  logic [4:0] r2_addr_ex_i,    // Execute rs2 address
    input  logic [4:0] rd_addr_ex_i,    // Execute rd address
    
    // Execute stage control
    input  logic       pc_sel_ex_i,     // Branch/jump taken
    input  logic       rslt_sel_ex_0,   // Load instruction (result_src[0])
    
    // Memory stage
    input  logic [4:0] rd_addr_me_i,    // Memory rd address
    input  logic       rf_rw_me_i,      // Memory register write enable
    
    // Writeback stage
    input  logic       rf_rw_wb_i,      // Writeback register write enable
    input  logic [4:0] rd_addr_wb_i,    // Writeback rd address
    
    // Stall outputs
    output logic       stall_fe_o,      // Fetch stage stall
    output logic       stall_de_o,      // Decode stage stall
    
    // Flush outputs
    output logic       flush_de_o,      // Decode stage flush
    output logic       flush_ex_o,      // Execute stage flush
    
    // Forwarding outputs
    output logic [1:0] fwd_a_ex_o,      // Execute rs1 forwarding select
    output logic [1:0] fwd_b_ex_o,      // Execute rs2 forwarding select
    output logic       fwd_a_de_o,      // Decode rs1 forwarding
    output logic       fwd_b_de_o       // Decode rs2 forwarding
);
```

### Port descriptions

#### Input ports — decode stage

| Port | Width | Description |
|------|-------|-------------|
| `r1_addr_de_i` | 5 bit | rs1 register address of the instruction in decode |
| `r2_addr_de_i` | 5 bit | rs2 register address of the instruction in decode |

#### Input ports — execute stage

| Port | Width | Description |
|------|-------|-------------|
| `r1_addr_ex_i` | 5 bit | rs1 register address of the instruction in execute |
| `r2_addr_ex_i` | 5 bit | rs2 register address of the instruction in execute |
| `rd_addr_ex_i` | 5 bit | Destination register (rd) address in execute |
| `pc_sel_ex_i` | 1 bit | Branch/jump taken (1 = taken, 0 = not taken) |
| `rslt_sel_ex_0` | 1 bit | Result source bit 0 (1 = load; read from memory) |

#### Input ports — memory stage

| Port | Width | Description |
|------|-------|-------------|
| `rd_addr_me_i` | 5 bit | rd address of the instruction in memory |
| `rf_rw_me_i` | 1 bit | Memory stage register file write enable |

#### Input ports — writeback stage

| Port | Width | Description |
|------|-------|-------------|
| `rd_addr_wb_i` | 5 bit | rd address of the instruction in writeback |
| `rf_rw_wb_i` | 1 bit | Writeback stage register file write enable |

#### Output ports — stall

| Port | Width | Description |
|------|-------|-------------|
| `stall_fe_o` | 1 bit | Stall fetch stage |
| `stall_de_o` | 1 bit | Stall decode stage |

#### Output ports — flush

| Port | Width | Description |
|------|-------|-------------|
| `flush_de_o` | 1 bit | Clear decode pipeline register |
| `flush_ex_o` | 1 bit | Clear execute pipeline register |

#### Output ports — forwarding

| Port | Width | Description |
|------|-------|-------------|
| `fwd_a_ex_o` | 2 bit | Forwarding select for execute rs1 |
| `fwd_b_ex_o` | 2 bit | Forwarding select for execute rs2 |
| `fwd_a_de_o` | 1 bit | Forward decode rs1 from WB |
| `fwd_b_de_o` | 1 bit | Forward decode rs2 from WB |

---

## Data Hazard Types

### RAW (read after write) hazard

A RAW hazard occurs when an instruction tries to read a register that has not yet been written.

```
Cycle:     1      2      3      4      5
         ┌──────┬──────┬──────┬──────┬──────┐
ADD x1   │  IF  │  DE  │  EX  │  MEM │  WB  │  ← writes x1
         └──────┴──────┴──────┴──────┴──────┘
               ┌──────┬──────┬──────┬──────┬──────┐
SUB x2,x1│     │  IF  │  DE  │  EX  │  MEM │  WB  │  ← reads x1
               └──────┴──────┴──────┴──────┴──────┘
                        ↑
                        │ RAW hazard: x1 not yet written!
```

### RAW hazard categories

| Category | Distance | Source → destination | Resolution |
|----------|----------|----------------------|------------|
| **EX-EX** | 1 cycle | MEM → EX | Forwarding |
| **MEM-EX** | 2 cycles | WB → EX | Forwarding |
| **WB-DE** | 3 cycles | WB → DE | Forwarding |
| **Load-use** | 1 cycle | MEM (load) → EX | Stall + forward |

### Load-use hazard

A load’s result is only ready in MEM, so the immediately following instruction cannot use it without a stall.

```
Cycle:     1      2      3      4      5      6
         ┌──────┬──────┬──────┬──────┬──────┐
LW x1    │  IF  │  DE  │  EX  │  MEM │  WB  │  ← x1 ready in MEM
         └──────┴──────┴──────┴──────┴──────┘
               ┌──────┬──────┬──────┬──────┬──────┐
ADD x2,x1│     │  IF  │  DE  │ stall│  EX  │  MEM │  WB
               └──────┴──────┴──────┴──────┴──────┘
                              ↑
                              │ 1-cycle stall (bubble)
                              │ then MEM→EX forward
```

### Control hazard

Branch or jump target is resolved in execute. On a wrong prediction, speculative instructions in the pipeline must be flushed.

```
Cycle:     1      2      3      4      5
         ┌──────┬──────┬──────┬──────┬──────┐
BEQ x1,x2│  IF  │  DE  │  EX  │  MEM │  WB  │  ← decision in EX
         └──────┴──────┴──────┴──────┴──────┘
               ┌──────┬──────┐
Wrong I1 │     │  IF  │  DE  │ flush │        ← wrong-path instr
               └──────┴──────┘
                     ┌──────┐
Wrong I2       │     │  IF  │ flush │          ← wrong-path instr
                     └──────┘
                              ┌──────┬──────┬──────┬──────┬──────┐
Target I │                    │  IF  │  DE  │  EX  │  MEM │  WB  │
                              └──────┴──────┴──────┴──────┴──────┘
```

---

## Forwarding Mechanism

### Forwarding paths

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          FORWARDING PATHS                                        │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│                    PIPELINE STAGES                                               │
│   ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐      │
│   │  FETCH  │───▶│  DECODE │───▶│ EXECUTE │───▶│  MEMORY │───▶│WRITEBACK│      │
│   └─────────┘    └────┬────┘    └────┬────┘    └────┬────┘    └────┬────┘      │
│                       │              │              │               │           │
│                       │              │              │               │           │
│                       │      ┌───────┴───────┐     │               │           │
│                       │      │   ALU/CSR     │     │               │           │
│                       │      │   Result      │     │               │           │
│                       │      └───────────────┘     │               │           │
│                       │              ▲              │               │           │
│                       │              │              │               │           │
│   ┌───────────────────┼──────────────┼──────────────┼───────────────┘           │
│   │                   │              │              │                           │
│   │   WB → DE         │              │   MEM → EX   │   WB → EX                 │
│   │   Forwarding      │              │   Forwarding │   Forwarding              │
│   │   (fwd_a_de)      │              │   (fwd=10)   │   (fwd=01)                │
│   │   (fwd_b_de)      ▼              │              │                           │
│   │              ┌─────────┐         │              │                           │
│   │              │ rs1/rs2 │◀────────┴──────────────┘                           │
│   │              │   MUX   │                                                     │
│   │              └─────────┘                                                     │
│   │                                                                              │
│   └──────────────────────────────────────────────────────────────────────────────│
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Execute stage forwarding (fwd_a_ex, fwd_b_ex)

```systemverilog
always_comb begin
    // Rs1 forwarding — execute stage
    if (rf_rw_me_i && (r1_addr_ex_i == rd_addr_me_i) && (r1_addr_ex_i != 0)) begin
        // Forward from MEM stage (1 cycle newer)
        fwd_a_ex_o = 2'b10;
    end else if (rf_rw_wb_i && (r1_addr_ex_i == rd_addr_wb_i) && (r1_addr_ex_i != 0)) begin
        // Forward from WB stage (2 cycles newer)
        fwd_a_ex_o = 2'b01;
    end else begin
        // Normal register file read
        fwd_a_ex_o = 2'b00;
    end

    // Rs2 forwarding — execute stage
    if (rf_rw_me_i && (r2_addr_ex_i == rd_addr_me_i) && (r2_addr_ex_i != 0)) begin
        // Forward from MEM stage
        fwd_b_ex_o = 2'b10;
    end else if (rf_rw_wb_i && (r2_addr_ex_i == rd_addr_wb_i) && (r2_addr_ex_i != 0)) begin
        // Forward from WB stage
        fwd_b_ex_o = 2'b01;
    end else begin
        // Normal register file read
        fwd_b_ex_o = 2'b00;
    end
end
```

### Forwarding select table

| fwd_x_ex | Source | Description |
|----------|--------|-------------|
| `2'b00` | Register file | Normal read, no hazard |
| `2'b01` | WB stage | Value written 2 cycles ahead |
| `2'b10` | MEM stage | Value computed 1 cycle ahead |

### Decode stage forwarding (fwd_a_de, fwd_b_de)

```systemverilog
always_comb begin
    // Forward from WB stage to decode
    fwd_a_de_o = rf_rw_wb_i && (r1_addr_de_i == rd_addr_wb_i) && (r1_addr_de_i != 0);
    fwd_b_de_o = rf_rw_wb_i && (r2_addr_de_i == rd_addr_wb_i) && (r2_addr_de_i != 0);
end
```

**Note:** Decode-stage forwarding is needed for branch decisions. The branch comparator runs in decode and needs the latest register values.

### Register x0 protection

```systemverilog
// x0 is always 0; do not forward
(r1_addr_ex_i != 0)  // x0 check
(r2_addr_ex_i != 0)  // x0 check
```

In RISC-V, `x0` is hardwired to zero. Writes to it are ignored and reads always return zero, so `x0` must not be forwarded.

---

## Stall Mechanism

### Load-use hazard detection

```systemverilog
always_comb begin
    // Load-use: load result consumed by the immediately following instruction
    lw_stall = rslt_sel_ex_0 && 
               ((r1_addr_de_i == rd_addr_ex_i) || (r2_addr_de_i == rd_addr_ex_i));
    
    // Stall signals
    stall_fe_o = lw_stall;  // Hold fetch
    stall_de_o = lw_stall;  // Hold decode
end
```

### Stall conditions

A load-use hazard occurs when all of the following hold:

1. **A load is in execute:** `rslt_sel_ex_0 = 1`
2. **The instruction in decode reads the load’s destination:**
   - `r1_addr_de_i == rd_addr_ex_i` OR
   - `r2_addr_de_i == rd_addr_ex_i`

### Stall behavior

```
Load-use stall sequence:
┌────────────────────────────────────────────────────────────────┐
│                                                                │
│  Cycle N:                                                      │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐                    │
│  │   DE    │───▶│   EX    │───▶│   MEM   │                    │
│  │  ADD    │    │  LW x1  │    │   ...   │                    │
│  │ x2,x1,x3│    │  0(x4)  │    │         │                    │
│  └─────────┘    └─────────┘    └─────────┘                    │
│       │              │                                         │
│       │              ▼                                         │
│       │     ┌─────────────────┐                               │
│       └────▶│  Hazard Detect  │                               │
│             │  x1 == x1 ✓     │                               │
│             │  rslt_sel[0]=1 ✓│                               │
│             │  → lw_stall = 1 │                               │
│             └─────────────────┘                               │
│                                                                │
│  Cycle N+1: (stall active)                                    │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    │
│  │   DE    │    │ bubble  │───▶│   EX    │───▶│   MEM   │    │
│  │  ADD    │    │  (NOP)  │    │  LW x1  │    │   ...   │    │
│  │(holding)     │         │    │(continues)│    │         │    │
│  └─────────┘    └─────────┘    └─────────┘    └─────────┘    │
│       │                              │                         │
│       │                              ▼                         │
│       │                      ┌─────────────┐                  │
│       │                      │  x1 value   │                  │
│       │                      │ ready in    │                  │
│       └──────────────────────│    MEM      │                  │
│                              └─────────────┘                  │
│                                                                │
│  Cycle N+2: (normal resume)                                   │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    │
│  │   ...   │───▶│   DE    │───▶│   EX    │───▶│   MEM   │    │
│  │         │    │  ADD    │    │ bubble  │    │  LW x1  │    │
│  │         │    │ x2,x1,x3│    │         │    │         │    │
│  └─────────┘    └─────────┘    └─────────┘    └─────────┘    │
│                      │              ▲                         │
│                      │              │                         │
│                      │      ┌───────────────┐                 │
│                      └─────▶│ MEM→EX Forward│                 │
│                             │   fwd = 10    │                 │
│                             └───────────────┘                 │
│                                                                │
└────────────────────────────────────────────────────────────────┘
```

### Stall + forward combination

For a load-use hazard:
1. **Cycle 1:** Hazard detected, stall begins
2. **Cycle 2:** Bubble inserted; LW advances to memory
3. **Cycle 3:** Value forwarded MEM→EX

---

## Flush Mechanism

### Flush conditions

```systemverilog
always_comb begin
    // Branch misprediction: decode stage flush
    flush_de_o = pc_sel_ex_i;  // Branch taken
    
    // Execute stage flush: load-use stall OR branch misprediction
    flush_ex_o = lw_stall || pc_sel_ex_i;
end
```

### Flush scenarios

#### Scenario 1: Branch taken (misprediction)

```
Cycle:     1      2      3      4      5      6
         ┌──────┬──────┬──────┬──────┬──────┐
BEQ      │  IF  │  DE  │  EX  │  MEM │  WB  │
         └──────┴──────┴──────┴──────┴──────┘
                              ↑
                              │ pc_sel_ex_i = 1 (branch taken)
                              │ flush_de_o = 1
                              │ flush_ex_o = 1
         
               ┌──────┬──────┐
Wrong I1 │     │  IF  │  DE  │ ← flush (becomes NOP)
               └──────┴──────┘
                     ┌──────┐
Wrong I2       │     │  IF  │   ← flush (becomes NOP)
                     └──────┘
                              ┌──────┬──────┬──────┬──────┬──────┐
Target   │                    │  IF  │  DE  │  EX  │  MEM │  WB  │
                              └──────┴──────┴──────┴──────┴──────┘
```

#### Scenario 2: Flush with load-use stall

```
Cycle:     1      2      3      4      5      6
         ┌──────┬──────┬──────┬──────┬──────┐
LW x1    │  IF  │  DE  │  EX  │  MEM │  WB  │
         └──────┴──────┴──────┴──────┴──────┘
               ┌──────┬──────┬──────┬──────┬──────┐
ADD x2,x1│     │  IF  │  DE  │stall │  EX  │  MEM │
               └──────┴──────┴──────┴──────┴──────┘
                              ↑
                              │ lw_stall = 1
                              │ flush_ex_o = 1 (bubble inject)
                              │ stall_fe_o = 1
                              │ stall_de_o = 1
```

### Flush priorities

```
┌─────────────────────────────────────────────────────────────────┐
│                      FLUSH PRIORITY TABLE                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   Condition                  │ flush_de │ flush_ex │ Note      │
│   ───────────────────────────┼──────────┼──────────┼───────────│
│   lw_stall = 1, pc_sel = 0   │    0     │    1     │ Bubble    │
│   lw_stall = 0, pc_sel = 1   │    1     │    1     │ Br flush  │
│   lw_stall = 1, pc_sel = 1   │    1     │    1     │ Both      │
│   lw_stall = 0, pc_sel = 0   │    0     │    0     │ Normal    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Decision Matrix

### Full hazard decision table

```
┌────────────────────────────────────────────────────────────────────────────────────────┐
│                              HAZARD DECISION MATRIX                                      │
├────────────────────────────────────────────────────────────────────────────────────────┤
│                                                                                        │
│  Inputs                                                Outputs                         │
│  ──────────────────────────────────────────────────────────────────────────────────── │
│  rf_rw_me │ rs1_ex=rd_me │ rs1_ex≠0 │                    │ fwd_a_ex = 10 (MEM→EX)     │
│  rf_rw_wb │ rs1_ex=rd_wb │ rs1_ex≠0 │ (no MEM match)       │ fwd_a_ex = 01 (WB→EX)      │
│  other    │              │          │                    │ fwd_a_ex = 00 (RegFile)    │
│                                                                                        │
│  rf_rw_me │ rs2_ex=rd_me │ rs2_ex≠0 │                    │ fwd_b_ex = 10 (MEM→EX)     │
│  rf_rw_wb │ rs2_ex=rd_wb │ rs2_ex≠0 │ (no MEM match)       │ fwd_b_ex = 01 (WB→EX)      │
│  other    │              │          │                    │ fwd_b_ex = 00 (RegFile)    │
│                                                                                        │
│  rf_rw_wb │ rs1_de=rd_wb │ rs1_de≠0 │                    │ fwd_a_de = 1               │
│  rf_rw_wb │ rs2_de=rd_wb │ rs2_de≠0 │                    │ fwd_b_de = 1               │
│                                                                                        │
│  rslt_sel[0]=1 │ (rs1_de=rd_ex ∨ rs2_de=rd_ex)          │ lw_stall = 1               │
│                │                                         │ stall_fe = 1               │
│                │                                         │ stall_de = 1               │
│                │                                         │ flush_ex = 1               │
│                                                                                        │
│  pc_sel_ex = 1 │                                         │ flush_de = 1               │
│                │                                         │ flush_ex = 1               │
│                                                                                        │
└────────────────────────────────────────────────────────────────────────────────────────┘
```

### Forwarding priority order

```
┌─────────────────────────────────────────────────────────────────┐
│                  FORWARDING PRIORITY ORDER                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   Priority 1: MEM stage (fwd = 10)                              │
│   ────────────────────────────────                              │
│   Newest value, computed one cycle earlier                      │
│   Condition: rf_rw_me && (rs_ex == rd_me) && (rs_ex != 0)      │
│                                                                 │
│   Priority 2: WB stage (fwd = 01)                               │
│   ───────────────────────────────                               │
│   Value from two cycles ahead                                   │
│   Condition: rf_rw_wb && (rs_ex == rd_wb) && (rs_ex != 0)      │
│              && !(MEM condition)                                │
│                                                                 │
│   Priority 3: Register file (fwd = 00)                          │
│   ────────────────────────────────────                          │
│   Normal register read, no hazard                               │
│   Condition: Otherwise                                          │
│                                                                 │
│   NOTE: MEM wins because the same register can be written       │
│         back-to-back; the latest value (in MEM) is correct.     │
│                                                                 │
│   Example:                                                      │
│   ADD x1, x2, x3    ; writes x1 (now in WB)                   │
│   SUB x1, x4, x5    ; writes x1 (now in MEM)                    │
│   OR  x6, x1, x7    ; reads x1 → forward from MEM              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Timing Diagrams

### Normal operation (no hazard)

```
clk     ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

         Cycle 1   Cycle 2   Cycle 3   Cycle 4   Cycle 5

Instr    ADD x1    SUB x5    OR x7     AND x9    XOR x11
         x2,x3     x6,x1     x8,x5     x10,x7    x12,x9

Stage    IF        DE        EX        MEM       WB
               │         │         │         │
fwd_a_ex ─────┴─────────┴─────────┴─────────┴───── 00
fwd_b_ex ─────────────────────────────────────────  00
stall    _____________________________________________  0
flush    _____________________________________________  0
```

### MEM→EX Forwarding

```
clk     ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

         Cycle 1   Cycle 2   Cycle 3   Cycle 4   Cycle 5

ADD x1   │ IF     │ DE      │ EX      │ MEM     │ WB
         │        │         │ result  │ fwd src │
         │        │         │  ready  │         │

SUB x2,x1│        │ IF      │ DE      │ EX      │ MEM
         │        │         │         │ x1 need │

fwd_a_ex ─────────────────────────────/‾‾‾‾‾‾‾‾‾‾‾‾\─────
                                      │   10      │

Pipeline │        │         │ x1=ALU  │─────────▶│ x1 to
Data Flow│        │         │ result  │ forward  │ SUB rs1
```

### Load-Use Hazard + Stall

```
clk     ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

         Cycle 1   Cycle 2   Cycle 3   Cycle 4   Cycle 5

LW x1    │ IF     │ DE      │ EX      │ MEM     │ WB
         │        │         │         │ x1 ready│

ADD x2,x1│        │ IF      │ DE(hold)│ DE      │ EX
         │        │         │ stall!  │ resume  │ fwd x1

lw_stall ─────────────────────/‾‾‾‾‾‾‾\________________________
                              │ detect │

stall_fe ─────────────────────/‾‾‾‾‾‾‾\________________________
stall_de ─────────────────────/‾‾‾‾‾‾‾\________________________
flush_ex ─────────────────────/‾‾‾‾‾‾‾\________________________

fwd_a_ex ───────────────────────────────────────/‾‾‾‾‾‾‾\──────
                                                │  10   │

Pipeline │        │         │ bubble  │ LW MEM  │ ADD EX
State    │        │         │ inject  │ x1 load │ x1 fwd
```

### Branch Misprediction + Flush

```
clk     ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

         Cycle 1   Cycle 2   Cycle 3   Cycle 4   Cycle 5

BEQ taken│ IF     │ DE      │ EX      │ MEM     │ WB
         │        │         │ resolve │         │
         │        │         │ taken!  │         │

Wrong I1 │        │ IF      │ DE      │ FLUSH   │
         │        │(predict │(wrong)  │(bubble) │
         │        │ not-take)         │         │

Wrong I2 │        │         │ IF      │ FLUSH   │
         │        │         │(wrong)  │(bubble) │

Target   │        │         │         │ IF      │ DE
         │        │         │         │(correct)│(start)

pc_sel   ─────────────────────/‾‾‾‾‾‾‾\________________________
                              │taken=1│

flush_de ─────────────────────/‾‾‾‾‾‾‾\________________________
flush_ex ─────────────────────/‾‾‾‾‾‾‾\________________________
```

---

## Performance Analysis

### Hazard impact

| Hazard type | Latency | Resolution | IPC impact |
|-------------|---------|------------|------------|
| RAW (ALU→ALU) | 0 cycles | Forwarding | None |
| RAW (MEM→ALU) | 0 cycles | Forwarding | None |
| Load-use | 1 cycle | Stall + forward | ~10–15% drop |
| Branch mispred | 2 cycles | Flush | ~5–10% drop |

### Forwarding effectiveness

```
┌─────────────────────────────────────────────────────────────────┐
│                FORWARDING EFFECTIVENESS                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   Without forwarding (stall only):                               │
│   ──────────────────────────────                                │
│   ADD x1, x2, x3    ; IF DE EX MEM WB                          │
│   SUB x4, x1, x5    ; IF DE -- -- EX MEM WB (3-cycle stall)    │
│                                                                 │
│   With forwarding:                                              │
│   ─────────────────                                             │
│   ADD x1, x2, x3    ; IF DE EX MEM WB                          │
│   SUB x4, x1, x5    ; IF DE EX MEM WB (0-cycle stall)         │
│                                                                 │
│   Gain: 3 cycles per instruction pair                           │
│                                                                 │
│   Load-use (unavoidable):                                       │
│   ────────────────────                                          │
│   LW  x1, 0(x2)     ; IF DE EX MEM WB                          │
│   ADD x3, x1, x4    ; IF DE -- EX MEM WB (1-cycle stall)       │
│                                                                 │
│   Note: Load-use cannot be fully removed; data arrives from     │
│         memory in MEM.                                            │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Stall statistics (typical workload)

| Metric | Value | Description |
|--------|-------|-------------|
| Load fraction | ~25% | Of all instructions |
| Load-use rate | ~30% | Of loads |
| Net stall rate | ~7.5% | Of all cycles |
| Branch fraction | ~15% | Of all instructions |
| Misprediction | ~10% | Of branches |
| Net flush rate | ~3% | Of all cycles |

### Optimization ideas

1. **Compiler:** Schedule instructions to reduce load-use hazards
2. **Branch prediction:** GSHARE, BTB, RAS to cut mispredictions
3. **Loop unrolling:** Fewer branches
4. **Prefetching:** Hide load latency

---

## Verification and Test

### Assertions

```systemverilog
// MEM forwarding priority check
assert property (@(posedge clk_i)
    (rf_rw_me_i && rf_rw_wb_i && 
     (r1_addr_ex_i == rd_addr_me_i) && 
     (r1_addr_ex_i == rd_addr_wb_i) && 
     (r1_addr_ex_i != 0)) |->
    (fwd_a_ex_o == 2'b10)
) else $error("MEM forwarding should have priority over WB");

// x0 forwarding check
assert property (@(posedge clk_i)
    (r1_addr_ex_i == 0) |-> (fwd_a_ex_o == 2'b00)
) else $error("x0 should never be forwarded");

// Load-use stall check
assert property (@(posedge clk_i)
    (rslt_sel_ex_0 && (r1_addr_de_i == rd_addr_ex_i) && (rd_addr_ex_i != 0)) |->
    lw_stall
) else $error("Load-use hazard should trigger stall");

// Stall/flush consistency
assert property (@(posedge clk_i)
    lw_stall |-> (stall_fe_o && stall_de_o && flush_ex_o)
) else $error("Load-use stall signals inconsistent");
```

### Test scenarios

#### Test 1: Back-to-back RAW hazard

```assembly
# MEM→EX forwarding test
ADD x1, x2, x3      # write x1
SUB x4, x1, x5      # read x1 (1 cycle later)
# Expect: fwd_a_ex = 10, stall = 0

# WB→EX forwarding test
ADD x1, x2, x3      # write x1
NOP                 # 1-cycle gap
SUB x4, x1, x5      # read x1 (2 cycles later)
# Expect: fwd_a_ex = 01, stall = 0
```

#### Test 2: Load-use hazard

```assembly
# Load-use stall test
LW  x1, 0(x2)       # load x1
ADD x3, x1, x4      # use x1 immediately
# Expect: 1-cycle stall, then fwd_a_ex = 10
```

#### Test 3: Multiple writes to same register

```assembly
# Forwarding priority test
ADD x1, x2, x3      # write x1 (will be in WB)
SUB x1, x4, x5      # write x1 again (will be in MEM)
OR  x6, x1, x7      # read x1
# Expect: fwd_a_ex = 10 from MEM (newest value)
```

#### Test 4: x0 register

```assembly
# x0 forwarding prevention test
ADD x0, x1, x2      # write x0 (ignored)
SUB x3, x0, x4      # read x0 (always 0)
# Expect: fwd_a_ex = 00, SUB rs1 = 0
```

#### Test 5: Branch flush

```assembly
# Branch misprediction test
BEQ x1, x2, target  # branch (predict not-taken)
ADD x3, x4, x5      # wrong path (should flush)
SUB x6, x7, x8      # wrong path (should flush)
target:
AND x9, x10, x11    # correct path
# Expect: flush_de = 1, flush_ex = 1
```

### Coverage points

```systemverilog
covergroup hazard_cg @(posedge clk);
    // Forwarding coverage
    fwd_a_type: coverpoint fwd_a_ex_o {
        bins no_fwd = {2'b00};
        bins wb_fwd = {2'b01};
        bins mem_fwd = {2'b10};
    }
    
    fwd_b_type: coverpoint fwd_b_ex_o {
        bins no_fwd = {2'b00};
        bins wb_fwd = {2'b01};
        bins mem_fwd = {2'b10};
    }
    
    // Stall coverage
    stall_type: coverpoint {stall_fe_o, stall_de_o} {
        bins no_stall = {2'b00};
        bins load_use = {2'b11};
    }
    
    // Flush coverage
    flush_type: coverpoint {flush_de_o, flush_ex_o} {
        bins no_flush = {2'b00};
        bins load_use_bubble = {2'b01};
        bins branch_flush = {2'b11};
    }
    
    // Cross coverage
    fwd_stall_cross: cross fwd_a_type, stall_type;
endgroup
```

---

## Summary

The `hazard_unit` is critical for correct operation of the Level RISC-V processor.

### Core functions

1. **Data forwarding:** Resolves RAW hazards via MEM→EX, WB→EX, and WB→DE
2. **Stall generation:** One-cycle stall on load-use hazards
3. **Flush control:** Clears the pipeline on branch misprediction and in stall-related cases

### Design properties

- **Fully combinational:** No registers, minimal delay
- **Prioritized forwarding:** MEM before WB
- **x0 protection:** No forwarding for the hardwired-zero register
- **Minimal stall:** Only mandatory load-use stalls

### Performance impact

- **Forwarding:** Saves ~3 cycles per dependent RAW pair
- **Load-use stall:** 1-cycle loss (unavoidable)
- **Branch flush:** 2-cycle loss on misprediction

This module provides the hazard management needed for an in-order five-stage pipeline and enables near one-instruction-per-cycle throughput when hazards are rare.
