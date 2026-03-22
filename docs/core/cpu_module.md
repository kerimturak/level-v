# CPU Module — Technical Documentation

## Contents

1. [Overview](#overview)
2. [Module Interface](#module-interface)
3. [Pipeline Architecture](#pipeline-architecture)
4. [Pipeline Register Structures](#pipeline-register-structures)
5. [Stall and Flush Mechanisms](#stall-and-flush-mechanisms)
6. [Exception Handling](#exception-handling)
7. [Branch Prediction Feedback](#branch-prediction-feedback)
8. [Memory Arbiter](#memory-arbiter)
9. [Hardware Interrupts](#hardware-interrupts)
10. [Timing Diagrams](#timing-diagrams)
11. [Performance Analysis](#performance-analysis)
12. [Verification and Test](#verification-and-test)

---

## Overview

### Purpose

The `cpu` module is the **top-level** module of the Level RISC-V processor. It integrates the five-stage pipeline architecture and coordinates data flow among all submodules.

### Key Features

| Feature | Value |
|---------|-------|
| **ISA** | RV32IMC (Base Integer + Multiply + Compressed) |
| **Pipeline depth** | 5 stages (Fetch, Decode, Execute, Memory, Writeback) |
| **Addressing** | 32-bit |
| **Memory model** | Von Neumann (unified memory) |
| **Branch prediction** | GSHARE + BTB + RAS |
| **Caches** | I-Cache + D-Cache (8-way, 8KB) |
| **Exception support** | Full M-mode exception handling |
| **CSR support** | Machine-mode CSRs |
| **Interrupt support** | Timer, software, external (PLIC) |

### Architectural block diagram

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                                    CPU TOP                                       │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────────┐   │
│  │  FETCH  │───▶│  DECODE │───▶│ EXECUTE │───▶│  MEMORY │───▶│  WRITEBACK  │   │
│  │ Stage 1 │    │ Stage 2 │    │ Stage 3 │    │ Stage 4 │    │   Stage 5   │   │
│  └────┬────┘    └────┬────┘    └────┬────┘    └────┬────┘    └──────┬──────┘   │
│       │              │              │              │                 │          │
│       │    pipe1     │    pipe2     │    pipe3     │      pipe4      │          │
│       └──────────────┴──────────────┴──────────────┴─────────────────┘          │
│                                                                                  │
│  ┌─────────────────────────────────────────────────────────────────────────┐   │
│  │                          HAZARD UNIT                                     │   │
│  │   • Data Forwarding (EX→EX, MEM→EX, WB→EX, WB→DE)                       │   │
│  │   • Load-Use Stall Detection                                             │   │
│  │   • Branch Flush Control                                                 │   │
│  └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│  ┌─────────────────────────────────────────────────────────────────────────┐   │
│  │                        MEMORY ARBITER                                    │   │
│  │   • I-Cache ↔ D-Cache Arbitration                                        │   │
│  │   • Wishbone Bus Interface                                               │   │
│  └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Module Interface

### Port definitions

```systemverilog
module cpu
  import level_param::*;
(
    // Clock and reset
    input  logic       clk_i,        // System clock
    input  logic       rst_ni,       // Active-low asynchronous reset
    
    // Hardware interrupts
    input  logic       timer_irq_i,  // CLINT timer interrupt (MTIP)
    input  logic       sw_irq_i,     // CLINT software interrupt (MSIP)
    input  logic       ext_irq_i,    // PLIC external interrupt (MEIP)
    
    // Memory interface
    output iomem_req_t iomem_req_o,  // Memory request bus
    input  iomem_res_t iomem_res_i   // Memory response bus
);
```

### Port descriptions

#### Clock and reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk_i` | Input | 1 bit | Positive-edge-triggered system clock |
| `rst_ni` | Input | 1 bit | Active-low asynchronous reset (0 = reset active) |

#### Hardware interrupts

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `timer_irq_i` | Input | 1 bit | CLINT timer interrupt (MTIP — Machine Timer Interrupt Pending) |
| `sw_irq_i` | Input | 1 bit | CLINT software interrupt (MSIP — Machine Software Interrupt Pending) |
| `ext_irq_i` | Input | 1 bit | PLIC external interrupt (MEIP — Machine External Interrupt Pending) |

#### Memory interface

| Port | Direction | Type | Description |
|------|-----------|------|-------------|
| `iomem_req_o` | Output | `iomem_req_t` | Wishbone-compatible memory request struct |
| `iomem_res_i` | Input | `iomem_res_t` | Wishbone-compatible memory response struct |

### Memory interface structures

```systemverilog
// Memory request structure (iomem_req_t)
typedef struct packed {
    logic [XLEN-1:0]       addr;     // Memory address
    logic [XLEN-1:0]       wdata;    // Write data
    logic [WB_SEL_WIDTH-1:0] sel;    // Byte select signals
    logic                  we;       // Write enable (1=write, 0=read)
    logic                  valid;    // Request valid
    logic [2:0]            burst;    // Burst type
} iomem_req_t;

// Memory response structure (iomem_res_t)
typedef struct packed {
    logic [XLEN-1:0]       rdata;    // Read data
    logic                  ready;    // Response ready
    logic                  error;    // Error status
} iomem_res_t;
```

---

## Pipeline Architecture

### Five-stage pipeline overview

```
Cycle:    1     2     3     4     5     6     7     8
        ┌─────┬─────┬─────┬─────┬─────┐
Instr 1 │ IF  │ DE  │ EX  │ MEM │ WB  │
        └─────┴─────┴─────┴─────┴─────┘
              ┌─────┬─────┬─────┬─────┬─────┐
Instr 2       │ IF  │ DE  │ EX  │ MEM │ WB  │
              └─────┴─────┴─────┴─────┴─────┘
                    ┌─────┬─────┬─────┬─────┬─────┐
Instr 3             │ IF  │ DE  │ EX  │ MEM │ WB  │
                    └─────┴─────┴─────┴─────┴─────┘
                          ┌─────┬─────┬─────┬─────┬─────┐
Instr 4                   │ IF  │ DE  │ EX  │ MEM │ WB  │
                          └─────┴─────┴─────┴─────┴─────┘
```

### Pipeline stages

#### Stage 1: Instruction Fetch (IF)

```systemverilog
fetch #(
    .RESET_VECTOR(RESET_VECTOR)
) i_fetch (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .flush_i      (fencei_flush),      // FENCE.I cache flush
    .flush_pc_i   (flush_pc),          // PC after flush
    .stall_i      (stall_cause),       // Stall cause
    .lx_ires_i    (fe_lx_ires),        // I-Cache response
    .pc_target_i  (ex_pc_target_last), // Branch target address
    .spec_hit_i   (ex_spec_hit),       // Speculation correct?
    .ex_mtvec_i   (ex_mtvec),          // Trap vector address
    .trap_active_i(fe_trap_active),    // Trap active?
    .misa_c_i     (ex_misa_c),         // C extension enabled?
    .tdata1_i     (ex_tdata1),         // Trigger data 1
    .tdata2_i     (ex_tdata2),         // Trigger data 2
    .tcontrol_i   (ex_tcontrol),       // Trigger control
    .spec_o       (fe_spec),           // Branch prediction info
    .lx_ireq_o    (lx_ireq),           // I-Cache request
    .pc_o         (fe_pc),             // Current PC
    .pc_incr_o    (fe_pc_incr),        // Next PC (PC+2/4)
    .inst_o       (fe_inst),           // Fetched instruction
    .imiss_stall_o(fe_imiss_stall),    // I-Cache miss stall
    .exc_type_o   (fe_exc_type),       // Exception type
    .instr_type_o (fe_instr_type),     // Instruction type
    .de_info_i    (de_info),           // Decode feedback
    .ex_info_i    (ex_info)            // Execute feedback
);
```

**Fetch stage responsibilities:**
- Program counter (PC) management
- Instruction cache access
- Compressed instruction (RV32C) decode
- Branch prediction (GSHARE, BTB, RAS)
- Instruction alignment (32-bit boundary)
- Exception detection (INSTR_ACCESS_FAULT, ILLEGAL_INSTRUCTION)

#### Stage 2: Instruction Decode (DE)

```systemverilog
decode i_decode (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),
    .fwd_a_i     (de_fwd_a),        // Rs1 forwarding from WB
    .fwd_b_i     (de_fwd_b),        // Rs2 forwarding from WB
    .wb_data_i   (wb_data),         // Writeback data
    .inst_i      (pipe1.inst),      // Instruction from fetch
    .instr_type_i(pipe1.instr_type),// Instruction type
    .rd_addr_i   (pipe4.rd_addr),   // WB destination register
    .rf_rw_en_i  (wb_rf_rw),        // WB register write enable
    .r1_data_o   (de_r1_data),      // Rs1 data
    .r2_data_o   (de_r2_data),      // Rs2 data
    .ctrl_o      (de_ctrl),         // Control signals
    .imm_o       (de_imm),          // Immediate value
    .exc_type_o  (de_exc_type)      // Exception type
);
```

**Decode stage responsibilities:**
- Instruction decode (opcode, funct3, funct7)
- Register file read (rs1, rs2)
- Immediate extension
- Control signal generation
- Information for hazard detection

#### Stage 3: Execute (EX)

```systemverilog
execution i_execution (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .stall_i      (stall_cause),
    .fwd_a_i      (ex_fwd_a),         // Rs1 forwarding select
    .fwd_b_i      (ex_fwd_b),         // Rs2 forwarding select
    .alu_result_i (pipe3.alu_result), // MEM stage ALU result
    .wb_data_i    (wb_data),          // WB stage data
    .r1_data_i    (pipe2.r1_data),    // Rs1 from decode
    .r2_data_i    (pipe2.r2_data),    // Rs2 from decode
    .alu_in1_sel_i(pipe2.alu_in1_sel),// ALU input 1 select
    .alu_in2_sel_i(pipe2.alu_in2_sel),// ALU input 2 select
    .instr_type_i (pipe2.instr_type), // Instruction type
    .trap_active_i(trap_active),      // Trap active flag
    .trap_tval_i  (trap_tval),        // Trap value
    .trap_cause_i (ex_trap_cause),    // Trap cause
    .trap_mepc_i  (ex_trap_mepc),     // Trap return address
    .timer_irq_i  (timer_irq_i),      // Timer interrupt
    .sw_irq_i     (sw_irq_i),         // Software interrupt
    .ext_irq_i    (ext_irq_i),        // External interrupt
    .rd_csr_i     (ex_rd_csr),        // CSR read enable
    .wr_csr_i     (ex_wr_csr),        // CSR write enable
    .csr_idx_i    (pipe2.csr_idx),    // CSR index
    .csr_or_data_i(pipe2.csr_or_data),// CSR operation or data
    .pc_i         (pipe2.pc),         // Current PC
    .pc_incr_i    (pipe2.pc_incr),    // Next PC
    .imm_i        (pipe2.imm),        // Immediate
    .pc_sel_i     (pipe2.pc_sel),     // Branch type
    .alu_ctrl_i   (pipe2.alu_ctrl),   // ALU operation
    .write_data_o (ex_wdata),         // Store data
    .pc_target_o  (ex_pc_target),     // Branch target
    .alu_result_o (ex_alu_result),    // ALU result
    .pc_sel_o     (ex_pc_sel),        // Branch taken
    .alu_stall_o  (ex_alu_stall),     // MUL/DIV stall
    .exc_type_o   (ex_alu_exc_type),  // Exception type
    .mtvec_o      (ex_mtvec),         // Trap vector
    .misa_c_o     (ex_misa_c),        // C-extension enable
    .tdata1_o     (ex_tdata1),        // Trigger data 1
    .tdata2_o     (ex_tdata2),        // Trigger data 2
    .tcontrol_o   (ex_tcontrol)       // Trigger control
);
```

**Execute stage responsibilities:**
- ALU operations (arithmetic, logical, compare)
- Branch/jump condition evaluation
- Multiply/divide operations
- CSR read/write
- Exception detection and handling
- Data forwarding

#### Stage 4: Memory Access (MEM)

```systemverilog
memory i_memory (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),
    .stall_i          (stall_cause),
    .fe_flush_cache_i (fencei_flush),   // FENCE.I cache flush
    .me_data_req_i    (me_data_req),    // Memory request (from pipe3)
    .ex_data_req_i    (ex_data_req),    // Memory request (from EX)
    .lx_dres_i        (lx_dres),        // D-Cache response
    .lx_dreq_o        (lx_dreq),        // D-Cache request
    .me_data_o        (me_rdata),       // Load data
    .dmiss_stall_o    (me_dmiss_stall), // D-Cache miss stall
    .fencei_stall_o   (me_fencei_stall) // FENCE.I stall
);
```

**Memory stage responsibilities:**
- Data cache access
- Load/store operations
- Byte/halfword/word alignment
- Cache miss handling
- FENCE.I cache flush

#### Stage 5: Write-Back (WB)

```systemverilog
writeback i_writeback (
    .clk_i           (clk_i),
    .rst_ni          (rst_ni),
    .data_sel_i      (pipe4.result_src), // Data source select
    .pc_incr_i       (pipe4.pc_incr),    // PC+2/4
    .pc_i            (pipe4.pc),         // Current PC
    .alu_result_i    (pipe4.alu_result), // ALU result
    .read_data_i     (pipe4.read_data),  // Memory data
    .stall_i         (stall_cause),      // Stall cause
    .rf_rw_en_i      (pipe4.rf_rw_en),   // Register write enable
    .rf_rw_en_o      (wb_rf_rw),         // Actual write enable
    .wb_data_o       (wb_data)           // Write-back data
);
```

**Write-back stage responsibilities:**
- Result source selection (ALU, memory, PC+4)
- Register file write
- Instruction commit

---

## Pipeline Register Structures

### pipe1: Fetch → Decode

```systemverilog
typedef struct packed {
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;    // Trace info
`endif
    logic [XLEN-1:0] pc;           // Program counter
    logic [XLEN-1:0] pc_incr;      // PC + 2 or PC + 4
    logic [XLEN-1:0] inst;         // 32-bit instruction
    exc_type_e       exc_type;     // Exception type
    instr_type_e     instr_type;   // Instruction type
    predict_info_t   spec;         // Branch prediction info
} pipe1_t;
```

**Pipeline register control:**

```systemverilog
always_ff @(posedge clk_i) begin
    if (!rst_ni || de_flush_en || |priority_flush || fencei_flush) begin
        // On reset or flush: load NOP
        pipe1 <= '{exc_type: NO_EXCEPTION, instr_type: instr_invalid, default: 0};
    end else if (de_enable) begin
        // Normal operation: load data from fetch
        pipe1 <= '{
            pc       : fe_pc,
            pc_incr  : fe_pc_incr,
            inst     : fe_inst,
            exc_type : fe_active_exc_type,
            instr_type: fe_instr_type,
            spec     : fe_spec
            // ... tracer fields
        };
    end
end
```

### pipe2: Decode → Execute

```systemverilog
typedef struct packed {
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;
`endif
    logic [XLEN-1:0] pc;           // Program counter
    logic [XLEN-1:0] pc_incr;      // Next PC
    logic            rf_rw_en;     // Register write enable
    logic            wr_en;        // Memory write enable
    logic [1:0]      rw_size;      // Load/store size
    logic [1:0]      result_src;   // Result source
    alu_op_e         alu_ctrl;     // ALU operation type
    pc_sel_e         pc_sel;       // Branch/jump type
    logic            alu_in1_sel;  // ALU input 1 select
    logic            alu_in2_sel;  // ALU input 2 select
    logic            ld_op_sign;   // Load sign extension
    logic            rd_csr;       // CSR read enable
    logic            wr_csr;       // CSR write enable
    logic [11:0]     csr_idx;      // CSR address
    logic            csr_or_data;  // CSR op or immediate
    logic            dcache_valid; // D-Cache valid
    logic [XLEN-1:0] r1_data;      // Rs1 value
    logic [XLEN-1:0] r2_data;      // Rs2 value
    logic [4:0]      r1_addr;      // Rs1 address
    logic [4:0]      r2_addr;      // Rs2 address
    logic [4:0]      rd_addr;      // Rd address
    logic [XLEN-1:0] imm;          // Immediate value
    instr_type_e     instr_type;   // Instruction type
    predict_info_t   spec;         // Branch prediction info
} pipe2_t;
```

### pipe3: Execute → Memory

```systemverilog
typedef struct packed {
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;
    logic            rd_en_csr;    // CSR read occurred
    logic            wr_en_csr;    // CSR write occurred
    logic [11:0]     csr_idx;      // CSR address
    instr_type_e     instr_type;   // Instruction type
    logic [XLEN-1:0] csr_wr_data;  // CSR write data
`endif
    logic [XLEN-1:0] pc_incr;      // Next PC
    logic [XLEN-1:0] pc;           // Program counter
    logic            rf_rw_en;     // Register write enable
    logic            wr_en;        // Memory write enable
    logic [1:0]      rw_size;      // Load/store size
    logic [1:0]      result_src;   // Result source
    logic            ld_op_sign;   // Load sign extension
    logic [4:0]      rd_addr;      // Rd address
    logic [XLEN-1:0] alu_result;   // ALU result
    logic [XLEN-1:0] write_data;   // Store data
    logic            dcache_valid; // D-Cache valid
    logic [XLEN-1:0] read_data;    // Load data
} pipe3_t;
```

### pipe4: Memory → Write-Back

```systemverilog
typedef struct packed {
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;
    logic            wr_en;
    logic [1:0]      rw_size;
    logic [XLEN-1:0] write_data;
    logic            rd_en_csr;
    logic            wr_en_csr;
    logic [11:0]     csr_idx;
    instr_type_e     instr_type;
    logic [XLEN-1:0] csr_wr_data;
    logic            dcache_valid;
`endif
    logic [XLEN-1:0] pc_incr;      // Next PC
    logic [XLEN-1:0] pc;           // Program counter
    logic            rf_rw_en;     // Register write enable
    logic [1:0]      result_src;   // Result source
    logic [4:0]      rd_addr;      // Rd address
    logic [XLEN-1:0] alu_result;   // ALU result
    logic [XLEN-1:0] read_data;    // Load data
} pipe4_t;
```

---

## Stall and Flush Mechanisms

### Stall causes

```systemverilog
typedef enum logic [2:0] {
    NO_STALL       = 3'b000,  // No stall
    IMISS_STALL    = 3'b001,  // I-Cache miss
    DMISS_STALL    = 3'b010,  // D-Cache miss
    LOAD_RAW_STALL = 3'b011,  // Load-use hazard
    ALU_STALL      = 3'b100,  // MUL/DIV wait
    FENCEI_STALL   = 3'b101   // FENCE.I cache flush
} stall_e;
```

### Stall priority ordering

```systemverilog
always_comb begin
    stall_cause = NO_STALL;
    
    if (me_fencei_stall) begin
        // Highest priority: FENCE.I dirty writeback
        stall_cause = FENCEI_STALL;
    end else if (fe_imiss_stall) begin
        // I-Cache miss
        stall_cause = IMISS_STALL;
    end else if (me_dmiss_stall) begin
        // D-Cache miss
        stall_cause = DMISS_STALL;
    end else if (fe_stall || de_stall) begin
        // Load-use hazard
        stall_cause = LOAD_RAW_STALL;
    end else if (ex_alu_stall) begin
        // MUL/DIV still in progress
        stall_cause = ALU_STALL;
    end
end
```

### Stall behavior

| Stall type | Affected stages | Description |
|------------|-----------------|-------------|
| `FENCEI_STALL` | Entire pipeline | Waiting for D-Cache dirty line writeback |
| `IMISS_STALL` | Fetch, decode | I-Cache miss; waiting for memory |
| `DMISS_STALL` | Entire pipeline | D-Cache miss; waiting for memory |
| `LOAD_RAW_STALL` | Fetch, decode | Load-use data hazard |
| `ALU_STALL` | Entire pipeline | MUL/DIV not yet complete |

### Flush mechanisms

#### Priority flush (exception-based)

```systemverilog
// Flush decision from exception priority
priority_flush = ex_exc_type != NO_EXCEPTION ? 3:          // EX exception
                 de_active_exc_type != NO_EXCEPTION ? 2 :  // DE exception
                 0;                                        // No flush
```

| priority_flush | Flush scope | Description |
|---------------|-------------|-------------|
| 3 | pipe1, pipe2 | Execute exception (highest priority) |
| 2 | pipe1 | Decode exception |
| 0 | None | No flush needed |

#### FENCE.I flush

```systemverilog
// Cache flush on FENCE.I or MISA write
fencei_flush = (pipe2.instr_type == fence_i) || 
               (ex_wr_csr && pipe2.csr_idx == 12'h301);  // misa write

// PC to resume after flush
flush_pc = pipe2.pc_incr;
```

#### Branch misprediction flush

```systemverilog
// Branch prediction correctness
if (ex_pc_sel) 
    ex_spec_hit = pipe2.spec.taken && (ex_pc_target == pipe2.spec.pc);
else 
    ex_spec_hit = !pipe2.spec.taken;

// Target PC on misprediction
if (!ex_spec_hit) begin
    if (ex_pc_sel) 
        ex_pc_target_last = ex_pc_target;  // Taken: go to target
    else 
        ex_pc_target_last = pipe2.pc_incr; // Not taken: sequential PC
end
```

### Flush and stall interaction

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        STALL / FLUSH INTERACTION                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Flush while stall active:                                                  │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ de_flush_en = stall_cause inside {IMISS, DMISS, ALU, FENCEI} ?      │   │
│  │               1'b0 : de_flush;                                       │   │
│  │                                                                      │   │
│  │ ex_flush_en = stall_cause inside {IMISS, DMISS, ALU, FENCEI} ?      │   │
│  │               1'b0 : ex_flush;                                       │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  Logic: While stalled, flush is deferred; when the stall clears, flush     │
│         applies. This avoids losing data during memory access.              │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Exception Handling

### Exception types

```systemverilog
typedef enum logic [4:0] {
    NO_EXCEPTION         = 5'd0,
    INSTR_MISALIGNED     = 5'd1,   // Instruction alignment fault
    INSTR_ACCESS_FAULT   = 5'd2,   // Instruction access fault
    ILLEGAL_INSTRUCTION  = 5'd3,   // Illegal instruction
    BREAKPOINT           = 5'd4,   // EBREAK
    LOAD_MISALIGNED      = 5'd5,   // Load alignment fault
    LOAD_ACCESS_FAULT    = 5'd6,   // Load access fault
    STORE_MISALIGNED     = 5'd7,   // Store alignment fault
    STORE_ACCESS_FAULT   = 5'd8,   // Store access fault
    ECALL_M              = 5'd11   // Machine mode ECALL
} exc_type_e;
```

### Exception sources by stage

| Stage | Exception types | Detection |
|-------|-----------------|-----------|
| **Fetch** | INSTR_ACCESS_FAULT, ILLEGAL_INSTRUCTION | No PMA grant, C-extension decode error |
| **Decode** | ILLEGAL_INSTRUCTION | Unrecognized opcode, invalid CSR |
| **Execute** | INSTR_MISALIGNED, LOAD_MISALIGNED, STORE_MISALIGNED | Address alignment check |
| **Memory** | LOAD_ACCESS_FAULT, STORE_ACCESS_FAULT | PMA violation |

### Exception priority

```systemverilog
// Exception mask: which stage has an exception?
excp_mask = {1'b0, 
             ex_exc_type != NO_EXCEPTION,        // [2] Execute
             de_active_exc_type != NO_EXCEPTION, // [1] Decode
             fe_active_exc_type != NO_EXCEPTION  // [0] Fetch
            };

// Trap active signal
trap_active = |excp_mask[3:1];
fe_trap_active = |{excp_mask[3:1], de_active_exc_type != NO_EXCEPTION};
de_trap_active = de_active_exc_type != NO_EXCEPTION;
```

### Trap cause and trap value

```systemverilog
// Trap cause: code of highest-priority exception
ex_trap_cause = ex_exc_type != NO_EXCEPTION ? trap_cause_decode(ex_exc_type) :
                de_active_exc_type != NO_EXCEPTION ? trap_cause_decode(de_active_exc_type) :
                fe_active_exc_type != NO_EXCEPTION ? trap_cause_decode(fe_active_exc_type) : 
                trap_cause_decode(ex_exc_type);

// Trap MEPC: PC of faulting instruction
ex_trap_mepc = ex_exc_type != NO_EXCEPTION ? pipe2.pc :
               de_active_exc_type != NO_EXCEPTION ? pipe1.pc :
               fe_active_exc_type != NO_EXCEPTION ? fe_pc : 
               pipe2.pc;
```

### Trap value (mtval)

```systemverilog
always_comb begin
    // Execute stage exceptions
    if (ex_exc_type != NO_EXCEPTION) begin
        unique case (ex_exc_type)
            ILLEGAL_INSTRUCTION: trap_tval = '0;  // Spike match: 0
            LOAD_MISALIGNED,
            STORE_MISALIGNED:    trap_tval = ex_alu_result;  // Faulting address
            default:             trap_tval = '0;
        endcase
    end
    // Decode stage exceptions
    else if (de_active_exc_type != NO_EXCEPTION) begin
        unique case (de_active_exc_type)
            ILLEGAL_INSTRUCTION: trap_tval = '0;
            INSTR_MISALIGNED:    trap_tval = pipe1.pc;  // Faulting PC
            default:             trap_tval = '0;
        endcase
    end
    // Fetch stage exceptions
    else if (fe_active_exc_type != NO_EXCEPTION) begin
        unique case (fe_active_exc_type)
            INSTR_MISALIGNED:    trap_tval = fe_pc;
            ILLEGAL_INSTRUCTION: trap_tval = '0;
            default:             trap_tval = '0;
        endcase
    end
end
```

### Exception flow diagram

```
┌────────────────────────────────────────────────────────────────────────────────┐
│                          EXCEPTION FLOW DIAGRAM                                │
├────────────────────────────────────────────────────────────────────────────────┤
│                                                                                │
│     Fetch          Decode         Execute        Memory         Writeback     │
│       │               │               │             │               │         │
│       ▼               ▼               ▼             ▼               ▼         │
│   ┌───────┐       ┌───────┐       ┌───────┐     ┌───────┐       ┌───────┐    │
│   │ fe_exc│──────▶│de_exc │──────▶│ex_exc │     │       │       │       │    │
│   │ _type │       │_type  │       │_type  │     │       │       │       │    │
│   └───────┘       └───────┘       └───────┘     └───────┘       └───────┘    │
│       │               │               │                                       │
│       └───────────────┴───────────────┘                                       │
│                       │                                                        │
│                       ▼                                                        │
│               ┌───────────────┐                                                │
│               │ Priority Mux  │                                                │
│               │ EX > DE > FE  │                                                │
│               └───────┬───────┘                                                │
│                       │                                                        │
│                       ▼                                                        │
│               ┌───────────────┐                                                │
│               │  CSR Update   │                                                │
│               │ mcause, mepc  │                                                │
│               │ mtval, mstatus│                                                │
│               └───────┬───────┘                                                │
│                       │                                                        │
│                       ▼                                                        │
│               ┌───────────────┐                                                │
│               │  PC ← mtvec   │                                                │
│               │  Flush pipe   │                                                │
│               └───────────────┘                                                │
│                                                                                │
└────────────────────────────────────────────────────────────────────────────────┘
```

---

## Branch Prediction Feedback

### Speculation hit/miss detection

```systemverilog
always_comb begin
    // Check whether branch is taken
    if (ex_pc_sel) begin
        // Branch/jump taken: is prediction and target correct?
        ex_spec_hit = pipe2.spec.taken && (ex_pc_target == pipe2.spec.pc);
    end else begin
        // Branch not taken: is not-taken prediction correct?
        ex_spec_hit = !pipe2.spec.taken;
    end
end
```

### Misprediction recovery

```systemverilog
always_comb begin
    if (!ex_spec_hit) begin
        // Misprediction: determine correct target
        if (ex_pc_sel)
            ex_pc_target_last = ex_pc_target;    // Should have been taken
        else
            ex_pc_target_last = pipe2.pc_incr;   // Should not have been taken
    end else begin
        ex_pc_target_last = ex_pc_target;
    end
end
```

### Pipeline feedback structures

```systemverilog
// Decode → Fetch feedback
typedef struct packed {
    predict_info_t spec;    // Branch prediction info
    logic          bjtype;  // Branch/jump instruction?
    logic [XLEN-1:0] pc;    // Instruction PC
} pipe_info_t;

// Execute → Fetch feedback
always_comb begin
    ex_info.spec   = pipe2.spec;
    ex_info.bjtype = is_branch(pipe2.instr_type);
    ex_info.pc     = pipe2.pc;
end
```

### Branch resolution timing

```
Cycle:     1      2      3      4      5      6
         ┌──────┬──────┬──────┬──────┐
Branch:  │  IF  │  DE  │  EX  │  MEM │
         │      │      │(resolve)    │
         └──────┴──────┴──────┴──────┘
                        │
                        ▼
         ┌──────────────────────┐
         │ spec_hit computation │
         │ Mispred: flush IF/DE │
         │ Correct: continue    │
         └──────────────────────┘

Misprediction penalty: 2 cycles (IF + DE flush)
```

---

## Memory Arbiter

### Memory arbiter connections

```systemverilog
memory_arbiter i_memory_arbiter (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),
    .icache_req_i(lx_ireq),     // I-Cache request
    .dcache_req_i(lx_dreq),     // D-Cache request
    .icache_res_o(fe_lx_ires),  // I-Cache response
    .dcache_res_o(lx_dres),     // D-Cache response
    .iomem_res_i (iomem_res_i), // External memory response
    .iomem_req_o (iomem_req_o)  // External memory request
);
```

### Arbitration logic

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                           MEMORY ARBITER                                     │
├──────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│   ┌─────────────┐                                    ┌─────────────┐        │
│   │  I-Cache    │──────┐                      ┌──────│   I-Cache   │        │
│   │  Request    │      │                      │      │   Response  │        │
│   └─────────────┘      │                      │      └─────────────┘        │
│                        │    ┌───────────┐     │                              │
│                        ├───▶│  ARBITER  │─────┤                              │
│                        │    │           │     │                              │
│   ┌─────────────┐      │    │  D > I    │     │      ┌─────────────┐        │
│   │  D-Cache    │──────┘    │ Priority  │     └──────│   D-Cache   │        │
│   │  Request    │           └─────┬─────┘            │   Response  │        │
│   └─────────────┘                 │                  └─────────────┘        │
│                                   │                                          │
│                                   ▼                                          │
│                          ┌───────────────┐                                   │
│                          │   Wishbone    │                                   │
│                          │     Bus       │                                   │
│                          └───────────────┘                                   │
│                                                                              │
│   Priority: D-Cache > I-Cache (minimize data hazards)                        │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## Hardware Interrupts

### Interrupt types

| Interrupt | Source | CSR bit | Description |
|-----------|--------|---------|-------------|
| Timer (MTIP) | CLINT | mip[7] | Timer interrupt |
| Software (MSIP) | CLINT | mip[3] | Software interrupt |
| External (MEIP) | PLIC | mip[11] | External device interrupt |

### Interrupt handling flow

```systemverilog
// Interrupts are delivered to the execute stage
execution i_execution (
    // ...
    .timer_irq_i  (timer_irq_i),   // CLINT timer
    .sw_irq_i     (sw_irq_i),      // CLINT software
    .ext_irq_i    (ext_irq_i),     // PLIC external
    // ...
);
```

### Interrupt priority

```
Interrupt priority (high to low):
1. External interrupt (MEIP) — PLIC
2. Timer interrupt (MTIP)    — CLINT
3. Software interrupt (MSIP) — CLINT
4. Synchronous exceptions

Note: Interrupts depend on mie (machine interrupt enable) and
      mstatus.MIE bits.
```

---

## Timing Diagrams

### Normal operation flow

```
clk_i    ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

         ┌─────────────────────────────────────────────────────
pipe1    │ I1        │ I2        │ I3        │ I4        │ I5
         └─────────────────────────────────────────────────────

         ┌─────────────────────────────────────────────────────
pipe2    │ --        │ I1        │ I2        │ I3        │ I4
         └─────────────────────────────────────────────────────

         ┌─────────────────────────────────────────────────────
pipe3    │ --        │ --        │ I1        │ I2        │ I3
         └─────────────────────────────────────────────────────

         ┌─────────────────────────────────────────────────────
pipe4    │ --        │ --        │ --        │ I1        │ I2
         └─────────────────────────────────────────────────────
```

### I-Cache Miss Stall

```
clk_i    ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

stall    ________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\__________
cause             IMISS_STALL (10 cycles)

         ┌─────────────────────────────────────────────────────
pipe1    │ I1    │ I1 (stall)│ I1 (stall)│ ...        │ I2
         └─────────────────────────────────────────────────────

         ┌─────────────────────────────────────────────────────
pipe2    │ --    │ nop       │ nop       │ ...        │ I1
         └─────────────────────────────────────────────────────
```

### Branch Misprediction Flush

```
clk_i    ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

Branch   ──────────────────────/‾‾‾‾\______________________________
Taken                           │EX  │

spec_hit ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\____/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

         ┌─────────────────────────────────────────────────────
pipe1    │ Br     │ X (wrong)│ Y (wrong)│ T1        │ T2
         └─────────────────────────────────────────────────────
                               ↑ flush    ↑ correct path

         ┌─────────────────────────────────────────────────────
pipe2    │ --     │ Br       │ nop      │ nop       │ T1
         └─────────────────────────────────────────────────────
                    ↑ resolve  ↑ flush

Misprediction penalty: 2 cycles
```

### Load-use hazard stall

```
clk_i    ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

LW x1    │ IF     │ DE       │ EX       │ MEM      │ WB
ADD x2,x1│        │ IF       │ IF(stall)│ DE       │ EX

stall    __________________/‾‾‾‾\______________________________
cause                       LOAD_RAW

         ┌─────────────────────────────────────────────────────
pipe1    │ LW     │ ADD      │ ADD(hold)│ I3       │ I4
         └─────────────────────────────────────────────────────

         ┌─────────────────────────────────────────────────────
pipe2    │ --     │ LW       │ bubble   │ ADD      │ I3
         └─────────────────────────────────────────────────────

Load-use penalty: 1 cycle (minimized with forwarding)
```

### Exception handling

```
clk_i    ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

Illegal  │ IF     │ DE       │ EX       │
Instr                        │(exc det) │

trap     ______________________________/‾‾‾‾\____________________
active

         ┌─────────────────────────────────────────────────────
pipe1    │ ILL    │ I2       │ I3       │ nop      │ handler
         └─────────────────────────────────────────────────────
                               ↑ flush    ↑ PC=mtvec

         ┌─────────────────────────────────────────────────────
pipe2    │ --     │ ILL      │ nop      │ nop      │ nop
         └─────────────────────────────────────────────────────
                    ↑ exc      ↑ flush

CSR Updates:
- mcause ← exception_code
- mepc   ← faulting_pc
- mtval  ← exception_info
- PC     ← mtvec
```

---

## Performance Analysis

### IPC (instructions per cycle)

| Case | IPC | Description |
|------|-----|-------------|
| Ideal | 1.0 | No stall or flush |
| Typical | 0.7–0.8 | Normal operation |
| Cache miss | 0.1–0.2 | Memory access latency |

### Stall penalties

| Stall type | Typical duration | Effect |
|------------|------------------|--------|
| I-Cache miss | ~10 cycles | IPC drop |
| D-Cache miss | ~10 cycles | Pipeline stall |
| Load-use hazard | 1 cycle | Minimal |
| MUL/DIV | 1–32 cycles | Operation-dependent |
| Branch mispred | 2 cycles | Pipeline flush |

### Optimization strategies

1. **Branch prediction accuracy**
   - GSHARE + BTB + RAS combination
   - Target: >90% accuracy

2. **Cache hit rate**
   - 8-way set associative
   - 8 KB capacity
   - Target: >95% hit rate

3. **Data forwarding**
   - MEM→EX forwarding
   - WB→EX forwarding
   - WB→DE forwarding

4. **Instruction fetch bandwidth**
   - Compressed instruction support
   - Alignment buffer

---

## Verification and Test

### Assertions

```systemverilog
// Pipeline consistency check
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (stall_cause == NO_STALL) |-> 
    (pipe1 != $past(pipe1) || de_flush_en)
) else $error("Pipeline should advance when not stalled");

// Exception priority check
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (ex_exc_type != NO_EXCEPTION && de_active_exc_type != NO_EXCEPTION) |->
    (priority_flush == 3)
) else $error("EX exception should have highest priority");

// Stall/flush mutual exclusion
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL}) |->
    (!de_flush_en && !ex_flush_en)
) else $error("Flush should be suppressed during cache stalls");
```

### Test scenarios

1. **Basic pipeline flow**
   - Back-to-back NOPs
   - Simple arithmetic
   - Register file R/W

2. **Hazard tests**
   - RAW hazard (data forwarding)
   - Load-use hazard (stall)
   - WAW hazard (in-order)

3. **Branch tests**
   - Conditional branch (taken/not-taken)
   - JAL/JALR
   - Misprediction recovery

4. **Exception tests**
   - Illegal instruction
   - Misaligned access
   - ECALL/EBREAK

5. **Interrupt tests**
   - Timer interrupt
   - External interrupt
   - Interrupt masking

6. **Cache tests**
   - I-Cache miss/hit
   - D-Cache miss/hit
   - FENCE.I

### Konata pipeline visualizer

```systemverilog
`ifdef KONATA_TRACER
    konata_logger i_konata_logger ();
`endif
```

The Konata trace format visualizes pipeline state:
- Instruction fetch, decode, execute, memory, writeback stages
- Stall and flush events
- Branch resolution

---

## Summary

The `cpu` module is the central coordination unit of the Level RISC-V processor. It:

1. Manages the **five-stage pipeline** (IF, DE, EX, MEM, WB)
2. Provides data flow through **pipeline registers** (pipe1–4)
3. Resolves data hazards with the **hazard unit**
4. Handles cache misses and other delays with **stall logic**
5. Handles branch mispredictions and exceptions with **flush logic**
6. **Exception handling** captures and processes fault conditions
7. **Memory arbiter** arbitrates between I-Cache and D-Cache
8. **Interrupt support** handles timer, software, and external interrupts

This design balances simplicity and performance and suits both learning and real-world RISC-V core applications.
