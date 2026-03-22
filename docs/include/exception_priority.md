# Exception Priority - Technical Documentation

## Contents

1. [Overview](#overview)
2. [RISC-V Exception Model](#risc-v-exception-model)
3. [Priority Configuration](#priority-configuration)
4. [Exception Types](#exception-types)
5. [Trap Handling](#trap-handling)
6. [Pipeline Integration](#pipeline-integration)
7. [Usage Examples](#usage-examples)

---

## Overview

### Purpose

The `exception_priority.svh` file defines the **priority order** of RISC-V exceptions and selects which exception is handled when multiple exceptions occur in the same cycle.

### File Location

```
rtl/include/exception_priority.svh
```

### Basic Concept

```
Multiple exceptions can occur at the same time:
- Instruction page fault (fetch)
- Illegal instruction (decode)
- Load/Store fault (memory)

The exception with the lowest priority number is taken first.
```

---

## RISC-V Exception Model

### Exception vs Interrupt

| Type | Property | Example |
|-----|---------|-------|
| **Exception** | Synchronous, instruction-related | Illegal instruction |
| **Interrupt** | Asynchronous, external | Timer interrupt |

### Exception Classes

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                         EXCEPTION CLASSIFICATION                                 │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                          INSTRUCTION EXCEPTIONS                          │   │
│   │                                                                          │   │
│   │   • Instruction Address Misaligned                                       │   │
│   │   • Instruction Access Fault                                             │   │
│   │   • Illegal Instruction                                                  │   │
│   │   • Breakpoint                                                           │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                            LOAD EXCEPTIONS                               │   │
│   │                                                                          │   │
│   │   • Load Address Misaligned                                              │   │
│   │   • Load Access Fault                                                    │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                           STORE EXCEPTIONS                               │   │
│   │                                                                          │   │
│   │   • Store/AMO Address Misaligned                                         │   │
│   │   • Store/AMO Access Fault                                               │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                         ENVIRONMENT CALLS                                │   │
│   │                                                                          │   │
│   │   • Environment Call from U-mode                                         │   │
│   │   • Environment Call from S-mode                                         │   │
│   │   • Environment Call from M-mode                                         │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Priority Configuration

### RISC-V Standard Priority

The RISC-V specification defines exception priorities:

```systemverilog
// exception_priority.svh

`ifndef EXCEPTION_PRIORITY_SVH
`define EXCEPTION_PRIORITY_SVH

//------------------------------------------------------------------------------
// EXCEPTION PRIORITY CONFIGURATION
// Lower number = Higher priority
// Based on RISC-V Privileged Specification
//------------------------------------------------------------------------------

// Instruction Exceptions (highest priority for same instruction)
localparam int PRIORITY_INSTR_ADDR_MISALIGNED = 0;
localparam int PRIORITY_INSTR_ACCESS_FAULT    = 1;
localparam int PRIORITY_ILLEGAL_INSTR         = 2;
localparam int PRIORITY_BREAKPOINT            = 3;

// Load Exceptions
localparam int PRIORITY_LOAD_ADDR_MISALIGNED  = 4;
localparam int PRIORITY_LOAD_ACCESS_FAULT     = 5;

// Store Exceptions
localparam int PRIORITY_STORE_ADDR_MISALIGNED = 6;
localparam int PRIORITY_STORE_ACCESS_FAULT    = 7;

// Environment Calls (lowest priority)
localparam int PRIORITY_ECALL_U               = 8;
localparam int PRIORITY_ECALL_S               = 9;
localparam int PRIORITY_ECALL_M               = 10;

`endif // EXCEPTION_PRIORITY_SVH
```

### Priority Table

| Priority | Exception | Code | Description |
|----------|-----------|------|----------|
| 0 | Instruction Address Misaligned | 0 | Highest priority |
| 1 | Instruction Access Fault | 1 | I-Cache/Bus fault |
| 2 | Illegal Instruction | 2 | Invalid opcode |
| 3 | Breakpoint | 3 | EBREAK instruction |
| 4 | Load Address Misaligned | 4 | Unaligned load |
| 5 | Load Access Fault | 5 | D-Cache/Bus fault |
| 6 | Store Address Misaligned | 6 | Unaligned store |
| 7 | Store Access Fault | 7 | D-Cache/Bus fault |
| 8 | Environment Call U-mode | 8 | ECALL from User |
| 9 | Environment Call S-mode | 9 | ECALL from Supervisor |
| 10 | Environment Call M-mode | 11 | ECALL from Machine |

---

## Exception Types

### Instruction Address Misaligned

```systemverilog
// Fetch stage'de kontrol
// Compressed (RV32C) may be 2-byte aligned
// Standard instructions must be 4-byte aligned

logic instr_addr_misaligned;

`ifdef RV32C_ENABLED
    assign instr_addr_misaligned = pc[0];  // Bit 0 must be 0
`else
    assign instr_addr_misaligned = |pc[1:0];  // Bits 1:0 must be 0
`endif
```

### Instruction Access Fault

```systemverilog
// I-Cache miss + bus error
// PMA non-executable region
// PMP execute violation

logic instr_access_fault;

assign instr_access_fault = icache_error || 
                            pma_exec_fault || 
                            pmp_exec_fault;
```

### Illegal Instruction

```systemverilog
// Decode stage'de kontrol
// - Invalid opcode
// - Invalid funct3/funct7
// - CSR access violation

logic illegal_instr;

assign illegal_instr = !valid_opcode || 
                       invalid_funct || 
                       csr_access_fault;
```

### Load/Store Misaligned

```systemverilog
// Memory stage'de kontrol
// LW/SW: 4-byte aligned
// LH/SH: 2-byte aligned
// LB/SB: no alignment requirement

logic addr_misaligned;

always_comb begin
    case (mem_size)
        MEM_SIZE_WORD: addr_misaligned = |addr[1:0];
        MEM_SIZE_HALF: addr_misaligned = addr[0];
        MEM_SIZE_BYTE: addr_misaligned = 1'b0;
        default:       addr_misaligned = 1'b1;
    endcase
end
```

### Load/Store Access Fault

```systemverilog
// D-Cache miss + bus error
// PMA read/write violation
// PMP read/write violation

logic load_access_fault;
logic store_access_fault;

assign load_access_fault  = dcache_error && is_load;
assign store_access_fault = dcache_error && is_store;
```

---

## Trap Handling

### Exception Priority Resolver

```systemverilog
// If multiple exceptions occur in the same cycle
// Select the highest-priority one

function automatic logic [3:0] resolve_exception_priority(
    input logic instr_addr_mis,
    input logic instr_access,
    input logic illegal,
    input logic breakpoint,
    input logic load_mis,
    input logic load_access,
    input logic store_mis,
    input logic store_access,
    input logic ecall
);
    // Priority order (low number = high priority)
    if (instr_addr_mis) return 4'd0;  // Instruction address misaligned
    if (instr_access)   return 4'd1;  // Instruction access fault
    if (illegal)        return 4'd2;  // Illegal instruction
    if (breakpoint)     return 4'd3;  // Breakpoint
    if (load_mis)       return 4'd4;  // Load address misaligned
    if (load_access)    return 4'd5;  // Load access fault
    if (store_mis)      return 4'd6;  // Store address misaligned
    if (store_access)   return 4'd7;  // Store access fault
    if (ecall)          return 4'd11; // Environment call M-mode
    return 4'd15;                     // No exception
endfunction
```

### Trap Entry

```systemverilog
// When an exception occurs
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        mepc   <= '0;
        mcause <= '0;
        mtval  <= '0;
    end else if (exception_valid) begin
        // Save PC
        mepc <= exception_pc;

        // Save cause (exception code)
        mcause <= {1'b0, 27'b0, exception_code};

        // Save trap value
        case (exception_code)
            EXC_INSTR_ADDR_MIS:  mtval <= exception_pc;
            EXC_INSTR_ACC_FAULT: mtval <= exception_pc;
            EXC_ILLEGAL_INSTR:   mtval <= exception_instr;
            EXC_LOAD_ADDR_MIS:   mtval <= exception_addr;
            EXC_LOAD_ACC_FAULT:  mtval <= exception_addr;
            EXC_STORE_ADDR_MIS:  mtval <= exception_addr;
            EXC_STORE_ACC_FAULT: mtval <= exception_addr;
            default:             mtval <= '0;
        endcase
    end
end
```

---

## Pipeline Integration

### Exception Propagation

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                        EXCEPTION FLOW IN PIPELINE                                │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   FETCH ─────► DECODE ─────► EXECUTE ─────► MEMORY ─────► WRITEBACK             │
│     │            │              │             │              │                   │
│     │            │              │             │              │                   │
│     ▼            ▼              ▼             ▼              ▼                   │
│  ┌──────┐    ┌──────┐      ┌──────┐      ┌──────┐      ┌──────┐                 │
│  │Instr │    │Illegal│     │ (none│      │Load/ │      │      │                 │
│  │Addr  │    │Instr │      │ usually)    │Store │      │Commit│                 │
│  │Fault │    │Break │      │      │      │Fault │      │      │                 │
│  └──────┘    └──────┘      └──────┘      └──────┘      └──────┘                 │
│     │            │              │             │              │                   │
│     │            │              │             │              │                   │
│     └────────────┴──────────────┴─────────────┴──────────────┘                   │
│                                  │                                               │
│                                  ▼                                               │
│                          ┌─────────────┐                                        │
│                          │  EXCEPTION  │                                        │
│                          │  RESOLVER   │                                        │
│                          └──────┬──────┘                                        │
│                                 │                                               │
│                                 ▼                                               │
│                          ┌─────────────┐                                        │
│                          │ TRAP ENTRY  │                                        │
│                          │ (CSR write) │                                        │
│                          └──────┬──────┘                                        │
│                                 │                                               │
│                                 ▼                                               │
│                          ┌─────────────┐                                        │
│                          │ FLUSH PIPE  │                                        │
│                          │ Jump mtvec  │                                        │
│                          └─────────────┘                                        │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Exception Register

Exception information is carried between pipeline stages:

```systemverilog
typedef struct packed {
    logic        valid;       // Exception aktif
    logic [3:0]  cause;       // Exception code
    logic [31:0] pc;          // Exception PC
    logic [31:0] tval;        // Trap value
} exception_t;

// Pipeline register
exception_t ex_exception_q, mem_exception_q;
```

### Precise Exception

RISC-V requires precise exceptions:

```systemverilog
// All instructions before the faulting instruction
// must have committed
// Sonrakiler flush edilmeli

always_comb begin
    if (exception_valid) begin
        // Flush younger instructions
        flush_if = 1'b1;
        flush_id = 1'b1;
        flush_ex = 1'b1;

        // Exception instruction commit edilmez
        mem_commit = 1'b0;
    end
end
```

---

## Usage Examples

### Exception Handler

```systemverilog
module exception_handler
  import level_param::*;
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // Exception inputs from pipeline
    input  logic        i_fetch_fault,
    input  logic        i_illegal_instr,
    input  logic        i_load_fault,
    input  logic        i_store_fault,
    input  logic [31:0] i_pc,
    input  logic [31:0] i_addr,
    input  logic [31:0] i_instr,

    // Exception output
    output logic        o_exception,
    output logic [3:0]  o_cause,
    output logic [31:0] o_tval
);

`include "exception_priority.svh"

    // Priority-based exception selection
    always_comb begin
        o_exception = 1'b0;
        o_cause     = '0;
        o_tval      = '0;

        if (i_fetch_fault) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_INSTR_ACCESS_FAULT[3:0];
            o_tval      = i_pc;
        end else if (i_illegal_instr) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_ILLEGAL_INSTR[3:0];
            o_tval      = i_instr;
        end else if (i_load_fault) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_LOAD_ACCESS_FAULT[3:0];
            o_tval      = i_addr;
        end else if (i_store_fault) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_STORE_ACCESS_FAULT[3:0];
            o_tval      = i_addr;
        end
    end

endmodule
```

### Test Code

```c
// Exception test (C code)

void test_illegal_instruction() {
    // Illegal instruction - should trap
    asm volatile(".word 0x00000000");
}

void test_load_misaligned() {
    volatile int* ptr = (int*)0x80000001;  // Misaligned
    int val = *ptr;  // Should trap
}

void test_store_access_fault() {
    volatile int* ptr = (int*)0x00000000;  // Invalid region
    *ptr = 0xDEADBEEF;  // Should trap
}
```

---

## Summary

The `exception_priority.svh` file:

1. **Priority Definition**: RISC-V exception priorities
2. **Exception Types**: 11 distinct exception types
3. **Trap Handling**: CSR registers (mepc, mcause, mtval)
4. **Precise exception**: Pipeline flush and recovery
5. **Configurable**: Customizable via parameters

This file forms the basis of the Level RISC-V core exception-handling mechanism.
