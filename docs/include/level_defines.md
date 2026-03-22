# Level Defines - Technical Documentation

## Contents

1. [Overview](#overview)
2. [Feature Flags](#feature-flags)
3. [Multiplier Implementations](#multiplier-implementations)
4. [Trace and Log Controls](#trace-and-log-controls)
5. [Simulation Controls](#simulation-controls)
6. [Makefile Integration](#makefile-integration)
7. [Usage Examples](#usage-examples)

---

## Overview

### Purpose

The `level_defines.svh` file provides **compile-time configuration** for the Level RISC-V core. This header provides central definitions for feature flags, multiplier selection, and trace controls.

### File Location

```
rtl/include/level_defines.svh
```

### Include Method

```systemverilog
`include "level_defines.svh"
```

---

## Feature Flags

### Multiplier Selection

Only one multiplier implementation may be active at a time:

```systemverilog
//------------------------------------------------------------------------------
// MULTIPLIER IMPLEMENTATION SELECTION
// Enable only ONE of the following multiplier implementations
//------------------------------------------------------------------------------

// Single-cycle Wallace tree multiplier (default - best performance)
`define FEAT_WALLACE_SINGLE

// Multi-cycle Wallace tree multiplier (area optimized)
//`define FEAT_WALLACE_MULTI

// DSP block multiplier (FPGA optimized)
//`define FEAT_DSP_MUL
```

### Multiplier Comparison

| Implementation | Latency | Throughput | Area | Use case |
|----------------|---------|------------|------|----------|
| WALLACE_SINGLE | 1 cycle | 1/cycle | High | Performance |
| WALLACE_MULTI | N cycle | 1/N cycle | Low | Area opt. |
| DSP_MUL | 1-3 cycle | 1/cycle | DSP | FPGA |

---

## Multiplier Implementations

### Wallace Single (Default)

```systemverilog
`define FEAT_WALLACE_SINGLE

// Usage
`ifdef FEAT_WALLACE_SINGLE
    // Single-cycle 32x32 Wallace tree
    wallace_mul_single u_mul (
        .i_a    (operand_a),
        .i_b    (operand_b),
        .o_prod (product)
    );
`endif
```

**Features:**
- 32x32 multiply in one cycle
- 64-bit result
- High area usage
- Long critical path

### Wallace Multi

```systemverilog
//`define FEAT_WALLACE_MULTI

// Usage
`ifdef FEAT_WALLACE_MULTI
    // Multi-cycle radix-4 Booth multiplier
    wallace_mul_multi u_mul (
        .clk_i      (clk),
        .rst_ni     (rst_n),
        .i_start    (mul_start),
        .i_a        (operand_a),
        .i_b        (operand_b),
        .o_prod     (product),
        .o_done     (mul_done)
    );
`endif
```

**Features:**
- Multi-cycle multiply (4-16 cycles)
- Low area usage
- Requires pipeline stalls

### DSP Multiplier

```systemverilog
//`define FEAT_DSP_MUL

// Usage
`ifdef FEAT_DSP_MUL
    // FPGA DSP48 block multiplier
    dsp_mul u_mul (
        .clk_i  (clk),
        .i_a    (operand_a),
        .i_b    (operand_b),
        .o_prod (product)
    );
`endif
```

**Features:**
- Uses FPGA DSP block
- 1-3 cycle latency (pipeline)
- Low logic usage
- Vendor-specific

---

## Trace and Log Controls

### Trace Flags

These flags are normally **commented out** and **enabled via the makefile**:

```systemverilog
//------------------------------------------------------------------------------
// TRACE AND LOGGING CONTROLS
// These are typically enabled via makefile +define+ flags
//------------------------------------------------------------------------------

// `define COMMIT_TRACER     // Carry trace info in pipeline registers
// `define KONATA_TRACER     // Konata pipeline visualizer support
// `define LOG_COMMIT        // Spike-compatible commit trace
// `define LOG_RAM           // RAM initialization messages
// `define LOG_UART          // UART TX file logging
// `define LOG_BP            // Branch predictor statistics
// `define LOG_BP_VERBOSE    // Per-branch verbose logging
```

### Flag Descriptions

| Flag | Description | Output |
|------|----------|-------|
| `COMMIT_TRACER` | Carries trace info in pipeline registers | - |
| `KONATA_TRACER` | Konata pipeline visualizer support | `pipeline.log` |
| `LOG_COMMIT` | Spike-comparable commit trace | `commit.log` |
| `LOG_RAM` | RAM load messages | Console |
| `LOG_UART` | UART TX output logged to file | `uart.log` |
| `LOG_BP` | Branch predictor statistics | Console |
| `LOG_BP_VERBOSE` | Verbose log per branch | Console |

---

## Simulation Controls

### Simulation Flags

```systemverilog
//------------------------------------------------------------------------------
// SIMULATION CONTROLS
// Enabled via makefile for simulation modes
//------------------------------------------------------------------------------

// `define SIM_FAST           // Disable all logging for speed
// `define SIM_UART_MONITOR   // UART monitoring + auto-stop
// `define SIM_COVERAGE       // Enable coverage collection
```

### SIM_FAST Mode

```systemverilog
`ifdef SIM_FAST
    // All logs disabled
    // Maximum simulation speed
`else
    // Normal debug modunda
    `ifdef LOG_COMMIT
        // Commit trace aktif
    `endif
`endif
```

### SIM_UART_MONITOR

```systemverilog
`ifdef SIM_UART_MONITOR
    // Monitor UART output
    // Stop simulation when PASS or FAIL is seen
    // Detect benchmark results
`endif
```

---

## Makefile Integration

### Passing Verilator Defines

```makefile
# Trace kontrolleri
LOG_COMMIT ?= 0
LOG_PIPELINE ?= 0
LOG_RAM ?= 0
LOG_UART ?= 0
LOG_BP ?= 0
LOG_BP_VERBOSE ?= 0
KONATA_TRACER ?= 0

# Pass defines to Verilator
VFLAGS_DEFINES :=
ifeq ($(LOG_COMMIT),1)
    VFLAGS_DEFINES += +define+LOG_COMMIT
endif
ifeq ($(KONATA_TRACER),1)
    VFLAGS_DEFINES += +define+KONATA_TRACER +define+COMMIT_TRACER
endif
# ... other flags
```

### Usage Examples

```bash
# Sadece commit trace
make run T=rv32ui-p-add LOG_COMMIT=1

# Pipeline visualizer
make run T=rv32ui-p-add KONATA_TRACER=1 LOG_PIPELINE=1

# Branch predictor stats
make run_coremark LOG_BP=1 SIM_UART_MONITOR=1

# Fast simulation
make run T=coremark SIM_FAST=1

# All logs
make run T=test LOG_COMMIT=1 LOG_RAM=1 LOG_UART=1 LOG_BP=1
```

---

## Usage Examples

### Conditional Compilation

```systemverilog
module example
  import level_param::*;
(
    input logic clk_i,
    // ...
);

`ifdef FEAT_WALLACE_SINGLE
    // Single-cycle multiplier
    assign mul_done = 1'b1;  // Always ready
`elsif FEAT_WALLACE_MULTI
    // Multi-cycle multiplier
    logic mul_busy;
    // ...
`endif

`ifdef LOG_COMMIT
    always_ff @(posedge clk_i) begin
        if (commit_valid) begin
            $display("core   0: 0x%08x (0x%08x) x%0d 0x%08x",
                     commit_pc, commit_instr, commit_rd, commit_data);
        end
    end
`endif

endmodule
```

### Guard Pattern

```systemverilog
`ifndef LEVEL_DEFINES_SVH
`define LEVEL_DEFINES_SVH

// Define contents

`endif // LEVEL_DEFINES_SVH
```

### Cross-Module Dependency

```systemverilog
// KONATA_TRACER aktifse, COMMIT_TRACER da gerekli
`ifdef KONATA_TRACER
    `ifndef COMMIT_TRACER
        `define COMMIT_TRACER
    `endif
`endif
```

---

## Flag Dependencies

### Relationship Diagram

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          FLAG DEPENDENCIES                                       │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   KONATA_TRACER ──────────────────────► COMMIT_TRACER                           │
│        │                                     │                                   │
│        │                                     ▼                                   │
│        │                              Pipeline registers                         │
│        │                              carry trace info                           │
│        │                                                                         │
│        ▼                                                                         │
│   LOG_PIPELINE ─────────────────────► pipeline.log output                       │
│                                                                                  │
│                                                                                  │
│   LOG_COMMIT ───────────────────────► commit.log output                         │
│        │                                     │                                   │
│        │                                     ▼                                   │
│        │                              Spike comparison                           │
│        │                                                                         │
│                                                                                  │
│   SIM_FAST ─────────────────────────► Disables all LOG_*                        │
│                                                                                  │
│                                                                                  │
│   LOG_BP_VERBOSE ───────────────────► LOG_BP                                    │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Implicit Dependencies

| Flag | Requires |
|------|----------|
| `KONATA_TRACER` | `COMMIT_TRACER` (auto-enabled) |
| `LOG_BP_VERBOSE` | `LOG_BP` (implied) |
| `SIM_FAST` | Disables all `LOG_*` flags |

---

## Best Practices

### 1. Multiplier Selection

```systemverilog
// Only one multiplier implementation should be active
`define FEAT_WALLACE_SINGLE
//`define FEAT_WALLACE_MULTI  // Comment out
//`define FEAT_DSP_MUL        // Comment out
```

### 2. Trace Logs

```systemverilog
// Normalde comment halinde
// Enable via Makefile
//`define LOG_COMMIT

// Makefile:
// make run T=test LOG_COMMIT=1
```

### 3. Debug vs Release

```bash
# Debug build (default)
make run T=test MODE=debug

# Release build (minimal logging)
make run T=coremark MODE=release SIM_FAST=1

# Test mode (assertions enabled)
make isa MODE=test
```

---

## Summary

The `level_defines.svh` file:

1. **Feature Selection**: Multiplier implementasyonu
2. **Trace Control**: Commit, pipeline, UART logging
3. **Simulation Modes**: Fast, coverage, UART monitor
4. **Makefile Integration**: Runtime define passing
5. **Conditional Compilation**: `ifdef/endif` pattern

This header file supports different configurations of the Level RISC-V core.
