# Single-Port Block RAM Module — Technical Documentation

## Table of Contents

1. [General Overview](#general-overview)
2. [Module Interface](#module-interface)
3. [Write-First Mode](#write-first-mode)
4. [FPGA Synthesis](#fpga-synthesis)
5. [Usage Examples](#usage-examples)

---

## General Overview

### Purpose

The `sp_bram` module is a single-port Block RAM template operating in **Write-First** mode. It is optimized for efficient BRAM inference on Xilinx FPGAs.

### File Location

```
rtl/ram/sp_bram.sv
```

### Key Features

| Feature | Value |
|---------|-------|
| **Port Count** | 1 (single-port) |
| **Write Mode** | Write-First |
| **Parametric** | Width and depth |
| **FPGA-friendly** | Xilinx BRAM inference |

---

## Module Interface

### Port Definitions

```systemverilog
module sp_bram #(
    parameter DATA_WIDTH = 32,   // Data width
    parameter NUM_SETS   = 1024  // Number of sets (depth)
) (
    input  logic                        clk,      // Clock
    input  logic                        chip_en,  // Chip enable
    input  logic [$clog2(NUM_SETS)-1:0] addr,     // Address
    input  logic                        wr_en,    // Write enable
    input  logic [      DATA_WIDTH-1:0] wr_data,  // Write data
    output logic [      DATA_WIDTH-1:0] rd_data   // Read data
);
```

### Parameter Table

| Parameter | Default | Description |
|-----------|---------|-------------|
| `DATA_WIDTH` | 32 | Data bus width (bits) |
| `NUM_SETS` | 1024 | Memory depth (rows) |

---

## Write-First Mode

### Behavior

In Write-First mode, during a write the new data is written to memory and also driven on the read port:

```systemverilog
always @(posedge clk) begin
    if (chip_en) begin
        if (wr_en) begin
            bram[addr] <= wr_data;   // Write to memory
            rd_data    <= wr_data;   // Drive new data on output
        end else begin
            rd_data <= bram[addr];   // Normal read
        end
    end
end
```

### Timing Diagram

```
clk      ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

chip_en  ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────

addr     ────┤ A1 ├────┤ A2 ├──────────────

wr_en    ────/‾‾‾‾\────────────────────────
              WRITE      READ

wr_data  ────┤ D1 ├────────────────────────

rd_data  ──────────┤ D1 ├────┤bram[A2]├────
                   (write-   (normal
                    first)    read)
```

### Write Mode Comparison

| Mode | rd_data During Write | Use Case |
|-----|----------------------|----------|
| **Write-First** | New data (wr_data) | Read-after-write same cycle |
| Read-First | Old data | When old value is required |
| No-Change | Unchanged | Power optimization |

---

## FPGA Synthesis

### Xilinx BRAM Inference

This template is automatically inferred as BRAM by Xilinx Vivado:

```
Inference conditions:
✓ Synchronous read (registered output)
✓ Single clock domain
✓ Gated with chip_en
✓ Write-first pattern
```

### Resource Usage

| Configuration | BRAM18K | BRAM36K |
|---------------|---------|---------|
| 32x1024 | 1 | 0.5 |
| 32x2048 | 2 | 1 |
| 32x4096 | 4 | 2 |
| 128x1024 | 4 | 2 |

---

## Usage Examples

### Cache Data Array

```systemverilog
sp_bram #(
    .DATA_WIDTH(128),    // Cache line width
    .NUM_SETS  (64)      // 64 sets
) u_cache_data (
    .clk    (clk_i),
    .chip_en(1'b1),
    .addr   (set_index),
    .wr_en  (cache_write),
    .wr_data(write_line),
    .rd_data(read_line)
);
```

### Register File

```systemverilog
sp_bram #(
    .DATA_WIDTH(32),
    .NUM_SETS  (32)
) u_regfile (
    .clk    (clk_i),
    .chip_en(1'b1),
    .addr   (reg_addr),
    .wr_en  (rf_we),
    .wr_data(rf_wdata),
    .rd_data(rf_rdata)
);
```

---

## Summary

The `sp_bram` module:

1. **Write-First**: New data on the output during write
2. **Parametric**: Configurable width and depth
3. **FPGA Optimized**: Xilinx BRAM inference
4. **Single-Port**: Simple interface

It serves as a basic memory block for structures such as caches and register files.

---

## See also

- [Dual-port BRAM (`dp_bram`)](dp_bram_module.md) — true dual-port write-first template used by the L2 and similar structures.
