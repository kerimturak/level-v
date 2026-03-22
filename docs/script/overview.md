# Script Directory — Technical Documentation

## Contents

1. [Overview](#overview)
2. [Directory Layout](#directory-layout)
3. [Makefiles](#makefiles)
4. [Python Scripts](#python-scripts)
5. [Shell Scripts](#shell-scripts)
6. [Configuration Files](#configuration-files)

---

## Overview

### Purpose

The `script/` directory holds all automation scripts that drive **build**, **test**, **simulation**, and **verification** for the Level RISC-V project.

### Directory Location

```
/home/kerim/level-v/script/
```

### Key Features

- Unified root `makefile` (all sim / test / synth rules)
- JSON for simulators (`verilator.json`, `modelsim.json`); test profiles in `script/config/tests/*.conf` plus `parse_test_conf.sh`
- Python utility tools
- Shell automation scripts
- Multiple simulators (Verilator, ModelSim)

---

## Directory Layout

```
script/
├── README.md                    # Script documentation
├── config/                      # JSON configuration files
│   ├── modelsim.json           # ModelSim settings
│   ├── verilator.json          # Verilator settings (+ optional verilator.local.json, gitignored; see docs/script/config.md)
│   └── tests/                  # Test profiles (.conf)
│       ├── default.conf        # Base profile
│       ├── isa.conf            # ISA test settings
│       ├── README.md
│       ├── riscv-dv.json       # (special) RISC-V DV
│       └── formal.json         # (special) formal
│
├── makefiles/                   # Local makefile override directory
│   ├── README.md
│   └── config/                  # Optional local.mk (usually not in git)
│       └── .gitkeep
│
├── python/                      # Python utility scripts
│   ├── requirements.txt        # Python dependencies
│   ├── requirements-dev.txt    # Development dependencies
│   ├── elf_to_mem.py          # ELF → .mem converter
│   ├── gen_linker.py          # Linker script generator
│   ├── torture_gen.py         # Torture test generator
│   ├── simple_torture_gen.py  # Simple torture generator
│   ├── hex2mem_32to128.py     # HEX format converter
│   ├── get_static_hex.py      # Static hex extractor
│   ├── compare_bp_stats.py    # Branch predictor analysis
│   ├── slang_lint.py          # Slang linter wrapper
│   ├── riscv_dv_gen.py        # RISCV-DV generator
│   ├── riscv_dv_config.py     # RISCV-DV configuration
│   ├── download_pdfs.py       # PDF downloader utility
│   ├── multiply.py            # Multiplier test generator
│   ├── convert_dump_to_elf_hex.py  # Dump converter
│   ├── fpga/                  # FPGA tools
│   ├── makefile/              # Python helpers for Make
│   │   ├── isa_pipeline.py    # ISA test pipeline
│   │   ├── elf_to_mem.py      # ELF converter
│   │   ├── hex_to_mem.py      # HEX converter
│   │   ├── compare_logs.py    # Log comparison
│   │   ├── generate_test_dashboard.py  # Test dashboard
│   │   └── html_diff_generator.py      # HTML diff
│   └── tests/                 # Python test scripts
│
└── shell/                       # Shell scripts
    ├── parse_test_conf.sh      # Test .conf → Makefile fragment
    ├── build_level_custom_c_test.sh    # Custom C test → elf/mem + optional sim
    ├── scaffold_level_project_skeleton.sh # Empty Level directory tree
    ├── guide_level_uart_custom_test.sh    # UART C test flow (guide text to stdout)
    ├── run_level_exception_priority_tests.sh # Exception priority matrix
    ├── guide_exception_priority_parametric.sh  # Parametric priority summary
    └── …                       # OpenLane / setup helpers
```

---

## Makefiles

All build / simulation / test / synthesis / lint rules are **merged into the repository root `makefile`**.

- Internal sections are marked with comments like `# ====== config/paths.mk ======`; list them with `grep "# ======" makefile`.
- RTL file list: `rtl/flist.f` (as `SV_SOURCES` in the makefile).
- Optional local override: `script/makefiles/config/local.mk`.

Short guide: [makefiles.md](makefiles.md).

## Python Scripts

### elf_to_mem.py - ELF/Binary Converter

```python
"""
ELF/binary -> .mem converter for RAM initialization.
Generates one hex line per block (default 16 bytes / 128 bits).

Usage:
  ./elf_to_mem.py --in test.bin --out test.mem --addr 0x80000000 \
      --block-bytes 16 --word-size 4 --word-endian little
"""
```

**Parameters:**
- `--in`: Input binary file
- `--out`: Output .mem file
- `--addr`: Base address (default: 0x80000000)
- `--block-bytes`: Block size (default: 16)
- `--word-size`: Word size (default: 4)
- `--word-endian`: little/big
- `--word-order`: high-to-low/low-to-high

### gen_linker.py - Linker Script Generator

```python
"""
Linker Script Generator for Level-V
Generates a linker script from a YAML memory map.

Usage:
    python3 gen_linker.py memory_map.yaml output.ld
    python3 gen_linker.py memory_map.yaml output.ld --header output.h
"""
```

**Features:**
- YAML memory map parse
- Linker script generation
- C header generation
- Stack/heap size calculation

### torture_gen.py - Torture Test Generator

```python
"""
RISC-V Torture Test Generator for Level-V
Generates random but valid RISC-V instruction sequences.

Features:
- Configurable instruction mix
- RV32I, M, C extension support
- Memory-safe load/store generation
- Branch coverage optimization
- Deterministic via seed control
"""

# Usage
python3 torture_gen.py --seed 12345 --max-instructions 1000 \
    --march rv32imc --output torture_test.S
```

### compare_bp_stats.py - Branch Predictor Analysis

```python
"""
Branch predictor statistics comparison tool.
Analyzes performance across different configurations.
"""
```

### slang_lint.py - Slang Linter Wrapper

```python
"""
Slang (pyslang) linter wrapper.
Analyzes SystemVerilog files with Slang.
"""
```

### makefile/ Subdirectory

| Script | Description |
|--------|----------|
| `isa_pipeline.py` | ISA test import pipeline |
| `elf_to_mem.py` | ELF → MEM converter (makefile-oriented copy) |
| `hex_to_mem.py` | HEX → MEM converter |
| `compare_logs.py` | RTL/Spike log comparison |
| `generate_test_dashboard.py` | HTML test dashboard |
| `html_diff_generator.py` | HTML diff report |

---

## Shell Scripts

Simulation and most test flows go through the **root `makefile`**. Test profiles are merged by `script/shell/parse_test_conf.sh` from `script/config/tests/default.conf` plus `<TEST_CONFIG>.conf`, producing `build/.test_config_<name>.mk`.

### parse_test_conf.sh — Test profile parser

```bash
# List profiles
./script/shell/parse_test_conf.sh --list

# Makefile fragment (makefile invokes this indirectly)
./script/shell/parse_test_conf.sh isa --make
```

### build_level_custom_c_test.sh - Custom Test Builder

```bash
#!/bin/bash
# Custom UART Test Build and Run Script

# Usage:
#   ./build_level_custom_c_test.sh uart_hello_test

# Steps:
# 1. Source check
# 2. Compile with riscv32-unknown-elf-gcc
# 3. Generate .bin, .hex, .mem files
# 4. Create objdump
# 5. Optionally run simulation
```

### scaffold_level_project_skeleton.sh — Project init

```bash
#!/bin/bash
# Initializes Level project layout
# Creates required directories and template files
```

---

## Configuration Files

### verilator.json — Verilator configuration

```json
{
  "simulation": {
    "max_cycles": 100000,
    "timeout": 0,
    "threads": "auto",
    "seed": "auto"
  },

  "build": {
    "mode": "release",
    "jobs": "auto",
    "opt_level": "-O3",
    "cpp_standard": "c++17"
  },

  "trace": {
    "enabled": true,
    "format": "fst",
    "depth": 99,
    "structs": true
  },

  "coverage": {
    "enabled": true,
    "line": true,
    "toggle": true
  },

  "logging": {
    "fast_sim": false,
    "bp_log": false,
    "commit_trace": true,
    "pipeline_log": true
  },

  "profiles": {
    "fast": { ... },
    "debug": { ... },
    "coverage": { ... }
  }
}
```

### modelsim.json — ModelSim configuration

```json
{
  "compilation": {
    "sv_mode": "-sv",
    "mfcu": "-mfcu",
    "svinputport": "relaxed",
    "timescale": "1ns/1ps"
  },

  "simulation": {
    "time_resolution": "ns",
    "voptargs": "+acc=npr"
  },

  "lint": {
    "enabled": true,
    "mode": "default"
  }
}
```

### tests/ Subdirectory — Test profiles (`.conf`)

With `TEST_CONFIG=<name>`, `<name>.conf` is layered on top of `default.conf`. Details: [script/config/tests/README.md on GitHub](https://github.com/kerimturak/level-v/blob/main/script/config/tests/README.md).

| File (example) | Description |
|----------------|-------------|
| `default.conf` | Shared base |
| `isa.conf` | riscv-tests ISA |
| `arch.conf` | riscv-arch-test |
| `coremark.conf` | CoreMark |
| `riscv-dv.json` | RISCV-DV (JSON, separate flow) |
| `formal.json` | Formal (JSON, separate flow) |

---

## Usage Examples

### Running Tests

```bash
# Single test
make run T=rv32ui-p-add

# ISA test suite
make isa

# Architecture tests
make arch

# CoreMark benchmark
make run_coremark

# Custom test build and run
./script/shell/build_level_custom_c_test.sh my_test
```

### Simulation Options

```bash
# Verilator with trace
make run T=rv32ui-p-add TRACE=1 LOG_COMMIT=1

# Fast mode (no trace)
make run T=coremark SIM_FAST=1

# Branch predictor stats
make run T=dhrystone LOG_BP=1

# Pipeline visualization
make run T=rv32ui-p-add KONATA_TRACER=1 LOG_PIPELINE=1
```

### Build Modes

```bash
# Debug build
make verilate MODE=debug

# Release build (optimized)
make verilate MODE=release

# Test mode
make verilate MODE=test
```

### Linting and Analysis

```bash
# Verilator lint
make lint

# svlint
make svlint

# Slang lint
make slang_lint

# Yosys structural check
make yosys_check
```

---

## Summary

The `script/` directory provides:

1. **Modular Makefiles**: Organized, maintainable makefile layout (unified at repo root)
2. **JSON Config**: Simulator and test configuration
3. **Python Tools**: ELF/HEX conversion, test generation, analysis
4. **Shell Scripts**: Automation and runner scripts
5. **Multi-Simulator**: Verilator and ModelSim support
6. **Test Suites**: ISA, arch, imperas, CoreMark, Dhrystone, Embench
7. **Verification**: Lint, Yosys check, formal verification
