# Python Scripts — Technical Documentation

## Contents

1. [Overview](#overview)
2. [Converter Scripts](#converter-scripts)
3. [Generator Scripts](#generator-scripts)
4. [Analysis Scripts](#analysis-scripts)
5. [Makefile Helpers](#makefile-helpers)

---

## Overview

### Directory Layout

```
script/python/
├── requirements.txt        # Python dependencies
├── requirements-dev.txt    # Development dependencies
│
├── elf_to_mem.py          # ELF/binary → .mem converter
├── gen_linker.py          # Linker script generator
├── hex2mem_32to128.py     # HEX format converter
├── get_static_hex.py      # Static hex extractor
├── convert_dump_to_elf_hex.py  # Dump converter
│
├── torture_gen.py         # Torture test generator
├── simple_torture_gen.py  # Simple torture generator
├── multiply.py            # Multiplier test generator
├── riscv_dv_gen.py        # RISCV-DV generator
├── riscv_dv_config.py     # RISCV-DV configuration
│
├── compare_bp_stats.py    # Branch predictor analysis
├── slang_lint.py          # Slang linter wrapper
├── download_pdfs.py       # PDF downloader utility
│
├── fpga/                  # FPGA tools
│
├── makefile/              # Python helpers for Make
│   ├── isa_pipeline.py    # ISA test import pipeline
│   ├── arch_pipeline.py   # Arch test import pipeline
│   ├── elf_to_mem.py      # ELF → MEM converter
│   ├── hex_to_mem.py      # HEX → MEM converter
│   ├── compare_logs.py    # Log comparison
│   ├── generate_test_dashboard.py  # Test dashboard
│   └── html_diff_generator.py      # HTML diff
│
└── tests/                 # Python test scripts
```

### Dependencies

```txt
# requirements.txt
pyyaml>=6.0          # YAML parsing
pyelftools>=0.29     # ELF file parsing
```

```txt
# requirements-dev.txt
pyslang>=4.0         # SystemVerilog linting
pytest>=7.0          # Unit testing
black>=23.0          # Code formatting
```

---

## Converter Scripts

### elf_to_mem.py - ELF/Binary Converter

**File:** `script/python/elf_to_mem.py`

#### Purpose

Converts ELF or binary files to `.mem` format. Produces hex lines compatible with RAM initialization via `$readmemh`.

#### Usage

```bash
# Binary → .mem
riscv32-unknown-elf-objcopy -O binary test.elf test.bin
python3 elf_to_mem.py --in test.bin --out test.mem --addr 0x80000000

# Full options
python3 elf_to_mem.py \
    --in test.bin \
    --out test.mem \
    --addr 0x80000000 \
    --block-bytes 16 \
    --word-size 4 \
    --word-endian little \
    --word-order high-to-low
```

#### Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `--in` | (required) | Input binary file |
| `--out` | (required) | Output .mem file |
| `--addr` | 0x80000000 | Base address (informational) |
| `--block-bytes` | 16 | Bytes per .mem line (128-bit block) |
| `--word-size` | 4 | Word size in bytes |
| `--word-endian` | little | Byte order in word (little/big) |
| `--word-order` | high-to-low | Word print order in block |
| `--pad` | 0x00 | Pad byte value |

#### Output Format

```
# Input: 16 bytes = 4 words (32-bit each)
# Word 0: 0x12345678, Word 1: 0xABCDEF00, Word 2: 0x11223344, Word 3: 0x55667788

# high-to-low order (default):
5566778811223344abcdef0012345678

# low-to-high order:
12345678abcdef00112233445566778
```

#### Code Structure

```python
def main():
    # Read binary
    data = infile.read_bytes()
    
    # Pad to block boundary
    if len(data) % block_bytes != 0:
        pad_len = block_bytes - (len(data) % block_bytes)
        data = data + bytes([pad_byte]) * pad_len
    
    lines = []
    for i in range(0, len(data), block_bytes):
        block = data[i:i+block_bytes]
        words = []
        
        for w in range(words_per_block):
            wbytes = block[w*word_size:(w+1)*word_size]
            if word_endian == 'little':
                val = int.from_bytes(wbytes, 'little')
            else:
                val = int.from_bytes(wbytes, 'big')
            words.append(val)
        
        # Order words
        if word_order == 'high-to-low':
            ordered = list(reversed(words))
        else:
            ordered = words
        
        # Format line
        fmt = ''.join(f"{w:0{word_size*2}x}" for w in ordered)
        lines.append(fmt)
    
    # Write output
    with outfile.open('w') as f:
        for ln in lines:
            f.write(ln + '\n')
```

---

### gen_linker.py - Linker Script Generator

**File:** `script/python/gen_linker.py`

#### Purpose

Generates a GCC linker script and C header from a YAML memory map file.

#### Usage

```bash
# Basic usage
python3 gen_linker.py memory_map.yaml output.ld

# With C header
python3 gen_linker.py memory_map.yaml output.ld --header memory_map.h
```

#### Memory Map YAML Format

```yaml
# memory_map.yaml
processor:
  name: "Level-V"
  isa: "RV32IMC_Zicsr"

memory:
  rom:
    origin: 0x80000000
    length: "32K"
    type: "rx"
  ram:
    origin: 0x80008000
    length: "32K"
    type: "rwx"

stack:
  size: "4K"

heap:
  size: "0"

entry: "_start"
```

#### Generated Linker Script

```ld
/*
 * Auto-generated Linker Script for Level-V
 * ISA: RV32IMC_Zicsr
 * 
 * Memory Layout:
 *   ROM: 0x80000000 - 0x80007FFF (32K)
 *   RAM: 0x80008000 - 0x8000FFFF (32K)
 *   Stack: 4K
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
    ROM (rx)  : ORIGIN = 0x80000000, LENGTH = 32K
    RAM (rwx) : ORIGIN = 0x80008000, LENGTH = 32K
}

SECTIONS
{
    .text : { *(.text*) } > ROM
    .rodata : { *(.rodata*) } > ROM
    .data : { *(.data*) } > RAM AT> ROM
    .bss : { *(.bss*) } > RAM
    
    _stack_top = ORIGIN(RAM) + LENGTH(RAM);
}
```

#### Generated C Header

```c
/* Auto-generated memory map header */
#ifndef MEMORY_MAP_H
#define MEMORY_MAP_H

#define ROM_BASE    0x80000000
#define ROM_SIZE    0x00008000
#define RAM_BASE    0x80008000
#define RAM_SIZE    0x00008000
#define STACK_SIZE  0x00001000
#define STACK_TOP   0x80010000

#endif /* MEMORY_MAP_H */
```

---

### hex2mem_32to128.py - HEX Format Converter

**File:** `script/python/hex2mem_32to128.py`

#### Purpose

Converts 32-bit hex files to 128-bit block format.

#### Usage

```bash
python3 hex2mem_32to128.py input.hex output.mem
```

#### Conversion

```
# Input (32-bit per line):
12345678
ABCDEF00
11223344
55667788

# Output (128-bit per line, 4 words combined):
5566778811223344ABCDEF0012345678
```

---

## Generator Scripts

### torture_gen.py - Torture Test Generator

**File:** `script/python/torture_gen.py`

#### Purpose

Generates random but valid RISC-V instruction sequences for processor stress testing.

#### Usage

```bash
python3 torture_gen.py \
    --seed 12345 \
    --max-instructions 1000 \
    --march rv32imc \
    --output torture_test.S
```

#### Parameters

| Parameter | Default | Description |
|-----------|---------|----------|
| `--seed` | random | Random seed (deterministic results) |
| `--max-instructions` | 1000 | Maximum instruction count |
| `--march` | rv32imc | Target architecture |
| `--output` | stdout | Output file |

#### Instruction Mix Configuration

```python
@dataclass
class GeneratorConfig:
    seed: int
    max_instructions: int = 1000
    march: str = 'rv32imc'
    
    # Instruction mix weights (percentages)
    weight_r_type: int = 30      # ADD, SUB, AND, OR, XOR, etc.
    weight_i_type: int = 25      # ADDI, ANDI, ORI, etc.
    weight_shift: int = 10       # SLL, SRL, SRA
    weight_load: int = 10        # LW, LH, LB
    weight_store: int = 10       # SW, SH, SB
    weight_lui_auipc: int = 5    # LUI, AUIPC
    weight_compressed: int = 10  # C.ADDI, C.LW, etc.
    
    # Branch configuration
    branch_probability: float = 0.05
    max_branch_distance: int = 10
    
    # Memory configuration
    data_region_size: int = 256
```

#### Register Management

```python
class RegisterFile:
    def __init__(self):
        self.all_regs = [f'x{i}' for i in range(1, 32)]
        # Reserved: x2 (sp), x3 (gp), x10 (data pointer)
        self.reserved = ['x2', 'x3', 'x10']
        self.usable = [r for r in self.all_regs if r not in self.reserved]
    
    def random_src(self) -> str:
        return random.choice(self.usable)
    
    def random_dst(self) -> str:
        return random.choice(self.usable)
```

#### Generated Test Example

```asm
# Auto-generated torture test
# Seed: 12345, Instructions: 100, March: rv32imc

.section .text
.global _start
_start:
    # Initialize data pointer
    la x10, _data
    
    # Random instruction sequence
    addi x5, x0, 42
    add x6, x5, x5
    c.addi x7, 10
    lw x8, 0(x10)
    sw x6, 4(x10)
    ...

.section .data
_data:
    .word 0x12345678
    .word 0xABCDEF00
    ...
```

---

### riscv_dv_gen.py - RISCV-DV Generator

**File:** `script/python/riscv_dv_gen.py`

#### Purpose

Random test generation with the RISCV-DV framework for comprehensive verification.

#### Usage

```bash
python3 riscv_dv_gen.py \
    --test riscv_arithmetic_basic_test \
    --iterations 10 \
    --seed 42 \
    --output-dir build/tests/riscv-dv
```

---

## Analysis Scripts

### compare_bp_stats.py - Branch Predictor Analysis

**File:** `script/python/compare_bp_stats.py`

#### Purpose

Analyzes branch predictor statistics and compares different configurations.

#### Usage

```bash
python3 compare_bp_stats.py \
    --log1 results/logs/verilator/test1/bp_stats.log \
    --log2 results/logs/verilator/test2/bp_stats.log \
    --output comparison.html
```

#### Statistics

- Total branches
- Correctly predicted
- Mispredicted
- Prediction accuracy (%)
- BTB hits/misses
- RAS push/pop counts

---

### slang_lint.py - Slang Linter Wrapper

**File:** `script/python/slang_lint.py`

#### Purpose

Slang (pyslang) SystemVerilog linter wrapper for Makefile integration.

#### Usage

```bash
python3 slang_lint.py rtl/core/*.sv rtl/pkg/*.sv

# With options
python3 slang_lint.py \
    --include rtl/include \
    --top level_wrapper \
    --report results/lint/slang.json \
    rtl/**/*.sv
```

#### Code Structure

```python
import pyslang

def lint_files(files, includes, top_module):
    # Create compilation
    comp = pyslang.Compilation()
    
    # Add include paths
    for inc in includes:
        comp.addSearchDirectory(inc)
    
    # Add source files
    for f in files:
        comp.addSyntaxTree(pyslang.SyntaxTree.fromFile(f))
    
    # Get diagnostics
    diags = comp.getAllDiagnostics()
    
    for d in diags:
        print(f"{d.location}: {d.severity}: {d.message}")
    
    return len([d for d in diags if d.severity == 'error']) == 0
```

---

## Makefile Helpers

### isa_pipeline.py - ISA Test Import

**File:** `script/python/makefile/isa_pipeline.py`

#### Purpose

Imports ISA tests from the riscv-tests suite. Performs ELF → MEM/HEX/DUMP conversion.

#### Usage

```bash
python3 isa_pipeline.py \
    --isa-dir subrepo/riscv-tests/isa \
    --level-root /path/to/level-v
```

#### Pipeline Steps

1. Locate ELF files
2. Convert to binary with objcopy
3. Build `.mem` with elf_to_mem.py
4. Build `.dump` with objdump
5. Extract pass/fail addresses
6. Copy results under `build/tests/riscv-tests/`

---

### compare_logs.py — Log Comparison

**File:** `script/python/makefile/compare_logs.py`

#### Purpose

Compares the RTL commit log with the Spike commit log to determine pass/fail.

#### Usage

```bash
python3 compare_logs.py \
    results/logs/verilator/test/commit.log \
    results/logs/spike/test/commit.log
```

#### Comparison Criteria

- PC values
- Instruction opcodes
- Register write-back values
- Memory store values

#### Output

```
[COMPARE] Comparing RTL log with Spike log...
[INFO] RTL commits: 1234
[INFO] Spike commits: 1234
[PASS] All commits match!

# Or on mismatch:
[FAIL] Mismatch at commit #456
  RTL:   PC=0x80000100 x5=0x12345678
  Spike: PC=0x80000100 x5=0x12345679
```

---

### generate_test_dashboard.py - HTML Dashboard

**File:** `script/python/makefile/generate_test_dashboard.py`

#### Purpose

Builds an HTML dashboard from test results.

#### Usage

```bash
python3 generate_test_dashboard.py \
    --results results/regression/*.json \
    --output results/reports/dashboard.html
```

#### Dashboard Contents

- Test suite summary (pass/fail counts)
- Per-test results table
- Execution time statistics
- Failure details with logs
- Historical trends (if available)

---

## Summary

Python scripts:

1. **Converters**: ELF/HEX/BIN → `.mem` conversion
2. **Generators**: Linker script, torture test, RISCV-DV
3. **Analysis**: Branch predictor stats, log comparison
4. **Linting**: Slang wrapper
5. **Makefile Helpers**: ISA import, log compare, dashboard
6. **Modular Design**: Each script focuses on one job
7. **CLI Interface**: Consistent interface via argparse
