# Ceres RISC-V Architecture Test Environment

This directory contains the target-specific environment files for running
riscv-arch-test compliance tests on the Ceres RV32IMC_Zicsr processor.

## Files

- `model_test.h` - Target-specific macros (RVMODEL_HALT, RVMODEL_DATA_BEGIN, etc.)
- `link.ld` - Linker script for Ceres memory map

## Supported Extensions

The Ceres processor supports the following ISA extensions:
- **I** - Base Integer Instructions
- **M** - Integer Multiplication and Division
- **C** - Compressed Instructions
- **Zicsr** - Control and Status Register Instructions
- **Zifencei** - Instruction-Fetch Fence

## Usage

```bash
# Full pipeline: Clone, Setup, Build, Import
make arch_auto

# Or step by step:
make arch_clone      # Clone riscv-arch-test repository
make arch_setup      # Verify environment files
make arch_build      # Build all supported extension tests
make arch_import     # Convert to simulation format

# Run tests
make arch            # Run all arch tests
make ta T=I-add-01   # Run single arch test
```

## Memory Map

```
0x80000000 - 0x8003FFFF  RAM (256KB)
  - .text.init  Code entry point
  - .tohost     Host communication interface
  - .text       Program code
  - .data       Initialized data
  - .bss        Uninitialized data
  - Stack       4KB stack at end
```

## Output Directories

After running `make arch_auto`:
- `build/tests/riscv-arch-test/elf/`   - ELF executables
- `build/tests/riscv-arch-test/dump/`  - Disassembly dumps
- `build/tests/riscv-arch-test/hex/`   - Verilog hex files
- `build/tests/riscv-arch-test/mem/`   - Memory initialization files
- `build/tests/riscv-arch-test/pass_fail_addr/` - Pass/Fail addresses
