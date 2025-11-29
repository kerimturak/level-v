# Imperas RISC-V Tests Environment for Ceres-V

This directory contains the target-specific configuration files for running
Imperas RISC-V tests on the Ceres-V processor.

## Overview

The Imperas RISC-V tests (riscv-ovpsim/imperas-riscv-tests) provide an
extended set of RISC-V architectural tests beyond the official riscv-arch-test.
They use the same test framework format (model_test.h + arch_test.h).

## Files

- `model_test.h` - Target-specific macros for Ceres-V (RVMODEL_*)
- `link.ld` - Linker script for 0x80000000 entry point

## Supported Extensions

- RV32I - Base Integer Instructions
- RV32M - Integer Multiplication/Division
- RV32C - Compressed Instructions
- RV32Zicsr - CSR Instructions

## Usage

```bash
# Full pipeline: Clone → Build → Import
make imperas_auto

# Individual steps
make imperas_clone      # Clone Imperas repo
make imperas_list       # List available tests
make imperas_build      # Build all extensions
make imperas_import     # Convert to MEM format

# Extension-specific builds
make imperas_build_I    # Build I extension tests
make imperas_build_M    # Build M extension tests
make imperas_build_C    # Build C extension tests
```

## Notes

The Imperas tests are more comprehensive than standard riscv-arch-test
and include additional corner-case tests.
