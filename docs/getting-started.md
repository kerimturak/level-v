---
title: "Getting started"
description: "Step-by-step guide to start using the Level RISC-V core"
date: 2025-12-01
draft: false
weight: 1
---

# Level RISC-V getting started

This guide walks new users through setup and first steps with the Level RISC-V core.

---

## Prerequisites

### Software

```bash
# 1. Verilator (Verilog simulator)
verilator --version  # 5.0 or newer

# 2. RISC-V toolchain
riscv32-unknown-elf-gcc --version

# 3. Python 3
python3 --version

# 4. Make
make --version

# 5. lcov (optional, for coverage reports)
lcov --version
```

### Hardware

- **OS**: Linux (Ubuntu 18.04+, Debian 10+) or macOS
- **CPU**: At least 4 cores (8+ recommended)
- **RAM**: At least 8 GB
- **Disk**: At least 5 GB free

### Windows

Use WSL2 (Windows Subsystem for Linux 2):

```bash
# Example: install Ubuntu on WSL2
wsl --install -d Ubuntu-22.04
wsl -d Ubuntu-22.04
```

---

## Setup

### Step 1: Clone the repository

```bash
git clone https://github.com/yourusername/level-v.git
cd level-v
```

### Step 2: Install dependencies

```bash
# Ubuntu/Debian
sudo apt-get update
sudo apt-get install -y verilator riscv-gnu-toolchain python3 make lcov

# macOS (Homebrew)
brew install verilator riscv-gnu-toolchain python3 lcov
```

### Step 3: Build the Verilator model

```bash
make verilate
```

**Expected output**:

```
[SUCCESS] Built: .../build/obj_dir/Vlevel_wrapper
```

### Step 4: Run a quick test

```bash
make quick
```

**Expected**: the quick regression suite completes successfully (runtime depends on machine).

---

## Basic usage

### Build

```bash
# Verilator C++ model (main RTL build)
make verilate

# Optional: set up Python venv for tooling
python3 -m venv .venv && source .venv/bin/activate
pip install -r script/python/requirements.txt
```

### Run tests

```bash
# Quick suite (~few minutes)
make quick

# Full regression (~longer)
make full

# Nightly-style full sweep (~hours)
make nightly

# Examples by category
make test_isa          # ISA tests
make test_arch         # Architecture tests
# CoreMark: see docs/coremark-build.md and COREMARK_QUICK_START.md
```

### Clean

```bash
# Remove build products
make clean

# Remove outputs (logs, etc.) — exact targets depend on makefile
make distclean

# Examples (if defined in your makefile)
make clean_build
make clean_logs
```

---

## Outputs and analysis

### Test results

```bash
# Inspect summary logs under build/ or results/ per your makefile
grep -i "fail\|error" build/logs/test_summary.log  # example path
```

### Waveforms

```bash
# Tracing is usually enabled via Verilator flags; open generated FST/VCD
# Example with Surfer (if installed)
surfer results/logs/verilator/<TEST>/waveform.fst &
```

### Coverage

```bash
# If your makefile defines a coverage target
make coverage
# Open generated HTML report as documented in makefile help
```

---

## Command cheat sheet

| Command | Description | Typical duration |
|---------|-------------|------------------|
| `make verilate` | Build Verilator model | few minutes |
| `make quick` | Quick test sweep | ~5+ min |
| `make full` | Full regression | longer |
| `make coverage` | Coverage (if enabled) | varies |
| `make clean` | Clean artifacts | \<1 min |
| `make help` | List targets | — |

---

## Troubleshooting

### `verilator: command not found`

```bash
sudo apt-get install verilator   # Debian/Ubuntu
brew install verilator             # macOS
which verilator
```

### `riscv32-unknown-elf-gcc: command not found`

Install a RISC-V GNU toolchain (distro package or [riscv-gnu-toolchain](https://github.com/riscv-collab/riscv-gnu-toolchain)). Add `bin` to `PATH` if installed manually.

### `make: command not found`

```bash
sudo apt-get install build-essential   # Linux
brew install make                      # macOS if needed
```

### Tests fail

```bash
make distclean
make verilate
make quick
# Inspect the latest log under results/ or build/ for the failing test
```

### Out of memory

```bash
make -j2 quick    # reduce parallelism
make -j1 quick
free -h
```

---

## Next steps

### Verification

1. See [Test manager](TEST_MANAGER_README.md) and [simulation overview](sim/overview.md).
2. Run ISA flows documented in the makefile / `docs/script/overview.md`.

### Microarchitecture

1. [Architecture](architecture.md)
2. [Exception priority](parametric-exception-priority.md)
3. Browse `rtl/core/` and module docs under `docs/core/`.

### Debug

1. [Troubleshooting](TROUBLESHOOTING.md)
2. Commit trace and `compare_logs` workflow in `docs/script/tool-ecosystem-design.md`.

---

## Suggested learning path

1. **Week 1**: Install, `make verilate`, `make quick`, skim logs.
2. **Week 2**: Read [Architecture](architecture.md), trace one test in the waveform viewer.
3. **Week 3**: Add or adapt a small C/assembly test (see `sim/test/custom/`).
4. **Week 4+**: CSRs, exceptions, and advanced verification topics.

### External references

- [RISC-V specifications](https://riscv.org/specifications/)
- [Verilator guide](https://verilator.org/guide/latest/)
- [RISC-V GNU toolchain](https://github.com/riscv-collab/riscv-gnu-toolchain)

---

## Checklist

Before you dive in:

- [ ] Verilator installed (`verilator --version`)
- [ ] RISC-V GCC installed (`riscv32-unknown-elf-gcc --version`)
- [ ] Python 3 installed (`python3 --version`)
- [ ] Make installed (`make --version`)
- [ ] Repository cloned
- [ ] `make verilate` succeeds
- [ ] `make quick` (or a single `make run_verilator TEST_NAME=...`) succeeds

---

## Help and support

1. Search [existing issues](https://github.com/kerimturak/level-v/issues).
2. Open a new issue with OS version, full error text, exact command, and steps to reproduce.

Contributions via pull request are welcome; opening an issue first for larger changes is appreciated.

---

## Notes

- First Verilator builds can take several minutes; incremental builds are faster.
- WSL2 can be slower than native Linux for large builds.

---

**Version**: 1.0  
**Last updated**: December 2025
