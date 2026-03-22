# Level RISC-V — Development Tools Guide

This document describes the open-source development tools used in the Level RISC-V project, how to install them, and usage examples.

---

## 📊 Tool Summary

| Tool | Category | Rating | License | Description |
|------|----------|:--------:|--------|-------------|
| **Verilator** | Simulation | ⭐⭐⭐⭐⭐ | LGPL | Fastest open-source RTL simulator |
| **Spike** | RISC-V ISS | ⭐⭐⭐⭐⭐ | BSD | Official RISC-V reference simulator |
| **Slang (pyslang)** | Linting | ⭐⭐⭐⭐⭐ | MIT | Most comprehensive SV parser/linter |
| **Yosys** | Synthesis | ⭐⭐⭐⭐⭐ | ISC | RTL synthesis framework |
| **svlint** | Linting | ⭐⭐⭐⭐ | MIT | Fast SV style linter |
| **GTKWave** | Waveform | ⭐⭐⭐⭐ | GPL | Mature VCD/FST viewer |
| **Surfer** | Waveform | ⭐⭐⭐⭐ | MIT | Modern, GPU-accelerated viewer |
> **Rating scale:** ⭐ Basic → ⭐⭐⭐⭐⭐ Professional

---

## 🚀 Simulation Tools

### Verilator (Recommended)

**Version:** 5.026  
**Rating:** ⭐⭐⭐⭐⭐  
**Website:** https://verilator.org

Verilator is the fastest open-source simulator that compiles SystemVerilog/Verilog RTL to C++/SystemC.

#### Features
- ✅ SystemVerilog 2017 support
- ✅ Multi-threaded simulation
- ✅ Lint and static analysis
- ✅ Coverage analysis
- ✅ FST/VCD waveform output
- ✅ C++ testbench integration

#### Installation
```bash
# Ubuntu 24.04
sudo apt install verilator

# From source (recommended, more up to date)
git clone https://github.com/verilator/verilator
cd verilator && git checkout v5.026
autoconf && ./configure --prefix=/opt/verilator
make -j$(nproc) && sudo make install
```

#### Usage
```bash
make verilate                    # Build model
make run_verilator TEST_NAME=rv32ui-p-add
make lint                        # Verilator lint (--lint-only -Wall)
```

---

### Spike (RISC-V ISS)

**Rating:** ⭐⭐⭐⭐⭐  
**Website:** https://github.com/riscv-software-src/riscv-isa-sim

Official RISC-V Instruction Set Simulator. Used as a golden model.

#### Features
- ✅ All RISC-V ISA extensions
- ✅ Commit trace log output
- ✅ Interactive debugging
- ✅ Memory model support

#### Usage
```bash
make spike TEST_NAME=rv32ui-p-add   # Run with Spike
make compare_logs                    # Compare RTL vs Spike
```

---

### Icarus Verilog

The project has **no Makefile target** for Icarus: Level RTL uses advanced SystemVerilog and does not practically build with Icarus. You may install and try it separately; the official flow is Verilator / ModelSim.

---

## 🔍 Linting Tools

### Slang (pyslang)

**Version:** 9.1.0  
**Rating:** ⭐⭐⭐⭐⭐  
**Website:** https://sv-lang.com

The most comprehensive SystemVerilog parser and linter. Full IEEE 1800-2023 alignment.

#### Features
- ✅ Full SV 2023 support
- ✅ Semantic analysis
- ✅ Type checking
- ✅ 200+ lint rules
- ✅ Python bindings (pyslang)

#### Installation
```bash
pip install pyslang
# or
make lint_install
```

#### Usage
```bash
make slang_lint      # Run lint
make slang_check     # Detailed analysis
```

#### Sample Output
```
rtl/core/cpu.sv:182:78: error: no implicit conversion from 'int' to 'spec_type_e'
rtl/core/cpu.sv:309:16: warning: 'case' marked 'unique' has 'default' label
```

---

### svlint

**Version:** 0.9.5  
**Rating:** ⭐⭐⭐⭐  
**Website:** https://github.com/dalance/svlint

Fast SystemVerilog style and naming linter. Rust-based.

#### Features
- ✅ Fast execution
- ✅ TOML configuration
- ✅ Customizable rules
- ✅ CI/CD friendly

#### Installation
```bash
make lint_install
# or
cargo install svlint
```

#### Usage
```bash
make svlint          # Run lint
```

#### Configuration (.svlint.toml)
```toml
[option]
exclude_paths = ["subrepo/", "build/"]

[rules]
prefix_module = false
style_keyword_1space = true
case_default = true
```

---

### Verilator Lint

**Rating:** ⭐⭐⭐⭐  

Built-in Verilator lint.

#### Usage
```bash
make lint                # Static analysis (--lint-only -Wall)
```

---

## 📊 Waveform Viewer

### GTKWave

**Rating:** ⭐⭐⭐⭐  
**Website:** http://gtkwave.sourceforge.net

Mature, widely used waveform viewer.

#### Features
- ✅ VCD, FST, LXT2 support
- ✅ TCL scripting
- ✅ Signal search
- ✅ Analog waveform

#### Installation
```bash
sudo apt install gtkwave
```

#### Usage
```bash
make gtkwave                    # Open latest waveform
make run_verilator TRACE=1      # Simulation with trace
```

---

### Surfer

**Rating:** ⭐⭐⭐⭐  
**Website:** https://surfer-project.org

Modern, GPU-accelerated waveform viewer. Rust-based.

#### Features
- ✅ GPU acceleration
- ✅ Modern UI
- ✅ Fast large-file loading
- ✅ VCD, FST, GHW support

#### Installation
```bash
make surfer_install
# or
cargo install --git https://gitlab.com/surfer-project/surfer surfer
```

#### Usage
```bash
make surfer                     # Open waveform
make surfer_file WAVE_FILE=path # Open specific file
make wave_compare               # GTKWave vs Surfer comparison
```

---

## 🔨 Synthesis Tools

### Yosys

**Rating:** ⭐⭐⭐⭐⭐  
**Website:** https://yosyshq.net/yosys

Open-source RTL synthesis framework.

#### Features
- ✅ Verilog/SystemVerilog parsing
- ✅ Various optimization passes
- ✅ FPGA and ASIC targets
- ✅ Formal verification support

#### Installation
```bash
sudo apt install yosys
```

#### Usage
```bash
make yosys_check                # Synthesis check
make yosys_synth                # Full synthesis
```

---

## 🧪 Test Framework

### riscv-tests

Official RISC-V ISA test suite.

```bash
make isa                        # Run all ISA tests
make t T=rv32ui-p-add           # Single test
```

### riscv-arch-test

RISC-V architecture compliance tests.

```bash
make arch                       # Run all arch tests
```

### CoreMark

Embedded system benchmark.

```bash
make run_coremark               # CoreMark (Verilator)
```

---

## 📋 Quick Reference

| Command | Description |
|---------|-------------|
| `make verilate` | Build Verilator model |
| `make run_verilator TEST_NAME=...` | Run simulation |
| `make svlint` | Run svlint |
| `make slang_lint` | Run Slang lint |
| `make lint_all` | Run all linters |
| `make lint_install` | Install lint tools |
| `make gtkwave` | Open GTKWave |
| `make surfer` | Open Surfer |
| `make yosys_check` | Yosys synthesis check |
| `make isa` | Run ISA tests |
| `make html` | Generate test dashboard |

---

## 🔧 Troubleshooting

### Verilator Errors

**BLKLOOPINIT error:**
```bash
# --Wno-BLKLOOPINIT added in verilator.mk
```

**VL_SYSTEM_IN error:**
```bash
# Upgrade to Verilator 5.026
```

### svlint Configuration Error
```bash
# Check the .svlint.toml file
# Rule names may be invalid
```

### pyslang Import Error
```bash
pip install --upgrade pyslang
```

---

## 📚 Additional Resources

- [Verilator Manual](https://verilator.org/guide/latest/)
- [Slang Documentation](https://sv-lang.com/)
- [svlint Manual](https://github.com/dalance/svlint/blob/master/MANUAL.md)
- [Yosys Manual](https://yosyshq.readthedocs.io/)
- [RISC-V Specifications](https://riscv.org/technical/specifications/)

---

*Last updated: November 2025*
