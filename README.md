# CERES RISC-V

Ceres-RISC-V is a lightweight and modular 32-bit RISC-V processor core implementing the RV32IMC instruction set along with support for CSR and FENCE instructions. Designed for simplicity, clarity, and extensibility — ideal for learning, experimentation, or FPGA deployment.

## 🚀 Quick Start

```bash
# Build Verilator model
make verilator_build

# Run quick smoke test (~5 min)
make quick

# Run full regression (~30 min)
make full

# Generate coverage report
make coverage
```

## 📊 Test Automation

Comprehensive test suite with 215+ tests:
- **ISA Tests:** 50 (RV32IMC)
- **Arch Tests:** 91 (I: 38, M: 8, C: 27, Priv: 18)
- **Imperas Tests:** 45 (I extension)
- **Benchmarks:** 13 + CoreMark

📖 **[Full Test Automation Guide](docs/test/test-automation-summary.md)**

### Available Commands
```bash
make quick      # Quick smoke test
make full       # Full regression
make nightly    # Nightly build
make coverage   # Coverage analysis
make help_lists # Show all test commands
```

## 🛠️ Requirements

- **Verilator** 5.0+
- **RISC-V Toolchain** (riscv32-unknown-elf-gcc)
- **Python 3** (for scripting)
- **lcov** (optional, for HTML coverage reports)
