# CERES RISC-V — Test Automation Summary

**Date:** November 29, 2025  
**Status:** ✅ Implemented

---

## 📊 Overview

Comprehensive test automation system with multiple test suites, coverage analysis, and CI/CD integration.

### Test Coverage Statistics

| Test Suite | Count | Extensions | Source |
|------------|-------|------------|--------|
| **ISA Tests** | 50 | I, M, C | riscv-tests |
| **Arch Tests** | 91 | I(38), M(8), C(27), Priv(18) | riscv-arch-test |
| **Imperas Tests** | 45 | I only | riscv-test-suite |
| **CSR Tests** | 15 | Machine CSR | riscv-tests |
| **Benchmarks** | 13 | dhrystone, median, etc. | riscv-tests |
| **CoreMark** | 1 | Full CoreMark | coremark |

**Total:** 215+ tests

---

## 🚀 Regression Test Commands

### Quick Smoke Test (~5 minutes)
```bash
make quick
# Runs: ISA + CSR tests
# Good for: Fast sanity check after changes
```

### Full Regression (~30 minutes)
```bash
make full
# or
make regression

# Runs: ISA + Arch + Imperas + CSR
# Good for: Pull requests, pre-merge validation
# Output: results/regression/report_YYYYMMDD_HHMMSS.txt
```

### Nightly Build (~60+ minutes)
```bash
make nightly

# Runs: Full regression + Benchmarks + CoreMark
# Good for: Scheduled nightly builds
# Output: results/regression/nightly_YYYYMMDD_HHMMSS.txt
```

---

## 🎯 Individual Test Suites

### ISA Tests (RV32IMC_Zicsr)
```bash
make isa                    # All ISA tests (50 tests)
make t T=rv32ui-p-add      # Single test

# Breakdown:
# - rv32ui: Base integer (I extension)
# - rv32um: Multiply/Divide (M extension)  
# - rv32uc: Compressed (C extension)
# - rv32mi: Machine mode CSR
```

### Architecture Tests
```bash
make arch                  # All arch tests (91 tests)
make ta T=I-add-01        # Single test

# Extensions covered:
# - I extension: 38 tests
# - M extension: 8 tests (mul, div, rem, etc.)
# - C extension: 27 tests (c.add, c.beqz, etc.)
# - Privilege: 18 tests
```

### Imperas Tests
```bash
make imperas              # All Imperas tests (45 tests)
make ti T=I-ADD-01       # Single test

# Note: Only I extension available in free repo
# Skip list: I-MISALIGN_JMP-01, I-MISALIGN_LDST-01, I-EBREAK-01
```

### Benchmarks
```bash
make bench                # All benchmarks
make tb T=dhrystone      # Single benchmark

# Available: dhrystone, median, multiply, qsort, etc.
```

### CoreMark
```bash
make cm                   # Build and run CoreMark
make cm_run              # Quick run (skip rebuild)
make cm MAX_CYCLES=10000000  # Extended runtime
```

---

## 📈 Coverage Analysis

### Quick Coverage (ISA only)
```bash
make coverage-quick

# Steps:
# 1. Rebuild with COVERAGE=1
# 2. Run ISA tests
# 3. Generate HTML report
# Output: results/coverage/index.html
```

### Full Coverage (ISA + Arch)
```bash
make coverage

# Steps:
# 1. Rebuild with COVERAGE=1
# 2. Run ISA tests
# 3. Run Arch tests
# 4. Generate HTML report
# Output: results/coverage/index.html
```

### Manual Coverage
```bash
# Build with coverage
make verilator_build COVERAGE=1

# Run any tests
make isa COVERAGE=1
make arch COVERAGE=1

# Generate report
make coverage-html

# View results
open results/coverage/index.html  # macOS
xdg-open results/coverage/index.html  # Linux
```

### Requirements
```bash
# For HTML coverage reports
sudo apt install lcov   # Ubuntu/Debian
brew install lcov       # macOS
```

---

## 🔧 Test Options

### Cycle Limits
Each test type has optimized defaults:

```bash
# Defaults (auto-applied):
# - ISA tests:     10,000 cycles
# - CSR tests:     10,000 cycles  
# - Arch tests:    100,000 cycles
# - Imperas tests: 200,000 cycles
# - Benchmarks:    1,000,000 cycles

# Override examples:
make arch ARCH_MAX_CYCLES=500000
make bench BENCH_MAX_CYCLES=5000000
make imperas IMPERAS_MAX_CYCLES=300000
```

### Log Management
```bash
# Clean all logs before batch run
make isa CLEAN_LOGS=1
make full CLEAN_LOGS=1

# Keep existing logs
make arch  # Default
```

### Fast Simulation
```bash
# Disable FST tracing for speed
make t T=rv32ui-p-add FAST_SIM=1
```

---

## 🤖 GitHub Actions CI/CD

### Automated Workflows

File: `.github/workflows/ci.yml`

#### On Every Push
```yaml
Trigger: push to main/develop
Jobs:
  - lint: Static Verilator lint check
  - build: Build Verilator model
  - quick-tests: Run ISA + CSR tests (~5 min)
```

#### On Pull Request
```yaml
Trigger: PR to main
Jobs:
  - lint: Static checks
  - build: Build model
  - full-tests: Full regression (~30 min)
```

#### Manual Trigger
```yaml
Trigger: workflow_dispatch
Options:
  - quick: Quick smoke test
  - full: Full regression
  - nightly: Nightly build
```

### Artifacts
- Test results retained for 7-30 days
- Coverage reports (if enabled)
- Build logs

### Caching
- Verilator installation (~5 min build → cached)
- RISC-V toolchain (~10 min download → cached)

---

## 📂 File Structure

```
level-v/
├── .github/workflows/
│   └── ci.yml                      # GitHub Actions CI pipeline
│
├── results/
│   ├── logs/                       # Individual test logs
│   ├── regression/                 # Regression reports
│   │   ├── report_YYYYMMDD.txt    # Full regression
│   │   ├── nightly_YYYYMMDD.txt   # Nightly reports
│   │   └── latest_summary.txt     # Latest summary
│   └── coverage/                   # Coverage reports
│       ├── index.html             # HTML coverage
│       └── annotated/             # Annotated source
│
├── sim/test/
│   ├── riscv_test_list.flist      # ISA tests
│   ├── arch_test.flist            # Arch tests (auto-generated)
│   ├── imperas_test_list.flist    # Imperas tests
│   └── machine_csr_test.flist     # CSR tests
│
└── docs/test/
    ├── test-automation.md         # General test docs
    ├── imperas-tests.md           # Imperas guide
    └── test-automation-summary.md # This file
```

---

## 🔍 Extension Coverage

### M Extension (Multiply/Divide)
✅ **ISA Tests:** 8 tests (rv32um-*)
- mul, mulh, mulhsu, mulhu
- div, divu, rem, remu

✅ **Arch Tests:** 8 tests (M-*)
- M-mul-01, M-div-01, etc.

### C Extension (Compressed)
✅ **ISA Tests:** 1 test (rv32uc-p-rvc)

✅ **Arch Tests:** 27 tests (C-*)
- C-add, C-addi, C-beqz, C-bnez, C-j, C-jr, etc.

### Missing from Imperas
⚠️ Imperas free repo only has I extension (45 tests)
- No M extension tests
- No C extension tests
- Use riscv-arch-test for M/C coverage

---

## 🎓 Usage Examples

### Daily Development Workflow
```bash
# 1. Make RTL changes
vim rtl/core/decoder.sv

# 2. Quick sanity check
make quick  # ~5 minutes

# 3. If pass, run full regression before commit
make full CLEAN_LOGS=1  # ~30 minutes

# 4. (Optional) Check coverage
make coverage-quick
open results/coverage/index.html
```

### Pre-Release Validation
```bash
# 1. Full nightly build
make nightly  # ~60+ minutes

# 2. Full coverage analysis
make coverage  # Includes ISA + Arch

# 3. Review reports
cat results/regression/nightly_*.txt
open results/coverage/index.html
```

### Debugging Failed Test
```bash
# 1. Run single test with full logs
make t T=rv32ui-p-add

# 2. Check logs
cat results/logs/verilator/rv32ui-p-add/run.log

# 3. View waveform
make wave TEST=rv32ui-p-add
```

---

## ✅ Implementation Checklist

- [x] **Regression Commands**
  - [x] `make quick` - Fast smoke test
  - [x] `make full` / `make regression` - Complete suite
  - [x] `make nightly` - Extended validation

- [x] **Test Categories**
  - [x] ISA tests with explicit MAX_CYCLES
  - [x] Arch tests with explicit MAX_CYCLES
  - [x] Imperas tests with explicit MAX_CYCLES
  - [x] CoreMark integration

- [x] **Coverage Analysis**
  - [x] `make coverage` - Full coverage
  - [x] `make coverage-quick` - Fast coverage
  - [x] `make coverage-html` - HTML reports
  - [x] Coverage data cleanup

- [x] **GitHub Actions CI**
  - [x] Static lint check
  - [x] Quick tests on push
  - [x] Full tests on PR
  - [x] Manual workflow dispatch
  - [x] Caching (Verilator, toolchain)
  - [x] Artifact retention

- [x] **Documentation**
  - [x] Help system updates
  - [x] This summary document
  - [x] Individual test suite docs

- [x] **Extension Coverage**
  - [x] Verified M extension tests (16 total)
  - [x] Verified C extension tests (28 total)
  - [x] Documented Imperas limitations

---

## 🚧 Future Improvements

### Potential Enhancements
1. **Parallel Test Execution**
   - Run independent tests in parallel
   - Reduce regression time from 30min → 10min

2. **Test Result Database**
   - Store historical results
   - Track regression trends over time

3. **Performance Benchmarking**
   - Track CoreMark scores
   - Dhrystone MIPS measurements

4. **Additional Test Suites**
   - Custom interrupt tests
   - Performance counter tests
   - Debug module tests

5. **Visual Dashboards**
   - Web-based test dashboard
   - Coverage trend graphs
   - Failure analysis tools

---

## 📞 Help

```bash
# Show all test commands
make help_lists

# Show Imperas test help
make imperas_help

# Show architecture test help
make arch_help

# Show CoreMark help
make coremark_help
```

---

**Maintained by:** CERES RISC-V Team  
**Last Updated:** November 29, 2025
