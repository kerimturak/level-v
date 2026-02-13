# Ceres-V Extended Test Suites

This document describes the extended test suites available for testing the Ceres-V RISC-V processor.

## Quick Reference

| Test Suite | Command | Description |
|------------|---------|-------------|
| Embench-IoT | `make embench` | Modern embedded benchmarks |
| Dhrystone | `make dhrystone` | Classic CPU benchmark |
| Torture | `make torture` | Random instruction stress tests |
| RISCV-DV | `make riscv_dv` | Google's test generator |
| Formal | `make formal` | Formal verification |

## 1. Embench-IoT

[Embench-IoT](https://github.com/embench/embench-iot) is a modern benchmark suite designed for embedded systems.

### Usage
```bash
# Clone, setup, and build
make embench

# Build and run all benchmarks
make embench_run

# List available benchmarks
make embench_list

# Show code size report
make embench_report

# Clean build files
make embench_clean
```

### Included Benchmarks
- aha-mont64, crc32, cubic, edn, huffbench
- matmult-int, md5sum, minver, nbody
- nettle-aes, nettle-sha256, nsichneu
- picojpeg, primecount, qrduino
- sglib-combined, slre, st, statemate
- tarfind, ud, wikisort

## 2. Dhrystone

[Dhrystone](https://en.wikipedia.org/wiki/Dhrystone) is a classic CPU benchmark for measuring integer performance.

### Usage
```bash
# Build benchmark
make dhrystone

# Build and run
make dhrystone_run

# Clean
make dhrystone_clean
```

### Configuration
- `DHRY_ITERS=N` - Number of iterations (default: 100000)
- `CPU_MHZ=N` - CPU frequency for DMIPS calculation

### Results Interpretation
- DMIPS/MHz = (Dhrystones/second) / 1757 / MHz
- Typical values: 1.0-2.5 DMIPS/MHz for simple in-order cores

## 3. Torture Tests

Random instruction sequence generator for stress testing the CPU.

### Usage
```bash
# Generate and build tests
make torture

# Run all tests
make torture_run

# Full batch test cycle
make torture_batch

# Clean
make torture_clean
```

### Configuration
- `TORTURE_NUM_TESTS=N` - Number of tests (default: 10)
- `TORTURE_SEED=N` - Random seed (default: timestamp)
- `TORTURE_MAX_INSNS=N` - Max instructions per test (default: 1000)

### Examples
```bash
# Generate 100 tests with specific seed
make torture TORTURE_NUM_TESTS=100 TORTURE_SEED=12345

# Run with different seed
make torture_batch TORTURE_SEED=98765
```

## 4. RISCV-DV

[RISCV-DV](https://github.com/chipsalliance/riscv-dv) is Google's UVM-based random instruction generator.

### Usage
```bash
# Generate, build all tests
make riscv_dv

# Run tests
make riscv_dv_run

# Compare with Spike ISS
make riscv_dv_compare

# List available test types
make riscv_dv_list

# Clean
make riscv_dv_clean
```

### Configuration
- `RISCV_DV_TEST=name` - Test type (default: riscv_arithmetic_basic_test)
- `RISCV_DV_ITER=N` - Number of iterations (default: 5)
- `RISCV_DV_SEED=N` - Random seed (default: 0)
- `RISCV_DV_ISA=rv32imc` - Target ISA

### Available Tests
- `riscv_arithmetic_basic_test` - Basic arithmetic operations
- `riscv_rand_instr_test` - Random instruction sequences
- `riscv_jump_stress_test` - Jump/branch stress test
- `riscv_loop_test` - Loop-based tests
- `riscv_rand_jump_test` - Random jumps
- `riscv_mmu_stress_test` - Memory stress test
- `riscv_illegal_instr_test` - Illegal instruction handling

## 5. Formal Verification

[RISCV-Formal](https://github.com/YosysHQ/riscv-formal) provides formal verification using SymbiYosys.

### Prerequisites
```bash
# Install Yosys
sudo apt install yosys

# Install SymbiYosys
pip3 install sby

# Install SMT solver
sudo apt install boolector  # or z3
```

### Usage
```bash
# Run formal verification
make formal

# Run bounded model checking
make formal_bmc

# Run inductive proof
make formal_prove

# Run coverage analysis
make formal_cover

# Show report
make formal_report

# Clean
make formal_clean
```

### Configuration
- `FORMAL_DEPTH=N` - BMC depth (default: 20)
- `FORMAL_MODE=mode` - bmc|prove|cover
- `FORMAL_ENGINE=solver` - boolector|z3|yices

### Note
Full formal verification requires adding RVFI (RISC-V Formal Interface) to the CPU. 
The wrapper in `env/riscv-formal/rvfi_wrapper.sv` is a template that needs to be connected to the CPU's internal signals.

## Directory Structure

```
env/
├── embench/
│   ├── crt0.S         # Startup code
│   ├── syscalls.c     # System calls
│   └── link.ld        # Linker script
├── dhrystone/
│   ├── crt0.S
│   ├── syscalls.c
│   ├── dhry.h
│   ├── dhry_1.c
│   ├── dhry_2.c
│   └── link.ld
├── torture/
│   ├── crt0.S
│   └── link.ld
├── riscv-dv/
│   └── link.ld
└── riscv-formal/
    └── rvfi_wrapper.sv

subrepo/
├── embench-iot/       # Cloned by `make embench_clone`
├── riscv-torture/     # Cloned by `make torture_clone`
├── riscv-dv/          # Cloned by `make riscv_dv_clone`
└── riscv-formal/      # Cloned by `make formal_clone`

build/tests/
├── embench/
├── dhrystone/
├── torture/
├── riscv-dv/
└── formal/
```

## Comparison with Other Test Suites

| Suite | Purpose | Coverage | Complexity |
|-------|---------|----------|------------|
| riscv-tests | ISA compliance | Basic | Low |
| riscv-arch-test | Architecture conformance | Good | Medium |
| Imperas | Commercial compliance | Excellent | High |
| CoreMark | Performance benchmark | N/A | Low |
| **Embench** | Modern benchmarks | N/A | Medium |
| **Dhrystone** | Classic benchmark | N/A | Low |
| **Torture** | Random stress | Random | High |
| **RISCV-DV** | Random generation | Configurable | High |
| **Formal** | Mathematical proof | Complete | Very High |

## Troubleshooting

### Common Issues

1. **Missing toolchain**
   ```
   Error: riscv-unknown-elf-gcc not found
   ```
   Install RISC-V toolchain: `apt install gcc-riscv64-unknown-elf`

2. **Python dependencies**
   ```bash
   pip3 install pyyaml  # For RISCV-DV
   ```

3. **Formal tools not installed**
   ```bash
   sudo apt install yosys boolector
   pip3 install sby
   ```

4. **Test timeout**
   Increase timeout: `make torture_run TIMEOUT=100000`

### Getting Help
```bash
make embench_help
make dhrystone_help
make torture_help
make riscv_dv_help
make formal_help
```
