# CoreMark Comparison Guide
## Running CoreMark on both Ceres-V and Spike for Comparison

This guide explains how to build and run CoreMark on both your Ceres-V processor (Verilator simulation) and Spike (ISS) with commit log generation for comparison.

## Quick Start

### 1. Build Both Versions

```bash
# Build CoreMark for both Ceres-V and Spike
make coremark_both COREMARK_ITERATIONS=10
```

This builds:
- **Ceres-V version**: Barebone port using MMIO (UART @ 0x20000000, Timer @ 0x30000000)
- **Spike version**: spike-pk port using syscalls (printf, gettimeofday)

### 2. Run on Spike Only

```bash
# Run CoreMark on Spike with commit logging
make cm_spike COREMARK_ITERATIONS=10
```

Output files:
- `build/tests/coremark-spike/coremark.exe` - Binary for Spike
- `results/logs/spike/coremark/uart_output.log` - Spike output
- `results/logs/spike/coremark/spike_commits.log` - Instruction trace (commit log)

### 3. Run Full Comparison

```bash
# Run CoreMark on both platforms and generate comparison report
make cm_compare COREMARK_ITERATIONS=10 MAX_CYCLES=50000000
```

This will:
1. Build both versions if needed
2. Run on Ceres-V (Verilator)
3. Run on Spike (ISS)
4. Generate comparison report

Output files:
- **Ceres-V logs**: `results/logs/verilator/coremark/`
  - `uart_output.log` - UART output with CoreMark results
  - `ceres_commits.log` - Instruction commit log
  - `waveform.fst` - Waveform dump (if enabled)

- **Spike logs**: `results/logs/spike/coremark/`
  - `uart_output.log` - Spike output
  - `spike_commits.log` - Instruction commit log

- **Comparison**: `results/comparison/coremark/`
  - `comparison_report.txt` - Side-by-side comparison

### 4. Quick Test (1 iteration)

```bash
# Quick comparison with minimal iterations
make cm_compare_quick
```

## Detailed Usage

### Available Targets

#### Spike Targets
```bash
make coremark_spike_setup      # Copy spike-pk port files
make coremark_spike_build      # Build for Spike
make coremark_spike_run        # Run on Spike with commit log
make cm_spike                  # Short alias for spike run
```

#### Comparison Targets
```bash
make coremark_both            # Build both versions
make coremark_compare         # Full comparison
make cm_compare               # Short alias
make cm_compare_quick         # Quick test (ITER=1)
```

#### Ceres-V Targets (existing)
```bash
make coremark                 # Build for Ceres-V
make run_coremark             # Run on Ceres-V
make cm                       # Short alias
make cm_quick                 # Quick test
make cm_fast                  # Fast mode (no trace)
```

### Configuration

#### Iteration Count
```bash
# Set number of iterations
make cm_compare COREMARK_ITERATIONS=100
```

Recommended values:
- `ITER=1`: Quick validation (~5-10M instructions)
- `ITER=10`: Light benchmark (~50-100M instructions)
- `ITER=100`: Standard benchmark (~500M-1B instructions)
- `ITER=2000`: Official benchmark (long runtime)

#### Simulation Cycles
```bash
# Set max cycles for Ceres-V simulation
make cm_compare MAX_CYCLES=100000000
```

### Commit Log Comparison

Both platforms generate instruction commit logs in the same format:

**Spike format:**
```
core   0: 3 0x80000000 (0x2000006f)
core   0: 3 0x80000200 (0x00000093) x1  0x00000000
```

**Ceres-V format (compatible):**
```
core   0: 3 0x80000000 (0x2000006f)
core   0: 3 0x80000200 (0x00000093) x1  0x00000000
```

Format: `core ID : privilege : PC (instruction) [reg updates] [mem accesses]`

### Using Your Comparison Script

After running the comparison, use your Python script to analyze the commit logs:

```bash
# Compare instruction traces
python3 your_compare_script.py \
    results/logs/verilator/coremark/ceres_commits.log \
    results/logs/spike/coremark/spike_commits.log
```

The commit logs contain:
- Program counter (PC)
- Instruction encoding
- Register writes
- Memory accesses

## Port Differences

### Ceres-V Barebone Port (`env/coremark/ceresv/`)

- **UART**: Direct MMIO @ 0x20000000
  - Control register @ +0x00
  - Status register @ +0x04
  - TX data register @ +0x0C

- **Timer**: Direct MMIO @ 0x30000000
  - Timer low @ +0x00
  - Timer high @ +0x04

- **Timing**: Hardware cycle counter
- **Entry**: Custom crt0.S startup code
- **Link**: Custom linker script (link.ld)

### Spike-pk Port (`env/coremark/spike-pk/`)

- **UART**: `printf()` syscall via pk
- **Timer**: `gettimeofday()` syscall via pk
- **Timing**: Microsecond-based (simulated time)
- **Entry**: Standard pk entry
- **Link**: Standard pk linking

## Troubleshooting

### Spike not found
```bash
# Check Spike installation
which spike
# or set explicitly
SPIKE_BIN=/path/to/spike make cm_spike
```

### pk not found
```bash
# Check pk installation
which pk
# or set explicitly
PK_BIN=/path/to/pk make cm_spike
```

### Commit log too large
Reduce iterations:
```bash
make cm_compare COREMARK_ITERATIONS=1
```

### Simulation timeout
Increase max cycles:
```bash
make cm_compare MAX_CYCLES=100000000
```

## Example Workflow

### 1. Quick Validation
```bash
# Test both platforms with 1 iteration
make cm_compare_quick
```

### 2. Light Benchmark
```bash
# Run with 10 iterations
make cm_compare COREMARK_ITERATIONS=10 MAX_CYCLES=50000000
```

### 3. Analyze Differences
```bash
# Use your comparison script
python3 compare_commits.py \
    results/logs/verilator/coremark/ceres_commits.log \
    results/logs/spike/coremark/spike_commits.log
```

### 4. Check Results
```bash
# View Ceres-V output
cat results/logs/verilator/coremark/uart_output.log

# View Spike output
cat results/logs/spike/coremark/uart_output.log

# View comparison report
cat results/comparison/coremark/comparison_report.txt
```

## File Locations

```
level-v/
├── env/coremark/
│   ├── ceresv/              # Ceres-V barebone port files
│   │   ├── core_portme.c
│   │   ├── core_portme.h
│   │   ├── core_portme.mak
│   │   ├── link.ld
│   │   └── memory_map.yaml
│   └── spike-pk/            # Spike-pk port files
│       ├── core_portme.c
│       ├── core_portme.h
│       └── core_portme.mak
├── build/tests/
│   ├── coremark/            # Ceres-V build output
│   │   ├── coremark.elf
│   │   ├── coremark.mem
│   │   └── coremark.dump
│   └── coremark-spike/      # Spike build output
│       └── coremark.exe
└── results/
    ├── logs/
    │   ├── verilator/coremark/    # Ceres-V simulation logs
    │   │   ├── uart_output.log
    │   │   ├── ceres_commits.log
    │   │   └── waveform.fst
    │   └── spike/coremark/        # Spike simulation logs
    │       ├── uart_output.log
    │       └── spike_commits.log
    └── comparison/coremark/       # Comparison output
        └── comparison_report.txt
```

## Configuration Files

### Spike Configuration
Location: `build/.test_config_coremark.mk`

Key settings:
```makefile
CFG_SPIKE_ISA := rv32imc_zicsr_zicntr_zifencei
CFG_SPIKE_LOG_COMMITS := 1
CFG_MAX_CYCLES := 50000000
```

### Memory Map
Location: `env/coremark/ceresv/memory_map.yaml`

Defines:
- ROM/RAM layout
- UART registers
- Timer registers
- Stack/heap configuration

## References

- CoreMark: https://github.com/eembc/coremark
- Spike: https://github.com/riscv-software-src/riscv-isa-sim
- pk (Proxy Kernel): https://github.com/riscv-software-src/riscv-pk
- Spike-pk port: `subrepo/coremark/SPIKE_PK_README.md`
