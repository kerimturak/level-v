# DCache Standalone Verification Environment

## Overview

This is a comprehensive verification environment for the dcache module, designed to isolate and debug cache issues without the complexity of the full SoC.

## Features

1. **Reference Model** (`dcache_model.sv`)
   - Behavioral model of 2-way set-associative cache
   - Implements data/tag/dirty/PLRU arrays
   - Can be compared against RTL

2. **Testbench** (`tb_dcache.sv`)
   - Minimal environment with simple memory controller
   - Directed test sequences
   - Hierarchical signal monitoring
   - Self-checking with error reporting

3. **Test Coverage**
   - **Test 1**: Fill all cache lines (cold misses)
   - **Test 2**: Read from filled lines (hits)
   - **Test 3**: Write to cache (mark dirty)
   - **Test 4**: Force writeback (dirty eviction)

## Directory Structure

```
verification/dcache_tb/
├── Makefile              # Build and run commands
├── README.md             # This file
├── dcache_model.sv       # Reference model
├── tb_dcache.sv          # Testbench
└── run_vsim.do           # ModelSim script
```

## Usage

### Prerequisites

- ModelSim (for simulation)
- Verilator (optional, for lint checking)

### Quick Start

```bash
cd verification/dcache_tb

# Compile and run with ModelSim
make sim

# Run with GUI
make gui

# Lint check with Verilator
make verilator

# Clean
make clean
```

### Test Configurations

#### Minimum Cache (512 bits = 2 sets, 2 ways)
```bash
# Edit rtl/pkg/ceres_param.sv:
#   DC_CAPACITY = 512

make test_min
```

#### 1KB Cache (4 sets, 2 ways)
```bash
# Edit rtl/pkg/ceres_param.sv:
#   DC_CAPACITY = 1024

make test_1kb
```

## Current Status

**TODO**:
- [ ] Connect actual dcache.sv RTL to testbench
- [ ] Add hierarchical signal comparison
- [ ] Implement backdoor memory checking
- [ ] Add more test scenarios (unaligned, burst writes, etc.)
- [ ] Add assertions for protocol checking
- [ ] Add coverage collection

## Test Scenarios

### Test 1: Fill Cache
- Reads 4 addresses mapping to all 4 cache lines
- All should miss (cache empty)
- Verifies basic fill mechanism

### Test 2: Read Hits
- Re-reads same 4 addresses
- All should hit
- Verifies hit detection and data return

### Test 3: Write Cache
- Writes to 2 cache lines
- Verifies dirty bit setting
- Prepares for writeback test

### Test 4: Writeback
- Reads new addresses forcing eviction
- Dirty lines should writeback first
- Verifies writeback mechanism

## Debug Strategy

1. **Run tests** - Identify which test fails
2. **Check waveforms** - Look at signal transitions
3. **Compare with model** - Use hierarchical references to compare RTL arrays with model arrays
4. **Add assertions** - Catch protocol violations
5. **Isolate bug** - Narrow down to specific signal/cycle

## Hierarchical Signal Access

To compare RTL with model, use SystemVerilog hierarchical references:

```systemverilog
// In testbench
logic match;
match = (tb_dcache.dut.data_array[0][0] == tb_dcache.model.data_array[0][0]);
```

## Known Issues

- DUT not yet instantiated in testbench (placeholder connections)
- Need to add cache interface type definitions from RTL
- Model PLRU may not match RTL implementation exactly

## Next Steps

1. Instantiate actual dcache RTL
2. Run Test 1 and debug fill mechanism
3. Add array comparison checkers
4. Extend test coverage
