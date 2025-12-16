# CERES RISC-V Troubleshooting Guide

## Common Build Issues

### 1. "invalid preprocessing directive #include" Error

**Symptoms:**
```
error: invalid preprocessing directive #include
    5 | #include "verilated.h"
      |  ^~~~~~~
```

**Cause:** ccache (compiler cache) corruption

**Solution:**
```bash
make clean_ccache
make verilate
```

**When this happens:**
- After Verilator upgrade
- After interrupted builds (Ctrl+C during compilation)
- After system crashes during build
- Random unexplained C++ errors in Verilator-generated files

---

### 2. "Signal unoptimizable: Circular combinational logic"

**Symptoms:**
```
%Warning-UNOPTFLAT: Circular combinational logic: signal_name
```

**Cause:** Combinational loops in RTL design

**Solution:**
See [COMBINATIONAL_LOOP_FIX.md](COMBINATIONAL_LOOP_FIX.md) for detailed explanation.

**Quick fix attempt:**
1. Check if signal can be registered
2. Look for feedback paths in `always_comb` blocks
3. Use Verilator's suggested `/* verilator lint_off UNOPTFLAT */` only as last resort

---

### 3. GCC Internal Compiler Error (Segmentation Fault)

**Symptoms:**
```
g++: internal compiler error: Segmentation fault signal terminated program cc1plus
```

**Cause:**
- ccache corruption (most common)
- Low system memory
- Compiler bug

**Solution:**
```bash
# Try ccache clean first
make clean_ccache

# If still fails, check memory
free -h

# Nuclear clean
make clean_verilator_nuclear

# If nothing works, disable ccache temporarily
export CCACHE_DISABLE=1
make verilate
```

---

### 4. Verilator "Too many statements in assignment"

**Symptoms:**
```
%Error: Too many statements in assignment; suggest break into multiple assignments
```

**Cause:** Complex combinational logic in single `always_comb` block

**Solution:**
1. Break into multiple `always_comb` blocks
2. Use intermediate signals
3. Adjust `--unroll-count` and `--unroll-stmts` in Makefile

---

### 5. Build Hangs / Infinite Compilation

**Symptoms:**
- Build stuck on one file
- High CPU usage but no progress
- No output for >10 minutes

**Cause:**
- Extremely complex generated code
- Combinational loops causing optimizer issues

**Solution:**
```bash
# Kill build
Ctrl+C

# Check what's hanging
ps aux | grep g++

# Try disabling optimization
VERILATOR_PROFILE=debug make verilate

# Or reduce complexity
--unroll-count 32  # instead of 64
```

---

### 6. "undefined reference to" Errors During Linking

**Symptoms:**
```
undefined reference to `Vceres_wrapper::eval()'
```

**Cause:**
- Incomplete build
- Mismatched object files from different builds

**Solution:**
```bash
make clean_verilator_deep
make verilate
```

---

### 7. Simulation Crashes with "Assertion failed"

**Symptoms:**
```
Assertion failed: (signal != nullptr), function eval, file Vceres_wrapper.cpp
```

**Cause:**
- Uninitialized signals in testbench
- Timing violations in design
- X-propagation issues

**Solution:**
1. Check testbench initialization
2. Enable debug mode:
   ```bash
   VERILATOR_PROFILE=debug make run_verilator TEST_NAME=your_test
   ```
3. Check wave file (`.fst`) for X values

---

### 8. "Maximum simulation time exceeded"

**Symptoms:**
```
[ERROR] Maximum simulation time exceeded (1000000 cycles)
```

**Cause:**
- Test taking too long
- Infinite loop in program
- Cache thrashing

**Solution:**
```bash
# Increase cycle limit
make run_verilator TEST_NAME=coremark MAX_CYCLES=100000000

# Or use benchmark profile
make run_verilator TEST_NAME=coremark VERILATOR_PROFILE=benchmark
```

---

### 9. FST Trace File Too Large

**Symptoms:**
```
[WARN] Trace file size: 15.2 GB
```

**Cause:**
- Deep trace depth
- Long simulation
- Too many signals

**Solution:**
```bash
# Reduce trace depth
make run_verilator TEST_NAME=test TRACE_DEPTH=10

# Or disable tracing for fast tests
make run_verilator TEST_NAME=test TRACE=0

# Or use FAST mode
make run_verilator TEST_NAME=test FAST=1
```

---

### 10. "No such file or directory" for Test

**Symptoms:**
```
[ERROR] Test not found: rv32ui-p-addd
```

**Cause:**
- Typo in test name
- Test not compiled

**Solution:**
```bash
# List available tests
make list_tests

# Compile all tests
make compile_tests

# Check specific test
ls -la tests/riscv-tests/isa/rv32ui-p-add
```

---

## Performance Issues

### Slow Compilation

**Symptoms:** Verilator takes >5 minutes to build

**Solutions:**
```bash
# Use more threads
make verilate BUILD_JOBS=32

# Reduce output splitting
--output-split 50000  # instead of 20000

# Use fast profile for development
VERILATOR_PROFILE=fast make verilate
```

### Slow Simulation

**Symptoms:** Tests take >1 minute

**Solutions:**
```bash
# Use FAST mode (no tracing)
make run_verilator TEST_NAME=test FAST=1

# Reduce verification
+define+SIM_FAST

# Use optimized build
VERILATOR_PROFILE=benchmark make verilate
```

---

## ccache Best Practices

### Check ccache Status
```bash
ccache -s
```

### Clear ccache
```bash
make clean_ccache
```

### Disable ccache Temporarily
```bash
export CCACHE_DISABLE=1
make verilate
unset CCACHE_DISABLE
```

### Configure ccache Size
```bash
ccache --max-size=10G
```

---

## When All Else Fails

### Nuclear Clean
```bash
make clean_verilator_nuclear
```

This will:
- Remove all build artifacts
- Clear ccache
- Delete dependency files
- Reset to pristine state

### Report a Bug

If issue persists:
1. Create minimal reproducible example
2. Run with debug flags:
   ```bash
   VERILATOR_PROFILE=debug make verilate 2>&1 | tee build.log
   ```
3. Check Verilator version:
   ```bash
   verilator --version
   ```
4. Open issue with:
   - Error message
   - Build log
   - System info (OS, GCC version)
   - Verilator version

---

## Useful Commands

```bash
# Check build status
make -n verilate           # Dry run

# Verbose build
make verilate V=1          # Show all commands

# Check Verilator config
cat script/config/verilator.json

# Monitor build progress
watch -n 1 'ps aux | grep verilator'

# Check disk space
df -h build/

# Check memory usage
free -h

# Kill stuck builds
pkill -9 -f verilator
```

---

## Environment Variables

```bash
# Verilator
export VERILATOR_ROOT=/home/user/tools/verilator
export VERILATOR_LOG_DIR=/path/to/logs

# ccache
export CCACHE_DIR=$HOME/.ccache
export CCACHE_MAXSIZE=10G
export CCACHE_DISABLE=1  # Temporarily disable

# Build
export BUILD_JOBS=16
export MAX_CYCLES=1000000
```

---

**Last Updated:** 2025-12-16
**Verilator Version:** 5.042
**GCC Version:** 11.x
