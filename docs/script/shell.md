# Shell Scripts — Technical Documentation

## Contents

1. [Overview](#overview)
2. [Simulation Scripts](#simulation-scripts)
3. [Build Scripts](#build-scripts)
4. [Config Parsers](#config-parsers)
5. [Utility Scripts](#utility-scripts)

---

## Overview

### Directory Layout

```
script/shell/
├── parse_test_conf.sh         # Test .conf → Makefile fragment
├── build_level_custom_c_test.sh       # Custom C test build + optional run
├── scaffold_level_project_skeleton.sh    # Empty Level project skeleton
├── guide_level_uart_custom_test.sh    # UART custom test guide (stdout)
├── run_level_exception_priority_tests.sh # Exception priority matrix
├── guide_exception_priority_parametric.sh  # Parametric priority summary
└── …                          # OpenLane / setup scripts
```

### Common Features

- **Shell**: Bash/Zsh compatible
- **Error Handling**: `set -euo pipefail`
- **Colored Output**: ANSI color codes
- **Logging**: Consistent log format
- **Signal Handling**: Cleanup on SIGINT/SIGTERM

---

## Simulation Scripts

### Verilator simulation (root makefile)

**Note:** `script/shell/run_verilator.sh` was removed; the flow uses the root `makefile` (`make verilate`, `make run`, `TEST_CONFIG=…`).

Examples:

```bash
make run T=rv32ui-p-add
make verilate TEST_CONFIG=isa
```

Test profiles: `script/config/tests/*.conf` and `parse_test_conf.sh`.

## Build Scripts

### build_level_custom_c_test.sh - Custom Test Builder

**File:** `script/shell/build_level_custom_c_test.sh`

#### Purpose

Builds custom C test programs. Creates startup, linker script, and output artifacts.

#### Usage

```bash
# Build and optionally run
./build_level_custom_c_test.sh uart_hello_test

# Build only
./build_level_custom_c_test.sh uart_hello_test --no-run
```

#### Script Structure

```bash
#!/bin/bash
set -e

# Ensure we're in project root
PROJ_ROOT="/home/kerim/level-v"
cd "$PROJ_ROOT"

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m'

# ============================================================================
# Configuration
# ============================================================================
TEST_NAME="${1:-uart_hello_test}"
TEST_SOURCE="${PROJ_ROOT}/sim/test/custom/${TEST_NAME}.c"
TEST_BUILD_DIR="${PROJ_ROOT}/build/tests/custom"

# Output files
TEST_ELF="${TEST_BUILD_DIR}/${TEST_NAME}.elf"
TEST_BIN="${TEST_BUILD_DIR}/${TEST_NAME}.bin"
TEST_HEX="${TEST_BUILD_DIR}/${TEST_NAME}.hex"
TEST_MEM="${TEST_BUILD_DIR}/${TEST_NAME}.mem"
TEST_DUMP="${TEST_BUILD_DIR}/${TEST_NAME}.dump"

# Toolchain
RISCV_PREFIX="riscv32-unknown-elf"
CC="${RISCV_PREFIX}-gcc"
OBJCOPY="${RISCV_PREFIX}-objcopy"
OBJDUMP="${RISCV_PREFIX}-objdump"

# Linker script
LINKER_SCRIPT="${PROJ_ROOT}/env/custom/link.ld"

# Compiler flags
CFLAGS="-march=rv32imc -mabi=ilp32 -static -mcmodel=medany"
CFLAGS+=" -fvisibility=hidden -nostdlib -nostartfiles"
LDFLAGS="-Wl,--gc-sections"

# Startup file
STARTUP_FILE="${PROJ_ROOT}/sim/test/custom/startup.s"

# ============================================================================
# Functions
# ============================================================================

print_header() {
    echo -e "${BLUE}╔════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${BLUE}║${NC}  $1"
    echo -e "${BLUE}╚════════════════════════════════════════════════════════════╝${NC}"
}

print_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

print_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

check_prerequisites() {
    print_info "Checking prerequisites..."
    
    if [ ! -f "$TEST_SOURCE" ]; then
        print_error "Test source not found: $TEST_SOURCE"
        exit 1
    fi
    
    if ! command -v "$CC" &> /dev/null; then
        print_error "Compiler not found: $CC"
        exit 1
    fi
    
    print_info "  ✓ Prerequisites OK"
}

compile_test() {
    print_header "Compiling: $TEST_NAME"
    
    mkdir -p "$TEST_BUILD_DIR"
    
    # Compile
    print_info "Compiling C source..."
    $CC $CFLAGS -c "$TEST_SOURCE" -o "${TEST_BUILD_DIR}/${TEST_NAME}.o"
    
    # Compile startup
    print_info "Compiling startup..."
    $CC $CFLAGS -c "$STARTUP_FILE" -o "${TEST_BUILD_DIR}/startup.o"
    
    # Link
    print_info "Linking..."
    $CC $CFLAGS $LDFLAGS -T "$LINKER_SCRIPT" \
        "${TEST_BUILD_DIR}/startup.o" \
        "${TEST_BUILD_DIR}/${TEST_NAME}.o" \
        -o "$TEST_ELF"
    
    print_info "  ✓ ELF created: $TEST_ELF"
}

generate_outputs() {
    print_header "Generating output files"
    
    # Binary
    print_info "Creating binary..."
    $OBJCOPY -O binary "$TEST_ELF" "$TEST_BIN"
    
    # HEX
    print_info "Creating HEX..."
    $OBJCOPY -O verilog "$TEST_ELF" "$TEST_HEX"
    
    # MEM (for Verilog $readmemh)
    print_info "Creating MEM..."
    python3 "${PROJ_ROOT}/script/python/elf_to_mem.py" \
        --in "$TEST_BIN" \
        --out "$TEST_MEM" \
        --block-bytes 16
    
    # Disassembly
    print_info "Creating disassembly..."
    $OBJDUMP -d -S "$TEST_ELF" > "$TEST_DUMP"
    
    print_info "  ✓ All outputs generated"
}

print_summary() {
    print_header "Build Summary"
    echo -e "  ELF:  $TEST_ELF"
    echo -e "  BIN:  $TEST_BIN"
    echo -e "  HEX:  $TEST_HEX"
    echo -e "  MEM:  $TEST_MEM"
    echo -e "  DUMP: $TEST_DUMP"
    
    # File sizes
    echo -e ""
    echo -e "  Sizes:"
    ls -lh "$TEST_ELF" | awk '{print "    ELF: " $5}'
    ls -lh "$TEST_BIN" | awk '{print "    BIN: " $5}'
}

# ============================================================================
# Main
# ============================================================================

main() {
    print_header "Level Custom Test Builder"
    
    check_prerequisites
    compile_test
    generate_outputs
    print_summary
    
    print_info "Build complete!"
}

main "$@"
```

---

## Config Parsers
Verilator / ModelSim JSON files (`script/config/verilator.json`, `modelsim.json`) are handled inside the root makefile; there are no separate `parse_*_config.sh` scripts.

### parse_test_conf.sh — Test profile parser

**File:** `script/shell/parse_test_conf.sh`

Merges `script/config/tests/default.conf` and `<profile>.conf`; with `--make` emits `CFG_*` and `+define+` lines (makefile writes `build/.test_config_<name>.mk`).

```bash
./script/shell/parse_test_conf.sh --list
./script/shell/parse_test_conf.sh isa --make
```

Details: [script/config/tests/README.md](../../script/config/tests/README.md).

---

## Utility Scripts

### scaffold_level_project_skeleton.sh — Project initialization

**File:** `script/shell/scaffold_level_project_skeleton.sh`

#### Purpose

Creates directory layout and template files for a new Level project. It creates a skeleton named `level-riscv/` in the current working directory (no CLI arguments; `PROJECT_NAME` is set inside the script).

#### Usage

```bash
cd /path/where/parent/should/live
./script/shell/scaffold_level_project_skeleton.sh
# → ./level-riscv/ ...
```

#### Created Layout

```
new_project/
├── rtl/
│   ├── core/
│   ├── include/
│   ├── periph/
│   ├── pkg/
│   ├── ram/
│   ├── tracer/
│   ├── util/
│   └── wrapper/
├── sim/
│   ├── tb/
│   ├── test/
│   └── do/
├── script/
│   ├── makefiles/     # optional local.mk
│   ├── python/
│   └── shell/
├── build/
├── results/
├── docs/
├── env/
├── subrepo/
├── makefile
└── README.md
```

### guide_level_uart_custom_test.sh — UART custom C test guide

**File:** `script/shell/guide_level_uart_custom_test.sh`

#### Purpose

Prints a short guide to stdout for writing / building / simulating a custom UART C test (it does not run tests; it shows `build_level_custom_c_test.sh` and `make` commands).

#### Usage

```bash
./script/shell/guide_level_uart_custom_test.sh
```

### run_level_exception_priority_tests.sh — Exception priority matrix

**File:** `script/shell/run_level_exception_priority_tests.sh`

#### Purpose

Runs a `make`-based regression / comparison flow for different `level_param` priority modes and CSR tests.

#### Usage

```bash
./script/shell/run_level_exception_priority_tests.sh
```

### guide_exception_priority_parametric.sh — Parametric priority guide

**File:** `script/shell/guide_exception_priority_parametric.sh`

Summary: prints exception priority parameters from `rtl/pkg/level_param.sv` and validation steps to the terminal.

```bash
./script/shell/guide_exception_priority_parametric.sh
```

---

## Common Patterns

### Error Handling

```bash
#!/usr/bin/env bash
set -euo pipefail

# -e: Exit on error
# -u: Error on undefined variable
# -o pipefail: Exit on pipe failure

# Custom error handler
trap 'echo "Error on line $LINENO"; exit 1' ERR
```

### Logging Functions

```bash
log_info()    { echo -e "\033[0;36m[INFO]\033[0m $*"; }
log_success() { echo -e "\033[0;32m[SUCCESS]\033[0m $*"; }
log_warn()    { echo -e "\033[1;33m[WARNING]\033[0m $*" >&2; }
log_error()   { echo -e "\033[0;31m[ERROR]\033[0m $*" >&2; }
```

### Signal Handling

```bash
cleanup() {
    # Kill background processes
    # Remove temp files
    # Restore state
    exit "${1:-0}"
}

trap 'cleanup 130' INT
trap 'cleanup 143' TERM
```

### Path Resolution

```bash
# Script directory
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# Project root
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"

# Resolve relative path
realpath() {
    cd "$(dirname "$1")" && pwd -P
}
```

---

## Summary

Shell scripts:

1. **Root makefile**: Verilator build and simulation
2. **parse_test_conf.sh**: Test `.conf` → Makefile fragment
3. **build_level_custom_c_test.sh**: Custom C test builder
4. **Utility scripts**: Initialization, quick starts, OpenLane helpers
5. **Error Handling**: Robust error and signal handling
6. **Logging**: Consistent colored output
7. **Portability**: Bash/Zsh compatible
