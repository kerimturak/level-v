# Shell Scripts - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Simülasyon Scripts](#simülasyon-scripts)
3. [Build Scripts](#build-scripts)
4. [Config Parsers](#config-parsers)
5. [Utility Scripts](#utility-scripts)

---

## Genel Bakış

### Dizin Yapısı

```
script/shell/
├── run_verilator.sh           # Verilator simulation runner
├── build_custom_test.sh       # Custom test builder
├── parse_verilator_config.sh  # Verilator JSON config parser
├── parse_modelsim_config.sh   # ModelSim JSON config parser
├── parse_test_config.sh       # Test suite config parser
├── init_ceres_structure.sh    # Proje initialization
├── uart_test_quickstart.sh    # UART test quick start
├── exception_priority_test.sh # Exception priority test
└── PARAMETRIC_PRIORITY_QUICKSTART.sh  # Priority quick start
```

### Ortak Özellikler

- **Shell**: Bash/Zsh compatible
- **Error Handling**: `set -euo pipefail`
- **Colored Output**: ANSI renk kodları
- **Logging**: Consistent log format
- **Signal Handling**: Cleanup on SIGINT/SIGTERM

---

## Simülasyon Scripts

### run_verilator.sh - Verilator Runner

**Dosya:** `script/shell/run_verilator.sh`

#### Amaç

Verilator simülasyonunu kontrollü bir şekilde çalıştırır. MEM dosyası resolution, logging, timeout ve signal handling sağlar.

#### Kullanım

```bash
# Basic usage
TEST_NAME=rv32ui-p-add ./run_verilator.sh

# With explicit MEM file
MEM_FILE=/path/to/test.mem ./run_verilator.sh

# With options
MAX_CYCLES=100000 TIMEOUT=60 VERBOSE=1 ./run_verilator.sh
```

#### Environment Variables

| Variable | Default | Açıklama |
|----------|---------|----------|
| `TEST_NAME` | (required) | Test adı (MEM file resolution için) |
| `MEM_FILE` | auto | Explicit MEM file path |
| `MAX_CYCLES` | 100000 | Maximum simulation cycles |
| `TIMEOUT` | 0 | Timeout in seconds (0=disabled) |
| `VERILATOR_LOG_DIR` | auto | Log output directory |
| `VERILATOR_THREADS` | 1 | Thread count for multi-threaded sim |
| `VERBOSE` | 0 | Verbose output |
| `QUIET` | 0 | Suppress info messages |

#### Script Yapısı

```bash
#!/usr/bin/env bash
set -euo pipefail

# Color codes
readonly RED='\033[0;31m'
readonly GREEN='\033[0;32m'
readonly YELLOW='\033[1;33m'
readonly CYAN='\033[0;36m'
readonly RESET='\033[0m'

# -----------------------------------------
# Path Configuration
# -----------------------------------------
ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
BUILD_DIR="${BUILD_DIR:-$ROOT_DIR/build}"
OBJ_DIR="${OBJ_DIR:-$BUILD_DIR/obj_dir}"
RUN_BIN="${RUN_BIN:-$OBJ_DIR/Vceres_wrapper}"

# -----------------------------------------
# Helper Functions
# -----------------------------------------
log_info() {
  [[ "$QUIET" == "1" ]] && return
  echo -e "${CYAN}[INFO]${RESET} $*"
}

log_success() {
  echo -e "${GREEN}[SUCCESS]${RESET} $*"
}

log_warn() {
  echo -e "${YELLOW}[WARNING]${RESET} $*" >&2
}

log_error() {
  echo -e "${RED}[ERROR]${RESET} $*" >&2
}

# Cleanup on signal
cleanup() {
  local exit_code=$?
  if [[ -n "${SIM_PID:-}" ]] && kill -0 "$SIM_PID" 2>/dev/null; then
    log_warn "Terminating simulation (PID: $SIM_PID)..."
    kill -TERM "$SIM_PID" 2>/dev/null || true
    wait "$SIM_PID" 2>/dev/null || true
  fi
  exit "$exit_code"
}

trap cleanup INT TERM

# -----------------------------------------
# Log Directory Setup
# -----------------------------------------
if [ -z "${VERILATOR_LOG_DIR:-}" ]; then
  VERILATOR_LOG_DIR="$RESULTS_DIR/logs/verilator/$TEST_NAME"
fi
mkdir -p "$VERILATOR_LOG_DIR"

# -----------------------------------------
# MEM File Resolution
# -----------------------------------------
resolve_mem_file() {
  if [ -n "${MEM_FILE:-}" ] && [ -f "$MEM_FILE" ]; then
    echo "$MEM_FILE"
    return 0
  fi
  
  # Search in known locations
  local search_paths=(
    "$BUILD_DIR/tests/riscv-tests/mem/${TEST_NAME}.mem"
    "$BUILD_DIR/tests/riscv-arch-test/mem/${TEST_NAME}.mem"
    "$BUILD_DIR/tests/imperas/mem/${TEST_NAME}.mem"
    "$BUILD_DIR/tests/coremark/${TEST_NAME}.mem"
    "$BUILD_DIR/tests/custom/${TEST_NAME}.mem"
  )
  
  for path in "${search_paths[@]}"; do
    if [ -f "$path" ]; then
      echo "$path"
      return 0
    fi
  done
  
  log_error "MEM file not found for test: $TEST_NAME"
  return 1
}

# -----------------------------------------
# Main Execution
# -----------------------------------------
main() {
  log_info "Starting Verilator simulation..."
  log_info "Test: $TEST_NAME"
  log_info "Max cycles: $MAX_CYCLES"
  
  # Resolve MEM file
  MEM_FILE=$(resolve_mem_file)
  log_info "MEM file: $MEM_FILE"
  
  # Build command
  local cmd="$RUN_BIN"
  cmd+=" +mem=$MEM_FILE"
  cmd+=" +max_cycles=$MAX_CYCLES"
  cmd+=" +log_dir=$VERILATOR_LOG_DIR"
  
  # Run simulation
  local start_time=$(date +%s)
  
  if [ "$TIMEOUT" -gt 0 ]; then
    timeout "$TIMEOUT" $cmd &
    SIM_PID=$!
  else
    $cmd &
    SIM_PID=$!
  fi
  
  wait "$SIM_PID"
  local exit_code=$?
  
  local end_time=$(date +%s)
  local elapsed=$((end_time - start_time))
  
  # Generate summary
  generate_summary "$exit_code" "$elapsed"
  
  return "$exit_code"
}

generate_summary() {
  local exit_code=$1
  local elapsed=$2
  
  cat > "$VERILATOR_LOG_DIR/summary.json" <<EOF
{
  "test_name": "$TEST_NAME",
  "exit_code": $exit_code,
  "elapsed_seconds": $elapsed,
  "max_cycles": $MAX_CYCLES,
  "mem_file": "$MEM_FILE",
  "timestamp": "$(date -Iseconds)"
}
EOF
  
  if [ "$exit_code" -eq 0 ]; then
    log_success "Simulation completed in ${elapsed}s"
  else
    log_error "Simulation failed with exit code $exit_code"
  fi
}

main "$@"
```

---

## Build Scripts

### build_custom_test.sh - Custom Test Builder

**Dosya:** `script/shell/build_custom_test.sh`

#### Amaç

Custom C test programlarını derler. Startup, linker script ve output dosyalarını oluşturur.

#### Kullanım

```bash
# Build and optionally run
./build_custom_test.sh uart_hello_test

# Build only
./build_custom_test.sh uart_hello_test --no-run
```

#### Script Yapısı

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
    print_header "CERES Custom Test Builder"
    
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

### parse_verilator_config.sh - Verilator Config Parser

**Dosya:** `script/shell/parse_verilator_config.sh`

#### Amaç

`verilator.json` dosyasını parse edip Makefile include edilebilir format üretir.

#### Kullanım

```bash
# Generate makefile include
./parse_verilator_config.sh --make > .verilator_config.mk

# With profile
./parse_verilator_config.sh --make --profile fast > .verilator_config.mk

# Show parsed values
./parse_verilator_config.sh --show
```

#### Script Yapısı

```bash
#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CONFIG_FILE="${SCRIPT_DIR}/../config/verilator.json"
LOCAL_CONFIG="${SCRIPT_DIR}/../config/verilator.local.json"

# Check jq availability
if ! command -v jq &> /dev/null; then
    echo "Error: jq is required but not installed" >&2
    exit 1
fi

# Parse arguments
OUTPUT_MODE="make"
PROFILE=""

while [[ $# -gt 0 ]]; do
    case $1 in
        --make) OUTPUT_MODE="make"; shift ;;
        --show) OUTPUT_MODE="show"; shift ;;
        --profile) PROFILE="$2"; shift 2 ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# Merge configs
if [ -f "$LOCAL_CONFIG" ]; then
    CONFIG=$(jq -s '.[0] * .[1]' "$CONFIG_FILE" "$LOCAL_CONFIG")
else
    CONFIG=$(cat "$CONFIG_FILE")
fi

# Apply profile if specified
if [ -n "$PROFILE" ]; then
    PROFILE_CONFIG=$(echo "$CONFIG" | jq ".profiles.$PROFILE // {}")
    CONFIG=$(echo "$CONFIG" | jq ". * $PROFILE_CONFIG")
fi

# Extract values
get_value() {
    echo "$CONFIG" | jq -r "$1 // empty"
}

# Output based on mode
case $OUTPUT_MODE in
    make)
        echo "# Auto-generated from verilator.json"
        echo "CFG_MAX_CYCLES := $(get_value '.simulation.max_cycles')"
        echo "CFG_TIMEOUT := $(get_value '.simulation.timeout')"
        echo "CFG_BUILD_MODE := $(get_value '.build.mode')"
        echo "CFG_OPT_LEVEL := $(get_value '.build.opt_level')"
        echo "CFG_TRACE_ENABLED := $(get_value '.trace.enabled')"
        echo "CFG_TRACE_FORMAT := $(get_value '.trace.format')"
        echo "CFG_TRACE_DEPTH := $(get_value '.trace.depth')"
        echo "CFG_COVERAGE_ENABLED := $(get_value '.coverage.enabled')"
        echo "CFG_LOG_COMMIT := $(get_value '.logging.commit_trace')"
        echo "CFG_LOG_PIPELINE := $(get_value '.logging.pipeline_log')"
        ;;
    show)
        echo "Verilator Configuration:"
        echo "========================"
        echo "Simulation:"
        echo "  max_cycles: $(get_value '.simulation.max_cycles')"
        echo "  timeout: $(get_value '.simulation.timeout')"
        echo "Build:"
        echo "  mode: $(get_value '.build.mode')"
        echo "  opt_level: $(get_value '.build.opt_level')"
        echo "Trace:"
        echo "  enabled: $(get_value '.trace.enabled')"
        echo "  format: $(get_value '.trace.format')"
        ;;
esac
```

### parse_modelsim_config.sh - ModelSim Config Parser

**Dosya:** `script/shell/parse_modelsim_config.sh`

Benzer yapıda, `modelsim.json` için config parsing.

### parse_test_config.sh - Test Config Parser

**Dosya:** `script/shell/parse_test_config.sh`

Test suite JSON config'lerini parse eder.

---

## Utility Scripts

### init_ceres_structure.sh - Proje Initialization

**Dosya:** `script/shell/init_ceres_structure.sh`

#### Amaç

Yeni CERES projesi için dizin yapısını ve template dosyalarını oluşturur.

#### Kullanım

```bash
./init_ceres_structure.sh /path/to/new/project
```

#### Oluşturulan Yapı

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
│   ├── makefiles/
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

### uart_test_quickstart.sh - UART Test Quick Start

**Dosya:** `script/shell/uart_test_quickstart.sh`

#### Amaç

UART test programını hızlıca derleyip çalıştırır.

#### Kullanım

```bash
./uart_test_quickstart.sh
```

### exception_priority_test.sh - Exception Priority Test

**Dosya:** `script/shell/exception_priority_test.sh`

#### Amaç

Parametrik exception priority sistemini test eder.

#### Kullanım

```bash
./exception_priority_test.sh
```

---

## Ortak Patterns

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

## Özet

Shell scripts:

1. **run_verilator.sh**: Comprehensive Verilator runner
2. **build_custom_test.sh**: Custom C test builder
3. **Config Parsers**: JSON → Makefile variable conversion
4. **Utility Scripts**: Initialization, quick starts
5. **Error Handling**: Robust error and signal handling
6. **Logging**: Consistent colored output
7. **Portability**: Bash/Zsh compatible
