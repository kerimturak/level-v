#!/bin/bash
# ============================================================================
# Custom UART Test Build and Run Script
# ============================================================================
# Bu script, özel C test programlarını derlemek ve çalıştırmak için kullanılır.
# Kullanım:
#   ./build_and_run_test.sh uart_hello_test
# ============================================================================

set -e  # Exit on error

# Ensure we're in the project root to avoid .lo files in unexpected places
PROJ_ROOT="/home/kerim/level-v"
cd "$PROJ_ROOT"

# Renkli çıktı için tanımlamalar
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# ============================================================================
# Konfigürasyon
# ============================================================================
TEST_NAME="${1:-uart_hello_test}"
TEST_SOURCE="${PROJ_ROOT}/sim/test/custom/${TEST_NAME}.c"
TEST_BUILD_DIR="${PROJ_ROOT}/build/tests/custom"
TEST_ELF="${TEST_BUILD_DIR}/${TEST_NAME}.elf"
TEST_BIN="${TEST_BUILD_DIR}/${TEST_NAME}.bin"
TEST_HEX="${TEST_BUILD_DIR}/${TEST_NAME}.hex"
TEST_MEM="${TEST_BUILD_DIR}/${TEST_NAME}.mem"

# Toolchain
RISCV_PREFIX="riscv32-unknown-elf"
CC="${RISCV_PREFIX}-gcc"
OBJCOPY="${RISCV_PREFIX}-objcopy"
OBJDUMP="${RISCV_PREFIX}-objdump"

# Linker script (CoreMark'tan örnek kullanalım)
LINKER_SCRIPT="${PROJ_ROOT}/subrepo/coremark/ceresv/link.ld"

# Derleme bayrakları
CFLAGS="-march=rv32imc -mabi=ilp32 -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles"
LDFLAGS="-Wl,--gc-sections"

# Startup dosyası
STARTUP_FILE="${PROJ_ROOT}/sim/test/custom/startup.s"

# ============================================================================
# Fonksiyonlar
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
    print_info "  ✓ Test source found: $TEST_SOURCE"
    
    if ! command -v "$CC" &> /dev/null; then
        print_error "RISC-V toolchain not found: $CC"
        exit 1
    fi
    print_info "  ✓ RISC-V toolchain found"
    
    if [ ! -f "$LINKER_SCRIPT" ]; then
        print_warn "Linker script not found, using default"
        # Default linker script yoksa, -Wl,-Ttext bayrakları kullanabiliriz
    fi
}

create_build_dir() {
    if [ ! -d "$TEST_BUILD_DIR" ]; then
        mkdir -p "$TEST_BUILD_DIR"
        print_info "Created build directory: $TEST_BUILD_DIR"
    fi
}

compile_test() {
    print_header "COMPILATION"
    
    # Check if startup file exists, create if not
    if [ ! -f "$STARTUP_FILE" ]; then
        print_warn "Startup file not found, creating default..."
        cat > "$STARTUP_FILE" << 'STARTUP_EOF'
.section .text._start
.globl _start

_start:
    la sp, __stack_end
    jal ra, main
    j _start

.section .bss
.align 4
__stack_start:
    .space 0x4000
__stack_end:
STARTUP_EOF
    fi
    
    local linker_opts="-Wl,-Ttext=0x80000000"
    if [ -f "$LINKER_SCRIPT" ]; then
        linker_opts="-Wl,-T${LINKER_SCRIPT}"
    fi
    
    echo -e "${YELLOW}Compiling: ${NC}${TEST_NAME}.c + startup.s"
    
    if $CC $CFLAGS $linker_opts $LDFLAGS \
        -o "$TEST_ELF" "$STARTUP_FILE" "$TEST_SOURCE" 2>&1 | tee "${TEST_BUILD_DIR}/compile.log"; then
        print_info "  ✓ Compilation successful"
        echo ""
    else
        print_error "Compilation failed!"
        echo -e "${RED}Log:${NC}"
        cat "${TEST_BUILD_DIR}/compile.log"
        exit 1
    fi
}

generate_binaries() {
    print_header "BINARY GENERATION"
    
    # Binary
    print_info "Generating binary..."
    $OBJCOPY -O binary "$TEST_ELF" "$TEST_BIN"
    print_info "  ✓ Binary: $TEST_BIN"
    
    # Hex (Verilog objcopy format)
    print_info "Generating Verilog HEX..."
    $OBJCOPY -O verilog "$TEST_ELF" "$TEST_HEX"
    print_info "  ✓ Hex: $TEST_HEX"
    
    # Memory file using project's hex_to_mem.py script
    print_info "Generating memory file (32-bit words)..."
    if python3 "${PROJ_ROOT}/script/python/makefile/hex_to_mem.py" "$TEST_HEX" "$TEST_MEM"; then
        print_info "  ✓ Memory file: $TEST_MEM"
    else
        print_error "Failed to generate memory file"
        exit 1
    fi
    echo ""
}

show_disassembly() {
    print_header "DISASSEMBLY PREVIEW"
    
    $OBJDUMP -d "$TEST_ELF" | head -50
    echo ""
    echo -e "${YELLOW}(Full disassembly saved to: ${TEST_BUILD_DIR}/${TEST_NAME}.disass)${NC}"
    $OBJDUMP -d "$TEST_ELF" > "${TEST_BUILD_DIR}/${TEST_NAME}.disass"
}

show_sizes() {
    print_header "SIZE INFORMATION"
    
    size "$TEST_ELF"
    echo ""
}

run_simulation() {
    print_header "RUNNING SIMULATION"
    
    echo -e "${YELLOW}Simulating with Verilator...${NC}"
    
    cd "$PROJ_ROOT"
    
    # Run directly with Verilator executable
    # Format: Vceres_wrapper <max_cycles> +INIT_FILE=<file>
    local VERILATOR_BIN="./build/obj_dir/Vceres_wrapper"
    local MAX_CYCLES=100000
    
    if [ ! -f "$VERILATOR_BIN" ]; then
        print_warn "Verilator executable not found. Building..."
        if ! make verilate > /dev/null 2>&1; then
            print_error "Failed to build Verilator"
            return 1
        fi
    fi
    
    echo -e "${YELLOW}Running: ${NC}$VERILATOR_BIN $MAX_CYCLES +INIT_FILE=$TEST_MEM"
    
    if timeout 60 "$VERILATOR_BIN" "$MAX_CYCLES" "+INIT_FILE=$TEST_MEM" 2>&1 | tee "${TEST_BUILD_DIR}/sim.log"; then
        print_info "  ✓ Simulation completed"
        echo ""
        
        # Check UART output
        if [ -f "$PROJ_ROOT/uart_output.log" ]; then
            print_header "UART OUTPUT"
            cat "$PROJ_ROOT/uart_output.log"
            echo ""
        fi
    else
        SIM_EXIT=$?
        if [ $SIM_EXIT -eq 124 ]; then
            print_warn "Simulation timed out (60s)"
        else
            print_warn "Simulation finished with code $SIM_EXIT"
        fi
        
        # Still show UART output if any
        if [ -f "$PROJ_ROOT/uart_output.log" ]; then
            print_header "UART OUTPUT (PARTIAL)"
            cat "$PROJ_ROOT/uart_output.log"
            echo ""
        fi
    fi
}

print_summary() {
    print_header "BUILD SUMMARY"
    
    echo -e "${GREEN}Test Name:${NC}      $TEST_NAME"
    echo -e "${GREEN}Source:${NC}         $TEST_SOURCE"
    echo -e "${GREEN}ELF:${NC}            $TEST_ELF"
    echo -e "${GREEN}Binary:${NC}         $TEST_BIN"
    echo -e "${GREEN}Memory:${NC}         $TEST_MEM"
    echo -e "${GREEN}Disassembly:${NC}    ${TEST_BUILD_DIR}/${TEST_NAME}.disass"
    echo -e "${GREEN}Compile Log:${NC}    ${TEST_BUILD_DIR}/compile.log"
    echo -e "${GREEN}Simulation Log:${NC}  ${TEST_BUILD_DIR}/sim.log"
    echo ""
    
    # File sizes
    if [ -f "$TEST_ELF" ]; then
        echo -e "${YELLOW}File sizes:${NC}"
        ls -lh "$TEST_ELF" "$TEST_BIN" "$TEST_MEM" 2>/dev/null | awk '{print "  " $9 " (" $5 ")"}'
    fi
    echo ""
}

# ============================================================================
# Main Execution
# ============================================================================

print_header "Custom UART Test Builder"

check_prerequisites
create_build_dir
compile_test
generate_binaries
show_sizes
show_disassembly

# Auto-run simulation (unless -n flag)
AUTO_RUN=1
if [[ "$2" == "-n" || "$2" == "--no-run" ]]; then
    AUTO_RUN=0
fi

if [ $AUTO_RUN -eq 1 ]; then
    run_simulation
fi

print_summary

print_info "Build completed successfully!"
