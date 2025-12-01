#!/bin/bash

# =============================================================================
# PARAMETRIC EXCEPTION PRIORITY TEST CONFIGURATION
# =============================================================================
#
# This script demonstrates how to build and test the Ceres RTL with different
# exception priority orders and compare results against Spike.
#
# USAGE:
#   ./exception_priority_test.sh [MODE] [TEST_NAME]
#
# MODES:
#   default              - RISC-V spec-compliant default (DEBUG > MISALIGNED > ...)
#   misaligned_first     - Test with instruction misaligned highest priority
#   illegal_first        - Test with illegal instruction highest priority
#   disabled_debug       - Test with debug breakpoints disabled
#   disabled_illegal     - Test with illegal instruction disabled
#   custom               - Manual priority override (edit script)
#
# EXAMPLES:
#   ./exception_priority_test.sh default breakpoint
#   ./exception_priority_test.sh misaligned_first ma_addr
#   ./exception_priority_test.sh disabled_debug illegal
#
# =============================================================================

set -e

# Configuration
PROJECT_ROOT="/home/kerim/level-v"
BUILD_DIR="${PROJECT_ROOT}/build"
OBJ_DIR="${BUILD_DIR}/obj_dir"
TEST_RESULT_DIR="${PROJECT_ROOT}/results/logs/verilator"

# Test mode and test name
PRIORITY_MODE="${1:-default}"
TEST_NAME="${2:-breakpoint}"

# Map priority modes to Verilator defines
get_verilator_defines() {
    local mode=$1
    case $mode in
        default)
            # Default: DEBUG > MISALIGNED > ACCESS_FAULT > ILLEGAL > EBREAK > ECALL
            echo ""
            ;;
        misaligned_first)
            # Misaligned highest priority: MISALIGNED > DEBUG > ACCESS_FAULT > ILLEGAL > EBREAK > ECALL
            echo "-DEXCEPTION_PRIORITY_MISALIGNED_FIRST"
            ;;
        illegal_first)
            # Illegal highest priority: ILLEGAL > DEBUG > MISALIGNED > ACCESS_FAULT > EBREAK > ECALL
            echo "-DEXCEPTION_PRIORITY_ILLEGAL_FIRST"
            ;;
        disabled_debug)
            # Debug breakpoints disabled
            echo "-DEXCEPTION_PRIORITY_DISABLED_DEBUG"
            ;;
        disabled_illegal)
            # Illegal instruction disabled
            echo "-DEXCEPTION_PRIORITY_DISABLED_ILLEGAL"
            ;;
        custom)
            # Custom: Edit below or pass via environment
            echo "${CUSTOM_VERILATOR_DEFINES:-}"
            ;;
        *)
            echo "Unknown mode: $mode"
            exit 1
            ;;
    esac
}

# Get defines for this mode
DEFINES=$(get_verilator_defines "$PRIORITY_MODE")

echo "=========================================================================="
echo "PARAMETRIC EXCEPTION PRIORITY TEST"
echo "=========================================================================="
echo "Priority Mode:     $PRIORITY_MODE"
echo "Test Name:         $TEST_NAME"
echo "Verilator Defines: $DEFINES"
echo "=========================================================================="

# Build with specified priority mode
echo ""
echo "[1] Building RTL with priority mode: $PRIORITY_MODE"
cd "$PROJECT_ROOT"

if [ -z "$DEFINES" ]; then
    echo "Using default priority configuration..."
    make clean_obj > /dev/null 2>&1 || true
    make verilate > /dev/null 2>&1
else
    echo "Using custom defines: $DEFINES"
    # Rebuild with custom defines
    cd "$OBJ_DIR"
    make verilate_clean > /dev/null 2>&1 || true
    cd "$PROJECT_ROOT"
    VERILATOR_FLAGS="$DEFINES" make verilate > /dev/null 2>&1
fi

echo "[✓] Build successful"

# Run the test
echo ""
echo "[2] Running test: $TEST_NAME"
cd "$PROJECT_ROOT"
make "csr TEST_NAME=$TEST_NAME" 2>&1 | tail -5

# Show results
TEST_LOG="${TEST_RESULT_DIR}/rv32mi-p-${TEST_NAME}/diff.log"
if [ -f "$TEST_LOG" ]; then
    echo ""
    echo "[3] Test Results:"
    echo "=========================================================================="
    head -3 "$TEST_LOG"
    echo "=========================================================================="
    
    # Count statistics
    PERFECT=$(grep -c "^✅ MATCH" "$TEST_LOG" || echo "0")
    TOTAL=$(grep -c "^" "$TEST_LOG" 2>/dev/null | head -1 || echo "0")
    PERCENTAGE=$((PERFECT * 100 / TOTAL))
    
    echo "Perfect Matches: $PERFECT / $TOTAL ($PERCENTAGE%)"
    echo "Test Mode:       $PRIORITY_MODE"
else
    echo "Test log not found at: $TEST_LOG"
fi

echo ""
echo "=========================================================================="
echo "SPIKE COMPARISON"
echo "=========================================================================="
echo ""
echo "To compare against Spike with the same priority configuration:"
echo ""
echo "  1. Spike uses RISC-V spec-compliant priority (default mode)"
echo "  2. Run Spike simulation with same test:"
echo "     spike -p1 --hart=0 rv32mi-p-${TEST_NAME}"
echo ""
echo "  3. Compare instruction traces"
echo ""
echo "=========================================================================="
