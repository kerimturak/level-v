#!/bin/bash

# =============================================================================
# PARAMETRIC EXCEPTION PRIORITY QUICK START GUIDE
# =============================================================================
#
# This script demonstrates the parametric exception priority system that allows
# testing different exception priority orders against Spike reference model.
#
# QUICK START:
#
# 1. View current configuration:
#    grep "EXC_PRIORITY" rtl/pkg/ceres_param.sv
#
# 2. Build with default priority (RISC-V spec-compliant):
#    make clean_obj && make verilate
#
# 3. Test and compare against Spike:
#    make csr TEST_NAME=breakpoint
#    cat results/logs/verilator/rv32mi-p-breakpoint/diff.log | head -10
#
# 4. Create custom priority configuration:
#    - Edit rtl/pkg/ceres_param.sv
#    - Change EXC_PRIORITY_* parameters
#    - Rebuild: make clean_obj && make verilate
#    - Test: make csr TEST_NAME=breakpoint
#
# =============================================================================

echo "=================================================================="
echo "PARAMETRIC EXCEPTION PRIORITY - QUICK START"
echo "=================================================================="
echo ""
echo "📋 RISC-V Specification Exception Priority (highest to lowest):"
echo ""
echo "   1. Instruction address breakpoint (debug trigger)"
echo "   2. Instruction address misaligned"
echo "   3. Instruction access fault"
echo "   4. Illegal instruction"
echo "   5. Breakpoint/EBREAK instruction"
echo "   6. ECALL"
echo ""
echo "=================================================================="
echo ""

# Show current configuration
echo "📍 Current configuration in rtl/pkg/ceres_param.sv:"
echo ""
grep -A 6 "^  localparam exc_priority_t EXC_PRIORITY" /home/kerim/level-v/rtl/pkg/ceres_param.sv | head -20
echo ""

echo "=================================================================="
echo "💡 USAGE EXAMPLES"
echo "=================================================================="
echo ""
echo "Example 1: Build with default priority (recommended for Spike match)"
echo "  $ make clean_obj && make verilate && make csr TEST_NAME=breakpoint"
echo ""
echo "Example 2: Modify priority order"
echo "  1. Edit rtl/pkg/ceres_param.sv"
echo "  2. Change: localparam exc_priority_t EXC_PRIORITY_... = PRIORITY_X;"
echo "  3. Rebuild: make clean_obj && make verilate"
echo "  4. Test: make csr TEST_NAME=breakpoint"
echo ""
echo "Example 3: Disable specific exception"
echo "  $ Edit: localparam exc_priority_t EXC_PRIORITY_ILLEGAL = PRIORITY_DISABLED;"
echo "  $ make clean_obj && make verilate"
echo "  $ make csr TEST_NAME=illegal"
echo ""

echo "=================================================================="
echo "🔧 AVAILABLE PRIORITY LEVELS"
echo "=================================================================="
echo ""
echo "  PRIORITY_1       = Highest (checked first)"
echo "  PRIORITY_2       = Very high"
echo "  PRIORITY_3       = High"
echo "  PRIORITY_4       = Medium"
echo "  PRIORITY_5       = Low"
echo "  PRIORITY_6       = Very low"
echo "  PRIORITY_7       = Lowest (checked last)"
echo "  PRIORITY_DISABLED = Exception disabled (not checked)"
echo ""

echo "=================================================================="
echo "📁 RELATED FILES"
echo "=================================================================="
echo ""
echo "  rtl/pkg/ceres_param.sv"
echo "    └─ Priority configuration (edit here)"
echo ""
echo "  rtl/core/stage01_fetch/fetch.sv"
echo "    └─ Exception detection logic (uses priorities)"
echo ""
echo "  rtl/include/exception_priority.svh"
echo "    └─ Alternative configuration templates"
echo ""
echo "  docs/PARAMETRIC_EXCEPTION_PRIORITY.md"
echo "    └─ Full documentation"
echo ""
echo "  script/exception_priority_test.sh"
echo "    └─ Automated test script"
echo ""

echo "=================================================================="
echo "📊 TEST RESULTS"
echo "=================================================================="
echo ""
echo "Default CSR test results (with spec-compliant priority):"
echo ""
grep -E "PASSED|FAILED" /home/kerim/level-v/results/logs/verilator/rv32mi-p-*/diff.log 2>/dev/null | head -16 | while read line; do
    if echo "$line" | grep -q "passed\|PASSED"; then
        echo "  ✓ $(basename $(dirname $line) | sed 's|diff.log||')"
    else
        echo "  ✗ $(basename $(dirname $line) | sed 's|diff.log||')"
    fi
done
echo ""

echo "=================================================================="
echo "🚀 NEXT STEPS"
echo "=================================================================="
echo ""
echo "1. Read full documentation:"
echo "   cat docs/PARAMETRIC_EXCEPTION_PRIORITY.md"
echo ""
echo "2. Test with different priorities:"
echo "   # Edit rtl/pkg/ceres_param.sv, then:"
echo "   make clean_obj && make verilate && make csr CLEAN_LOGS=1"
echo ""
echo "3. Compare specific test against Spike:"
echo "   spike -p1 --hart=0 subrepo/riscv-tests/isa/rv32mi-p-breakpoint"
echo ""
echo "=================================================================="
echo ""
