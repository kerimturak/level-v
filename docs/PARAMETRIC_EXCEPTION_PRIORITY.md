# Parametric Exception Priority Configuration

## Overview

The Ceres RISC-V core now supports **parametric exception priority configuration**. This allows testing different exception priority orders against the Spike simulator to validate compliance with the RISC-V Privileged Specification.

## RISC-V Specification Background

The RISC-V Privileged ISA Specification (Section 3.1.15 - Machine Cause Register) defines the following synchronous exception priority order (highest to lowest):

### Official Priority Order (Spec Compliant)

1. **Instruction address breakpoint** (cause 3, debug trigger)
2. **Instruction address misaligned** (cause 0)
3. **Instruction access fault** (cause 1)
4. **Illegal instruction** (cause 2)
5. **Breakpoint/EBREAK** (cause 3, from EBREAK/C.EBREAK instruction)
6. **Load/store/AMO address breakpoint** (cause 3, debug trigger)
7. **Load/store/AMO address misaligned** (cause 4, 6 - implementation-defined priority)
8. **Load/store/AMO access fault** (cause 5, 7)
9. **Environment call (ECALL)** (cause 8, 9, 10, 11 - depends on privilege mode)

### Important Notes

- **Cause 3 is shared** between multiple exception types with different priorities
- **Implementation-defined**: Load/store/AMO misaligned exceptions can have higher OR lower priority than page-fault/access-fault exceptions
- **Debug Mode** has special priority considerations as per RISC-V Debug Specification

## Current Ceres Implementation

The fetch pipeline in `rtl/core/stage01_fetch/fetch.sv` uses parametric exception detection. The default order follows the RISC-V specification:

```
DEBUG_BREAKPOINT (hardware trigger)
  ↓
INSTR_MISALIGNED
  ↓
INSTR_ACCESS_FAULT
  ↓
ILLEGAL_INSTRUCTION
  ↓
EBREAK (software breakpoint)
  ↓
ECALL
```

## Configuration System

### Parametric Priority Levels

Eight priority levels are defined in `rtl/pkg/ceres_param.sv`:

```systemverilog
typedef enum logic [4:0] {
    PRIORITY_1,           // Highest priority (checked first)
    PRIORITY_2,
    PRIORITY_3,
    PRIORITY_4,
    PRIORITY_5,
    PRIORITY_6,
    PRIORITY_7,           // Lowest priority (checked last)
    PRIORITY_DISABLED     // Exception disabled
} exc_priority_t;
```

### Configuration Macros (ceres_param.sv)

Default assignments (spec-compliant):

```systemverilog
localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_1;
localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_2;
localparam exc_priority_t EXC_PRIORITY_INSTR_ACCESS_FAULT = PRIORITY_3;
localparam exc_priority_t EXC_PRIORITY_ILLEGAL = PRIORITY_4;
localparam exc_priority_t EXC_PRIORITY_EBREAK = PRIORITY_5;
localparam exc_priority_t EXC_PRIORITY_ECALL = PRIORITY_6;
```

### Priority Check Function

Helper function in `ceres_param.sv`:

```systemverilog
function automatic logic check_exc_priority(
    input exc_priority_t exc_pri,
    input exc_priority_t min_pri
);
    return (exc_pri <= min_pri) && (exc_pri != PRIORITY_DISABLED);
endfunction
```

## Usage Examples

### Example 1: Default (Spec-Compliant) Build

```bash
cd /home/kerim/level-v
make verilate
make csr TEST_NAME=breakpoint
```

This builds with the RISC-V spec-compliant exception priority order.

### Example 2: Custom Priority - Disable Debug Breakpoints

Edit `rtl/pkg/ceres_param.sv`:

```systemverilog
localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_DISABLED;
```

Then rebuild:

```bash
make clean_obj
make verilate
make csr TEST_NAME=breakpoint
```

### Example 3: Custom Priority - Swap Misaligned and Breakpoint

Edit `rtl/pkg/ceres_param.sv`:

```systemverilog
localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_2;
localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_1;
```

Rebuild and test:

```bash
make clean_obj
make verilate
make csr TEST_NAME=ma_fetch
```

## Using Verilog Defines (Verilator)

For runtime configuration without modifying source files, use Verilator's `-D` flag.

### In Makefile

```makefile
# Define custom priority mode
PRIORITY_MODE ?= default

ifeq ($(PRIORITY_MODE),disabled_debug)
    VERILATOR_FLAGS += -DEXC_PRIORITY_DEBUG_BREAKPOINT=PRIORITY_DISABLED
endif

ifeq ($(PRIORITY_MODE),illegal_first)
    VERILATOR_FLAGS += \
        -DEXC_PRIORITY_ILLEGAL=PRIORITY_1 \
        -DEXC_PRIORITY_DEBUG_BREAKPOINT=PRIORITY_2
endif
```

### Command Line

```bash
verilator -DEXC_PRIORITY_ILLEGAL=PRIORITY_DISABLED \
          -DEXC_PRIORITY_DEBUG_BREAKPOINT=PRIORITY_1 \
          rtl/...
```

## Testing Against Spike

### Step 1: Build Default Configuration

```bash
cd /home/kerim/level-v
make verilate        # Default RISC-V spec-compliant priority
make csr TEST_NAME=breakpoint
```

### Step 2: Compare with Spike

```bash
# Run Spike with same test
spike -p1 --hart=0 /path/to/rv32mi-p-breakpoint

# Spike always uses RISC-V spec-compliant priority
# Compare instruction traces:
diff <(spike output) <(ceres output)
```

### Step 3: Test Alternative Priorities

If Ceres doesn't match Spike with default priority, try alternative orders:

```bash
# Test with illegal instruction highest priority
make clean_obj
# Edit ceres_param.sv to set PRIORITY_ILLEGAL = PRIORITY_1
make verilate
make csr TEST_NAME=breakpoint
```

## Configuration Templates

### template `exception_priority.svh`

Located in `rtl/include/exception_priority.svh`, this file contains alternative configuration templates:

```systemverilog
`ifdef EXCEPTION_PRIORITY_MISALIGNED_FIRST
  // MISALIGNED > DEBUG > ACCESS_FAULT > ILLEGAL > EBREAK > ECALL
`endif

`ifdef EXCEPTION_PRIORITY_ILLEGAL_FIRST
  // ILLEGAL > DEBUG > MISALIGNED > ACCESS_FAULT > EBREAK > ECALL
`endif

`ifdef EXCEPTION_PRIORITY_DISABLED_DEBUG
  // Debug breakpoints disabled
`endif
```

## Debugging Priority Issues

### Problem: RTL exceptions differ from Spike

1. **Verify default configuration**
   ```bash
   cat rtl/pkg/ceres_param.sv | grep "EXC_PRIORITY"
   ```

2. **Check exception detection in fetch.sv**
   - Line ~185: Exception priority logic
   - Search for `has_debug_breakpoint`, `has_instr_misaligned`, etc.

3. **Run with trace enabled**
   ```bash
   make csr TRACE=1 TEST_NAME=breakpoint
   # Check detailed logs in results/logs/verilator/rv32mi-p-breakpoint/
   ```

4. **Compare against Spike**
   ```bash
   diff <(spike -p1 rv32mi-p-breakpoint) <(ceres trace)
   ```

### Problem: Exception shows but shouldn't

- **Check if exception is enabled**: Look for `PRIORITY_DISABLED`
- **Check priority order**: Ensure higher-priority exceptions are checked first
- **Check enable signals**: Verify `has_<exception>` is correctly computed

### Problem: Expected exception missing

- **Check if exception has correct priority**: May be masked by higher-priority exception
- **Check enable conditions**: 
  - Misaligned: PC alignment check
  - Access fault: PMA/grand check
  - Illegal: Instruction decode
  - Breakpoint: tdata1[2] && (pc == tdata2)

## Files Modified

| File | Purpose |
|------|---------|
| `rtl/pkg/ceres_param.sv` | Added priority level enum and configuration macros |
| `rtl/core/stage01_fetch/fetch.sv` | Refactored exception detection to use parametric priority |
| `rtl/include/exception_priority.svh` | Alternative priority configuration templates |
| `script/exception_priority_test.sh` | Test automation script |

## Key Functions

### ceres_param.sv

- `check_exc_priority()` - Checks if exception priority is enabled
- Exception priority assignment macros

### fetch.sv

- Exception detection signals (has_debug_breakpoint, has_instr_misaligned, etc.)
- Priority-based exception selection logic

## Testing Workflow

1. **Default (Spec-Compliant)**
   ```bash
   make verilate
   make csr TEST_NAME=breakpoint
   # Should match Spike exactly
   ```

2. **Alternative Priority Order**
   ```bash
   # Edit ceres_param.sv with custom priorities
   make clean_obj && make verilate
   make csr TEST_NAME=breakpoint
   # Compare with Spike (may differ)
   ```

3. **Disabled Exception**
   ```bash
   # Set EXC_PRIORITY_BREAKPOINT = PRIORITY_DISABLED
   make clean_obj && make verilate
   make csr TEST_NAME=breakpoint
   # Compare results
   ```

4. **Validation**
   - Run multiple priority configurations
   - Document which priorities match Spike
   - Ensure at least one configuration matches specification

## Implementation Details

### Exception Priority Detection Logic

From `fetch.sv` (lines ~185-230):

```systemverilog
// Detect all exceptions present
has_debug_breakpoint = fetch_valid && tdata1_i[2] && (pc_o == tdata2_i);
has_instr_misaligned = fetch_valid && (misa_c_i ? pc_o[0] : (pc_o[1:0] != 2'b00));
has_instr_access_fault = fetch_valid && !grand;
has_illegal_instr = fetch_valid && illegal_instr && buff_res.valid;
has_ebreak = fetch_valid && (instr_type_o == ebreak);
has_ecall = fetch_valid && (instr_type_o == ecall);

// Parametric priority-based selection
exc_type_o = NO_EXCEPTION;

if (has_debug_breakpoint && check_exc_priority(...)) begin
    exc_type_o = BREAKPOINT;
end else if (has_instr_misaligned && check_exc_priority(...)) begin
    exc_type_o = INSTR_MISALIGNED;
    ...
```

### Performance Considerations

- **No runtime overhead**: Priority levels are compile-time constants
- **Verilator synthesis**: All priority checks are combinational logic
- **No additional latency**: Exception detection same cycle as instruction fetch

## Future Enhancements

- [ ] Makefile targets for different priority modes
- [ ] Python test generator for Spike comparison
- [ ] Dynamic priority switching (runtime parameter)
- [ ] Load/store exception priority configuration
- [ ] Virtual/user mode exception priorities

## References

- RISC-V Privileged ISA Specification v1.12 - Section 3.1.15
- RISC-V Debug Specification v0.13.2
- Ceres RTL Documentation: `docs/README.md`

---

**Last Updated**: 2025-11-30  
**Author**: Kerim TURAK  
**Project**: level-v (Ceres RISC-V Core)
