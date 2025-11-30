/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/

`ifndef EXCEPTION_PRIORITY_SVH
`define EXCEPTION_PRIORITY_SVH

/*
 * PARAMETRIC EXCEPTION PRIORITY CONFIGURATION
 * ============================================================================
 * 
 * This header defines the exception priority order for RISC-V M-mode exceptions.
 * 
 * RISC-V Privileged ISA Specification (Section 3.1.15) defines the following
 * exception priority order (highest to lowest) for synchronous exceptions:
 * 
 * 1. Instruction address breakpoint (debug trigger)
 * 2. Instruction address misaligned
 * 3. Instruction access fault
 * 4. Illegal instruction
 * 5. Breakpoint/EBREAK instruction
 * 6. Load/store/AMO address breakpoint (debug trigger)
 * 7. Load/store/AMO address misaligned (implementation-defined priority)
 * 8. Load/store/AMO access fault
 * 9. Environment call (ECALL)
 * 
 * NOTE: Cause 3 is shared between:
 *   - Instruction address breakpoint (highest priority)
 *   - Breakpoint/EBREAK instruction (lower priority)
 *   - Load/store/AMO address breakpoint (lowest priority within cause 3)
 * 
 * USAGE:
 * ------
 * 
 * To test with different exception priorities, override the macros below:
 * 
 *   Example 1: Disable illegal instruction exception (for testing)
 *   `define EXC_PRIORITY_ILLEGAL PRIORITY_DISABLED
 *   
 *   Example 2: Swap priority of breakpoint and misaligned:
 *   `define EXC_PRIORITY_DEBUG_BREAKPOINT PRIORITY_2
 *   `define EXC_PRIORITY_INSTR_MISALIGNED PRIORITY_1
 * 
 * Pass these defines to verilator via -D flag:
 *   verilator -DEXC_PRIORITY_ILLEGAL=PRIORITY_DISABLED ...
 * 
 * Or set them in your Makefile:
 *   VERILATOR_FLAGS += -D$(EXCEPTION_PRIORITY_MODE)
 * 
 * PRIORITY LEVELS (lower enum value = higher priority when evaluated):
 * -------------------------------------------------------------------
 * PRIORITY_1        = Highest priority (checked first)
 * PRIORITY_2        = High priority
 * PRIORITY_3        = Medium-high priority
 * PRIORITY_4        = Medium priority
 * PRIORITY_5        = Medium-low priority
 * PRIORITY_6        = Low priority
 * PRIORITY_7        = Lowest priority (checked last)
 * PRIORITY_DISABLED = Exception disabled (not checked)
 * 
 */

// ============================================================================
// RISC-V SPECIFICATION COMPLIANT DEFAULT PRIORITY ORDER
// ============================================================================
// These are the default (spec-compliant) priority assignments.
// They can be overridden via Verilog defines or generate blocks.

`ifndef EXC_PRIORITY_DEBUG_BREAKPOINT
`define EXC_PRIORITY_DEBUG_BREAKPOINT PRIORITY_1      // Highest: Hardware breakpoint
`endif

`ifndef EXC_PRIORITY_INSTR_MISALIGNED
`define EXC_PRIORITY_INSTR_MISALIGNED PRIORITY_2      // Instruction misaligned
`endif

`ifndef EXC_PRIORITY_INSTR_ACCESS_FAULT
`define EXC_PRIORITY_INSTR_ACCESS_FAULT PRIORITY_3    // Instruction access fault
`endif

`ifndef EXC_PRIORITY_ILLEGAL
`define EXC_PRIORITY_ILLEGAL PRIORITY_4                // Illegal instruction
`endif

`ifndef EXC_PRIORITY_EBREAK
`define EXC_PRIORITY_EBREAK PRIORITY_5                 // EBREAK/C.EBREAK
`endif

`ifndef EXC_PRIORITY_ECALL
`define EXC_PRIORITY_ECALL PRIORITY_6                  // ECALL (lowest)
`endif

// ============================================================================
// ALTERNATIVE PRIORITY CONFIGURATIONS (for testing)
// ============================================================================

`ifdef EXCEPTION_PRIORITY_DEBUG_FIRST
// Debug triggers highest priority (for debug-intensive testing)
// Order: DEBUG_BREAKPOINT > INSTR_MISALIGNED > INSTR_ACCESS_FAULT > ILLEGAL > EBREAK > ECALL
// This is the default, so no override needed
`endif

`ifdef EXCEPTION_PRIORITY_MISALIGNED_FIRST
// Instruction misaligned highest priority (for alignment testing)
// Order: INSTR_MISALIGNED > DEBUG_BREAKPOINT > INSTR_ACCESS_FAULT > ILLEGAL > EBREAK > ECALL
`undef EXC_PRIORITY_INSTR_MISALIGNED
`undef EXC_PRIORITY_DEBUG_BREAKPOINT
`define EXC_PRIORITY_INSTR_MISALIGNED PRIORITY_1
`define EXC_PRIORITY_DEBUG_BREAKPOINT PRIORITY_2
`endif

`ifdef EXCEPTION_PRIORITY_ILLEGAL_FIRST
// Illegal instruction highest priority (for instruction validation testing)
// Order: ILLEGAL > DEBUG_BREAKPOINT > INSTR_MISALIGNED > INSTR_ACCESS_FAULT > EBREAK > ECALL
`undef EXC_PRIORITY_ILLEGAL
`undef EXC_PRIORITY_DEBUG_BREAKPOINT
`define EXC_PRIORITY_ILLEGAL PRIORITY_1
`define EXC_PRIORITY_DEBUG_BREAKPOINT PRIORITY_2
`endif

`ifdef EXCEPTION_PRIORITY_DISABLED_DEBUG
// Debug breakpoints disabled
`undef EXC_PRIORITY_DEBUG_BREAKPOINT
`define EXC_PRIORITY_DEBUG_BREAKPOINT PRIORITY_DISABLED
`endif

`ifdef EXCEPTION_PRIORITY_DISABLED_ILLEGAL
// Illegal instruction disabled
`undef EXC_PRIORITY_ILLEGAL
`define EXC_PRIORITY_ILLEGAL PRIORITY_DISABLED
`endif

`endif  // EXCEPTION_PRIORITY_SVH
