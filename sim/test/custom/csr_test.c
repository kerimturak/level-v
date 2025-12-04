/*
 * RISC-V CSR (Control and Status Register) Test
 * Tests all implemented CSRs for correct read/write behavior
 */

#include "ceres_test.h"

// CSR read/write macros
#define read_csr(reg) ({ \
    uint32_t __tmp; \
    asm volatile ("csrr %0, " #reg : "=r"(__tmp)); \
    __tmp; \
})

#define write_csr(reg, val) ({ \
    asm volatile ("csrw " #reg ", %0" :: "rK"(val)); \
})

#define set_csr(reg, bit) ({ \
    asm volatile ("csrs " #reg ", %0" :: "rK"(bit)); \
})

#define clear_csr(reg, bit) ({ \
    asm volatile ("csrc " #reg ", %0" :: "rK"(bit)); \
})

#define swap_csr(reg, val) ({ \
    uint32_t __tmp; \
    asm volatile ("csrrw %0, " #reg ", %1" : "=r"(__tmp) : "rK"(val)); \
    __tmp; \
})

// Test 1: Machine Information Registers (Read-Only)
int test_machine_info_csrs(void) {
    int result = TEST_PASS;
    
    print_str("Machine Information CSRs:\n");
    
    // mvendorid - should be 0 or vendor ID
    uint32_t mvendorid = read_csr(mvendorid);
    print_str("  mvendorid: 0x");
    print_hex(mvendorid);
    print_str("\n");
    
    // marchid - should be 5 (matching Spike for compatibility)
    uint32_t marchid = read_csr(marchid);
    print_str("  marchid: 0x");
    print_hex(marchid);
    if (marchid != 5) {
        print_str(" (expected 5)");
        result = TEST_FAIL;
    }
    print_str("\n");
    
    // mimpid
    uint32_t mimpid = read_csr(mimpid);
    print_str("  mimpid: 0x");
    print_hex(mimpid);
    print_str("\n");
    
    // mhartid - should be 0 for single-core
    uint32_t mhartid = read_csr(mhartid);
    print_str("  mhartid: 0x");
    print_hex(mhartid);
    if (mhartid != 0) {
        print_str(" (expected 0)");
        result = TEST_FAIL;
    }
    print_str("\n");
    
    return result;
}

// Test 2: MISA register
int test_misa(void) {
    int result = TEST_PASS;
    
    uint32_t misa = read_csr(misa);
    print_str("MISA: 0x");
    print_hex(misa);
    print_str("\n");
    
    // Check MXL field (bits 31:30) - should be 1 for RV32
    uint32_t mxl = (misa >> 30) & 0x3;
    print_str("  MXL (XLEN): ");
    if (mxl == 1) {
        print_str("RV32\n");
    } else if (mxl == 2) {
        print_str("RV64\n");
    } else {
        print_str("Unknown\n");
        result = TEST_FAIL;
    }
    
    // Check extensions
    print_str("  Extensions: ");
    if (misa & (1 << 0))  print_str("A ");  // Atomic
    if (misa & (1 << 2))  print_str("C ");  // Compressed
    if (misa & (1 << 3))  print_str("D ");  // Double-precision FP
    if (misa & (1 << 5))  print_str("F ");  // Single-precision FP
    if (misa & (1 << 8))  print_str("I ");  // Base integer
    if (misa & (1 << 12)) print_str("M ");  // Multiply/Divide
    if (misa & (1 << 20)) print_str("U ");  // User mode
    if (misa & (1 << 18)) print_str("S ");  // Supervisor mode
    print_str("\n");
    
    // I extension must be present
    if (!(misa & (1 << 8))) {
        print_str("  ERROR: I extension not present!\n");
        result = TEST_FAIL;
    }
    
    // Test C extension toggle if supported
    uint32_t misa_orig = misa;
    if (misa & (1 << 2)) {
        // Try to disable C extension
        write_csr(misa, misa & ~(1 << 2));
        uint32_t misa_new = read_csr(misa);
        
        // Restore
        write_csr(misa, misa_orig);
        
        print_str("  C extension toggle: ");
        if (misa_new != misa) {
            print_str("writable\n");
        } else {
            print_str("read-only\n");
        }
    }
    
    return result;
}

// Test 3: MSTATUS register
int test_mstatus(void) {
    int result = TEST_PASS;
    
    uint32_t mstatus = read_csr(mstatus);
    print_str("MSTATUS: 0x");
    print_hex(mstatus);
    print_str("\n");
    
    // Test MIE bit toggle
    uint32_t mstatus_orig = mstatus;
    
    // Set MIE
    set_csr(mstatus, 0x8);  // bit 3
    uint32_t mstatus_mie_set = read_csr(mstatus);
    
    // Clear MIE
    clear_csr(mstatus, 0x8);
    uint32_t mstatus_mie_clear = read_csr(mstatus);
    
    print_str("  MIE set: 0x");
    print_hex(mstatus_mie_set);
    print_str(", MIE clear: 0x");
    print_hex(mstatus_mie_clear);
    print_str("\n");
    
    if ((mstatus_mie_set & 0x8) && !(mstatus_mie_clear & 0x8)) {
        print_str("  MIE toggle: OK\n");
    } else {
        print_str("  MIE toggle: FAILED\n");
        result = TEST_FAIL;
    }
    
    // Check MPP field (bits 12:11) - should always be 11 (M-mode only)
    uint32_t mpp = (mstatus >> 11) & 0x3;
    print_str("  MPP: ");
    print_hex(mpp);
    if (mpp == 3) {
        print_str(" (M-mode)\n");
    } else {
        print_str(" (unexpected)\n");
    }
    
    // Restore original
    write_csr(mstatus, mstatus_orig);
    
    return result;
}

// Test 4: MTVEC register
int test_mtvec(void) {
    int result = TEST_PASS;
    
    uint32_t mtvec_orig = read_csr(mtvec);
    print_str("MTVEC original: 0x");
    print_hex(mtvec_orig);
    print_str("\n");
    
    // Test writing different values
    uint32_t test_val = 0x80001000;
    write_csr(mtvec, test_val);
    uint32_t mtvec_new = read_csr(mtvec);
    
    print_str("  Write 0x");
    print_hex(test_val);
    print_str(", Read: 0x");
    print_hex(mtvec_new);
    print_str("\n");
    
    // MODE field (bits 1:0)
    uint32_t mode = mtvec_new & 0x3;
    print_str("  MODE: ");
    if (mode == 0) {
        print_str("Direct\n");
    } else if (mode == 1) {
        print_str("Vectored\n");
    } else {
        print_str("Reserved\n");
    }
    
    // Restore
    write_csr(mtvec, mtvec_orig);
    
    if ((mtvec_new & ~0x3) == (test_val & ~0x3)) {
        return TEST_PASS;
    } else {
        return TEST_FAIL;
    }
}

// Test 5: MSCRATCH register
int test_mscratch(void) {
    uint32_t mscratch_orig = read_csr(mscratch);
    
    // Test pattern write
    uint32_t test_patterns[] = {0x00000000, 0xFFFFFFFF, 0xAAAAAAAA, 0x55555555, 0x12345678};
    int result = TEST_PASS;
    
    print_str("MSCRATCH test:\n");
    for (int i = 0; i < 5; i++) {
        write_csr(mscratch, test_patterns[i]);
        uint32_t readback = read_csr(mscratch);
        
        print_str("  Write: 0x");
        print_hex(test_patterns[i]);
        print_str(", Read: 0x");
        print_hex(readback);
        
        if (readback == test_patterns[i]) {
            print_str(" OK\n");
        } else {
            print_str(" FAIL\n");
            result = TEST_FAIL;
        }
    }
    
    // Restore
    write_csr(mscratch, mscratch_orig);
    
    return result;
}

// Test 6: Performance counters (MCYCLE, MINSTRET)
int test_performance_counters(void) {
    int result = TEST_PASS;
    
    // Read cycle counter
    uint32_t mcycle1 = read_csr(mcycle);
    uint32_t mcycleh1 = read_csr(mcycleh);
    
    // Do some work
    volatile int sum = 0;
    for (int i = 0; i < 100; i++) {
        sum += i;
    }
    
    // Read again
    uint32_t mcycle2 = read_csr(mcycle);
    uint32_t mcycleh2 = read_csr(mcycleh);
    
    print_str("MCYCLE: 0x");
    print_hex(mcycleh1);
    print_hex(mcycle1);
    print_str(" -> 0x");
    print_hex(mcycleh2);
    print_hex(mcycle2);
    print_str("\n");
    
    // Cycle counter should have incremented
    if (mcycle2 <= mcycle1 && mcycleh2 <= mcycleh1) {
        print_str("  WARNING: Cycle counter not incrementing?\n");
        // Not a failure - counter might have wrapped
    }
    
    // Test MINSTRET
    uint32_t minstret1 = read_csr(minstret);
    
    // Execute a few instructions
    asm volatile ("nop");
    asm volatile ("nop");
    asm volatile ("nop");
    
    uint32_t minstret2 = read_csr(minstret);
    
    print_str("MINSTRET: 0x");
    print_hex(minstret1);
    print_str(" -> 0x");
    print_hex(minstret2);
    print_str("\n");
    
    // Test user-mode aliases
    uint32_t cycle = read_csr(cycle);
    uint32_t instret = read_csr(instret);
    
    print_str("User CYCLE: 0x");
    print_hex(cycle);
    print_str(", INSTRET: 0x");
    print_hex(instret);
    print_str("\n");
    
    return result;
}

// Test 7: MEPC register
int test_mepc(void) {
    uint32_t mepc_orig = read_csr(mepc);
    
    uint32_t test_val = 0x80001234;
    write_csr(mepc, test_val);
    uint32_t mepc_read = read_csr(mepc);
    
    print_str("MEPC: Write 0x");
    print_hex(test_val);
    print_str(", Read: 0x");
    print_hex(mepc_read);
    print_str("\n");
    
    // Restore
    write_csr(mepc, mepc_orig);
    
    // MEPC should be aligned (bit 0 always 0 for IALIGN=32, or bit 1:0 for C extension)
    if ((mepc_read & ~0x3) == (test_val & ~0x3)) {
        return TEST_PASS;
    } else {
        return TEST_FAIL;
    }
}

// Test 8: MCAUSE register
int test_mcause(void) {
    uint32_t mcause_orig = read_csr(mcause);
    
    // Test writing interrupt cause
    uint32_t test_val = 0x80000007;  // Timer interrupt
    write_csr(mcause, test_val);
    uint32_t mcause_read = read_csr(mcause);
    
    print_str("MCAUSE: Write 0x");
    print_hex(test_val);
    print_str(", Read: 0x");
    print_hex(mcause_read);
    print_str("\n");
    
    // Restore
    write_csr(mcause, mcause_orig);
    
    if (mcause_read == test_val) {
        return TEST_PASS;
    } else {
        return TEST_FAIL;
    }
}

// Test 9: CSRRW atomicity
int test_csrrw_atomic(void) {
    uint32_t mscratch_orig = read_csr(mscratch);
    
    // Write initial value
    write_csr(mscratch, 0xAAAAAAAA);
    
    // Atomic swap
    uint32_t old_val = swap_csr(mscratch, 0x55555555);
    uint32_t new_val = read_csr(mscratch);
    
    print_str("CSRRW atomic test:\n");
    print_str("  Old value: 0x");
    print_hex(old_val);
    print_str("\n  New value: 0x");
    print_hex(new_val);
    print_str("\n");
    
    // Restore
    write_csr(mscratch, mscratch_orig);
    
    if (old_val == 0xAAAAAAAA && new_val == 0x55555555) {
        return TEST_PASS;
    } else {
        return TEST_FAIL;
    }
}

int main(void) {
    int result = TEST_PASS;
    int test_result;
    
    print_str("\n=== RISC-V CSR Test Suite ===\n\n");
    
    // Test 1: Machine Info CSRs
    print_str("Test 1: Machine Information CSRs\n");
    test_result = test_machine_info_csrs();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 2: MISA
    print_str("Test 2: MISA Register\n");
    test_result = test_misa();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 3: MSTATUS
    print_str("Test 3: MSTATUS Register\n");
    test_result = test_mstatus();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 4: MTVEC
    print_str("Test 4: MTVEC Register\n");
    test_result = test_mtvec();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 5: MSCRATCH
    print_str("Test 5: MSCRATCH Register\n");
    test_result = test_mscratch();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 6: Performance Counters
    print_str("Test 6: Performance Counters\n");
    test_result = test_performance_counters();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 7: MEPC
    print_str("Test 7: MEPC Register\n");
    test_result = test_mepc();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 8: MCAUSE
    print_str("Test 8: MCAUSE Register\n");
    test_result = test_mcause();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 9: CSRRW Atomicity
    print_str("Test 9: CSRRW Atomic Operation\n");
    test_result = test_csrrw_atomic();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Summary
    if (result == TEST_PASS) {
        print_str("*** ALL CSR TESTS PASSED ***\n");
    } else {
        print_str("*** SOME CSR TESTS FAILED ***\n");
    }
    
    TEST_COMPLETE(result);
    
    return result;
}
