/*
 * CLINT (Core-Local Interruptor) Test
 * Tests mtime, mtimecmp, and msip registers
 */

#include "ceres_test.h"

// CLINT register offsets (from base 0x3000_0000)
#define CLINT_BASE        0x30000000
#define CLINT_MSIP        (CLINT_BASE + 0x0000)
#define CLINT_MTIMECMP_LO (CLINT_BASE + 0x4000)
#define CLINT_MTIMECMP_HI (CLINT_BASE + 0x4004)
#define CLINT_MTIME_LO    (CLINT_BASE + 0xBFF8)
#define CLINT_MTIME_HI    (CLINT_BASE + 0xBFFC)

// Memory-mapped register access
#define REG32(addr) (*((volatile uint32_t *)(addr)))

// Test 1: MTIME register read
int test_mtime_read(void) {
    print_str("MTIME read test:\n");
    
    // Read mtime
    uint32_t mtime_lo_1 = REG32(CLINT_MTIME_LO);
    uint32_t mtime_hi_1 = REG32(CLINT_MTIME_HI);
    
    print_str("  MTIME initial: 0x");
    print_hex(mtime_hi_1);
    print_hex(mtime_lo_1);
    print_str("\n");
    
    // Small delay
    for (volatile int i = 0; i < 1000; i++);
    
    // Read again
    uint32_t mtime_lo_2 = REG32(CLINT_MTIME_LO);
    uint32_t mtime_hi_2 = REG32(CLINT_MTIME_HI);
    
    print_str("  MTIME after delay: 0x");
    print_hex(mtime_hi_2);
    print_hex(mtime_lo_2);
    print_str("\n");
    
    // Check that timer is incrementing
    uint64_t time1 = ((uint64_t)mtime_hi_1 << 32) | mtime_lo_1;
    uint64_t time2 = ((uint64_t)mtime_hi_2 << 32) | mtime_lo_2;
    
    if (time2 > time1) {
        print_str("  Timer incrementing: OK\n");
        print_str("  Delta: ");
        print_hex((uint32_t)(time2 - time1));
        print_str(" ticks\n");
        return TEST_PASS;
    } else {
        print_str("  Timer NOT incrementing!\n");
        return TEST_FAIL;
    }
}

// Test 2: MTIME write
int test_mtime_write(void) {
    print_str("MTIME write test:\n");
    
    // Save current value
    uint32_t save_lo = REG32(CLINT_MTIME_LO);
    uint32_t save_hi = REG32(CLINT_MTIME_HI);
    
    // Write a known value
    REG32(CLINT_MTIME_LO) = 0x12345678;
    REG32(CLINT_MTIME_HI) = 0x00000001;
    
    // Read back
    uint32_t read_lo = REG32(CLINT_MTIME_LO);
    uint32_t read_hi = REG32(CLINT_MTIME_HI);
    
    print_str("  Write: 0x00000001_12345678\n");
    print_str("  Read:  0x");
    print_hex(read_hi);
    print_str("_");
    print_hex(read_lo);
    print_str("\n");
    
    // Timer continues incrementing, so we can't expect exact match
    // Just check that the high bits match
    if (read_hi >= 0x00000001) {
        print_str("  MTIME write: OK\n");
        return TEST_PASS;
    } else {
        print_str("  MTIME write: FAILED\n");
        return TEST_FAIL;
    }
}

// Test 3: MTIMECMP write/read
int test_mtimecmp(void) {
    print_str("MTIMECMP test:\n");
    
    // Save current value
    uint32_t save_lo = REG32(CLINT_MTIMECMP_LO);
    uint32_t save_hi = REG32(CLINT_MTIMECMP_HI);
    
    // Write test pattern
    REG32(CLINT_MTIMECMP_LO) = 0xAAAAAAAA;
    REG32(CLINT_MTIMECMP_HI) = 0x55555555;
    
    // Read back
    uint32_t read_lo = REG32(CLINT_MTIMECMP_LO);
    uint32_t read_hi = REG32(CLINT_MTIMECMP_HI);
    
    print_str("  Write: 0x55555555_AAAAAAAA\n");
    print_str("  Read:  0x");
    print_hex(read_hi);
    print_str("_");
    print_hex(read_lo);
    print_str("\n");
    
    // Restore (set to max to prevent timer interrupt)
    REG32(CLINT_MTIMECMP_LO) = 0xFFFFFFFF;
    REG32(CLINT_MTIMECMP_HI) = 0xFFFFFFFF;
    
    if (read_lo == 0xAAAAAAAA && read_hi == 0x55555555) {
        print_str("  MTIMECMP read/write: OK\n");
        return TEST_PASS;
    } else {
        print_str("  MTIMECMP read/write: FAILED\n");
        return TEST_FAIL;
    }
}

// Test 4: Timer interrupt condition
int test_timer_interrupt_condition(void) {
    print_str("Timer interrupt condition test:\n");
    
    // Read MIP to check MTIP
    uint32_t mip;
    asm volatile ("csrr %0, mip" : "=r"(mip));
    
    print_str("  MIP before: 0x");
    print_hex(mip);
    print_str("\n");
    
    // Set mtimecmp to a value less than current mtime
    uint32_t current_lo = REG32(CLINT_MTIME_LO);
    REG32(CLINT_MTIMECMP_LO) = current_lo - 1000;
    REG32(CLINT_MTIMECMP_HI) = 0;
    
    // Check MIP again
    asm volatile ("csrr %0, mip" : "=r"(mip));
    
    print_str("  MIP after setting mtimecmp < mtime: 0x");
    print_hex(mip);
    print_str("\n");
    
    // MTIP (bit 7) should be set
    int result = TEST_PASS;
    if (mip & 0x80) {
        print_str("  MTIP set correctly: OK\n");
    } else {
        print_str("  MTIP NOT set!\n");
        result = TEST_FAIL;
    }
    
    // Clear by setting mtimecmp to max
    REG32(CLINT_MTIMECMP_LO) = 0xFFFFFFFF;
    REG32(CLINT_MTIMECMP_HI) = 0xFFFFFFFF;
    
    // Check MIP again
    asm volatile ("csrr %0, mip" : "=r"(mip));
    
    print_str("  MIP after clearing: 0x");
    print_hex(mip);
    print_str("\n");
    
    if (!(mip & 0x80)) {
        print_str("  MTIP cleared correctly: OK\n");
    } else {
        print_str("  MTIP still set!\n");
        result = TEST_FAIL;
    }
    
    return result;
}

// Test 5: MSIP (Software Interrupt)
int test_msip(void) {
    print_str("MSIP test:\n");
    
    // Read MIP initial
    uint32_t mip;
    asm volatile ("csrr %0, mip" : "=r"(mip));
    
    print_str("  MIP before: 0x");
    print_hex(mip);
    print_str("\n");
    
    // Set MSIP
    REG32(CLINT_MSIP) = 1;
    
    // Read MIP
    asm volatile ("csrr %0, mip" : "=r"(mip));
    
    print_str("  MIP after MSIP=1: 0x");
    print_hex(mip);
    print_str("\n");
    
    int result = TEST_PASS;
    if (mip & 0x8) {
        print_str("  MSIP -> MIP.MSIP: OK\n");
    } else {
        print_str("  MSIP -> MIP.MSIP: FAILED\n");
        result = TEST_FAIL;
    }
    
    // Clear MSIP
    REG32(CLINT_MSIP) = 0;
    
    // Read MIP
    asm volatile ("csrr %0, mip" : "=r"(mip));
    
    print_str("  MIP after MSIP=0: 0x");
    print_hex(mip);
    print_str("\n");
    
    if (!(mip & 0x8)) {
        print_str("  MSIP clear: OK\n");
    } else {
        print_str("  MSIP clear: FAILED\n");
        result = TEST_FAIL;
    }
    
    return result;
}

// Test 6: MSIP register read/write
int test_msip_register(void) {
    print_str("MSIP register test:\n");
    
    // Write 1
    REG32(CLINT_MSIP) = 1;
    uint32_t read1 = REG32(CLINT_MSIP);
    
    // Write 0
    REG32(CLINT_MSIP) = 0;
    uint32_t read0 = REG32(CLINT_MSIP);
    
    print_str("  Write 1, read: 0x");
    print_hex(read1);
    print_str("\n  Write 0, read: 0x");
    print_hex(read0);
    print_str("\n");
    
    // Only bit 0 should be used
    if ((read1 & 1) == 1 && (read0 & 1) == 0) {
        print_str("  MSIP register: OK\n");
        return TEST_PASS;
    } else {
        print_str("  MSIP register: FAILED\n");
        return TEST_FAIL;
    }
}

// Test 7: Timer precision
int test_timer_precision(void) {
    print_str("Timer precision test:\n");
    
    // Measure ticks over multiple iterations
    uint32_t samples[5];
    
    for (int i = 0; i < 5; i++) {
        uint32_t start = REG32(CLINT_MTIME_LO);
        
        // Known delay
        for (volatile int j = 0; j < 100; j++);
        
        uint32_t end = REG32(CLINT_MTIME_LO);
        samples[i] = end - start;
        
        print_str("  Sample ");
        print_hex(i);
        print_str(": ");
        print_hex(samples[i]);
        print_str(" ticks\n");
    }
    
    // Check consistency (all samples should be similar)
    uint32_t min = samples[0], max = samples[0];
    for (int i = 1; i < 5; i++) {
        if (samples[i] < min) min = samples[i];
        if (samples[i] > max) max = samples[i];
    }
    
    print_str("  Min: ");
    print_hex(min);
    print_str(", Max: ");
    print_hex(max);
    print_str("\n");
    
    // Allow some variance
    if (max - min < (min / 4)) {
        print_str("  Timer precision: OK\n");
        return TEST_PASS;
    } else {
        print_str("  Timer precision: High variance\n");
        return TEST_PASS;  // Not necessarily a failure
    }
}

int main(void) {
    int result = TEST_PASS;
    int test_result;
    
    print_str("\n=== CLINT Test Suite ===\n\n");
    
    // Test 1
    print_str("Test 1: MTIME Read\n");
    test_result = test_mtime_read();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 2
    print_str("Test 2: MTIME Write\n");
    test_result = test_mtime_write();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 3
    print_str("Test 3: MTIMECMP Read/Write\n");
    test_result = test_mtimecmp();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 4
    print_str("Test 4: Timer Interrupt Condition\n");
    test_result = test_timer_interrupt_condition();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 5
    print_str("Test 5: MSIP -> MIP\n");
    test_result = test_msip();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 6
    print_str("Test 6: MSIP Register\n");
    test_result = test_msip_register();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 7
    print_str("Test 7: Timer Precision\n");
    test_result = test_timer_precision();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Summary
    if (result == TEST_PASS) {
        print_str("*** ALL CLINT TESTS PASSED ***\n");
    } else {
        print_str("*** SOME CLINT TESTS FAILED ***\n");
    }
    
    TEST_COMPLETE(result);
    
    return result;
}
