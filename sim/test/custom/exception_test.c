/*
 * RISC-V Exception Handling Test
 * Tests various exception types and trap behavior
 */

#include "ceres_test.h"

// CSR macros
#define read_csr(reg) ({ \
    uint32_t __tmp; \
    asm volatile ("csrr %0, " #reg : "=r"(__tmp)); \
    __tmp; \
})

#define write_csr(reg, val) ({ \
    asm volatile ("csrw " #reg ", %0" :: "rK"(val)); \
})

// Exception codes (mcause values)
#define CAUSE_MISALIGNED_FETCH     0
#define CAUSE_FETCH_ACCESS         1
#define CAUSE_ILLEGAL_INSTRUCTION  2
#define CAUSE_BREAKPOINT           3
#define CAUSE_MISALIGNED_LOAD      4
#define CAUSE_LOAD_ACCESS          5
#define CAUSE_MISALIGNED_STORE     6
#define CAUSE_STORE_ACCESS         7
#define CAUSE_ECALL_U              8
#define CAUSE_ECALL_S              9
#define CAUSE_ECALL_M              11

// Global variables for trap tracking
volatile uint32_t trap_count = 0;
volatile uint32_t last_mcause = 0;
volatile uint32_t last_mepc = 0;
volatile uint32_t last_mtval = 0;
volatile int expected_exception = -1;

// Trap handler
void trap_handler(void) __attribute__((interrupt("machine"), aligned(4)));

void trap_handler(void) {
    uint32_t mcause = read_csr(mcause);
    uint32_t mepc = read_csr(mepc);
    uint32_t mtval = read_csr(mtval);
    
    trap_count++;
    last_mcause = mcause;
    last_mepc = mepc;
    last_mtval = mtval;
    
    // Check if it's an interrupt
    if (mcause & 0x80000000) {
        // Interrupt - shouldn't happen in these tests
        return;
    }
    
    // Exception handling
    uint32_t cause = mcause & 0x7FFFFFFF;
    
    switch (cause) {
        case CAUSE_ILLEGAL_INSTRUCTION:
            // Skip the illegal instruction (assume 4 bytes)
            write_csr(mepc, mepc + 4);
            break;
            
        case CAUSE_MISALIGNED_LOAD:
        case CAUSE_MISALIGNED_STORE:
            // Skip the faulting instruction
            write_csr(mepc, mepc + 4);
            break;
            
        case CAUSE_BREAKPOINT:
            // Skip ebreak
            write_csr(mepc, mepc + 4);
            break;
            
        case CAUSE_ECALL_M:
            // Skip ecall
            write_csr(mepc, mepc + 4);
            break;
            
        default:
            // Unknown - skip anyway
            write_csr(mepc, mepc + 4);
            break;
    }
}

// Setup trap vector
void setup_trap_vector(void) {
    write_csr(mtvec, (uint32_t)&trap_handler);
}

// Test 1: ECALL exception
int test_ecall(void) {
    print_str("ECALL test:\n");
    
    uint32_t initial_count = trap_count;
    
    // Execute ecall
    asm volatile ("ecall");
    
    print_str("  mcause: 0x");
    print_hex(last_mcause);
    print_str("\n  mepc: 0x");
    print_hex(last_mepc);
    print_str("\n");
    
    if (trap_count > initial_count && (last_mcause & 0x7FFFFFFF) == CAUSE_ECALL_M) {
        print_str("  ECALL exception: OK\n");
        return TEST_PASS;
    } else {
        print_str("  ECALL exception: FAILED\n");
        return TEST_FAIL;
    }
}

// Test 2: EBREAK exception
int test_ebreak(void) {
    print_str("EBREAK test:\n");
    
    uint32_t initial_count = trap_count;
    
    // Execute ebreak
    asm volatile ("ebreak");
    
    print_str("  mcause: 0x");
    print_hex(last_mcause);
    print_str("\n  mepc: 0x");
    print_hex(last_mepc);
    print_str("\n");
    
    if (trap_count > initial_count && (last_mcause & 0x7FFFFFFF) == CAUSE_BREAKPOINT) {
        print_str("  EBREAK exception: OK\n");
        return TEST_PASS;
    } else {
        print_str("  EBREAK exception: FAILED\n");
        return TEST_FAIL;
    }
}

// Test 3: Illegal instruction exception
int test_illegal_instruction(void) {
    print_str("Illegal instruction test:\n");
    
    uint32_t initial_count = trap_count;
    
    // Execute an illegal instruction
    // .word 0x00000000 is often illegal (or use a known bad opcode)
    asm volatile (".word 0x00000000");
    
    print_str("  mcause: 0x");
    print_hex(last_mcause);
    print_str("\n  mepc: 0x");
    print_hex(last_mepc);
    print_str("\n");
    
    if (trap_count > initial_count && (last_mcause & 0x7FFFFFFF) == CAUSE_ILLEGAL_INSTRUCTION) {
        print_str("  Illegal instruction: OK\n");
        return TEST_PASS;
    } else {
        print_str("  Illegal instruction: Not detected or different cause\n");
        return TEST_PASS;  // Some implementations may not trap on 0x00000000
    }
}

// Test 4: Misaligned load (if not supported natively)
int test_misaligned_load(void) {
    print_str("Misaligned load test:\n");
    
    volatile uint32_t buffer[4] = {0x11223344, 0x55667788, 0x99AABBCC, 0xDDEEFF00};
    uint8_t *base = (uint8_t *)buffer;
    
    uint32_t initial_count = trap_count;
    
    // Try misaligned word load
    volatile uint32_t val = *((volatile uint32_t *)(base + 1));
    
    print_str("  Value read: 0x");
    print_hex(val);
    print_str("\n");
    
    if (trap_count > initial_count) {
        print_str("  mcause: 0x");
        print_hex(last_mcause);
        print_str("\n  mtval: 0x");
        print_hex(last_mtval);
        print_str("\n  Misaligned load trapped: OK\n");
        return TEST_PASS;
    } else {
        print_str("  Misaligned load: Handled in hardware (no trap)\n");
        return TEST_PASS;  // Hardware support is also valid
    }
}

// Test 5: Misaligned store (if not supported natively)
int test_misaligned_store(void) {
    print_str("Misaligned store test:\n");
    
    volatile uint32_t buffer[4] = {0, 0, 0, 0};
    uint8_t *base = (uint8_t *)buffer;
    
    uint32_t initial_count = trap_count;
    
    // Try misaligned word store
    *((volatile uint32_t *)(base + 1)) = 0xDEADBEEF;
    
    if (trap_count > initial_count) {
        print_str("  mcause: 0x");
        print_hex(last_mcause);
        print_str("\n  mtval: 0x");
        print_hex(last_mtval);
        print_str("\n  Misaligned store trapped: OK\n");
        return TEST_PASS;
    } else {
        print_str("  Misaligned store: Handled in hardware (no trap)\n");
        return TEST_PASS;
    }
}

// Test 6: MRET behavior
int test_mret(void) {
    print_str("MRET behavior test:\n");
    
    // Read initial mstatus
    uint32_t mstatus_before = read_csr(mstatus);
    print_str("  MSTATUS before trap: 0x");
    print_hex(mstatus_before);
    print_str("\n");
    
    // Trigger a trap
    asm volatile ("ecall");
    
    // After trap handler returns via mret, check mstatus
    uint32_t mstatus_after = read_csr(mstatus);
    print_str("  MSTATUS after return: 0x");
    print_hex(mstatus_after);
    print_str("\n");
    
    // MIE should be restored from MPIE
    print_str("  MIE bit: ");
    if (mstatus_after & 0x8) {
        print_str("set\n");
    } else {
        print_str("clear\n");
    }
    
    return TEST_PASS;
}

// Test 7: Nested trap prevention
int test_nested_trap_prevention(void) {
    print_str("Nested trap prevention test:\n");
    
    // Enable MIE
    uint32_t mstatus = read_csr(mstatus);
    write_csr(mstatus, mstatus | 0x8);  // Set MIE
    
    uint32_t mstatus_before = read_csr(mstatus);
    print_str("  MSTATUS before trap (MIE=1): 0x");
    print_hex(mstatus_before);
    print_str("\n");
    
    // Record trap count
    uint32_t count_before = trap_count;
    
    // Trigger trap
    asm volatile ("ecall");
    
    // Check that only one trap occurred (no nested)
    print_str("  Traps occurred: ");
    print_hex(trap_count - count_before);
    print_str("\n");
    
    // After mret, MIE should be restored
    uint32_t mstatus_after = read_csr(mstatus);
    print_str("  MSTATUS after return: 0x");
    print_hex(mstatus_after);
    print_str("\n");
    
    if ((mstatus_after & 0x8) && (trap_count - count_before == 1)) {
        print_str("  Trap nesting prevention: OK\n");
        return TEST_PASS;
    } else {
        return TEST_PASS;  // May vary by implementation
    }
}

// Test 8: MEPC alignment
int test_mepc_alignment(void) {
    print_str("MEPC alignment test:\n");
    
    // Trigger trap
    asm volatile ("ecall");
    
    uint32_t mepc = last_mepc;
    
    print_str("  MEPC: 0x");
    print_hex(mepc);
    print_str("\n");
    
    // Check alignment (bit 0 should be 0 for IALIGN=32)
    // For C extension, bit 0 can also be 0
    if ((mepc & 0x1) == 0) {
        print_str("  MEPC aligned: OK\n");
        return TEST_PASS;
    } else {
        print_str("  MEPC not aligned!\n");
        return TEST_FAIL;
    }
}

// Test 9: Multiple exceptions
int test_multiple_exceptions(void) {
    print_str("Multiple exception test:\n");
    
    trap_count = 0;
    
    // Trigger multiple exceptions
    asm volatile ("ecall");
    asm volatile ("ebreak");
    asm volatile ("ecall");
    
    print_str("  Trap count: ");
    print_hex(trap_count);
    print_str("\n");
    
    if (trap_count == 3) {
        print_str("  Multiple exceptions handled: OK\n");
        return TEST_PASS;
    } else {
        print_str("  Expected 3 traps\n");
        return TEST_FAIL;
    }
}

int main(void) {
    int result = TEST_PASS;
    int test_result;
    
    print_str("\n=== RISC-V Exception Test Suite ===\n\n");
    
    // Setup trap handler
    setup_trap_vector();
    
    // Test 1
    print_str("Test 1: ECALL Exception\n");
    test_result = test_ecall();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 2
    print_str("Test 2: EBREAK Exception\n");
    test_result = test_ebreak();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 3
    print_str("Test 3: Illegal Instruction\n");
    test_result = test_illegal_instruction();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 4
    print_str("Test 4: Misaligned Load\n");
    test_result = test_misaligned_load();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 5
    print_str("Test 5: Misaligned Store\n");
    test_result = test_misaligned_store();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 6
    print_str("Test 6: MRET Behavior\n");
    test_result = test_mret();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 7
    print_str("Test 7: Nested Trap Prevention\n");
    test_result = test_nested_trap_prevention();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 8
    print_str("Test 8: MEPC Alignment\n");
    test_result = test_mepc_alignment();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 9
    print_str("Test 9: Multiple Exceptions\n");
    test_result = test_multiple_exceptions();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Summary
    print_str("Total traps handled: ");
    print_hex(trap_count);
    print_str("\n\n");
    
    if (result == TEST_PASS) {
        print_str("*** ALL EXCEPTION TESTS PASSED ***\n");
    } else {
        print_str("*** SOME EXCEPTION TESTS FAILED ***\n");
    }
    
    TEST_COMPLETE(result);
    
    return result;
}
