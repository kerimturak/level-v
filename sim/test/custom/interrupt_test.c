/*
 * RISC-V Interrupt Test
 * Tests timer, software and external interrupts
 */

#include "ceres_test.h"

// CSR addresses
#define CSR_MSTATUS   0x300
#define CSR_MIE       0x304
#define CSR_MTVEC     0x305
#define CSR_MSCRATCH  0x340
#define CSR_MEPC      0x341
#define CSR_MCAUSE    0x342
#define CSR_MTVAL     0x343
#define CSR_MIP       0x344

// Interrupt enable bits (MIE register)
#define MIE_MSIE      (1 << 3)   // Machine Software Interrupt Enable
#define MIE_MTIE      (1 << 7)   // Machine Timer Interrupt Enable
#define MIE_MEIE      (1 << 11)  // Machine External Interrupt Enable

// Interrupt pending bits (MIP register)
#define MIP_MSIP      (1 << 3)   // Machine Software Interrupt Pending
#define MIP_MTIP      (1 << 7)   // Machine Timer Interrupt Pending
#define MIP_MEIP      (1 << 11)  // Machine External Interrupt Pending

// MSTATUS bits
#define MSTATUS_MIE   (1 << 3)   // Machine Interrupt Enable
#define MSTATUS_MPIE  (1 << 7)   // Previous MIE

// CLINT addresses
#define CLINT_BASE        0x30000000
#define CLINT_MSIP        (CLINT_BASE + 0x0000)
#define CLINT_MTIMECMP_LO (CLINT_BASE + 0x4000)
#define CLINT_MTIMECMP_HI (CLINT_BASE + 0x4004)
#define CLINT_MTIME_LO    (CLINT_BASE + 0xBFF8)
#define CLINT_MTIME_HI    (CLINT_BASE + 0xBFFC)

// Volatile counters for interrupt tracking
volatile uint32_t timer_irq_count = 0;
volatile uint32_t sw_irq_count = 0;
volatile uint32_t ext_irq_count = 0;
volatile uint32_t unknown_irq_count = 0;

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

// Memory-mapped register access
#define REG32(addr) (*((volatile uint32_t *)(addr)))

// Forward declaration
void trap_handler(void) __attribute__((interrupt("machine")));

// Trap handler - called on any trap/interrupt
void trap_handler(void) {
    uint32_t mcause = read_csr(mcause);
    uint32_t mepc = read_csr(mepc);
    
    // Check if it's an interrupt (MSB = 1)
    if (mcause & 0x80000000) {
        uint32_t irq_code = mcause & 0x7FFFFFFF;
        
        switch (irq_code) {
            case 3:  // Machine Software Interrupt
                sw_irq_count++;
                // Clear software interrupt by writing 0 to MSIP
                REG32(CLINT_MSIP) = 0;
                break;
                
            case 7:  // Machine Timer Interrupt
                timer_irq_count++;
                // Clear timer interrupt by setting mtimecmp to max
                REG32(CLINT_MTIMECMP_LO) = 0xFFFFFFFF;
                REG32(CLINT_MTIMECMP_HI) = 0xFFFFFFFF;
                break;
                
            case 11: // Machine External Interrupt
                ext_irq_count++;
                // External interrupt handling would go here
                // (typically read PLIC claim register)
                break;
                
            default:
                unknown_irq_count++;
                break;
        }
    } else {
        // It's an exception, not an interrupt
        // For now, just skip the faulting instruction
        write_csr(mepc, mepc + 4);
    }
}

// Set up trap vector
void setup_trap_vector(void) {
    // Set mtvec to point to our handler (direct mode)
    write_csr(mtvec, (uint32_t)&trap_handler);
}

// Test 1: Read MIP register (should reflect hardware state)
int test_mip_read(void) {
    uint32_t mip = read_csr(mip);
    
    // Initially, no interrupts should be pending (unless timer wrapped)
    print_str("MIP register value: 0x");
    print_hex(mip);
    print_str("\n");
    
    return TEST_PASS;  // Just informational
}

// Test 2: Software Interrupt
int test_software_interrupt(void) {
    uint32_t initial_count = sw_irq_count;
    
    // Enable software interrupt in MIE
    set_csr(mie, MIE_MSIE);
    
    // Enable global interrupts
    set_csr(mstatus, MSTATUS_MIE);
    
    // Trigger software interrupt
    REG32(CLINT_MSIP) = 1;
    
    // Small delay to allow interrupt to fire
    for (volatile int i = 0; i < 100; i++);
    
    // Disable interrupts
    clear_csr(mstatus, MSTATUS_MIE);
    clear_csr(mie, MIE_MSIE);
    
    // Check if interrupt was handled
    if (sw_irq_count > initial_count) {
        print_str("Software interrupt handled successfully\n");
        return TEST_PASS;
    } else {
        print_str("Software interrupt NOT handled\n");
        return TEST_FAIL;
    }
}

// Test 3: Timer Interrupt
int test_timer_interrupt(void) {
    uint32_t initial_count = timer_irq_count;
    
    // Read current mtime
    uint32_t mtime_lo = REG32(CLINT_MTIME_LO);
    uint32_t mtime_hi = REG32(CLINT_MTIME_HI);
    
    print_str("Current mtime: 0x");
    print_hex(mtime_hi);
    print_hex(mtime_lo);
    print_str("\n");
    
    // Set mtimecmp to trigger soon (current + small delta)
    REG32(CLINT_MTIMECMP_LO) = mtime_lo + 1000;
    REG32(CLINT_MTIMECMP_HI) = mtime_hi;
    
    // Enable timer interrupt
    set_csr(mie, MIE_MTIE);
    
    // Enable global interrupts
    set_csr(mstatus, MSTATUS_MIE);
    
    // Wait for interrupt (with timeout)
    for (volatile int i = 0; i < 10000; i++) {
        if (timer_irq_count > initial_count) break;
    }
    
    // Disable interrupts
    clear_csr(mstatus, MSTATUS_MIE);
    clear_csr(mie, MIE_MTIE);
    
    // Check if interrupt was handled
    if (timer_irq_count > initial_count) {
        print_str("Timer interrupt handled successfully\n");
        return TEST_PASS;
    } else {
        print_str("Timer interrupt NOT handled (timeout)\n");
        return TEST_FAIL;
    }
}

// Test 4: MIE/MIP enable/disable
int test_interrupt_enable_disable(void) {
    // Save initial state
    uint32_t mie_initial = read_csr(mie);
    
    // Enable all interrupt types
    write_csr(mie, MIE_MSIE | MIE_MTIE | MIE_MEIE);
    uint32_t mie_enabled = read_csr(mie);
    
    // Disable all
    write_csr(mie, 0);
    uint32_t mie_disabled = read_csr(mie);
    
    // Restore
    write_csr(mie, mie_initial);
    
    print_str("MIE enabled: 0x");
    print_hex(mie_enabled);
    print_str(", disabled: 0x");
    print_hex(mie_disabled);
    print_str("\n");
    
    // Check that writes worked correctly
    // Note: Only bits 3, 7, 11 should be writable (MSIE, MTIE, MEIE)
    if ((mie_enabled & 0x888) == 0x888 && (mie_disabled & 0x888) == 0) {
        return TEST_PASS;
    } else {
        return TEST_FAIL;
    }
}

// Test 5: Nested interrupt prevention
int test_mstatus_mie(void) {
    // Read initial mstatus
    uint32_t mstatus = read_csr(mstatus);
    
    print_str("Initial MSTATUS: 0x");
    print_hex(mstatus);
    print_str("\n");
    
    // Enable global interrupts
    set_csr(mstatus, MSTATUS_MIE);
    uint32_t mstatus_enabled = read_csr(mstatus);
    
    // Disable global interrupts
    clear_csr(mstatus, MSTATUS_MIE);
    uint32_t mstatus_disabled = read_csr(mstatus);
    
    print_str("MSTATUS enabled: 0x");
    print_hex(mstatus_enabled);
    print_str(", disabled: 0x");
    print_hex(mstatus_disabled);
    print_str("\n");
    
    if ((mstatus_enabled & MSTATUS_MIE) && !(mstatus_disabled & MSTATUS_MIE)) {
        return TEST_PASS;
    } else {
        return TEST_FAIL;
    }
}

int main(void) {
    int result = TEST_PASS;
    
    print_str("\n=== RISC-V Interrupt Test ===\n\n");
    
    // Set up trap handler first
    setup_trap_vector();
    
    // Test 1: Read MIP
    print_str("Test 1: MIP Register Read\n");
    test_mip_read();
    print_str("\n");
    
    // Test 2: MIE enable/disable
    print_str("Test 2: MIE Enable/Disable\n");
    if (test_interrupt_enable_disable() != TEST_PASS) {
        result = TEST_FAIL;
        print_str("FAILED\n");
    } else {
        print_str("PASSED\n");
    }
    print_str("\n");
    
    // Test 3: MSTATUS.MIE
    print_str("Test 3: MSTATUS.MIE Control\n");
    if (test_mstatus_mie() != TEST_PASS) {
        result = TEST_FAIL;
        print_str("FAILED\n");
    } else {
        print_str("PASSED\n");
    }
    print_str("\n");
    
    // Test 4: Software Interrupt
    print_str("Test 4: Software Interrupt\n");
    if (test_software_interrupt() != TEST_PASS) {
        result = TEST_FAIL;
        print_str("FAILED\n");
    } else {
        print_str("PASSED\n");
    }
    print_str("\n");
    
    // Test 5: Timer Interrupt
    print_str("Test 5: Timer Interrupt\n");
    if (test_timer_interrupt() != TEST_PASS) {
        result = TEST_FAIL;
        print_str("FAILED\n");
    } else {
        print_str("PASSED\n");
    }
    print_str("\n");
    
    // Summary
    print_str("=== Interrupt Statistics ===\n");
    print_str("Timer IRQs: ");
    print_hex(timer_irq_count);
    print_str("\nSoftware IRQs: ");
    print_hex(sw_irq_count);
    print_str("\nExternal IRQs: ");
    print_hex(ext_irq_count);
    print_str("\nUnknown IRQs: ");
    print_hex(unknown_irq_count);
    print_str("\n");
    
    if (result == TEST_PASS) {
        print_str("\n*** ALL INTERRUPT TESTS PASSED ***\n");
    } else {
        print_str("\n*** SOME INTERRUPT TESTS FAILED ***\n");
    }
    
    // Signal test complete
    TEST_COMPLETE(result);
    
    return result;
}
