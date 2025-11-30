/**
 * Branch Prediction Test - Ceres-V RV32IMC_Zicsr
 * 
 * Tests various branch patterns:
 * - Predictable branches (always taken/not taken)
 * - Semi-random branches  
 * - Branch with loop
 */

#include "ceres_test.h"

int main(void) {
    uart_init();
    
    TEST_HEADER("Branch Prediction Test");
    uart_puts("(Check BP stats for results)\n\n");
    
    /* Pattern 1: Always taken */
    uart_puts("Test 1: Always-taken branches\n");
    for (int i = 0; i < 50; i++) {
        if (1)  /* Always true */
            continue;
    }
    
    /* Pattern 2: Alternating */
    uart_puts("Test 2: Alternating branches\n");
    for (int i = 0; i < 50; i++) {
        if (i & 1)  /* Alternates */
            continue;
    }
    
    /* Pattern 3: Mostly taken, rare not taken */
    uart_puts("Test 3: Mostly taken branches\n");
    for (int i = 0; i < 50; i++) {
        if (i != 25)  /* Taken 49/50 times */
            continue;
    }
    
    /* Pattern 4: Mostly not taken */
    uart_puts("Test 4: Mostly not-taken branches\n");
    for (int i = 0; i < 50; i++) {
        if (i == 25)  /* Taken 1/50 times */
            continue;
    }
    
    uart_puts("\nCheck bp_stats.log for branch prediction stats\n");
    TEST_FOOTER();
    
    return 0;
}
