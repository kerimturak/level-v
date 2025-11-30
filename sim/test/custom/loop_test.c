/**
 * Loop Test - Ceres-V RV32IMC_Zicsr
 * 
 * Tests loop execution and branch prediction
 * Loops with different patterns
 */

#include "ceres_test.h"

int main(void) {
    uart_init();
    
    TEST_HEADER("Loop Test - Branch Prediction");
    
    /* Simple loop */
    uart_puts("Loop 1: Simple counter (10 iterations)\n");
    for (int i = 0; i < 10; i++) {
        if (i % 5 == 0) uart_putc('X');
    }
    uart_puts("\n\n");
    
    /* Nested loop */
    uart_puts("Loop 2: Nested (3x3)\n");
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            uart_putc('.');
        }
        uart_putc('\n');
    }
    uart_puts("\n");
    
    /* Conditional loop */
    uart_puts("Loop 3: Conditional break\n");
    int count = 0;
    for (int i = 0; i < 20; i++) {
        if (i > 10) break;
        count++;
    }
    uart_puts("Executed: ");
    uart_putc('0' + count);
    uart_puts(" times\n");
    
    TEST_FOOTER();
    
    return 0;
}
