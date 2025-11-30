/**
 * Fibonacci Test - Ceres-V RV32IMC_Zicsr
 * 
 * Computes fibonacci sequence and prints results via UART
 */

#include "ceres_test.h"

int main(void) {
    uart_init();
    
    uart_puts("======================================\n");
    uart_puts("  Fibonacci Sequence Test\n");
    uart_puts("  Computing first 10 Fibonacci numbers\n");
    uart_puts("======================================\n\n");
    
    uint32_t a = 0, b = 1;
    
    for (int i = 0; i < 10; i++) {
        uart_puts("Fib(");
        uart_putdec(i);
        uart_puts(") = ");
        uart_putdec(a);
        uart_puts("\n");
        
        uint32_t temp = a + b;
        a = b;
        b = temp;
    }
    
    uart_puts("\nTest completed successfully!\n");
    
    return 0;
}
