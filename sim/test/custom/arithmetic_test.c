/**
 * Arithmetic Test - Ceres-V RV32IMC_Zicsr
 * 
 * Tests arithmetic operations: add, sub, mul, div
 */

#include "ceres_test.h"

int main(void) {
    uart_init();
    
    uart_puts("======================================\n");
    uart_puts("  Arithmetic Test\n");
    uart_puts("======================================\n\n");
    
    /* Addition */
    uart_puts("Test 1: Addition\n");
    uint32_t a = 100, b = 200;
    uint32_t result = a + b;
    uart_puts("  ");
    uart_putdec(a);
    uart_puts(" + ");
    uart_putdec(b);
    uart_puts(" = ");
    uart_putdec(result);
    uart_puts("\n");
    
    /* Subtraction */
    uart_puts("Test 2: Subtraction\n");
    a = 500;
    b = 123;
    result = a - b;
    uart_puts("  ");
    uart_putdec(a);
    uart_puts(" - ");
    uart_putdec(b);
    uart_puts(" = ");
    uart_putdec(result);
    uart_puts("\n");
    
    /* Multiplication */
    uart_puts("Test 3: Multiplication\n");
    a = 12;
    b = 34;
    result = a * b;
    uart_puts("  ");
    uart_putdec(a);
    uart_puts(" * ");
    uart_putdec(b);
    uart_puts(" = ");
    uart_putdec(result);
    uart_puts("\n");
    
    /* Division */
    uart_puts("Test 4: Division\n");
    a = 1000;
    b = 7;
    result = a / b;
    uart_puts("  ");
    uart_putdec(a);
    uart_puts(" / ");
    uart_putdec(b);
    uart_puts(" = ");
    uart_putdec(result);
    uart_puts("\n");
    
    /* Modulo */
    uart_puts("Test 5: Modulo\n");
    result = a % b;
    uart_puts("  ");
    uart_putdec(a);
    uart_puts(" %% ");
    uart_putdec(b);
    uart_puts(" = ");
    uart_putdec(result);
    uart_puts("\n");
    
    uart_puts("\nAll tests completed!\n");
    
    return 0;
}
