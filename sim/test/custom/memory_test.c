/**
 * Memory Access Test - Ceres-V RV32IMC_Zicsr
 * 
 * Tests memory read/write patterns
 */

#include "ceres_test.h"

int main(void) {
    uart_init();
    
    uart_puts("======================================\n");
    uart_puts("  Memory Access Test\n");
    uart_puts("======================================\n\n");
    
    /* Test 1: Sequential writes */
    uart_puts("Test 1: Sequential write pattern\n");
    for (int i = 0; i < 64; i++) {
        TEST_RAM[i] = i * 0x11223344;
    }
    uart_puts("Wrote 64 words\n");
    
    /* Test 2: Sequential reads */
    uart_puts("Test 2: Sequential read pattern\n");
    uint32_t sum = 0;
    for (int i = 0; i < 64; i++) {
        sum += TEST_RAM[i];
    }
    uart_puts("Sum: ");
    uart_puthex(sum);
    uart_puts("\n");
    
    /* Test 3: Random access pattern */
    uart_puts("Test 3: Random access pattern\n");
    TEST_RAM[0] = 0x12345678;
    TEST_RAM[16] = 0xdeadbeef;
    TEST_RAM[32] = 0xcafebabe;
    TEST_RAM[48] = 0xfeedface;
    
    uint32_t val = TEST_RAM[0] + TEST_RAM[16] + TEST_RAM[32] + TEST_RAM[48];
    uart_puts("Random access sum: ");
    uart_puthex(val);
    uart_puts("\n");
    
    uart_puts("\nTest completed!\n");
    
    return 0;
}
