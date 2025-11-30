/**
 * Fibonacci Test - Ceres-V RV32IMC_Zicsr
 * 
 * Computes fibonacci sequence and prints results via UART
 */

#include <stdint.h>

/* UART MMIO Map */
#define UART_CTRL        (*(volatile uint32_t*)0x20000000)
#define UART_STATUS      (*(volatile uint32_t*)0x20000004)
#define UART_RDATA       (*(volatile uint32_t*)0x20000008)
#define UART_WDATA       (*(volatile uint32_t*)0x2000000c)

#define UART_STATUS_TX_FULL   0x1
#define UART_CTRL_TX_EN       0x1

/* UART Helper Functions */
void uart_init(void) {
    UART_CTRL = UART_CTRL_TX_EN;
}

void uart_putc(char c) {
    while (UART_STATUS & UART_STATUS_TX_FULL);
    UART_WDATA = (uint32_t)c;
}

void uart_puts(const char *str) {
    while (*str) {
        uart_putc(*str++);
    }
}

void uart_puthex(uint32_t val) {
    const char *hex = "0123456789abcdef";
    uart_putc('0');
    uart_putc('x');
    for (int i = 28; i >= 0; i -= 4) {
        uart_putc(hex[(val >> i) & 0xf]);
    }
}

void uart_putdec(uint32_t val) {
    if (val == 0) {
        uart_putc('0');
        return;
    }
    
    char buf[10];
    int len = 0;
    uint32_t temp = val;
    
    while (temp > 0) {
        buf[len++] = '0' + (temp % 10);
        temp /= 10;
    }
    
    for (int i = len - 1; i >= 0; i--) {
        uart_putc(buf[i]);
    }
}

/* Main Test */
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
