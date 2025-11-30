/**
 * UART Hello Test - Ceres-V RV32IMC_Zicsr
 * 
 * Simple test program that writes "Hello from Ceres!" via UART
 * Demonstrates basic UART initialization and character transmission
 */

#include <stdint.h>
#include <string.h>

/* ========================================================================
 * Hardware Definitions (Same as ceres.h)
 * ======================================================================== */
#define CPU_CLK          50000000   /* 50 MHz */
#define BAUD_RATE        115200

/* UART MMIO Map */
#define UART_CTRL        (*(volatile uint32_t*)0x20000000)
#define UART_STATUS      (*(volatile uint32_t*)0x20000004)
#define UART_RDATA       (*(volatile uint32_t*)0x20000008)
#define UART_WDATA       (*(volatile uint32_t*)0x2000000c)

/* Status Register Bits */
#define UART_STATUS_TX_FULL   0x1
#define UART_STATUS_RX_FULL   0x2
#define UART_STATUS_TX_EMPTY  0x4
#define UART_STATUS_RX_EMPTY  0x8

/* Control Register Bits */
#define UART_CTRL_TX_EN   0x1
#define UART_CTRL_RX_EN   0x2

/* Timer (for delays if needed) */
#define TIMER_LOW        (*(volatile uint32_t*)0x30000000)
#define TIMER_HIGH       (*(volatile uint32_t*)0x30000004)

/* ========================================================================
 * UART Functions
 * ======================================================================== */

/**
 * Initialize UART with CPU clock and baud rate
 */
void uart_init(void)
{
    uint32_t baud_div = CPU_CLK / BAUD_RATE;
    
    /* Control register: [31:16] baud_div, [1] rx_en, [0] tx_en */
    UART_CTRL = (baud_div << 16) | UART_CTRL_TX_EN | UART_CTRL_RX_EN;
}

/**
 * Send a single character via UART
 * Waits until TX FIFO is not full
 */
void uart_putc(char c)
{
    /* Wait until TX FIFO is not full */
    while (UART_STATUS & UART_STATUS_TX_FULL);
    
    /* Write character to TX data register */
    UART_WDATA = (uint32_t)c;
}

/**
 * Send a null-terminated string via UART
 */
void uart_puts(const char *str)
{
    while (*str) {
        if (*str == '\n') {
            uart_putc('\r');  /* Add carriage return before newline */
        }
        uart_putc(*str++);
    }
}

/**
 * Send a hex number via UART (for debugging)
 */
void uart_puthex(uint32_t val)
{
    const char hex_chars[] = "0123456789ABCDEF";
    
    uart_puts("0x");
    for (int i = 7; i >= 0; i--) {
        uint32_t nibble = (val >> (i * 4)) & 0xF;
        uart_putc(hex_chars[nibble]);
    }
}

/**
 * Send a decimal number via UART
 */
void uart_putdec(int32_t val)
{
    if (val < 0) {
        uart_putc('-');
        val = -val;
    }
    
    /* Count digits */
    uint32_t divisor = 1;
    int32_t temp = val;
    while (temp >= 10) {
        divisor *= 10;
        temp /= 10;
    }
    
    /* Print each digit */
    while (divisor > 0) {
        uint32_t digit = val / divisor;
        uart_putc('0' + digit);
        val %= divisor;
        divisor /= 10;
    }
}

/* ========================================================================
 * Main Program
 * ======================================================================== */

int main(void)
{
    /* Initialize UART */
    uart_init();
    
    /* Send welcome message */
    uart_puts("\n");
    uart_puts("========================================\n");
    uart_puts("  Ceres-V UART Test Program\n");
    uart_puts("  Hello from Ceres!\n");
    uart_puts("========================================\n");
    uart_puts("\n");
    
    /* Test 1: Basic string output */
    uart_puts("[TEST 1] Basic string output:\n");
    uart_puts("  This is a test string sent via UART.\n");
    uart_puts("\n");
    
    /* Test 2: Character output */
    uart_puts("[TEST 2] Character output:\n");
    uart_puts("  Alphabet: ");
    for (char c = 'A'; c <= 'Z'; c++) {
        uart_putc(c);
    }
    uart_puts("\n");
    uart_puts("\n");
    
    /* Test 3: Hexadecimal numbers */
    uart_puts("[TEST 3] Hexadecimal numbers:\n");
    uart_puts("  0x12345678 = ");
    uart_puthex(0x12345678);
    uart_puts("\n");
    uart_puts("  0xDEADBEEF = ");
    uart_puthex(0xDEADBEEF);
    uart_puts("\n");
    uart_puts("\n");
    
    /* Test 4: Decimal numbers */
    uart_puts("[TEST 4] Decimal numbers:\n");
    uart_puts("  123 = ");
    uart_putdec(123);
    uart_puts("\n");
    uart_puts("  -456 = ");
    uart_putdec(-456);
    uart_puts("\n");
    uart_puts("  50000000 = ");
    uart_putdec(50000000);
    uart_puts("\n");
    uart_puts("\n");
    
    /* Test 5: Loop with counter */
    uart_puts("[TEST 5] Loop counter (0-9):\n");
    uart_puts("  ");
    for (int i = 0; i < 10; i++) {
        uart_putdec(i);
        uart_putc(' ');
    }
    uart_puts("\n");
    uart_puts("\n");
    
    /* Test 6: Simple calculation */
    uart_puts("[TEST 6] Calculation result:\n");
    int sum = 0;
    for (int i = 1; i <= 5; i++) {
        sum += i;
    }
    uart_puts("  Sum of 1..5 = ");
    uart_putdec(sum);
    uart_puts(" (expected: 15)\n");
    uart_puts("\n");
    
    /* Test 7: Memory address test */
    uart_puts("[TEST 7] Memory addresses:\n");
    uart_puts("  main() function at: ");
    uart_puthex((uint32_t)main);
    uart_puts("\n");
    uart_puts("\n");
    
    /* Final message */
    uart_puts("========================================\n");
    uart_puts("  All tests completed successfully!\n");
    uart_puts("========================================\n");
    uart_puts("\n");
    
    /* Infinite loop or return */
    while (1) {
        /* Keep the program running */
        asm volatile("nop");
    }
    
    return 0;
}
