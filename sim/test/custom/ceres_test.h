/**
 * Ceres-V Custom Test Common Header
 * 
 * Shared utilities for all custom tests
 */

#ifndef CERES_TEST_H
#define CERES_TEST_H

#include <stdint.h>

/* ========================================================================
 * UART MMIO Definitions
 * ======================================================================== */

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

/* ========================================================================
 * Memory Definitions
 * ======================================================================== */

#define RAM_BASE          0x80001000
#define TEST_RAM          ((volatile uint32_t*)RAM_BASE)

/* ========================================================================
 * UART Functions
 * ======================================================================== */

static inline void uart_init(void) {
    UART_CTRL = UART_CTRL_TX_EN;
}

static inline void uart_putc(char c) {
    while (UART_STATUS & UART_STATUS_TX_FULL);
    UART_WDATA = (uint32_t)c;
}

static inline void uart_puts(const char *str) {
    while (*str) {
        uart_putc(*str++);
    }
}

static inline void uart_puthex(uint32_t val) {
    const char *hex = "0123456789abcdef";
    uart_putc('0');
    uart_putc('x');
    for (int i = 28; i >= 0; i -= 4) {
        uart_putc(hex[(val >> i) & 0xf]);
    }
}

static inline void uart_putdec(uint32_t val) {
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

/* ========================================================================
 * Test Utilities
 * ======================================================================== */

#define TEST_HEADER(name) \
    uart_puts("======================================\n"); \
    uart_puts("  " name "\n"); \
    uart_puts("======================================\n\n")

#define TEST_FOOTER() \
    uart_puts("\n======================================\n"); \
    uart_puts("  Test completed!\n"); \
    uart_puts("======================================\n")

#endif /* CERES_TEST_H */
