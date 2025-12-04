/* ============================================================
 * Ceres-V Board Support for Embench-IoT
 * ============================================================
 * This file is included by board.c
 */

#include <stdint.h>

/* Memory-mapped peripherals */
#define UART_BASE       0x20000000UL
#define UART_DATA       (*(volatile uint32_t*)(UART_BASE + 0x00))
#define UART_STATUS     (*(volatile uint32_t*)(UART_BASE + 0x04))
#define UART_TX_READY   (1 << 0)

#define CLINT_BASE      0x30000000UL
#define MTIME_LO        (*(volatile uint32_t*)(CLINT_BASE + 0xBFF8))
#define MTIME_HI        (*(volatile uint32_t*)(CLINT_BASE + 0xBFFC))

/* Timing variables */
static volatile uint64_t benchmark_start_time;
static volatile uint64_t benchmark_end_time;

/* Read 64-bit mtime */
static inline uint64_t read_mtime(void) {
    uint32_t lo, hi, hi2;
    do {
        hi = MTIME_HI;
        lo = MTIME_LO;
        hi2 = MTIME_HI;
    } while (hi != hi2);
    return ((uint64_t)hi << 32) | lo;
}

/* UART output */
static void uart_putc(char c) {
    while (!(UART_STATUS & UART_TX_READY));
    UART_DATA = c;
}

static void uart_puts(const char* s) {
    while (*s) {
        if (*s == '\n') uart_putc('\r');
        uart_putc(*s++);
    }
}

static void uart_puthex(uint32_t val) {
    const char hex[] = "0123456789abcdef";
    for (int i = 7; i >= 0; i--) {
        uart_putc(hex[(val >> (i * 4)) & 0xF]);
    }
}

/* ============================================================
 * Embench Board Support Functions
 * ============================================================
 */

void initialise_board(void) {
    /* Clear performance counters */
    __asm__ volatile ("csrw mcycle, zero");
    __asm__ volatile ("csrw minstret, zero");
    
    uart_puts("\r\n[Ceres-V] Embench Benchmark\r\n");
}

void start_trigger(void) {
    benchmark_start_time = read_mtime();
}

void stop_trigger(void) {
    benchmark_end_time = read_mtime();
    
    uint64_t elapsed = benchmark_end_time - benchmark_start_time;
    
    uart_puts("Elapsed ticks: 0x");
    uart_puthex((uint32_t)(elapsed >> 32));
    uart_puthex((uint32_t)elapsed);
    uart_puts("\r\n");
}
