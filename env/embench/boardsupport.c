/* ============================================================
 * Level-V Board Support for Embench-IoT
 * ============================================================
 * This file is included by board.c
 */

#include <stdint.h>
#include "cpu_clock.h"

/* Memory-mapped peripherals — level-V UART (uart.sv) */
#define UART_BASE       0x20000000UL
#define UART_CTRL       (*(volatile uint32_t*)(UART_BASE + 0x00))
#define UART_STATUS     (*(volatile uint32_t*)(UART_BASE + 0x04))
#define UART_WDATA      (*(volatile uint32_t*)(UART_BASE + 0x0c))
#define UART_CTRL_TX_EN (1u << 0)
#define UART_CTRL_RX_EN (1u << 1)
#define UART_STATUS_TX_FULL (1u << 0)
#define UART_BAUD 115200u

/* Timing variables — mcycle snapshot at start/stop of benchmark() */
static uint64_t benchmark_start_mcycles;

/* 64-bit mcycle (RV32: mcycle + mcycleh, overflow-safe read) */
static inline uint64_t read_mcycle64(void) {
    uint32_t hi1, hi2, lo;
    do {
        __asm__ volatile("csrr %0, mcycleh" : "=r"(hi1));
        __asm__ volatile("csrr %0, mcycle" : "=r"(lo));
        __asm__ volatile("csrr %0, mcycleh" : "=r"(hi2));
    } while (hi1 != hi2);
    return ((uint64_t)hi2 << 32) | (uint64_t)lo;
}

/* UART output */
static void board_uart_hw_init(void) {
    uint32_t baud_div = (uint32_t)(CPU_CLK_HZ / UART_BAUD);
    UART_CTRL = (baud_div << 16) | UART_CTRL_TX_EN | UART_CTRL_RX_EN;
}

static void uart_putc(char c) {
    while (UART_STATUS & UART_STATUS_TX_FULL) {
    }
    UART_WDATA = (uint32_t)c;
}

static void uart_puts(const char* s) {
    while (*s) {
        if (*s == '\n') uart_putc('\r');
        uart_putc(*s++);
    }
}

static void uart_put_u64_dec(uint64_t v) {
    char buf[24];
    int  n = 0;
    if (v == 0) {
        uart_putc('0');
        return;
    }
    while (v > 0 && n < (int)sizeof(buf)) {
        buf[n++] = (char)('0' + (v % 10ULL));
        v /= 10ULL;
    }
    while (n > 0) {
        uart_putc(buf[--n]);
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

    board_uart_hw_init();
    uart_puts("\r\n[Level-V] Embench Benchmark\r\n");
}

void start_trigger(void) {
    benchmark_start_mcycles = read_mcycle64();
}

void stop_trigger(void) {
    uint64_t end   = read_mcycle64();
    uint64_t delta = end - benchmark_start_mcycles;

    /*
     * Parse-friendly line for host scripts / future embench.py integration.
     * Suite geometric mean is computed off-target; each run exports core cycles only.
     */
    uart_puts("EMBENCH_MCYCLES: ");
    uart_put_u64_dec(delta);
    uart_puts("\r\n");
}
