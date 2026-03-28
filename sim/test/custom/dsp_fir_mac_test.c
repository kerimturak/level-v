/**
 * DSP-style FIR filter demo — many MACs, UART + mcycle (RV32 Zicsr).
 * FPGA-friendly short run; not a certified BEEBS/DSPstone build.
 */
#include <stdint.h>
#include "level_test.h"

#define NTAPS 16
#define NSAMP 48
#define REPEAT 256

static const int16_t taps[NTAPS] = {
    -12, 18, -35, 160, 92, -286, -192, 1024,
    1024, -192, -286, 92, 160, -35, 18, -12,
};

static int16_t delay[NTAPS];
static int16_t samples[NSAMP];

static inline uint64_t read_mcycle64(void) {
    uint32_t hi1, hi2, lo;
    do {
        __asm__ volatile("csrr %0, mcycleh" : "=r"(hi1));
        __asm__ volatile("csrr %0, mcycle" : "=r"(lo));
        __asm__ volatile("csrr %0, mcycleh" : "=r"(hi2));
    } while (hi1 != hi2);
    return ((uint64_t)hi2 << 32) | (uint64_t)lo;
}

static int32_t fir_sample(int16_t x) {
    int32_t acc = 0;
    for (int k = NTAPS - 1; k > 0; k--) delay[k] = delay[k - 1];
    delay[0] = x;
    for (int k = 0; k < NTAPS; k++) acc += (int32_t)taps[k] * (int32_t)delay[k];
    return acc >> 10;
}

int main(void) {
    uart_init();
    TEST_HEADER("DSP FIR MAC demo");

    for (int i = 0; i < NSAMP; i++) samples[i] = (int16_t)(i * 3 - (NSAMP * 3) / 2);
    for (int k = 0; k < NTAPS; k++) delay[k] = 0;

    uint64_t t0 = read_mcycle64();
    volatile int32_t sink = 0;
    for (int r = 0; r < REPEAT; r++) {
        for (int i = 0; i < NSAMP; i++) sink += fir_sample(samples[i]);
    }
    uint64_t t1 = read_mcycle64();
    uint64_t dcyc = t1 - t0;

    uart_puts("Repeats: ");
    uart_putdec((uint32_t)REPEAT);
    uart_puts("  samples/frame: ");
    uart_putdec((uint32_t)NSAMP);
    uart_puts("\nmcycle (delta): ");
    uart_puthex((uint32_t)dcyc);
    uart_puts("\nMAC-heavy sink: ");
    uart_puthex((uint32_t)sink);
    uart_puts("\n");
    TEST_FOOTER();
    TEST_COMPLETE(TEST_PASS);
    return 0;
}
