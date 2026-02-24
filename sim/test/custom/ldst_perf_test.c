/*
 * LD/ST Buffer Performance Characterization Test
 *
 * Goal:
 * - Produce repeatable cycle numbers for patterns that expose
 *   load-store dependency behavior.
 * - Compare outputs between baseline(main) and ldst_buffer branches.
 */

#include "ceres_test.h"

#define ARR_WORDS 256u
#define MASK      (ARR_WORDS - 1u)
#define N_ITERS   512u

volatile uint32_t arr_a[ARR_WORDS] __attribute__((aligned(64)));
volatile uint32_t arr_b[ARR_WORDS] __attribute__((aligned(64)));

static inline uint32_t get_cycle(void) {
    uint32_t cycle;
    __asm__ volatile("csrr %0, mcycle" : "=r"(cycle));
    return cycle;
}

typedef struct {
    uint32_t cycles;
    uint32_t sum;
} bench_res_t;

static void init_arrays(void) {
    for (uint32_t i = 0; i < ARR_WORDS; i++) {
        arr_a[i] = 0u;
        arr_b[i] = (i * 9u) ^ 0x13579bdfu;
    }
}

static bench_res_t bench_dep_store_load_same(void) {
    bench_res_t r;
    uint32_t sum = 0;
    uint32_t start = get_cycle();

    for (uint32_t i = 0; i < N_ITERS; i++) {
        uint32_t idx = i & MASK;
        arr_a[idx] = (i * 17u) + 3u;
        sum += arr_a[idx];
    }

    r.cycles = get_cycle() - start;
    r.sum = sum;
    return r;
}

static bench_res_t bench_indep_store_load_diff(void) {
    bench_res_t r;
    uint32_t sum = 0;
    uint32_t start = get_cycle();

    for (uint32_t i = 0; i < N_ITERS; i++) {
        uint32_t idx = i & MASK;
        arr_a[idx] = (i * 13u) ^ 0x55aa00ffu;
        sum += arr_b[(idx + 64u) & MASK];
    }

    r.cycles = get_cycle() - start;
    r.sum = sum;
    return r;
}

static bench_res_t bench_store_burst_then_load(void) {
    bench_res_t r;
    uint32_t sum = 0;
    uint32_t start = get_cycle();

    for (uint32_t i = 0; i < N_ITERS; i++) {
        arr_a[i & MASK] = (i * 5u) + 1u;
    }
    for (uint32_t i = 0; i < N_ITERS; i++) {
        sum += arr_a[i & MASK];
    }

    r.cycles = get_cycle() - start;
    r.sum = sum;
    return r;
}

int main(void) {
    uart_init();
    TEST_HEADER("LD/ST Perf Test");

    init_arrays();

    bench_res_t dep = bench_dep_store_load_same();
    bench_res_t ind = bench_indep_store_load_diff();
    bench_res_t bur = bench_store_burst_then_load();

    uart_puts("LDST_PERF_BEGIN\n");

    uart_puts("dep_cycles=");
    uart_putdec(dep.cycles);
    uart_puts(" dep_sum=");
    uart_puthex(dep.sum);
    uart_puts("\n");

    uart_puts("ind_cycles=");
    uart_putdec(ind.cycles);
    uart_puts(" ind_sum=");
    uart_puthex(ind.sum);
    uart_puts("\n");

    uart_puts("burst_cycles=");
    uart_putdec(bur.cycles);
    uart_puts(" burst_sum=");
    uart_puthex(bur.sum);
    uart_puts("\n");

    uart_puts("LDST_PERF_END\n");

    uart_puts("\n");
    while (1) {
    }

    return 0;
}
