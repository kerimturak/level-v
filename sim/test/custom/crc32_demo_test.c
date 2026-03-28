/**
 * CRC-32 (IEEE Ethernet polynomial) over a synthetic buffer.
 * MiBench-like workload flavour; implementation is standalone for Level-V.
 */
#include <stdint.h>
#include "level_test.h"

#define BLEN 4096
#define ROUNDS 32

static uint8_t buf[BLEN];

static uint32_t crc32_ieee(const uint8_t *p, unsigned n) {
    uint32_t c = 0xFFFFFFFFu;
    for (unsigned i = 0; i < n; i++) {
        c ^= (uint32_t)p[i];
        for (int k = 0; k < 8; k++) {
            uint32_t m = -(c & 1u);
            c = (c >> 1) ^ (0xEDB88320u & m);
        }
    }
    return ~c;
}

static inline uint64_t read_mcycle64(void) {
    uint32_t hi1, hi2, lo;
    do {
        __asm__ volatile("csrr %0, mcycleh" : "=r"(hi1));
        __asm__ volatile("csrr %0, mcycle" : "=r"(lo));
        __asm__ volatile("csrr %0, mcycleh" : "=r"(hi2));
    } while (hi1 != hi2);
    return ((uint64_t)hi2 << 32) | (uint64_t)lo;
}

int main(void) {
    uart_init();
    TEST_HEADER("CRC32 buffer demo");

    for (unsigned i = 0; i < BLEN; i++) buf[i] = (uint8_t)((i * 131u + 17u) & 0xFFu);

    uint64_t t0 = read_mcycle64();
    uint32_t crc = 0;
    for (int r = 0; r < ROUNDS; r++) crc ^= crc32_ieee(buf, BLEN);
    uint64_t t1 = read_mcycle64();

    uart_puts("bytes: ");
    uart_putdec((uint32_t)BLEN);
    uart_puts("  rounds: ");
    uart_putdec((uint32_t)ROUNDS);
    uart_puts("\nCRC xor: ");
    uart_puthex(crc);
    uart_puts("\nmcycle: ");
    uart_puthex((uint32_t)(t1 - t0));
    uart_puts("\n");
    TEST_FOOTER();
    TEST_COMPLETE(TEST_PASS);
    return 0;
}
