#ifndef CERES_H
#define CERES_H

#include <stdint.h>

/* --------------------------------------------------------------------------
 * Clock / Baudrate definitions
 * -------------------------------------------------------------------------- */
#define CLOCKS_PER_SEC   50000000
#define CPU_CLK          CLOCKS_PER_SEC
#define BAUD_RATE        115200

/* --------------------------------------------------------------------------
 * UART MMIO Map
 * -------------------------------------------------------------------------- */
#define UART_CTRL        (*(volatile uint32_t*)0x20000000)
#define UART_STATUS      (*(volatile uint32_t*)0x20000004)
#define UART_RDATA       (*(volatile uint32_t*)0x20000008)
#define UART_WDATA       (*(volatile uint32_t*)0x2000000c)

/* Status bit helpers */
#define UART_TX_FULL     (UART_STATUS & 0x1)
#define UART_RX_FULL     ((UART_STATUS >> 1) & 0x1)
#define UART_TX_EMPTY    ((UART_STATUS >> 2) & 0x1)
#define UART_RX_EMPTY    ((UART_STATUS >> 3) & 0x1)

/* --------------------------------------------------------------------------
 * Timer MMIO Map (64-bit monotonik sayaç)
 * -------------------------------------------------------------------------- */
#define TIMER_LOW        (*(volatile uint32_t*)0x30000000)
#define TIMER_HIGH       (*(volatile uint32_t*)0x30000004)

/* --------------------------------------------------------------------------
 * UART Control Register Structs
 * -------------------------------------------------------------------------- */
typedef union {
    struct {
        unsigned int tx_en    : 1;
        unsigned int rx_en    : 1;
        unsigned int null     : 14;
        unsigned int baud_div : 16;
    } fields;
    uint32_t bits;
} uart_ctrl;

typedef union {
    struct {
        unsigned int tx_full  : 1;
        unsigned int rx_full  : 1;
        unsigned int tx_empty : 1;
        unsigned int rx_empty : 1;
        unsigned int null     : 28;
    } fields;
    uint32_t bits;
} uart_status;

/* --------------------------------------------------------------------------
 * Function Prototypes
 * (CoreMark portunun ihtiyaç duyduğu minimal fonksiyonlar)
 * -------------------------------------------------------------------------- */
void init_uart(void);
static inline void uart_send_char(char c);
static inline uint64_t timer_read_64(void);

/* CoreMark’ın istediği tip */
// typedef uint32_t ee_size_t;

/* --------------------------------------------------------------------------
 * UART Initialization
 * -------------------------------------------------------------------------- */
void init_uart(void)
{
    uart_ctrl c;
    c.bits = 0;

    c.fields.tx_en = 1;
    c.fields.rx_en = 1;               /* BURADA HATA VARDI → düzeltildi      */
    c.fields.baud_div = CPU_CLK / BAUD_RATE;

    UART_CTRL = c.bits;
}

/* --------------------------------------------------------------------------
 * UART Char Write (CoreMark için gerekli)
 * -------------------------------------------------------------------------- */
static inline void uart_send_char(char c)
{
    /* TX FIFO doluysa bekle */
    while (UART_TX_FULL)
        ;

    UART_WDATA = c;
}

/* --------------------------------------------------------------------------
 * 64-bit Timer Safe Read
 * (CoreMark'ın timer implementasyonunda kullanılabilir)
 * -------------------------------------------------------------------------- */
static inline uint64_t timer_read_64(void)
{
    uint32_t hi1, lo, hi2;

    do {
        hi1 = TIMER_HIGH;
        lo  = TIMER_LOW;
        hi2 = TIMER_HIGH;
    } while (hi1 != hi2);

    return ((uint64_t)hi1 << 32) | lo;
}

#endif /* CERES_H */
