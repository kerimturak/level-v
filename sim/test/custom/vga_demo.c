/*
 * VGA display demo — 640×480 @ 60 Hz, 1 bpp from main RAM.
 *
 * Default SoC RAM is 40 KiB (FPGA BRAM). A full 1bpp frame is 37.5 KiB, so there
 * is little room for code/stack if the whole frame lived in RAM. We paint only
 * the lines that fit below physical RAM top; RTL (vga_fb_wishbone) returns black
 * for framebuffer reads past 0x8000_0000 + WRAPPER_RAM_SIZE_KB.
 */

#include <stdint.h>
#include "cpu_clock.h"

#define BAUD_RATE 115200u

#define UART_CTRL   (*(volatile uint32_t*)0x20000000)
#define UART_STATUS (*(volatile uint32_t*)0x20000004)
#define UART_WDATA  (*(volatile uint32_t*)0x2000000c)

#define UART_CTRL_TX_EN     0x1
#define UART_CTRL_RX_EN     0x2
#define UART_STATUS_TX_FULL 0x1

#define VGA_BASE       0x2000A000
#define VGA_CTRL       (*(volatile uint32_t*)(VGA_BASE + 0x00))
#define VGA_FB_BASE    (*(volatile uint32_t*)(VGA_BASE + 0x10))
#define VGA_FB_STRIDE  (*(volatile uint32_t*)(VGA_BASE + 0x14))
#define VGA_PALETTE    (*(volatile uint32_t*)(VGA_BASE + 0x20))
#define VGA_COLOR      (*(volatile uint32_t*)(VGA_BASE + 0x24))

#define VGA_CTRL_EN       (1u << 0)
#define VGA_CTRL_MODE     (1u << 1)
#define VGA_CTRL_BPP_1    (0u << 2)

#define RAM_BASE    0x80000000u
#define RAM_KB      40u
#define RAM_LAST    (RAM_BASE + (RAM_KB * 1024u))

#define FB_ADDR   0x80002000u
#define STRIDE_B  80u
#define LINE_WORD (STRIDE_B / 4u)

#define MAX_Y_RAW (((RAM_LAST) - (FB_ADDR)) / (STRIDE_B))
/* Cap at 480 visible lines when RAM is larger than a full 1bpp frame. */
#define MAX_Y ((MAX_Y_RAW) < 480u ? (MAX_Y_RAW) : 480u)

static void uart_init(void)
{
    uint32_t baud_div = (uint32_t)(CPU_CLK_HZ / BAUD_RATE);
    if (baud_div < 1u) baud_div = 1u;
    UART_CTRL = (baud_div << 16) | UART_CTRL_TX_EN | UART_CTRL_RX_EN;
}

static void uart_putc(char c)
{
    while (UART_STATUS & UART_STATUS_TX_FULL);
    UART_WDATA = (uint32_t)c;
}

static void uart_puts(const char *s)
{
    while (*s) {
        if (*s == '\n') uart_putc('\r');
        uart_putc(*s++);
    }
}

static void draw_bars(void)
{
    for (uint32_t y = 0; y < MAX_Y; y++) {
        uint32_t band = (y / 60u) & 7u;
        uint32_t pat    = (band & 1u) ? 0xFFFFFFFFu : 0u;
        if ((band & 2u) != 0u)
            pat ^= 0xAAAAAAAAu;
        volatile uint32_t *row = (volatile uint32_t *)(FB_ADDR + y * STRIDE_B);
        for (uint32_t i = 0; i < LINE_WORD; i++) row[i] = pat;
    }
}

int main(void)
{
    uart_init();
    uart_puts("\r\nvga_demo: 40K RAM — partial FB fill; bottom clamped black in RTL\r\n");

    draw_bars();

    __asm__ volatile("fence iorw, iorw" ::: "memory");

    VGA_PALETTE = 0;
    VGA_COLOR   = 0x000u;
    VGA_PALETTE = 15;
    VGA_COLOR   = 0xFFFu;

    VGA_FB_BASE   = FB_ADDR;
    VGA_FB_STRIDE = STRIDE_B;
    VGA_CTRL      = VGA_CTRL_EN | VGA_CTRL_MODE | VGA_CTRL_BPP_1;

    uart_puts("vga_demo: running\r\n");
    for (;;);
}
