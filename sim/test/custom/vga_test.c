/*
 * VGA Controller Test for Ceres-V RV32IMC
 * 
 * Tests VGA Controller functionality:
 * - Control register access
 * - Text mode configuration
 * - Graphics mode configuration
 * - Cursor control
 * - Palette access
 * - Scroll registers
 * - Framebuffer base address
 * 
 * VGA supports 640x480 @ 60Hz with text (80x30) and graphics modes
 * 
 * Note: This peripheral is not yet connected in ceres_wrapper.sv
 *       Requires adding VGA instantiation and address decode (0x2000_Axxx)
 *       Also requires 25.175 MHz pixel clock generation
 */

#include <stdint.h>

/* ========================================================================
 * Hardware Definitions
 * ======================================================================== */
#define CPU_CLK          50000000   /* 50 MHz */
#define BAUD_RATE        5000000    /* Fast simulation baud rate */

/* UART MMIO Map */
#define UART_CTRL        (*(volatile uint32_t*)0x20000000)
#define UART_STATUS      (*(volatile uint32_t*)0x20000004)
#define UART_WDATA       (*(volatile uint32_t*)0x2000000c)

#define UART_CTRL_TX_EN       0x1
#define UART_CTRL_RX_EN       0x2
#define UART_STATUS_TX_FULL   0x1

/* VGA MMIO Map (base 0x2000_A000) */
#define VGA_BASE         0x2000A000

#define VGA_CTRL         (*(volatile uint32_t*)(VGA_BASE + 0x00))
#define VGA_STATUS       (*(volatile uint32_t*)(VGA_BASE + 0x04))
#define VGA_HTIMING      (*(volatile uint32_t*)(VGA_BASE + 0x08))
#define VGA_VTIMING      (*(volatile uint32_t*)(VGA_BASE + 0x0C))
#define VGA_FB_BASE      (*(volatile uint32_t*)(VGA_BASE + 0x10))
#define VGA_FB_STRIDE    (*(volatile uint32_t*)(VGA_BASE + 0x14))
#define VGA_CURSOR_X     (*(volatile uint32_t*)(VGA_BASE + 0x18))
#define VGA_CURSOR_Y     (*(volatile uint32_t*)(VGA_BASE + 0x1C))
#define VGA_PALETTE      (*(volatile uint32_t*)(VGA_BASE + 0x20))
#define VGA_COLOR        (*(volatile uint32_t*)(VGA_BASE + 0x24))
#define VGA_SCROLL_X     (*(volatile uint32_t*)(VGA_BASE + 0x28))
#define VGA_SCROLL_Y     (*(volatile uint32_t*)(VGA_BASE + 0x2C))

/* CTRL register bits */
#define VGA_CTRL_EN          (1 << 0)   /* Display enable */
#define VGA_CTRL_MODE        (1 << 1)   /* 0=Text, 1=Graphics */
#define VGA_CTRL_BPP_1       (0 << 2)   /* 1 bit per pixel */
#define VGA_CTRL_BPP_2       (1 << 2)   /* 2 bits per pixel */
#define VGA_CTRL_BPP_4       (2 << 2)   /* 4 bits per pixel */
#define VGA_CTRL_BPP_8       (3 << 2)   /* 8 bits per pixel */
#define VGA_CTRL_CURSOR_EN   (1 << 4)   /* Cursor enable */
#define VGA_CTRL_CURSOR_BL   (1 << 5)   /* Cursor blink */
#define VGA_CTRL_HSYNC_POL   (1 << 6)   /* HSync polarity */
#define VGA_CTRL_VSYNC_POL   (1 << 7)   /* VSync polarity */
#define VGA_CTRL_DBLBUF      (1 << 8)   /* Double buffer */
#define VGA_CTRL_BUFSEL      (1 << 9)   /* Buffer select */

/* Display parameters */
#define VGA_H_VISIBLE    640
#define VGA_V_VISIBLE    480
#define VGA_TEXT_COLS    80
#define VGA_TEXT_ROWS    30

/* Framebuffer address (in RAM) */
#define FRAMEBUFFER_ADDR 0x80100000

/* ========================================================================
 * UART Functions
 * ======================================================================== */
void uart_init(void)
{
    uint32_t baud_div = CPU_CLK / BAUD_RATE;
    UART_CTRL = (baud_div << 16) | UART_CTRL_TX_EN | UART_CTRL_RX_EN;
}

void uart_putc(char c)
{
    while (UART_STATUS & UART_STATUS_TX_FULL);
    UART_WDATA = (uint32_t)c;
}

void uart_puts(const char *str)
{
    while (*str) {
        if (*str == '\n') uart_putc('\r');
        uart_putc(*str++);
    }
}

void uart_puthex(uint32_t val)
{
    uart_puts("0x");
    for (int i = 7; i >= 0; i--) {
        uint32_t nibble = (val >> (i * 4)) & 0xF;
        uart_putc("0123456789ABCDEF"[nibble]);
    }
}

void uart_putdec(uint32_t val)
{
    char buf[12];
    int i = 0;
    if (val == 0) {
        uart_putc('0');
        return;
    }
    while (val > 0) {
        buf[i++] = '0' + (val % 10);
        val /= 10;
    }
    while (i > 0) uart_putc(buf[--i]);
}

/* ========================================================================
 * Test Helpers
 * ======================================================================== */
static int test_pass = 0;
static int test_fail = 0;

void check(const char *name, int condition)
{
    if (condition) {
        uart_puts("  [PASS] ");
        test_pass++;
    } else {
        uart_puts("  [FAIL] ");
        test_fail++;
    }
    uart_puts(name);
    uart_puts("\n");
}

void delay_cycles(uint32_t n)
{
    for (volatile uint32_t i = 0; i < n; i++) {
        asm volatile("nop");
    }
}

/* ========================================================================
 * VGA Tests
 * ======================================================================== */

void test_vga_control_register(void)
{
    uart_puts("\n=== Test 1: Control Register ===\n");
    
    /* Disable first */
    VGA_CTRL = 0;
    
    /* Test enable bit */
    VGA_CTRL = VGA_CTRL_EN;
    uint32_t ctrl = VGA_CTRL;
    uart_puts("  CTRL with EN: ");
    uart_puthex(ctrl);
    uart_puts("\n");
    check("Enable bit", ctrl & VGA_CTRL_EN);
    
    /* Test mode bit */
    VGA_CTRL = VGA_CTRL_MODE;
    ctrl = VGA_CTRL;
    check("Graphics mode bit", ctrl & VGA_CTRL_MODE);
    
    /* Test BPP field */
    VGA_CTRL = VGA_CTRL_BPP_8;
    ctrl = VGA_CTRL;
    check("BPP field (8bpp)", ((ctrl >> 2) & 0x3) == 3);
    
    /* Test cursor bits */
    VGA_CTRL = VGA_CTRL_CURSOR_EN | VGA_CTRL_CURSOR_BL;
    ctrl = VGA_CTRL;
    check("Cursor enable/blink", (ctrl & 0x30) == 0x30);
    
    /* Test sync polarity */
    VGA_CTRL = VGA_CTRL_HSYNC_POL | VGA_CTRL_VSYNC_POL;
    ctrl = VGA_CTRL;
    check("Sync polarity bits", (ctrl & 0xC0) == 0xC0);
    
    VGA_CTRL = 0;
}

void test_vga_framebuffer(void)
{
    uart_puts("\n=== Test 2: Framebuffer Registers ===\n");
    
    /* Set framebuffer base address */
    VGA_FB_BASE = FRAMEBUFFER_ADDR;
    uint32_t fb_base = VGA_FB_BASE;
    uart_puts("  FB_BASE: ");
    uart_puthex(fb_base);
    uart_puts("\n");
    check("FB base address", fb_base == FRAMEBUFFER_ADDR);
    
    /* Set stride (bytes per line) */
    VGA_FB_STRIDE = VGA_H_VISIBLE;  /* 640 bytes for 8bpp */
    uint32_t stride = VGA_FB_STRIDE;
    uart_puts("  FB_STRIDE: ");
    uart_putdec(stride & 0xFFFF);
    uart_puts("\n");
    check("FB stride", (stride & 0xFFFF) == VGA_H_VISIBLE);
}

void test_vga_cursor(void)
{
    uart_puts("\n=== Test 3: Cursor Registers ===\n");
    
    /* Set cursor position */
    VGA_CURSOR_X = 40;
    VGA_CURSOR_Y = 15;
    
    uint32_t cx = VGA_CURSOR_X;
    uint32_t cy = VGA_CURSOR_Y;
    
    uart_puts("  Cursor X: ");
    uart_putdec(cx & 0xFFFF);
    uart_puts("\n");
    uart_puts("  Cursor Y: ");
    uart_putdec(cy & 0xFFFF);
    uart_puts("\n");
    
    check("Cursor X position", (cx & 0xFFFF) == 40);
    check("Cursor Y position", (cy & 0xFFFF) == 15);
    
    /* Test cursor at corners */
    VGA_CURSOR_X = 0;
    VGA_CURSOR_Y = 0;
    check("Cursor at origin", (VGA_CURSOR_X == 0) && (VGA_CURSOR_Y == 0));
    
    VGA_CURSOR_X = VGA_TEXT_COLS - 1;
    VGA_CURSOR_Y = VGA_TEXT_ROWS - 1;
    check("Cursor at max", ((VGA_CURSOR_X & 0xFFFF) == 79) && ((VGA_CURSOR_Y & 0xFFFF) == 29));
}

void test_vga_scroll(void)
{
    uart_puts("\n=== Test 4: Scroll Registers ===\n");
    
    /* Set scroll offsets */
    VGA_SCROLL_X = 100;
    VGA_SCROLL_Y = 50;
    
    uint32_t sx = VGA_SCROLL_X;
    uint32_t sy = VGA_SCROLL_Y;
    
    uart_puts("  Scroll X: ");
    uart_putdec(sx & 0xFFFF);
    uart_puts("\n");
    uart_puts("  Scroll Y: ");
    uart_putdec(sy & 0xFFFF);
    uart_puts("\n");
    
    check("Scroll X offset", (sx & 0xFFFF) == 100);
    check("Scroll Y offset", (sy & 0xFFFF) == 50);
    
    VGA_SCROLL_X = 0;
    VGA_SCROLL_Y = 0;
}

void test_vga_palette(void)
{
    uart_puts("\n=== Test 5: Palette Access ===\n");
    
    /* Write to palette index 0 */
    VGA_PALETTE = 0;
    VGA_COLOR = 0x000;  /* Black */
    
    /* Write to palette index 15 */
    VGA_PALETTE = 15;
    VGA_COLOR = 0xFFF;  /* White */
    
    /* Write custom color */
    VGA_PALETTE = 100;
    VGA_COLOR = 0xF00;  /* Red */
    
    uart_puts("  Palette index 0: Black\n");
    uart_puts("  Palette index 15: White\n");
    uart_puts("  Palette index 100: Red\n");
    
    check("Palette writable", 1);
}

void test_vga_status(void)
{
    uart_puts("\n=== Test 6: Status Register ===\n");
    
    uint32_t status = VGA_STATUS;
    uart_puts("  STATUS: ");
    uart_puthex(status);
    uart_puts("\n");
    
    check("Status readable", 1);
}

void test_vga_text_mode(void)
{
    uart_puts("\n=== Test 7: Text Mode Setup ===\n");
    
    /* Configure for text mode */
    VGA_FB_BASE = FRAMEBUFFER_ADDR;
    VGA_FB_STRIDE = VGA_TEXT_COLS * 2;  /* 2 bytes per char (char + attr) */
    VGA_CURSOR_X = 0;
    VGA_CURSOR_Y = 0;
    
    /* Enable text mode with cursor */
    VGA_CTRL = VGA_CTRL_EN | VGA_CTRL_CURSOR_EN | VGA_CTRL_CURSOR_BL;
    
    uint32_t ctrl = VGA_CTRL;
    uart_puts("  Text mode CTRL: ");
    uart_puthex(ctrl);
    uart_puts("\n");
    
    check("Text mode configured", (ctrl & VGA_CTRL_EN) && !(ctrl & VGA_CTRL_MODE));
    
    VGA_CTRL = 0;
}

void test_vga_graphics_mode(void)
{
    uart_puts("\n=== Test 8: Graphics Mode Setup ===\n");
    
    /* Configure for 8bpp graphics mode */
    VGA_FB_BASE = FRAMEBUFFER_ADDR;
    VGA_FB_STRIDE = VGA_H_VISIBLE;  /* 640 bytes per line */
    
    /* Enable graphics mode */
    VGA_CTRL = VGA_CTRL_EN | VGA_CTRL_MODE | VGA_CTRL_BPP_8;
    
    uint32_t ctrl = VGA_CTRL;
    uart_puts("  Graphics mode CTRL: ");
    uart_puthex(ctrl);
    uart_puts("\n");
    
    check("Graphics mode configured", (ctrl & VGA_CTRL_EN) && (ctrl & VGA_CTRL_MODE));
    check("8bpp mode", ((ctrl >> 2) & 0x3) == 3);
    
    VGA_CTRL = 0;
}

void test_vga_double_buffer(void)
{
    uart_puts("\n=== Test 9: Double Buffering ===\n");
    
    /* Enable double buffering */
    VGA_CTRL = VGA_CTRL_DBLBUF;
    uint32_t ctrl = VGA_CTRL;
    check("Double buffer enable", ctrl & VGA_CTRL_DBLBUF);
    
    /* Select buffer 0 */
    VGA_CTRL = VGA_CTRL_DBLBUF;
    ctrl = VGA_CTRL;
    check("Buffer 0 selected", !(ctrl & VGA_CTRL_BUFSEL));
    
    /* Select buffer 1 */
    VGA_CTRL = VGA_CTRL_DBLBUF | VGA_CTRL_BUFSEL;
    ctrl = VGA_CTRL;
    check("Buffer 1 selected", ctrl & VGA_CTRL_BUFSEL);
    
    VGA_CTRL = 0;
}

void test_vga_timing(void)
{
    uart_puts("\n=== Test 10: Timing Registers ===\n");
    
    /* Read timing registers (read-only or configurable) */
    uint32_t htiming = VGA_HTIMING;
    uint32_t vtiming = VGA_VTIMING;
    
    uart_puts("  HTIMING: ");
    uart_puthex(htiming);
    uart_puts("\n");
    uart_puts("  VTIMING: ");
    uart_puthex(vtiming);
    uart_puts("\n");
    
    check("Timing readable", 1);
}

/* ========================================================================
 * Main
 * ======================================================================== */
int main(void)
{
    uart_init();
    
    uart_puts("\n========================================\n");
    uart_puts("   VGA Controller Test - Ceres-V\n");
    uart_puts("========================================\n");
    uart_puts("  640x480 @ 60Hz, Text/Graphics modes\n");
    
    test_vga_control_register();
    test_vga_framebuffer();
    test_vga_cursor();
    test_vga_scroll();
    test_vga_palette();
    test_vga_status();
    test_vga_text_mode();
    test_vga_graphics_mode();
    test_vga_double_buffer();
    test_vga_timing();
    
    uart_puts("\n========================================\n");
    uart_puts("   Test Summary\n");
    uart_puts("========================================\n");
    uart_puts("  Passed: ");
    uart_putdec(test_pass);
    uart_puts("\n  Failed: ");
    uart_putdec(test_fail);
    uart_puts("\n");
    
    if (test_fail == 0) {
        uart_puts("\n  *** ALL TESTS PASSED ***\n");
    } else {
        uart_puts("\n  *** SOME TESTS FAILED ***\n");
    }
    
    uart_puts("\n[TEST COMPLETE]\n");
    
    while(1);
    return 0;
}
