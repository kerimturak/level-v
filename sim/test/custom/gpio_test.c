/*
 * GPIO Test for Ceres-V RV32IMC
 * 
 * Tests GPIO controller functionality:
 * - Direction control
 * - Output register write
 * - Input register read (loopback)
 * - Atomic set/clear/toggle
 * 
 * Note: This peripheral is not yet connected in ceres_wrapper.sv
 *       Requires adding GPIO instantiation and address decode (0x2000_4xxx)
 *       Currently uses loopback simulation
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
#define UART_RDATA       (*(volatile uint32_t*)0x20000008)
#define UART_WDATA       (*(volatile uint32_t*)0x2000000c)

#define UART_CTRL_TX_EN       0x1
#define UART_CTRL_RX_EN       0x2
#define UART_STATUS_TX_FULL   0x1

/* GPIO MMIO Map (base 0x2000_4000 per ceres_param.sv) */
#define GPIO_BASE        0x20004000
#define GPIO_DIR         (*(volatile uint32_t*)(GPIO_BASE + 0x00))
#define GPIO_OUT         (*(volatile uint32_t*)(GPIO_BASE + 0x04))
#define GPIO_IN          (*(volatile uint32_t*)(GPIO_BASE + 0x08))
#define GPIO_SET         (*(volatile uint32_t*)(GPIO_BASE + 0x0C))
#define GPIO_CLR         (*(volatile uint32_t*)(GPIO_BASE + 0x10))
#define GPIO_TGL         (*(volatile uint32_t*)(GPIO_BASE + 0x14))
#define GPIO_PUE         (*(volatile uint32_t*)(GPIO_BASE + 0x18))
#define GPIO_PDE         (*(volatile uint32_t*)(GPIO_BASE + 0x1C))
#define GPIO_IE          (*(volatile uint32_t*)(GPIO_BASE + 0x20))
#define GPIO_IS          (*(volatile uint32_t*)(GPIO_BASE + 0x24))

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

void uart_puthex8(uint8_t val)
{
    const char hex_chars[] = "0123456789ABCDEF";
    uart_putc(hex_chars[(val >> 4) & 0xF]);
    uart_putc(hex_chars[val & 0xF]);
}

void uart_puthex(uint32_t val)
{
    uart_puts("0x");
    for (int i = 7; i >= 0; i--) {
        uint32_t nibble = (val >> (i * 4)) & 0xF;
        uart_putc("0123456789ABCDEF"[nibble]);
    }
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

/* ========================================================================
 * GPIO Tests
 * ======================================================================== */

void test_gpio_direction(void)
{
    uart_puts("\n=== Test 1: Direction Register ===\n");
    
    /* Write direction register */
    GPIO_DIR = 0xFFFF0000;  /* Upper 16 bits output, lower 16 bits input */
    
    /* Read back */
    uint32_t dir = GPIO_DIR;
    uart_puts("  DIR: ");
    uart_puthex(dir);
    uart_puts("\n");
    
    check("Direction register write/read", dir == 0xFFFF0000);
    
    /* Test all outputs */
    GPIO_DIR = 0xFFFFFFFF;
    check("All outputs", GPIO_DIR == 0xFFFFFFFF);
    
    /* Test all inputs */
    GPIO_DIR = 0x00000000;
    check("All inputs", GPIO_DIR == 0x00000000);
}

void test_gpio_output(void)
{
    uart_puts("\n=== Test 2: Output Register ===\n");
    
    /* Set all as outputs */
    GPIO_DIR = 0xFFFFFFFF;
    
    /* Write output pattern */
    GPIO_OUT = 0xA5A5A5A5;
    uint32_t out = GPIO_OUT;
    uart_puts("  OUT: ");
    uart_puthex(out);
    uart_puts("\n");
    
    check("Output register write/read", out == 0xA5A5A5A5);
    
    /* Test alternating pattern */
    GPIO_OUT = 0x5A5A5A5A;
    check("Alternating pattern", GPIO_OUT == 0x5A5A5A5A);
}

void test_gpio_atomic_ops(void)
{
    uart_puts("\n=== Test 3: Atomic Operations ===\n");
    
    GPIO_DIR = 0xFFFFFFFF;
    GPIO_OUT = 0x00000000;
    
    /* Test SET */
    GPIO_SET = 0x000000FF;  /* Set lower 8 bits */
    uint32_t val = GPIO_OUT;
    uart_puts("  After SET: ");
    uart_puthex(val);
    uart_puts("\n");
    check("Atomic SET", val == 0x000000FF);
    
    /* Test CLR */
    GPIO_CLR = 0x0000000F;  /* Clear lower 4 bits */
    val = GPIO_OUT;
    uart_puts("  After CLR: ");
    uart_puthex(val);
    uart_puts("\n");
    check("Atomic CLR", val == 0x000000F0);
    
    /* Test TGL */
    GPIO_TGL = 0x000000FF;  /* Toggle lower 8 bits */
    val = GPIO_OUT;
    uart_puts("  After TGL: ");
    uart_puthex(val);
    uart_puts("\n");
    check("Atomic TGL", val == 0x0000000F);
}

void test_gpio_loopback(void)
{
    uart_puts("\n=== Test 4: Loopback (Simulated) ===\n");
    
    /* In simulation, GPIO input might be tied to output or external */
    /* This test checks if input register is readable */
    
    GPIO_DIR = 0xFFFFFFFF;  /* All outputs */
    GPIO_OUT = 0x12345678;
    
    /* Read input - in loopback, should match output */
    uint32_t in_val = GPIO_IN;
    uart_puts("  OUT: ");
    uart_puthex(GPIO_OUT);
    uart_puts("\n");
    uart_puts("  IN:  ");
    uart_puthex(in_val);
    uart_puts("\n");
    
    /* Note: This may not work without proper loopback in simulation */
    uart_puts("  [INFO] Loopback requires external connection\n");
}

void test_gpio_pullup(void)
{
    uart_puts("\n=== Test 5: Pull-up/Pull-down ===\n");
    
    /* Test pull-up enable register */
    GPIO_PUE = 0x0000FFFF;
    uint32_t pue = GPIO_PUE;
    uart_puts("  PUE: ");
    uart_puthex(pue);
    uart_puts("\n");
    check("Pull-up enable", pue == 0x0000FFFF);
    
    /* Test pull-down enable register */
    GPIO_PDE = 0xFFFF0000;
    uint32_t pde = GPIO_PDE;
    uart_puts("  PDE: ");
    uart_puthex(pde);
    uart_puts("\n");
    check("Pull-down enable", pde == 0xFFFF0000);
}

/* ========================================================================
 * Main
 * ======================================================================== */
int main(void)
{
    uart_init();
    
    uart_puts("\n========================================\n");
    uart_puts("   GPIO Test - Ceres-V RV32IMC\n");
    uart_puts("========================================\n");
    
    test_gpio_direction();
    test_gpio_output();
    test_gpio_atomic_ops();
    test_gpio_loopback();
    test_gpio_pullup();
    
    uart_puts("\n========================================\n");
    uart_puts("   Test Summary\n");
    uart_puts("========================================\n");
    uart_puts("  Passed: ");
    uart_putc('0' + (test_pass / 10));
    uart_putc('0' + (test_pass % 10));
    uart_puts("\n  Failed: ");
    uart_putc('0' + (test_fail / 10));
    uart_putc('0' + (test_fail % 10));
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
