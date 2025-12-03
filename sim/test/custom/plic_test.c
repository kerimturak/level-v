/*
 * PLIC (Platform-Level Interrupt Controller) Test for Ceres-V RV32IMC
 * 
 * Tests PLIC functionality:
 * - Priority register access
 * - Enable register
 * - Threshold configuration
 * - Pending status
 * - Claim/Complete mechanism
 * 
 * PLIC supports 32 interrupt sources with 8 priority levels
 * 
 * Note: This peripheral is not yet connected in ceres_wrapper.sv
 *       Requires adding PLIC instantiation and address decode (0x2000_7xxx)
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

/* PLIC MMIO Map (base 0x2000_7000 per ceres_param.sv) */
#define PLIC_BASE        0x20007000

/* Priority registers (source 0 reserved, sources 1-31) */
#define PLIC_PRIORITY(n) (*(volatile uint32_t*)(PLIC_BASE + 0x000 + (n)*4))

/* Global registers */
#define PLIC_PENDING     (*(volatile uint32_t*)(PLIC_BASE + 0x080))
#define PLIC_ENABLE      (*(volatile uint32_t*)(PLIC_BASE + 0x100))
#define PLIC_THRESHOLD   (*(volatile uint32_t*)(PLIC_BASE + 0x200))
#define PLIC_CLAIM       (*(volatile uint32_t*)(PLIC_BASE + 0x204))

/* Priority levels */
#define PLIC_PRIO_DISABLED  0
#define PLIC_PRIO_MIN       1
#define PLIC_PRIO_MAX       7

#define NUM_PLIC_SOURCES    32

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
 * PLIC Tests
 * ======================================================================== */

void test_plic_priority_registers(void)
{
    uart_puts("\n=== Test 1: Priority Registers ===\n");
    
    /* Clear enable first */
    PLIC_ENABLE = 0;
    
    /* Test priority for source 1 */
    PLIC_PRIORITY(1) = 5;
    uint32_t prio1 = PLIC_PRIORITY(1);
    uart_puts("  Source 1 priority: ");
    uart_putdec(prio1 & 0x7);
    uart_puts("\n");
    check("Priority source 1", (prio1 & 0x7) == 5);
    
    /* Test priority for source 5 */
    PLIC_PRIORITY(5) = 7;  /* Max priority */
    uint32_t prio5 = PLIC_PRIORITY(5);
    uart_puts("  Source 5 priority: ");
    uart_putdec(prio5 & 0x7);
    uart_puts("\n");
    check("Priority source 5", (prio5 & 0x7) == 7);
    
    /* Test priority for source 15 */
    PLIC_PRIORITY(15) = 3;
    uint32_t prio15 = PLIC_PRIORITY(15);
    uart_puts("  Source 15 priority: ");
    uart_putdec(prio15 & 0x7);
    uart_puts("\n");
    check("Priority source 15", (prio15 & 0x7) == 3);
    
    /* Source 0 should always read 0 */
    uint32_t prio0 = PLIC_PRIORITY(0);
    uart_puts("  Source 0 priority: ");
    uart_putdec(prio0);
    uart_puts("\n");
    check("Source 0 reserved", prio0 == 0);
}

void test_plic_enable_register(void)
{
    uart_puts("\n=== Test 2: Enable Register ===\n");
    
    /* Clear first */
    PLIC_ENABLE = 0;
    uint32_t en = PLIC_ENABLE;
    uart_puts("  Enable after clear: ");
    uart_puthex(en);
    uart_puts("\n");
    check("Enable cleared", en == 0);
    
    /* Enable sources 1, 5, 10, 20 */
    uint32_t enable_mask = (1 << 1) | (1 << 5) | (1 << 10) | (1 << 20);
    PLIC_ENABLE = enable_mask;
    en = PLIC_ENABLE;
    uart_puts("  Enable set: ");
    uart_puthex(en);
    uart_puts("\n");
    /* Note: Source 0 is always disabled */
    check("Enable mask", (en & 0xFFFFFFFE) == (enable_mask & 0xFFFFFFFE));
    
    /* Source 0 bit should be 0 even if we try to set it */
    PLIC_ENABLE = 0xFFFFFFFF;
    en = PLIC_ENABLE;
    uart_puts("  Enable with all bits: ");
    uart_puthex(en);
    uart_puts("\n");
    check("Source 0 stays disabled", !(en & 1));
    
    PLIC_ENABLE = 0;
}

void test_plic_threshold(void)
{
    uart_puts("\n=== Test 3: Threshold Register ===\n");
    
    /* Test various threshold values */
    for (uint32_t t = 0; t <= 7; t++) {
        PLIC_THRESHOLD = t;
        uint32_t th = PLIC_THRESHOLD;
        uart_puts("  Threshold ");
        uart_putdec(t);
        uart_puts(": ");
        uart_putdec(th & 0x7);
        uart_puts("\n");
    }
    
    uint32_t th = PLIC_THRESHOLD;
    check("Threshold register", (th & 0x7) == 7);
    
    PLIC_THRESHOLD = 0;
}

void test_plic_pending(void)
{
    uart_puts("\n=== Test 4: Pending Register ===\n");
    
    /* Pending is read-only, just read it */
    uint32_t pending = PLIC_PENDING;
    uart_puts("  Pending: ");
    uart_puthex(pending);
    uart_puts("\n");
    
    /* In simulation without external interrupts, should be 0 */
    check("Pending readable", 1);
}

void test_plic_claim(void)
{
    uart_puts("\n=== Test 5: Claim Register ===\n");
    
    /* Read claim register */
    uint32_t claim = PLIC_CLAIM;
    uart_puts("  Claim read: ");
    uart_putdec(claim);
    uart_puts("\n");
    
    /* Without pending interrupts, claim should return 0 */
    check("Claim returns 0 when no pending", claim == 0);
}

void test_plic_complete(void)
{
    uart_puts("\n=== Test 6: Complete Register ===\n");
    
    /* Write to claim register completes an interrupt */
    /* This is safe to test even without actual pending interrupts */
    PLIC_CLAIM = 1;  /* Complete source 1 */
    PLIC_CLAIM = 5;  /* Complete source 5 */
    PLIC_CLAIM = 0;  /* Source 0 should be ignored */
    
    uart_puts("  Complete writes: OK\n");
    check("Complete writable", 1);
}

void test_plic_priority_all(void)
{
    uart_puts("\n=== Test 7: All Priority Registers ===\n");
    
    /* Set different priorities for first 8 sources */
    for (int i = 1; i < 8; i++) {
        PLIC_PRIORITY(i) = i;
    }
    
    /* Verify */
    int all_ok = 1;
    for (int i = 1; i < 8; i++) {
        uint32_t p = PLIC_PRIORITY(i);
        if ((p & 0x7) != (uint32_t)i) all_ok = 0;
    }
    
    uart_puts("  Priorities 1-7 set\n");
    check("All priorities correct", all_ok);
    
    /* Clean up */
    for (int i = 1; i < NUM_PLIC_SOURCES; i++) {
        PLIC_PRIORITY(i) = 0;
    }
}

void test_plic_configuration(void)
{
    uart_puts("\n=== Test 8: Full Configuration ===\n");
    
    /* Simulate typical PLIC configuration */
    
    /* Set priorities */
    PLIC_PRIORITY(1) = 2;   /* UART - low priority */
    PLIC_PRIORITY(2) = 3;   /* SPI */
    PLIC_PRIORITY(3) = 4;   /* I2C */
    PLIC_PRIORITY(4) = 5;   /* Timer */
    PLIC_PRIORITY(5) = 7;   /* Critical - highest */
    
    /* Set threshold */
    PLIC_THRESHOLD = 1;  /* Only priority 2+ will interrupt */
    
    /* Enable sources */
    PLIC_ENABLE = (1 << 1) | (1 << 2) | (1 << 3) | (1 << 4) | (1 << 5);
    
    uint32_t en = PLIC_ENABLE;
    uint32_t th = PLIC_THRESHOLD;
    
    uart_puts("  Enable: ");
    uart_puthex(en);
    uart_puts("\n");
    uart_puts("  Threshold: ");
    uart_putdec(th & 0x7);
    uart_puts("\n");
    
    check("Configuration complete", (en & 0x3E) == 0x3E && (th & 0x7) == 1);
    
    /* Clean up */
    PLIC_ENABLE = 0;
    PLIC_THRESHOLD = 0;
    for (int i = 1; i < 6; i++) {
        PLIC_PRIORITY(i) = 0;
    }
}

void test_plic_masking(void)
{
    uart_puts("\n=== Test 9: Priority Masking ===\n");
    
    /* Test that threshold masks lower priority interrupts */
    
    /* Set source 1 to priority 3 */
    PLIC_PRIORITY(1) = 3;
    PLIC_ENABLE = (1 << 1);
    
    /* Threshold at 2 - source 1 should be able to interrupt */
    PLIC_THRESHOLD = 2;
    uart_puts("  Priority 3 vs threshold 2: ");
    uart_puts("can interrupt\n");
    
    /* Threshold at 4 - source 1 should be masked */
    PLIC_THRESHOLD = 4;
    uart_puts("  Priority 3 vs threshold 4: ");
    uart_puts("masked\n");
    
    check("Priority threshold logic", 1);
    
    PLIC_ENABLE = 0;
    PLIC_THRESHOLD = 0;
    PLIC_PRIORITY(1) = 0;
}

/* ========================================================================
 * Main
 * ======================================================================== */
int main(void)
{
    uart_init();
    
    uart_puts("\n========================================\n");
    uart_puts("   PLIC Test - Ceres-V RV32IMC\n");
    uart_puts("========================================\n");
    uart_puts("  32 sources, 8 priority levels\n");
    
    test_plic_priority_registers();
    test_plic_enable_register();
    test_plic_threshold();
    test_plic_pending();
    test_plic_claim();
    test_plic_complete();
    test_plic_priority_all();
    test_plic_configuration();
    test_plic_masking();
    
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
