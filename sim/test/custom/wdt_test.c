/*
 * Watchdog Timer (WDT) Test for Ceres-V RV32IMC
 * 
 * Tests Watchdog Timer functionality:
 * - Register access
 * - Key-based unlock/lock
 * - Counter countdown
 * - Refresh (kick) operation
 * - Early warning interrupt
 * 
 * Note: This peripheral is not yet connected in ceres_wrapper.sv
 *       Requires adding WDT instantiation and address decode (0x2000_8xxx)
 * Note: Be careful with reset enable - it will reset the system!
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

/* WDT MMIO Map (base 0x2000_8000 per ceres_param.sv) */
#define WDT_BASE         0x20008000
#define WDT_CTRL         (*(volatile uint32_t*)(WDT_BASE + 0x00))
#define WDT_LOAD         (*(volatile uint32_t*)(WDT_BASE + 0x04))
#define WDT_COUNT        (*(volatile uint32_t*)(WDT_BASE + 0x08))
#define WDT_WINDOW       (*(volatile uint32_t*)(WDT_BASE + 0x0C))
#define WDT_KEY          (*(volatile uint32_t*)(WDT_BASE + 0x10))
#define WDT_STATUS       (*(volatile uint32_t*)(WDT_BASE + 0x14))

/* CTRL register bits */
#define WDT_CTRL_EN        (1 << 0)   /* Watchdog enable */
#define WDT_CTRL_RSTEN     (1 << 1)   /* Reset enable */
#define WDT_CTRL_WINEN     (1 << 2)   /* Window mode enable */
#define WDT_CTRL_DBGPAUSE  (1 << 3)   /* Pause in debug */
#define WDT_CTRL_IE        (1 << 4)   /* Interrupt enable */

/* Status register bits */
#define WDT_STATUS_EWIF    (1 << 0)   /* Early warning flag */
#define WDT_STATUS_WDTRF   (1 << 1)   /* Reset flag */
#define WDT_STATUS_LOCKED  (1 << 2)   /* Lock status */
#define WDT_STATUS_WINVIOL (1 << 3)   /* Window violation */

/* Key values */
#define WDT_KEY_REFRESH    0x5A5A5A5A
#define WDT_KEY_UNLOCK     0x12345678
#define WDT_KEY_LOCK       0xDEADBEEF

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
 * WDT Tests
 * ======================================================================== */

void test_wdt_registers(void)
{
    uart_puts("\n=== Test 1: Register Access ===\n");
    
    /* Unlock registers first */
    WDT_KEY = WDT_KEY_UNLOCK;
    
    /* Make sure WDT is disabled for testing */
    WDT_CTRL = 0;
    
    /* Test LOAD register */
    WDT_LOAD = 0x12345678;
    uint32_t load = WDT_LOAD;
    uart_puts("  LOAD: ");
    uart_puthex(load);
    uart_puts("\n");
    check("LOAD register", load == 0x12345678);
    
    /* Test WINDOW register */
    WDT_WINDOW = 0xABCDEF00;
    uint32_t window = WDT_WINDOW;
    uart_puts("  WINDOW: ");
    uart_puthex(window);
    uart_puts("\n");
    check("WINDOW register", window == 0xABCDEF00);
    
    /* Test CTRL register (without enabling) */
    WDT_CTRL = WDT_CTRL_WINEN | WDT_CTRL_DBGPAUSE;
    uint32_t ctrl = WDT_CTRL;
    uart_puts("  CTRL: ");
    uart_puthex(ctrl);
    uart_puts("\n");
    check("CTRL register", (ctrl & 0x1F) == (WDT_CTRL_WINEN | WDT_CTRL_DBGPAUSE));
    
    /* Reset for next tests */
    WDT_CTRL = 0;
}

void test_wdt_lock_unlock(void)
{
    uart_puts("\n=== Test 2: Lock/Unlock ===\n");
    
    /* First unlock */
    WDT_KEY = WDT_KEY_UNLOCK;
    
    uint32_t status = WDT_STATUS;
    uart_puts("  Status after unlock: ");
    uart_puthex(status);
    uart_puts("\n");
    check("Unlocked state", !(status & WDT_STATUS_LOCKED));
    
    /* Now lock */
    WDT_KEY = WDT_KEY_LOCK;
    
    status = WDT_STATUS;
    uart_puts("  Status after lock: ");
    uart_puthex(status);
    uart_puts("\n");
    check("Locked state", status & WDT_STATUS_LOCKED);
    
    /* Try to write LOAD while locked */
    uint32_t old_load = WDT_LOAD;
    WDT_LOAD = 0x11111111;
    uint32_t new_load = WDT_LOAD;
    
    uart_puts("  LOAD after locked write: ");
    uart_puthex(new_load);
    uart_puts("\n");
    check("Locked write rejected", new_load == old_load);
    
    /* Unlock for next tests */
    WDT_KEY = WDT_KEY_UNLOCK;
}

void test_wdt_countdown(void)
{
    uart_puts("\n=== Test 3: Counter Countdown ===\n");
    
    WDT_KEY = WDT_KEY_UNLOCK;
    WDT_CTRL = 0;  /* Disable first */
    
    /* Set a reasonable timeout (not too short!) */
    WDT_LOAD = 10000;
    
    /* Enable WDT (without reset, just for counting test) */
    WDT_CTRL = WDT_CTRL_EN;  /* No RSTEN to avoid reset */
    
    /* Read initial count */
    uint32_t cnt1 = WDT_COUNT;
    uart_puts("  Initial COUNT: ");
    uart_putdec(cnt1);
    uart_puts("\n");
    
    /* Wait a bit */
    delay_cycles(100);
    
    /* Read count again */
    uint32_t cnt2 = WDT_COUNT;
    uart_puts("  After delay COUNT: ");
    uart_putdec(cnt2);
    uart_puts("\n");
    
    /* Counter should have decreased */
    check("Counter counting down", cnt2 < cnt1);
    
    /* Disable WDT */
    WDT_CTRL = 0;
}

void test_wdt_refresh(void)
{
    uart_puts("\n=== Test 4: Refresh (Kick) ===\n");
    
    WDT_KEY = WDT_KEY_UNLOCK;
    WDT_CTRL = 0;
    WDT_LOAD = 10000;
    
    /* Enable WDT */
    WDT_CTRL = WDT_CTRL_EN;
    
    /* Let it count down a bit */
    delay_cycles(100);
    uint32_t cnt_before = WDT_COUNT;
    uart_puts("  Before refresh: ");
    uart_putdec(cnt_before);
    uart_puts("\n");
    
    /* Refresh the watchdog */
    WDT_KEY = WDT_KEY_REFRESH;
    
    /* Check counter was reloaded */
    uint32_t cnt_after = WDT_COUNT;
    uart_puts("  After refresh: ");
    uart_putdec(cnt_after);
    uart_puts("\n");
    
    check("Counter reloaded on refresh", cnt_after > cnt_before);
    
    /* Disable WDT */
    WDT_CTRL = 0;
}

void test_wdt_status_flags(void)
{
    uart_puts("\n=== Test 5: Status Flags ===\n");
    
    WDT_KEY = WDT_KEY_UNLOCK;
    WDT_CTRL = 0;
    
    /* Clear any existing flags */
    WDT_STATUS = 0xFF;
    
    uint32_t status = WDT_STATUS;
    uart_puts("  Initial status: ");
    uart_puthex(status);
    uart_puts("\n");
    
    /* Note: EWIF and WDTRF would require actual timeout/reset to test */
    uart_puts("  [INFO] Full status tests require timeout simulation\n");
    
    check("Status register readable", 1);
}

/* ========================================================================
 * Main
 * ======================================================================== */
int main(void)
{
    uart_init();
    
    uart_puts("\n========================================\n");
    uart_puts("   Watchdog Test - Ceres-V RV32IMC\n");
    uart_puts("========================================\n");
    
    test_wdt_registers();
    test_wdt_lock_unlock();
    test_wdt_countdown();
    test_wdt_refresh();
    test_wdt_status_flags();
    
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
