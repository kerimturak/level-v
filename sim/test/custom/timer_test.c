/*
 * Timer (GPTimer) Test for Ceres-V RV32IMC
 * 
 * Tests General Purpose Timer functionality:
 * - Timer control register access
 * - Counter increment verification
 * - Prescaler functionality
 * - Compare/Capture registers
 * - Status register flags
 * 
 * Note: This peripheral is not yet connected in ceres_wrapper.sv
 *       Requires adding Timer instantiation and address decode (0x2000_6xxx)
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

/* Timer MMIO Map (base 0x2000_6000 per ceres_param.sv) */
#define TIMER_BASE       0x20006000
#define TIMER_STRIDE     0x40    /* 0x40 bytes per timer */

/* Timer 0 registers */
#define TIM0_CTRL        (*(volatile uint32_t*)(TIMER_BASE + 0x00))
#define TIM0_CNT         (*(volatile uint32_t*)(TIMER_BASE + 0x04))
#define TIM0_PSC         (*(volatile uint32_t*)(TIMER_BASE + 0x08))
#define TIM0_ARR         (*(volatile uint32_t*)(TIMER_BASE + 0x0C))
#define TIM0_CCR0        (*(volatile uint32_t*)(TIMER_BASE + 0x10))
#define TIM0_CCR1        (*(volatile uint32_t*)(TIMER_BASE + 0x14))
#define TIM0_SR          (*(volatile uint32_t*)(TIMER_BASE + 0x18))
#define TIM0_IER         (*(volatile uint32_t*)(TIMER_BASE + 0x1C))

/* Timer 1 registers */
#define TIM1_CTRL        (*(volatile uint32_t*)(TIMER_BASE + TIMER_STRIDE + 0x00))
#define TIM1_CNT         (*(volatile uint32_t*)(TIMER_BASE + TIMER_STRIDE + 0x04))
#define TIM1_PSC         (*(volatile uint32_t*)(TIMER_BASE + TIMER_STRIDE + 0x08))
#define TIM1_ARR         (*(volatile uint32_t*)(TIMER_BASE + TIMER_STRIDE + 0x0C))

/* CTRL register bits */
#define TIM_CTRL_EN      (1 << 0)   /* Timer enable */
#define TIM_CTRL_DIR     (1 << 1)   /* Count direction (0=up, 1=down) */
#define TIM_CTRL_OPM     (1 << 2)   /* One-pulse mode */
#define TIM_CTRL_ARPE    (1 << 3)   /* Auto-reload preload enable */

/* Status register bits */
#define TIM_SR_UIF       (1 << 0)   /* Update interrupt flag */
#define TIM_SR_CC0IF     (1 << 1)   /* CC0 interrupt flag */
#define TIM_SR_CC1IF     (1 << 2)   /* CC1 interrupt flag */

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
 * Timer Tests
 * ======================================================================== */

void test_timer_registers(void)
{
    uart_puts("\n=== Test 1: Register Access ===\n");
    
    /* Stop timer first */
    TIM0_CTRL = 0;
    
    /* Test ARR (auto-reload) register */
    TIM0_ARR = 0x12345678;
    uint32_t arr = TIM0_ARR;
    uart_puts("  ARR: ");
    uart_puthex(arr);
    uart_puts("\n");
    check("ARR register", arr == 0x12345678);
    
    /* Test PSC (prescaler) register */
    TIM0_PSC = 0x0000ABCD;
    uint32_t psc = TIM0_PSC;
    uart_puts("  PSC: ");
    uart_puthex(psc);
    uart_puts("\n");
    check("PSC register (16-bit)", (psc & 0xFFFF) == 0xABCD);
    
    /* Test CCR0 register */
    TIM0_CCR0 = 0x11223344;
    check("CCR0 register", TIM0_CCR0 == 0x11223344);
    
    /* Test CCR1 register */
    TIM0_CCR1 = 0x55667788;
    check("CCR1 register", TIM0_CCR1 == 0x55667788);
    
    /* Test CTRL register */
    TIM0_CTRL = TIM_CTRL_ARPE | TIM_CTRL_DIR;
    uint32_t ctrl = TIM0_CTRL;
    uart_puts("  CTRL: ");
    uart_puthex(ctrl);
    uart_puts("\n");
    check("CTRL register", (ctrl & 0xF) == (TIM_CTRL_ARPE | TIM_CTRL_DIR));
    
    /* Cleanup */
    TIM0_CTRL = 0;
}

void test_timer_counting(void)
{
    uart_puts("\n=== Test 2: Counter Operation ===\n");
    
    /* Setup timer: no prescaler, count up to 1000 */
    TIM0_CTRL = 0;
    TIM0_PSC = 0;
    TIM0_ARR = 1000;
    TIM0_CNT = 0;  /* Reset counter if writable */
    
    /* Read initial count */
    uint32_t cnt1 = TIM0_CNT;
    uart_puts("  Initial CNT: ");
    uart_putdec(cnt1);
    uart_puts("\n");
    
    /* Enable timer */
    TIM0_CTRL = TIM_CTRL_EN;
    
    /* Wait a bit */
    delay_cycles(100);
    
    /* Read count again */
    uint32_t cnt2 = TIM0_CNT;
    uart_puts("  After delay CNT: ");
    uart_putdec(cnt2);
    uart_puts("\n");
    
    /* Counter should have incremented */
    check("Counter incrementing", cnt2 > cnt1);
    
    /* Disable timer */
    TIM0_CTRL = 0;
    
    /* Read count after stop */
    uint32_t cnt3 = TIM0_CNT;
    delay_cycles(50);
    uint32_t cnt4 = TIM0_CNT;
    
    uart_puts("  After stop CNT: ");
    uart_putdec(cnt3);
    uart_puts(" -> ");
    uart_putdec(cnt4);
    uart_puts("\n");
    check("Counter stopped", cnt4 == cnt3);
}

void test_timer_prescaler(void)
{
    uart_puts("\n=== Test 3: Prescaler ===\n");
    
    /* Setup timer with prescaler = 10 */
    TIM0_CTRL = 0;
    TIM0_PSC = 10;
    TIM0_ARR = 0xFFFFFFFF;
    TIM0_CNT = 0;
    
    /* Enable timer */
    TIM0_CTRL = TIM_CTRL_EN;
    
    /* Wait */
    delay_cycles(200);
    
    uint32_t cnt_psc = TIM0_CNT;
    uart_puts("  With PSC=10, CNT: ");
    uart_putdec(cnt_psc);
    uart_puts("\n");
    
    /* Disable and reset */
    TIM0_CTRL = 0;
    TIM0_PSC = 0;
    TIM0_CNT = 0;
    
    /* Enable without prescaler */
    TIM0_CTRL = TIM_CTRL_EN;
    delay_cycles(200);
    uint32_t cnt_nopsc = TIM0_CNT;
    
    uart_puts("  Without PSC, CNT: ");
    uart_putdec(cnt_nopsc);
    uart_puts("\n");
    
    TIM0_CTRL = 0;
    
    /* Counter without prescaler should be faster */
    check("Prescaler slows counting", cnt_nopsc > cnt_psc);
}

void test_timer_overflow(void)
{
    uart_puts("\n=== Test 4: Overflow Flag ===\n");
    
    /* Setup timer with small ARR for quick overflow */
    TIM0_CTRL = 0;
    TIM0_PSC = 0;
    TIM0_ARR = 50;
    TIM0_CNT = 0;
    TIM0_SR = 0xFF;  /* Clear all flags */
    
    /* Enable timer */
    TIM0_CTRL = TIM_CTRL_EN;
    
    /* Wait for overflow */
    delay_cycles(500);
    
    uint32_t sr = TIM0_SR;
    uart_puts("  Status: ");
    uart_puthex(sr);
    uart_puts("\n");
    
    TIM0_CTRL = 0;
    
    check("Update flag set on overflow", sr & TIM_SR_UIF);
    
    /* Clear flag by writing 1 */
    TIM0_SR = TIM_SR_UIF;
    sr = TIM0_SR;
    check("Flag cleared by W1C", !(sr & TIM_SR_UIF));
}

void test_timer_compare(void)
{
    uart_puts("\n=== Test 5: Compare Match ===\n");
    
    /* Setup timer with compare value */
    TIM0_CTRL = 0;
    TIM0_PSC = 0;
    TIM0_ARR = 1000;
    TIM0_CCR0 = 50;
    TIM0_CNT = 0;
    TIM0_SR = 0xFF;  /* Clear all flags */
    TIM0_IER = 0;    /* Disable interrupts */
    
    /* Enable timer */
    TIM0_CTRL = TIM_CTRL_EN;
    
    /* Wait for compare match */
    delay_cycles(300);
    
    uint32_t sr = TIM0_SR;
    uart_puts("  Status after compare: ");
    uart_puthex(sr);
    uart_puts("\n");
    
    TIM0_CTRL = 0;
    
    check("Compare match flag set", sr & TIM_SR_CC0IF);
}

/* ========================================================================
 * Main
 * ======================================================================== */
int main(void)
{
    uart_init();
    
    uart_puts("\n========================================\n");
    uart_puts("   Timer Test - Ceres-V RV32IMC\n");
    uart_puts("========================================\n");
    
    test_timer_registers();
    test_timer_counting();
    test_timer_prescaler();
    test_timer_overflow();
    test_timer_compare();
    
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
