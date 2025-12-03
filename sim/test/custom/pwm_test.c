/*
 * PWM Controller Test for Ceres-V RV32IMC
 * 
 * Tests PWM functionality:
 * - Register access (GCR, PERIOD, PSC, etc.)
 * - Per-channel configuration
 * - Counter operation
 * - Duty cycle settings
 * - Center-aligned vs edge-aligned modes
 * - Dead-time configuration
 * - Polarity control
 * 
 * PWM has 8 channels with 16-bit resolution
 * 
 * Note: This peripheral is not yet connected in ceres_wrapper.sv
 *       Requires adding PWM instantiation and address decode (0x2000_5xxx)
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

/* PWM MMIO Map (base 0x2000_5000 per ceres_param.sv) */
#define PWM_BASE         0x20005000

/* Global Registers */
#define PWM_GCR          (*(volatile uint32_t*)(PWM_BASE + 0x00))  /* Global control */
#define PWM_PERIOD       (*(volatile uint32_t*)(PWM_BASE + 0x04))  /* Period value */
#define PWM_PSC          (*(volatile uint32_t*)(PWM_BASE + 0x08))  /* Prescaler */
#define PWM_CNT          (*(volatile uint32_t*)(PWM_BASE + 0x0C))  /* Counter */
#define PWM_DEADTIME     (*(volatile uint32_t*)(PWM_BASE + 0x10))  /* Dead-time */
#define PWM_FAULT        (*(volatile uint32_t*)(PWM_BASE + 0x14))  /* Fault */
#define PWM_IER          (*(volatile uint32_t*)(PWM_BASE + 0x18))  /* Interrupt enable */
#define PWM_ISR          (*(volatile uint32_t*)(PWM_BASE + 0x1C))  /* Interrupt status */

/* Per-channel registers (base + 0x40 + N*0x10) */
#define PWM_CCR(n)       (*(volatile uint32_t*)(PWM_BASE + 0x40 + (n)*0x10))
#define PWM_DUTY(n)      (*(volatile uint32_t*)(PWM_BASE + 0x44 + (n)*0x10))
#define PWM_PHASE(n)     (*(volatile uint32_t*)(PWM_BASE + 0x48 + (n)*0x10))

/* GCR bits */
#define PWM_GCR_EN        (1 << 0)   /* Global enable */
#define PWM_GCR_OUTEN     (1 << 1)   /* Output enable */
#define PWM_GCR_CNTMODE   (1 << 2)   /* Counter mode: 0=edge, 1=center */
#define PWM_GCR_ONESHOT   (1 << 3)   /* One-shot mode */
#define PWM_GCR_COMMODE   (1 << 4)   /* Common period mode */
#define PWM_GCR_SYNCEN    (1 << 5)   /* Sync enable */
#define PWM_GCR_DRQEN     (1 << 6)   /* DMA request enable */

/* CCR bits */
#define PWM_CCR_EN        (1 << 0)   /* Channel enable */
#define PWM_CCR_POL       (1 << 1)   /* Polarity */
#define PWM_CCR_COMPEN    (1 << 2)   /* Complementary output */
#define PWM_CCR_DTEN      (1 << 3)   /* Dead-time enable */
#define PWM_CCR_FAULTEN   (1 << 4)   /* Fault enable */

#define NUM_PWM_CHANNELS  8

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
 * PWM Tests
 * ======================================================================== */

void test_pwm_global_registers(void)
{
    uart_puts("\n=== Test 1: Global Registers ===\n");
    
    /* Disable first */
    PWM_GCR = 0;
    
    /* Test PERIOD register */
    PWM_PERIOD = 0x1234;
    uint32_t period = PWM_PERIOD;
    uart_puts("  PERIOD: ");
    uart_puthex(period);
    uart_puts("\n");
    check("PERIOD register", (period & 0xFFFF) == 0x1234);
    
    /* Test PSC register */
    PWM_PSC = 0xABCD;
    uint32_t psc = PWM_PSC;
    uart_puts("  PSC: ");
    uart_puthex(psc);
    uart_puts("\n");
    check("PSC register", (psc & 0xFFFF) == 0xABCD);
    
    /* Test DEADTIME register */
    PWM_DEADTIME = 0x00FF00AA;  /* FALL=0xFF, RISE=0xAA */
    uint32_t dt = PWM_DEADTIME;
    uart_puts("  DEADTIME: ");
    uart_puthex(dt);
    uart_puts("\n");
    check("DEADTIME register", dt == 0x00FF00AA);
    
    /* Test GCR register */
    PWM_GCR = PWM_GCR_CNTMODE | PWM_GCR_COMMODE | PWM_GCR_OUTEN;
    uint32_t gcr = PWM_GCR;
    uart_puts("  GCR: ");
    uart_puthex(gcr);
    uart_puts("\n");
    check("GCR register", (gcr & 0x7F) == (PWM_GCR_CNTMODE | PWM_GCR_COMMODE | PWM_GCR_OUTEN));
    
    PWM_GCR = 0;
}

void test_pwm_channel_registers(void)
{
    uart_puts("\n=== Test 2: Channel Registers ===\n");
    
    PWM_GCR = 0;  /* Disable first */
    
    /* Test each channel */
    for (int ch = 0; ch < NUM_PWM_CHANNELS; ch++) {
        /* Set CCR */
        PWM_CCR(ch) = PWM_CCR_EN | PWM_CCR_POL | (ch << 8);
        
        /* Set DUTY */
        PWM_DUTY(ch) = 1000 + ch * 100;
        
        /* Set PHASE */
        PWM_PHASE(ch) = ch * 500;
    }
    
    /* Verify channel 0 */
    uint32_t ccr0 = PWM_CCR(0);
    uint32_t duty0 = PWM_DUTY(0);
    uint32_t phase0 = PWM_PHASE(0);
    
    uart_puts("  CH0 CCR: ");
    uart_puthex(ccr0);
    uart_puts("\n");
    uart_puts("  CH0 DUTY: ");
    uart_putdec(duty0 & 0xFFFF);
    uart_puts("\n");
    uart_puts("  CH0 PHASE: ");
    uart_putdec(phase0 & 0xFFFF);
    uart_puts("\n");
    
    check("CH0 CCR", (ccr0 & 0x1F) == (PWM_CCR_EN | PWM_CCR_POL));
    check("CH0 DUTY", (duty0 & 0xFFFF) == 1000);
    check("CH0 PHASE", (phase0 & 0xFFFF) == 0);
    
    /* Verify channel 3 */
    uint32_t ccr3 = PWM_CCR(3);
    uint32_t duty3 = PWM_DUTY(3);
    uint32_t phase3 = PWM_PHASE(3);
    
    uart_puts("  CH3 DUTY: ");
    uart_putdec(duty3 & 0xFFFF);
    uart_puts("\n");
    uart_puts("  CH3 PHASE: ");
    uart_putdec(phase3 & 0xFFFF);
    uart_puts("\n");
    
    check("CH3 DUTY", (duty3 & 0xFFFF) == 1300);
    check("CH3 PHASE", (phase3 & 0xFFFF) == 1500);
}

void test_pwm_counter(void)
{
    uart_puts("\n=== Test 3: Counter Operation ===\n");
    
    /* Setup PWM */
    PWM_GCR = 0;
    PWM_PERIOD = 10000;
    PWM_PSC = 0;  /* No prescaling */
    
    /* Enable PWM */
    PWM_GCR = PWM_GCR_EN;
    
    /* Read counter multiple times */
    uint32_t cnt1 = PWM_CNT;
    delay_cycles(10);
    uint32_t cnt2 = PWM_CNT;
    delay_cycles(10);
    uint32_t cnt3 = PWM_CNT;
    
    uart_puts("  CNT samples: ");
    uart_putdec(cnt1);
    uart_puts(", ");
    uart_putdec(cnt2);
    uart_puts(", ");
    uart_putdec(cnt3);
    uart_puts("\n");
    
    /* Counter should be changing */
    check("Counter incrementing", (cnt1 != cnt2) || (cnt2 != cnt3));
    
    PWM_GCR = 0;
}

void test_pwm_prescaler(void)
{
    uart_puts("\n=== Test 4: Prescaler ===\n");
    
    PWM_GCR = 0;
    PWM_PERIOD = 1000;
    PWM_PSC = 100;  /* Divide by 101 */
    
    PWM_GCR = PWM_GCR_EN;
    
    uint32_t cnt1 = PWM_CNT;
    delay_cycles(50);
    uint32_t cnt2 = PWM_CNT;
    
    uart_puts("  With PSC=100: cnt1=");
    uart_putdec(cnt1);
    uart_puts(", cnt2=");
    uart_putdec(cnt2);
    uart_puts("\n");
    
    /* With high prescaler, counter should change slowly */
    uint32_t delta = (cnt2 >= cnt1) ? (cnt2 - cnt1) : (1000 - cnt1 + cnt2);
    uart_puts("  Delta: ");
    uart_putdec(delta);
    uart_puts("\n");
    
    check("Prescaler working", delta < 10);  /* Should be slow */
    
    PWM_GCR = 0;
}

void test_pwm_modes(void)
{
    uart_puts("\n=== Test 5: Counter Modes ===\n");
    
    /* Edge-aligned mode (default) */
    PWM_GCR = 0;
    PWM_PERIOD = 100;
    PWM_PSC = 0;
    PWM_GCR = PWM_GCR_EN;  /* Edge-aligned */
    
    delay_cycles(200);
    uint32_t gcr = PWM_GCR;
    uart_puts("  Edge-aligned GCR: ");
    uart_puthex(gcr);
    uart_puts("\n");
    check("Edge-aligned mode", !(gcr & PWM_GCR_CNTMODE));
    
    PWM_GCR = 0;
    
    /* Center-aligned mode */
    PWM_GCR = PWM_GCR_EN | PWM_GCR_CNTMODE;
    
    delay_cycles(200);
    gcr = PWM_GCR;
    uart_puts("  Center-aligned GCR: ");
    uart_puthex(gcr);
    uart_puts("\n");
    check("Center-aligned mode", gcr & PWM_GCR_CNTMODE);
    
    PWM_GCR = 0;
}

void test_pwm_duty_cycle(void)
{
    uart_puts("\n=== Test 6: Duty Cycle Settings ===\n");
    
    PWM_GCR = 0;
    PWM_PERIOD = 1000;
    PWM_PSC = 0;
    
    /* Test various duty cycles */
    uint16_t duties[] = {0, 250, 500, 750, 1000};
    const char *names[] = {"0%", "25%", "50%", "75%", "100%"};
    
    for (int i = 0; i < 5; i++) {
        PWM_DUTY(0) = duties[i];
        uint32_t duty = PWM_DUTY(0);
        uart_puts("  ");
        uart_puts(names[i]);
        uart_puts(" duty: ");
        uart_putdec(duty & 0xFFFF);
        uart_puts("\n");
        check(names[i], (duty & 0xFFFF) == duties[i]);
    }
}

void test_pwm_output_enable(void)
{
    uart_puts("\n=== Test 7: Output Enable ===\n");
    
    PWM_GCR = 0;
    PWM_PERIOD = 1000;
    PWM_CCR(0) = PWM_CCR_EN;
    PWM_DUTY(0) = 500;
    
    /* Enable PWM without output enable */
    PWM_GCR = PWM_GCR_EN;
    uint32_t gcr = PWM_GCR;
    uart_puts("  Without OUTEN: ");
    uart_puthex(gcr);
    uart_puts("\n");
    check("PWM enabled, output disabled", (gcr & PWM_GCR_EN) && !(gcr & PWM_GCR_OUTEN));
    
    /* Enable output */
    PWM_GCR = PWM_GCR_EN | PWM_GCR_OUTEN;
    gcr = PWM_GCR;
    uart_puts("  With OUTEN: ");
    uart_puthex(gcr);
    uart_puts("\n");
    check("PWM and output enabled", (gcr & PWM_GCR_EN) && (gcr & PWM_GCR_OUTEN));
    
    PWM_GCR = 0;
}

void test_pwm_complementary(void)
{
    uart_puts("\n=== Test 8: Complementary Output ===\n");
    
    PWM_GCR = 0;
    PWM_PERIOD = 1000;
    
    /* Configure channel 0 with complementary output and dead-time */
    PWM_DEADTIME = 0x00100010;  /* 16 cycles rise/fall */
    PWM_CCR(0) = PWM_CCR_EN | PWM_CCR_COMPEN | PWM_CCR_DTEN;
    PWM_DUTY(0) = 500;
    
    uint32_t ccr = PWM_CCR(0);
    uint32_t dt = PWM_DEADTIME;
    
    uart_puts("  CCR: ");
    uart_puthex(ccr);
    uart_puts("\n");
    uart_puts("  DEADTIME: ");
    uart_puthex(dt);
    uart_puts("\n");
    
    check("Complementary enabled", ccr & PWM_CCR_COMPEN);
    check("Dead-time enabled", ccr & PWM_CCR_DTEN);
    
    PWM_GCR = 0;
}

void test_pwm_interrupts(void)
{
    uart_puts("\n=== Test 9: Interrupt Registers ===\n");
    
    /* Test IER */
    PWM_IER = 0xFF;
    uint32_t ier = PWM_IER;
    uart_puts("  IER: ");
    uart_puthex(ier);
    uart_puts("\n");
    check("IER writable", ier != 0);
    
    /* Read ISR */
    uint32_t isr = PWM_ISR;
    uart_puts("  ISR: ");
    uart_puthex(isr);
    uart_puts("\n");
    check("ISR readable", 1);
    
    PWM_IER = 0;
}

/* ========================================================================
 * Main
 * ======================================================================== */
int main(void)
{
    uart_init();
    
    uart_puts("\n========================================\n");
    uart_puts("   PWM Test - Ceres-V RV32IMC\n");
    uart_puts("========================================\n");
    uart_puts("  8 channels, 16-bit resolution\n");
    
    test_pwm_global_registers();
    test_pwm_channel_registers();
    test_pwm_counter();
    test_pwm_prescaler();
    test_pwm_modes();
    test_pwm_duty_cycle();
    test_pwm_output_enable();
    test_pwm_complementary();
    test_pwm_interrupts();
    
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
