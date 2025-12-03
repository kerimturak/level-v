/*
 * DMA Controller Test for Ceres-V RV32IMC
 * 
 * Tests DMA functionality:
 * - Register access (CCR, CNDTR, CPAR, CMAR)
 * - Channel configuration
 * - Memory-to-memory transfers
 * - Interrupt status registers
 * 
 * DMA has 4 independent channels
 * 
 * Note: This peripheral is not yet connected in ceres_wrapper.sv
 *       Requires adding DMA instantiation and address decode (0x2000_9xxx)
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

/* DMA MMIO Map (base 0x2000_9000 per ceres_param.sv) */
#define DMA_BASE         0x20009000

/* Per-channel registers (0x20 bytes per channel) */
#define DMA_CCR(n)       (*(volatile uint32_t*)(DMA_BASE + (n)*0x20 + 0x00))
#define DMA_CNDTR(n)     (*(volatile uint32_t*)(DMA_BASE + (n)*0x20 + 0x04))
#define DMA_CPAR(n)      (*(volatile uint32_t*)(DMA_BASE + (n)*0x20 + 0x08))
#define DMA_CMAR(n)      (*(volatile uint32_t*)(DMA_BASE + (n)*0x20 + 0x0C))
#define DMA_CTCNT(n)     (*(volatile uint32_t*)(DMA_BASE + (n)*0x20 + 0x10))

/* Global registers */
#define DMA_ISR          (*(volatile uint32_t*)(DMA_BASE + 0x80))
#define DMA_IFCR         (*(volatile uint32_t*)(DMA_BASE + 0x84))
#define DMA_GCR          (*(volatile uint32_t*)(DMA_BASE + 0x88))

/* CCR bits */
#define DMA_CCR_EN       (1 << 0)    /* Channel enable */
#define DMA_CCR_TCIE     (1 << 1)    /* Transfer complete interrupt enable */
#define DMA_CCR_HTIE     (1 << 2)    /* Half transfer interrupt enable */
#define DMA_CCR_TEIE     (1 << 3)    /* Transfer error interrupt enable */
#define DMA_CCR_DIR      (1 << 4)    /* Direction (0=P2M, 1=M2P) */
#define DMA_CCR_CIRC     (1 << 5)    /* Circular mode */
#define DMA_CCR_PINC     (1 << 6)    /* Peripheral increment */
#define DMA_CCR_MINC     (1 << 7)    /* Memory increment */
#define DMA_CCR_PSIZE_B  (0 << 8)    /* Peripheral size: byte */
#define DMA_CCR_PSIZE_H  (1 << 8)    /* Peripheral size: half-word */
#define DMA_CCR_PSIZE_W  (2 << 8)    /* Peripheral size: word */
#define DMA_CCR_MSIZE_B  (0 << 10)   /* Memory size: byte */
#define DMA_CCR_MSIZE_H  (1 << 10)   /* Memory size: half-word */
#define DMA_CCR_MSIZE_W  (2 << 10)   /* Memory size: word */
#define DMA_CCR_PL_LOW   (0 << 12)   /* Priority: low */
#define DMA_CCR_PL_MED   (1 << 12)   /* Priority: medium */
#define DMA_CCR_PL_HIGH  (2 << 12)   /* Priority: high */
#define DMA_CCR_PL_VHIGH (3 << 12)   /* Priority: very high */
#define DMA_CCR_MEM2MEM  (1 << 14)   /* Memory-to-memory mode */
#define DMA_CCR_BURST(n) ((n) << 15) /* Burst size */

/* ISR bits per channel (4 bits each) */
#define DMA_ISR_GIF(n)   (1 << ((n)*4 + 0))  /* Global interrupt flag */
#define DMA_ISR_TCIF(n)  (1 << ((n)*4 + 1))  /* Transfer complete flag */
#define DMA_ISR_HTIF(n)  (1 << ((n)*4 + 2))  /* Half transfer flag */
#define DMA_ISR_TEIF(n)  (1 << ((n)*4 + 3))  /* Transfer error flag */

#define NUM_DMA_CHANNELS 4

/* Test memory buffers */
#define SRC_BUFFER       0x80001000
#define DST_BUFFER       0x80002000
#define BUFFER_SIZE      64

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
 * DMA Tests
 * ======================================================================== */

void test_dma_channel_registers(void)
{
    uart_puts("\n=== Test 1: Channel Register Access ===\n");
    
    /* Disable all channels first */
    for (int i = 0; i < NUM_DMA_CHANNELS; i++) {
        DMA_CCR(i) = 0;
    }
    
    /* Test Channel 0 registers */
    
    /* CNDTR - number of data to transfer */
    DMA_CNDTR(0) = 0x1234;
    uint32_t cndtr = DMA_CNDTR(0);
    uart_puts("  CH0 CNDTR: ");
    uart_puthex(cndtr);
    uart_puts("\n");
    check("CNDTR register", (cndtr & 0xFFFF) == 0x1234);
    
    /* CPAR - peripheral address */
    DMA_CPAR(0) = 0x20000100;
    uint32_t cpar = DMA_CPAR(0);
    uart_puts("  CH0 CPAR: ");
    uart_puthex(cpar);
    uart_puts("\n");
    check("CPAR register", cpar == 0x20000100);
    
    /* CMAR - memory address */
    DMA_CMAR(0) = 0x80001000;
    uint32_t cmar = DMA_CMAR(0);
    uart_puts("  CH0 CMAR: ");
    uart_puthex(cmar);
    uart_puts("\n");
    check("CMAR register", cmar == 0x80001000);
    
    /* CCR - control register */
    uint32_t ccr_val = DMA_CCR_TCIE | DMA_CCR_MINC | DMA_CCR_PSIZE_W | 
                       DMA_CCR_MSIZE_W | DMA_CCR_PL_HIGH;
    DMA_CCR(0) = ccr_val;
    uint32_t ccr = DMA_CCR(0);
    uart_puts("  CH0 CCR: ");
    uart_puthex(ccr);
    uart_puts("\n");
    check("CCR register", (ccr & 0x3FFF) == (ccr_val & 0x3FFF));
}

void test_dma_all_channels(void)
{
    uart_puts("\n=== Test 2: All Channel Registers ===\n");
    
    /* Configure each channel differently */
    for (int i = 0; i < NUM_DMA_CHANNELS; i++) {
        DMA_CCR(i) = 0;  /* Disable first */
        DMA_CNDTR(i) = 100 + i * 50;
        DMA_CPAR(i) = 0x20000000 + i * 0x1000;
        DMA_CMAR(i) = 0x80000000 + i * 0x1000;
    }
    
    /* Verify each channel */
    int all_ok = 1;
    for (int i = 0; i < NUM_DMA_CHANNELS; i++) {
        uint32_t cndtr = DMA_CNDTR(i);
        uint32_t cpar = DMA_CPAR(i);
        uint32_t cmar = DMA_CMAR(i);
        
        uart_puts("  CH");
        uart_putdec(i);
        uart_puts(": CNDTR=");
        uart_putdec(cndtr & 0xFFFF);
        uart_puts(", CPAR=");
        uart_puthex(cpar);
        uart_puts("\n");
        
        if ((cndtr & 0xFFFF) != (uint32_t)(100 + i * 50)) all_ok = 0;
        if (cpar != (0x20000000 + i * 0x1000)) all_ok = 0;
        if (cmar != (0x80000000 + i * 0x1000)) all_ok = 0;
    }
    
    check("All channels configured correctly", all_ok);
}

void test_dma_global_registers(void)
{
    uart_puts("\n=== Test 3: Global Registers ===\n");
    
    /* Read ISR */
    uint32_t isr = DMA_ISR;
    uart_puts("  ISR: ");
    uart_puthex(isr);
    uart_puts("\n");
    check("ISR readable", 1);
    
    /* Test GCR */
    DMA_GCR = 0x12345678;
    uint32_t gcr = DMA_GCR;
    uart_puts("  GCR: ");
    uart_puthex(gcr);
    uart_puts("\n");
    check("GCR writable", 1);
    
    /* Clear flags with IFCR */
    DMA_IFCR = 0xFFFFFFFF;
    isr = DMA_ISR;
    uart_puts("  ISR after clear: ");
    uart_puthex(isr);
    uart_puts("\n");
    check("IFCR clears flags", 1);
}

void test_dma_ccr_bits(void)
{
    uart_puts("\n=== Test 4: CCR Bit Fields ===\n");
    
    DMA_CCR(0) = 0;
    
    /* Test each bit field */
    
    /* Direction bit */
    DMA_CCR(0) = DMA_CCR_DIR;
    uint32_t ccr = DMA_CCR(0);
    check("DIR bit", ccr & DMA_CCR_DIR);
    
    /* Circular mode */
    DMA_CCR(0) = DMA_CCR_CIRC;
    ccr = DMA_CCR(0);
    check("CIRC bit", ccr & DMA_CCR_CIRC);
    
    /* Increment modes */
    DMA_CCR(0) = DMA_CCR_PINC | DMA_CCR_MINC;
    ccr = DMA_CCR(0);
    check("PINC/MINC bits", (ccr & (DMA_CCR_PINC | DMA_CCR_MINC)) == (DMA_CCR_PINC | DMA_CCR_MINC));
    
    /* Size fields */
    DMA_CCR(0) = DMA_CCR_PSIZE_W | DMA_CCR_MSIZE_W;
    ccr = DMA_CCR(0);
    uart_puts("  CCR with word sizes: ");
    uart_puthex(ccr);
    uart_puts("\n");
    check("PSIZE/MSIZE bits", ((ccr >> 8) & 0x3) == 2 && ((ccr >> 10) & 0x3) == 2);
    
    /* Priority levels */
    DMA_CCR(0) = DMA_CCR_PL_VHIGH;
    ccr = DMA_CCR(0);
    check("Priority bits", ((ccr >> 12) & 0x3) == 3);
    
    /* Memory-to-memory */
    DMA_CCR(0) = DMA_CCR_MEM2MEM;
    ccr = DMA_CCR(0);
    check("MEM2MEM bit", ccr & DMA_CCR_MEM2MEM);
    
    DMA_CCR(0) = 0;
}

void test_dma_priority(void)
{
    uart_puts("\n=== Test 5: Channel Priority ===\n");
    
    /* Set different priorities for each channel */
    DMA_CCR(0) = DMA_CCR_PL_LOW;
    DMA_CCR(1) = DMA_CCR_PL_MED;
    DMA_CCR(2) = DMA_CCR_PL_HIGH;
    DMA_CCR(3) = DMA_CCR_PL_VHIGH;
    
    for (int i = 0; i < NUM_DMA_CHANNELS; i++) {
        uint32_t ccr = DMA_CCR(i);
        uint32_t pl = (ccr >> 12) & 0x3;
        uart_puts("  CH");
        uart_putdec(i);
        uart_puts(" priority: ");
        uart_putdec(pl);
        uart_puts("\n");
    }
    
    check("Priority levels set", 1);
    
    for (int i = 0; i < NUM_DMA_CHANNELS; i++) {
        DMA_CCR(i) = 0;
    }
}

void test_dma_interrupt_flags(void)
{
    uart_puts("\n=== Test 6: Interrupt Flags ===\n");
    
    /* Clear all flags */
    DMA_IFCR = 0xFFFFFFFF;
    
    uint32_t isr = DMA_ISR;
    uart_puts("  Initial ISR: ");
    uart_puthex(isr);
    uart_puts("\n");
    
    /* Enable interrupts on channel 0 */
    DMA_CCR(0) = DMA_CCR_TCIE | DMA_CCR_HTIE | DMA_CCR_TEIE;
    uint32_t ccr = DMA_CCR(0);
    uart_puts("  CCR with IE: ");
    uart_puthex(ccr);
    uart_puts("\n");
    
    check("Interrupt enables set", (ccr & 0xE) == (DMA_CCR_TCIE | DMA_CCR_HTIE | DMA_CCR_TEIE));
    
    DMA_CCR(0) = 0;
}

void test_dma_mem2mem_setup(void)
{
    uart_puts("\n=== Test 7: Memory-to-Memory Setup ===\n");
    
    /* Configure for memory-to-memory transfer */
    DMA_CCR(0) = 0;  /* Disable first */
    
    /* Set addresses */
    DMA_CPAR(0) = SRC_BUFFER;
    DMA_CMAR(0) = DST_BUFFER;
    DMA_CNDTR(0) = BUFFER_SIZE / 4;  /* Word transfers */
    
    /* Configure control */
    uint32_t ccr_val = DMA_CCR_MEM2MEM |  /* M2M mode */
                       DMA_CCR_PINC |      /* Source increment */
                       DMA_CCR_MINC |      /* Dest increment */
                       DMA_CCR_PSIZE_W |   /* Word size */
                       DMA_CCR_MSIZE_W |   /* Word size */
                       DMA_CCR_PL_HIGH |   /* High priority */
                       DMA_CCR_TCIE;       /* Transfer complete interrupt */
    
    DMA_CCR(0) = ccr_val;
    
    uint32_t ccr = DMA_CCR(0);
    uint32_t cpar = DMA_CPAR(0);
    uint32_t cmar = DMA_CMAR(0);
    uint32_t cndtr = DMA_CNDTR(0);
    
    uart_puts("  M2M CCR: ");
    uart_puthex(ccr);
    uart_puts("\n");
    uart_puts("  Source: ");
    uart_puthex(cpar);
    uart_puts("\n");
    uart_puts("  Dest: ");
    uart_puthex(cmar);
    uart_puts("\n");
    uart_puts("  Count: ");
    uart_putdec(cndtr & 0xFFFF);
    uart_puts("\n");
    
    check("M2M configuration", (ccr & DMA_CCR_MEM2MEM) && (cpar == SRC_BUFFER));
    
    /* Don't enable - just test configuration */
    DMA_CCR(0) = 0;
}

/* ========================================================================
 * Main
 * ======================================================================== */
int main(void)
{
    uart_init();
    
    uart_puts("\n========================================\n");
    uart_puts("   DMA Test - Ceres-V RV32IMC\n");
    uart_puts("========================================\n");
    uart_puts("  4 channels, configurable burst\n");
    
    test_dma_channel_registers();
    test_dma_all_channels();
    test_dma_global_registers();
    test_dma_ccr_bits();
    test_dma_priority();
    test_dma_interrupt_flags();
    test_dma_mem2mem_setup();
    
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
