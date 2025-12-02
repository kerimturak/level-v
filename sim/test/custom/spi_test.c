/**
 * SPI Loopback Test - Ceres-V RV32IMC_Zicsr
 * 
 * Test program that verifies SPI master functionality using loopback
 * Connect MOSI to MISO externally for this test, or the testbench
 * will provide loopback functionality
 */

#include <stdint.h>
#include <string.h>

/* ========================================================================
 * Hardware Definitions
 * ======================================================================== */
#define CPU_CLK          50000000   /* 50 MHz */
#define BAUD_RATE        115200

/* UART MMIO Map */
#define UART_CTRL        (*(volatile uint32_t*)0x20000000)
#define UART_STATUS      (*(volatile uint32_t*)0x20000004)
#define UART_RDATA       (*(volatile uint32_t*)0x20000008)
#define UART_WDATA       (*(volatile uint32_t*)0x2000000c)

/* UART Status Register Bits */
#define UART_STATUS_TX_FULL   0x1
#define UART_STATUS_RX_FULL   0x2
#define UART_STATUS_TX_EMPTY  0x4
#define UART_STATUS_RX_EMPTY  0x8

/* UART Control Register Bits */
#define UART_CTRL_TX_EN   0x1
#define UART_CTRL_RX_EN   0x2

/* SPI MMIO Map (base 0x2001_0000) */
#define SPI_CTRL         (*(volatile uint32_t*)0x20010000)
#define SPI_STATUS       (*(volatile uint32_t*)0x20010004)
#define SPI_RDATA        (*(volatile uint32_t*)0x20010008)
#define SPI_WDATA        (*(volatile uint32_t*)0x2001000c)

/* SPI Control Register Bits
 * [31:16] sck_div  - Clock divider
 * [3]     cpol     - Clock polarity
 * [2]     cpha     - Clock phase  
 * [1]     cs_n     - Chip select (0=active, 1=inactive)
 * [0]     spi_en   - SPI enable
 */
#define SPI_CTRL_EN       0x01
#define SPI_CTRL_CS_N     0x02
#define SPI_CTRL_CPHA     0x04
#define SPI_CTRL_CPOL     0x08

/* SPI Status Register Bits
 * [3] tx_empty
 * [2] tx_full
 * [1] rx_empty
 * [0] rx_full
 */
#define SPI_STATUS_RX_FULL    0x01
#define SPI_STATUS_RX_EMPTY   0x02
#define SPI_STATUS_TX_FULL    0x04
#define SPI_STATUS_TX_EMPTY   0x08

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
    const char hex_chars[] = "0123456789ABCDEF";
    uart_puts("0x");
    for (int i = 7; i >= 0; i--) {
        uint32_t nibble = (val >> (i * 4)) & 0xF;
        uart_putc(hex_chars[nibble]);
    }
}

void uart_puthex8(uint8_t val)
{
    const char hex_chars[] = "0123456789ABCDEF";
    uart_putc(hex_chars[(val >> 4) & 0xF]);
    uart_putc(hex_chars[val & 0xF]);
}

/* ========================================================================
 * SPI Functions
 * ======================================================================== */

/**
 * Initialize SPI with given clock divider and mode
 * @param sck_div  Clock divider (SPI clock = CPU_CLK / (2 * sck_div))
 * @param mode     SPI mode (0-3)
 */
void spi_init(uint16_t sck_div, uint8_t mode)
{
    uint32_t ctrl = (sck_div << 16);
    
    /* Set CPOL/CPHA based on mode */
    if (mode & 0x02) ctrl |= SPI_CTRL_CPOL;
    if (mode & 0x01) ctrl |= SPI_CTRL_CPHA;
    
    /* Enable SPI, CS inactive */
    ctrl |= SPI_CTRL_EN | SPI_CTRL_CS_N;
    
    SPI_CTRL = ctrl;
}

/**
 * Assert chip select (active low)
 */
void spi_cs_low(void)
{
    uint32_t ctrl = SPI_CTRL;
    ctrl &= ~SPI_CTRL_CS_N;  /* Clear CS_N bit (CS active) */
    SPI_CTRL = ctrl;
}

/**
 * Deassert chip select
 */
void spi_cs_high(void)
{
    uint32_t ctrl = SPI_CTRL;
    ctrl |= SPI_CTRL_CS_N;   /* Set CS_N bit (CS inactive) */
    SPI_CTRL = ctrl;
}

/**
 * Wait until TX FIFO is not full (with timeout)
 */
static inline int spi_wait_tx_ready(void)
{
    int timeout = 10000;
    while ((SPI_STATUS & SPI_STATUS_TX_FULL) && --timeout > 0);
    return timeout > 0;
}

/**
 * Wait until RX FIFO has data (with timeout)
 */
static inline int spi_wait_rx_ready(void)
{
    int timeout = 10000;
    while ((SPI_STATUS & SPI_STATUS_RX_EMPTY) && --timeout > 0);
    return timeout > 0;
}

/**
 * Transfer a single byte (full duplex)
 * Returns received byte, or 0xFF on timeout
 */
uint8_t spi_transfer(uint8_t tx_data)
{
    /* Wait for TX ready */
    if (!spi_wait_tx_ready()) {
        uart_puts("TX timeout! ");
        return 0xFF;
    }
    
    /* Write TX data */
    SPI_WDATA = tx_data;
    
    /* Wait for transfer complete (RX data available) */
    if (!spi_wait_rx_ready()) {
        uart_puts("RX timeout! ");
        return 0xFF;
    }
    
    /* Read RX data */
    return (uint8_t)(SPI_RDATA & 0xFF);
}

/**
 * Transfer multiple bytes
 */
void spi_transfer_buf(uint8_t *tx_buf, uint8_t *rx_buf, uint32_t len)
{
    for (uint32_t i = 0; i < len; i++) {
        rx_buf[i] = spi_transfer(tx_buf[i]);
    }
}

/* ========================================================================
 * Test Functions
 * ======================================================================== */

int test_spi_loopback(void)
{
    int errors = 0;
    
    uart_puts("\n[TEST] SPI Loopback Test\n");
    
    /* Initialize SPI: Fast clock for simulation, Mode 0 */
    /* sck_div=2 means SPI clock = CPU_CLK/(2*2) = 12.5MHz */
    spi_init(2, 0);
    uart_puts("  init done\n");
    
    /* Assert CS */
    spi_cs_low();
    uart_puts("  CS low\n");
    
    /* Test pattern */
    uint8_t test_data[] = {0xA5, 0x5A, 0xFF, 0x00, 0x12, 0x34, 0x56, 0x78};
    uint8_t rx_data[8];
    
    uart_puts("  Sending: ");
    for (int i = 0; i < 8; i++) {
        uart_puthex8(test_data[i]);
        uart_putc(' ');
    }
    uart_puts("\n");
    
    /* Transfer data */
    spi_transfer_buf(test_data, rx_data, 8);
    
    uart_puts("  Received: ");
    for (int i = 0; i < 8; i++) {
        uart_puthex8(rx_data[i]);
        uart_putc(' ');
    }
    uart_puts("\n");
    
    /* In loopback, MISO connected to MOSI, so we should receive what we sent
     * But there's typically 1 byte delay in loopback due to shift register */
    uart_puts("  Note: With external loopback, TX[n] should equal RX[n+1]\n");
    
    /* Deassert CS */
    spi_cs_high();
    
    /* Check if SPI engine completed without error */
    uint32_t status = SPI_STATUS;
    uart_puts("  Final status: ");
    uart_puthex(status);
    uart_puts("\n");
    
    if (status & SPI_STATUS_TX_EMPTY) {
        uart_puts("  TX FIFO empty: OK\n");
    } else {
        uart_puts("  TX FIFO not empty: FAIL\n");
        errors++;
    }
    
    return errors;
}

int test_spi_modes(void)
{
    int errors = 0;
    
    uart_puts("\n[TEST] SPI Mode Test\n");
    
    for (int mode = 0; mode < 4; mode++) {
        uart_puts("  Testing Mode ");
        uart_putc('0' + mode);
        uart_puts("... ");
        
        spi_init(2, mode);  /* Fast clock for simulation */
        spi_cs_low();
        
        uint8_t tx = 0xAA;
        uint8_t rx = spi_transfer(tx);
        
        spi_cs_high();
        
        uart_puts("TX=");
        uart_puthex8(tx);
        uart_puts(" RX=");
        uart_puthex8(rx);
        uart_puts("\n");
    }
    
    return errors;
}

int test_spi_registers(void)
{
    uart_puts("\n[TEST] SPI Register Test\n");
    int errors = 0;
    
    /* Read initial status */
    uart_puts("  Initial STATUS: ");
    uart_puthex(SPI_STATUS);
    uart_puts("\n");
    
    /* Write to CTRL and read back */
    uint32_t test_ctrl = (100 << 16) | SPI_CTRL_EN | SPI_CTRL_CS_N;
    SPI_CTRL = test_ctrl;
    
    uint32_t read_ctrl = SPI_CTRL;
    uart_puts("  CTRL write: ");
    uart_puthex(test_ctrl);
    uart_puts(" read: ");
    uart_puthex(read_ctrl);
    
    if ((read_ctrl & 0xFFFF000F) == (test_ctrl & 0xFFFF000F)) {
        uart_puts(" OK\n");
    } else {
        uart_puts(" FAIL\n");
        errors++;
    }
    
    return errors;
}

/* ========================================================================
 * Main Entry Point
 * ======================================================================== */

void main(void)
{
    int total_errors = 0;
    
    /* Initialize UART for debug output */
    uart_init();
    
    uart_puts("\n");
    uart_puts("========================================\n");
    uart_puts("  Ceres-V SPI Test Program\n");
    uart_puts("========================================\n");
    
    /* Run tests */
    total_errors += test_spi_registers();
    total_errors += test_spi_loopback();
    total_errors += test_spi_modes();
    
    /* Summary */
    uart_puts("\n========================================\n");
    if (total_errors == 0) {
        uart_puts("  ALL TESTS PASSED!\n");
    } else {
        uart_puts("  TESTS FAILED: ");
        uart_putc('0' + total_errors);
        uart_puts(" errors\n");
    }
    uart_puts("========================================\n");
    
    /* Signal test complete */
    while (1) {
        asm volatile("wfi");
    }
}
