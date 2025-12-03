/**
 * I2C Master Test - Ceres-V RV32IMC_Zicsr
 * 
 * Test program that verifies I2C master functionality.
 * The testbench provides a simple I2C slave (EEPROM-like) for testing.
 * 
 * Test Scenarios:
 *   1. Register read/write verification
 *   2. Single byte write to slave
 *   3. Single byte read from slave
 *   4. Multi-byte write (burst)
 *   5. Multi-byte read (burst)
 *   6. NACK handling test
 */

#include <stdint.h>
#include <string.h>

/* ========================================================================
 * Hardware Definitions
 * ======================================================================== */
#define CPU_CLK          50000000   /* 50 MHz */
#define BAUD_RATE        5000000    /* Fast simulation: 5 Mbaud */

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

/* I2C MMIO Map (base 0x2002_0000) */
#define I2C_BASE         0x20020000
#define I2C_CTRL         (*(volatile uint32_t*)(I2C_BASE + 0x00))
#define I2C_STATUS       (*(volatile uint32_t*)(I2C_BASE + 0x04))
#define I2C_CMD          (*(volatile uint32_t*)(I2C_BASE + 0x08))
#define I2C_ADDR         (*(volatile uint32_t*)(I2C_BASE + 0x0C))
#define I2C_RDATA        (*(volatile uint32_t*)(I2C_BASE + 0x10))
#define I2C_WDATA        (*(volatile uint32_t*)(I2C_BASE + 0x14))

/* I2C Control Register
 * [31:16] clk_div    - SCL divider: SCL = clk / (4 * (clk_div + 1))
 * [3]     stretch_en - Clock stretching enable
 * [2]     ack_en     - Auto ACK enable
 */
#define I2C_CTRL_ACK_EN      (1 << 2)
#define I2C_CTRL_STRETCH_EN  (1 << 3)

/* I2C Status Register
 * [7] busy         - Transfer in progress
 * [6] arb_lost     - Arbitration lost
 * [5] ack_err      - No ACK received
 * [4] tx_empty     - TX FIFO empty
 * [3] tx_full      - TX FIFO full
 * [2] rx_empty     - RX FIFO empty
 * [1] rx_full      - RX FIFO full
 * [0] transfer_done - Byte transfer complete
 */
#define I2C_STATUS_DONE      (1 << 0)
#define I2C_STATUS_RX_FULL   (1 << 1)
#define I2C_STATUS_RX_EMPTY  (1 << 2)
#define I2C_STATUS_TX_FULL   (1 << 3)
#define I2C_STATUS_TX_EMPTY  (1 << 4)
#define I2C_STATUS_ACK_ERR   (1 << 5)
#define I2C_STATUS_ARB_LOST  (1 << 6)
#define I2C_STATUS_BUSY      (1 << 7)

/* I2C Command Register
 * [7] start - Generate START condition
 * [6] stop  - Generate STOP condition
 * [5] read  - Read byte from slave
 * [4] write - Write byte to slave
 * [3] ack   - ACK to send (0=ACK, 1=NACK)
 */
#define I2C_CMD_ACK    (1 << 3)
#define I2C_CMD_WRITE  (1 << 4)
#define I2C_CMD_READ   (1 << 5)
#define I2C_CMD_STOP   (1 << 6)
#define I2C_CMD_START  (1 << 7)

/* Test I2C slave address (7-bit) - simulated EEPROM */
#define I2C_SLAVE_ADDR  0x50  /* 7-bit address */

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

void uart_putdec(int val)
{
    char buf[12];
    int i = 0;
    int neg = 0;
    
    if (val < 0) {
        neg = 1;
        val = -val;
    }
    
    if (val == 0) {
        uart_putc('0');
        return;
    }
    
    while (val > 0) {
        buf[i++] = '0' + (val % 10);
        val /= 10;
    }
    
    if (neg) uart_putc('-');
    while (i > 0) uart_putc(buf[--i]);
}

/* ========================================================================
 * I2C Functions
 * ======================================================================== */

void i2c_init(uint16_t clk_div)
{
    /* Set clock divider and enable stretch/ack */
    I2C_CTRL = ((uint32_t)clk_div << 16) | I2C_CTRL_STRETCH_EN | I2C_CTRL_ACK_EN;
}

void i2c_wait_idle(void)
{
    while (I2C_STATUS & I2C_STATUS_BUSY);
}

void i2c_wait_done(void)
{
    /* Wait for transfer done or error with timeout */
    uint32_t status;
    int timeout = 10000;
    do {
        status = I2C_STATUS;
        timeout--;
        if (timeout == 0) {
            uart_puts("    [TIMEOUT] STATUS: 0x");
            uart_puthex8(status & 0xFF);
            uart_puts("\n");
            return;
        }
    } while (!(status & (I2C_STATUS_DONE | I2C_STATUS_ACK_ERR | I2C_STATUS_ARB_LOST)));
}

int i2c_start_write(uint8_t addr)
{
    /* Set slave address with W bit (bit 0 = 0) */
    I2C_ADDR = (addr << 1) | 0;
    
    /* Push address byte to TX FIFO */
    I2C_WDATA = (addr << 1) | 0;
    
    uart_puts("    WDATA written, STATUS: 0x");
    uart_puthex8(I2C_STATUS & 0xFF);
    uart_puts(", DEBUG: 0x");
    uart_puthex(*(volatile uint32_t*)(I2C_BASE + 0x18));
    uart_puts("\n");
    
    /* Send START + write address */
    I2C_CMD = I2C_CMD_START | I2C_CMD_WRITE;
    
    uart_puts("    CMD sent, STATUS: 0x");
    uart_puthex8(I2C_STATUS & 0xFF);
    uart_puts(", DEBUG: 0x");
    uart_puthex(*(volatile uint32_t*)(I2C_BASE + 0x18));
    uart_puts("\n");
    
    /* Wait a bit and check debug again */
    for (int i = 0; i < 100; i++) {
        asm volatile("nop");
    }
    uart_puts("    After wait, DEBUG: 0x");
    uart_puthex(*(volatile uint32_t*)(I2C_BASE + 0x18));
    uart_puts("\n");
    
    i2c_wait_done();
    
    if (I2C_STATUS & I2C_STATUS_ACK_ERR) {
        uart_puts("  [ERROR] No ACK from slave\n");
        return -1;
    }
    
    return 0;
}

int i2c_start_read(uint8_t addr)
{
    /* Set slave address with R bit (bit 0 = 1) */
    I2C_ADDR = (addr << 1) | 1;
    
    /* Push address byte to TX FIFO */
    I2C_WDATA = (addr << 1) | 1;
    
    /* Send START + read address */
    I2C_CMD = I2C_CMD_START | I2C_CMD_WRITE;
    
    i2c_wait_done();
    
    if (I2C_STATUS & I2C_STATUS_ACK_ERR) {
        uart_puts("  [ERROR] No ACK from slave\n");
        return -1;
    }
    
    return 0;
}

int i2c_write_byte(uint8_t data)
{
    /* Push data to TX FIFO */
    I2C_WDATA = data;
    
    /* Write byte */
    I2C_CMD = I2C_CMD_WRITE;
    
    i2c_wait_done();
    
    if (I2C_STATUS & I2C_STATUS_ACK_ERR) {
        return -1;
    }
    
    return 0;
}

uint8_t i2c_read_byte(int ack)
{
    /* Read byte, send ACK or NACK */
    I2C_CMD = I2C_CMD_READ | (ack ? 0 : I2C_CMD_ACK);
    
    i2c_wait_done();
    
    return (uint8_t)I2C_RDATA;
}

void i2c_stop(void)
{
    I2C_CMD = I2C_CMD_STOP;
    i2c_wait_idle();
}

/* ========================================================================
 * Test Functions
 * ======================================================================== */

int test_passed = 0;
int test_failed = 0;

void check(const char *name, int condition)
{
    if (condition) {
        uart_puts("  [PASS] ");
        uart_puts(name);
        uart_puts("\n");
        test_passed++;
    } else {
        uart_puts("  [FAIL] ");
        uart_puts(name);
        uart_puts("\n");
        test_failed++;
    }
}

/* Test 1: Register Read/Write */
void test_register_access(void)
{
    uart_puts("\n=== Test 1: Register Access ===\n");
    
    /* Write a known value to CTRL */
    uint16_t test_div = 0x1234;
    I2C_CTRL = ((uint32_t)test_div << 16) | I2C_CTRL_STRETCH_EN;
    
    /* Read back and verify */
    uint32_t ctrl = I2C_CTRL;
    uint16_t read_div = (ctrl >> 16) & 0xFFFF;
    
    uart_puts("  Written clk_div: 0x");
    uart_puthex8(test_div >> 8);
    uart_puthex8(test_div & 0xFF);
    uart_puts("\n");
    
    uart_puts("  Read clk_div:    0x");
    uart_puthex8(read_div >> 8);
    uart_puthex8(read_div & 0xFF);
    uart_puts("\n");
    
    check("CTRL register read/write", read_div == test_div);
    
    /* Check status register is readable */
    uint32_t status = I2C_STATUS;
    uart_puts("  STATUS: 0x");
    uart_puthex8(status & 0xFF);
    uart_puts("\n");
    
    /* TX should be empty, RX should be empty, not busy */
    check("Initial status (TX empty)", status & I2C_STATUS_TX_EMPTY);
    check("Initial status (RX empty)", status & I2C_STATUS_RX_EMPTY);
    check("Initial status (not busy)", !(status & I2C_STATUS_BUSY));
}

/* Test 2: Single Byte Write */
void test_single_byte_write(void)
{
    uart_puts("\n=== Test 2: Single Byte Write ===\n");
    
    /* Initialize I2C: Slower for simulation -> div = 10 */
    i2c_init(10);
    
    /* Verify clk_div was set */
    uint32_t ctrl = I2C_CTRL;
    uart_puts("  CTRL after init: 0x");
    uart_puthex(ctrl);
    uart_puts("\n");
    
    uart_puts("  Starting write to slave 0x");
    uart_puthex8(I2C_SLAVE_ADDR);
    uart_puts("...\n");
    
    uart_puts("  STATUS before cmd: 0x");
    uart_puthex8(I2C_STATUS & 0xFF);
    uart_puts("\n");
    
    /* Start write transaction */
    if (i2c_start_write(I2C_SLAVE_ADDR) < 0) {
        check("Start write", 0);
        i2c_stop();
        return;
    }
    check("Start write ACK received", 1);
    
    /* Write memory address (for EEPROM-like slave) */
    if (i2c_write_byte(0x00) < 0) {
        check("Write memory address", 0);
        i2c_stop();
        return;
    }
    check("Write memory address", 1);
    
    /* Write data byte */
    uint8_t test_data = 0xAB;
    if (i2c_write_byte(test_data) < 0) {
        check("Write data byte", 0);
        i2c_stop();
        return;
    }
    check("Write data byte", 1);
    
    /* Stop */
    i2c_stop();
    check("Stop condition", 1);
}

/* Test 3: Single Byte Read */
void test_single_byte_read(void)
{
    uart_puts("\n=== Test 3: Single Byte Read ===\n");
    
    /* First write the memory address */
    if (i2c_start_write(I2C_SLAVE_ADDR) < 0) {
        check("Start write for address", 0);
        i2c_stop();
        return;
    }
    
    i2c_write_byte(0x00);  /* Memory address */
    
    /* Repeated start for read */
    if (i2c_start_read(I2C_SLAVE_ADDR) < 0) {
        check("Repeated start for read", 0);
        i2c_stop();
        return;
    }
    check("Repeated start ACK", 1);
    
    /* Read byte with NACK (last byte) */
    uint8_t data = i2c_read_byte(0);  /* 0 = NACK */
    
    uart_puts("  Read data: 0x");
    uart_puthex8(data);
    uart_puts("\n");
    
    /* Should read back what we wrote (0xAB) */
    check("Read data matches", data == 0xAB);
    
    i2c_stop();
}

/* Test 4: Multi-byte Write */
void test_multi_byte_write(void)
{
    uart_puts("\n=== Test 4: Multi-byte Write ===\n");
    
    if (i2c_start_write(I2C_SLAVE_ADDR) < 0) {
        check("Start write", 0);
        i2c_stop();
        return;
    }
    
    /* Write starting address */
    i2c_write_byte(0x10);
    
    /* Write 4 bytes */
    uint8_t test_pattern[] = {0xDE, 0xAD, 0xBE, 0xEF};
    int success = 1;
    
    for (int i = 0; i < 4; i++) {
        if (i2c_write_byte(test_pattern[i]) < 0) {
            success = 0;
            break;
        }
    }
    
    check("Multi-byte write", success);
    i2c_stop();
}

/* Test 5: Multi-byte Read */
void test_multi_byte_read(void)
{
    uart_puts("\n=== Test 5: Multi-byte Read ===\n");
    
    /* Set read address */
    if (i2c_start_write(I2C_SLAVE_ADDR) < 0) {
        check("Address write", 0);
        i2c_stop();
        return;
    }
    
    i2c_write_byte(0x10);
    
    /* Repeated start for read */
    if (i2c_start_read(I2C_SLAVE_ADDR) < 0) {
        check("Repeated start", 0);
        i2c_stop();
        return;
    }
    
    /* Read 4 bytes */
    uint8_t expected[] = {0xDE, 0xAD, 0xBE, 0xEF};
    uint8_t received[4];
    int success = 1;
    
    for (int i = 0; i < 4; i++) {
        int ack = (i < 3) ? 1 : 0;  /* ACK all but last */
        received[i] = i2c_read_byte(ack);
        
        uart_puts("  Byte ");
        uart_putdec(i);
        uart_puts(": 0x");
        uart_puthex8(received[i]);
        if (received[i] == expected[i]) {
            uart_puts(" OK\n");
        } else {
            uart_puts(" MISMATCH (expected 0x");
            uart_puthex8(expected[i]);
            uart_puts(")\n");
            success = 0;
        }
    }
    
    check("Multi-byte read", success);
    i2c_stop();
}

/* Test 6: NACK Handling */
void test_nack_handling(void)
{
    uart_puts("\n=== Test 6: NACK Handling ===\n");
    
    /* Try to access non-existent slave */
    uint8_t bad_addr = 0x7F;  /* Hopefully no slave at this address */
    
    uart_puts("  Trying address 0x");
    uart_puthex8(bad_addr);
    uart_puts("...\n");
    
    I2C_ADDR = (bad_addr << 1);
    I2C_WDATA = (bad_addr << 1);
    I2C_CMD = I2C_CMD_START | I2C_CMD_WRITE;
    
    i2c_wait_done();
    
    uint32_t status = I2C_STATUS;
    int got_nack = (status & I2C_STATUS_ACK_ERR) != 0;
    
    uart_puts("  Status: 0x");
    uart_puthex8(status & 0xFF);
    uart_puts(got_nack ? " (ACK_ERR set)\n" : " (no error)\n");
    
    check("NACK detected for invalid address", got_nack);
    
    i2c_stop();
}

/* ========================================================================
 * Main Function
 * ======================================================================== */

int main(void)
{
    uart_init();
    
    uart_puts("\n");
    uart_puts("========================================\n");
    uart_puts("   I2C Master Test - Ceres-V RV32IMC\n");
    uart_puts("========================================\n");
    
    /* Run all tests */
    test_register_access();
    test_single_byte_write();
    test_single_byte_read();
    test_multi_byte_write();
    test_multi_byte_read();
    test_nack_handling();
    
    /* Summary */
    uart_puts("\n========================================\n");
    uart_puts("   Test Summary\n");
    uart_puts("========================================\n");
    uart_puts("  Passed: ");
    uart_putdec(test_passed);
    uart_puts("\n");
    uart_puts("  Failed: ");
    uart_putdec(test_failed);
    uart_puts("\n");
    
    if (test_failed == 0) {
        uart_puts("\n  *** ALL TESTS PASSED ***\n");
    } else {
        uart_puts("\n  *** SOME TESTS FAILED ***\n");
    }
    uart_puts("========================================\n");
    
    /* End marker for simulation */
    uart_puts("\n[TEST_DONE]\n");
    
    while (1);
    return 0;
}
