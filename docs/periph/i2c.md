# I2C Master Controller - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Register Map](#register-map)
4. [I2C Protokolü](#i2c-protokolü)
5. [State Machine](#state-machine)
6. [FIFO Yapısı](#fifo-yapısı)
7. [Clock Stretching](#clock-stretching)

---

## Genel Bakış

### Amaç

`i2c_master` modülü, **FIFO buffered I2C Master** controller olarak Standard (100kHz), Fast (400kHz) ve Fast+ (1MHz) modlarını destekler.

### Dosya Konumu

```
rtl/periph/i2c/i2c_master.sv
```

### Özellikler

- Standard mode: 100 kHz
- Fast mode: 400 kHz
- Fast+ mode: 1 MHz
- 8-byte TX/RX FIFO buffers
- Clock stretching desteği
- Auto-ACK capability
- Arbitration loss detection
- Open-drain output interface

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module i2c_master
  import ceres_param::*;
(
    input  logic clk_i,
    input  logic rst_ni,

    // Register interface
    input  logic            stb_i,
    input  logic [     2:0] adr_i,       // 3-bit for 6 registers
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,

    // I2C Interface (open-drain)
    output logic i2c_scl_o,      // SCL output
    output logic i2c_scl_oe_o,   // SCL output enable
    input  logic i2c_scl_i,      // SCL input (clock stretching)
    output logic i2c_sda_o,      // SDA output
    output logic i2c_sda_oe_o,   // SDA output enable
    input  logic i2c_sda_i,      // SDA input

    // Interrupt
    output logic irq_o
);
```

### Open-Drain Interface

```
┌───────────────────────────────────────────────────────┐
│                  I2C OPEN-DRAIN                        │
├───────────────────────────────────────────────────────┤
│                                                        │
│   i2c_scl_oe_o = 1 → SCL driven low (scl_o = 0)       │
│   i2c_scl_oe_o = 0 → SCL released (pulled high)       │
│                                                        │
│   i2c_sda_oe_o = 1 → SDA driven low (sda_o = 0)       │
│   i2c_sda_oe_o = 0 → SDA released (pulled high)       │
│                                                        │
│   External pull-up resistors required!                 │
│                                                        │
└───────────────────────────────────────────────────────┘
```

---

## Register Map

| Offset | Register | Açıklama |
|--------|----------|----------|
| 0x00 | CTRL | Control register |
| 0x04 | STATUS | Status register (read-only) |
| 0x08 | CMD | Command register |
| 0x0C | ADDR | Slave address |
| 0x10 | RDATA | RX data (FIFO pop) |
| 0x14 | WDATA | TX data (FIFO push) |

### CTRL Register

```
┌─────────────────────────────────────────────────────────────────────┐
│ [31:16] │ clk_div - SCL clock divider                               │
│ [3]     │ stretch_en - Clock stretching enable                      │
│ [2]     │ ack_en - Auto ACK enable for reads                        │
└─────────────────────────────────────────────────────────────────────┘
```

### STATUS Register

```
┌─────────────────────────────────────────────────────────────────────┐
│ [7] │ busy - Transfer in progress                                   │
│ [6] │ arb_lost - Arbitration lost (sticky)                          │
│ [5] │ ack_err - No ACK received (sticky)                            │
│ [4] │ tx_empty - TX FIFO empty                                      │
│ [3] │ tx_full - TX FIFO full                                        │
│ [2] │ rx_empty - RX FIFO empty                                      │
│ [1] │ rx_full - RX FIFO full                                        │
│ [0] │ transfer_done - Byte transfer complete (sticky)               │
└─────────────────────────────────────────────────────────────────────┘
```

### CMD Register

```
┌─────────────────────────────────────────────────────────────────────┐
│ [7] │ start - Generate START condition                              │
│ [6] │ stop - Generate STOP condition                                │
│ [5] │ read - Read byte from slave                                   │
│ [4] │ write - Write byte to slave                                   │
│ [3] │ ack - ACK to send (0=ACK, 1=NACK)                            │
└─────────────────────────────────────────────────────────────────────┘
```

---

## I2C Protokolü

### Baud Rate Calculation

```
SCL frequency = clk_i / (4 * (clk_div + 1))

Example (50 MHz clock):
  100 kHz: clk_div = 124  → 50M / (4*125) = 100 kHz
  400 kHz: clk_div = 30   → 50M / (4*31)  = 403 kHz
  1 MHz:   clk_div = 11   → 50M / (4*12)  = 1.04 MHz
```

### I2C Timing

```
┌───────────────────────────────────────────────────────────────────────┐
│                        I2C BIT TIMING                                  │
├───────────────────────────────────────────────────────────────────────┤
│                                                                        │
│        ┌─────────────────────────────────────────┐                    │
│ SCL    │                                         │                    │
│     ───┘                                         └────────            │
│                                                                        │
│           ─────────────────────────────────────                       │
│ SDA     ─X─────────────────────────────────────X─                     │
│           DATA VALID                                                   │
│                                                                        │
│        │◄──── clk_div ────►│◄──── clk_div ────►│                      │
│                                                                        │
└───────────────────────────────────────────────────────────────────────┘
```

### START/STOP Conditions

```
START: SDA falls while SCL high
   ┌───┐
SCL│   └────────────────
   └───────┐
SDA        └────────────

STOP: SDA rises while SCL high
        ┌───────────────
SCL────┘
            ┌───────────
SDA────────┘
```

---

## State Machine

### State Enum

```systemverilog
typedef enum logic [3:0] {
    I2C_IDLE,
    I2C_START_1,       // SDA goes low while SCL high
    I2C_START_2,       // SCL goes low
    I2C_BIT_SETUP,     // Setup data on SDA
    I2C_BIT_SCL_HIGH,  // SCL goes high, sample/hold
    I2C_BIT_SCL_LOW,   // SCL goes low
    I2C_ACK_SETUP,     // Setup ACK on SDA
    I2C_ACK_SCL_HIGH,  // Sample ACK
    I2C_ACK_SCL_LOW,   // SCL goes low after ACK
    I2C_STOP_1,        // SCL goes high
    I2C_STOP_2,        // SDA goes high (STOP)
    I2C_STRETCH        // Wait for clock stretch release
} i2c_state_t;
```

### State Diagram

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          I2C STATE MACHINE                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│   ┌────────┐  cmd_start    ┌───────────┐        ┌───────────┐              │
│   │  IDLE  │ ────────────► │  START_1  │ ─────► │  START_2  │              │
│   └────────┘               └───────────┘        └─────┬─────┘              │
│        ▲                                              │                     │
│        │                                              ▼                     │
│        │                                        ┌───────────┐              │
│        │                          ┌───────────► │ BIT_SETUP │ ◄────┐       │
│        │                          │             └─────┬─────┘      │       │
│        │                          │                   │            │       │
│        │                          │                   ▼            │       │
│        │                          │           ┌─────────────┐      │       │
│        │                          │           │BIT_SCL_HIGH │ ─────┤       │
│        │                          │           └─────┬───────┘      │       │
│        │                          │                 │ ◄── STRETCH │       │
│        │                          │                 ▼              │       │
│        │                          │           ┌─────────────┐      │       │
│        │                          └─────────── │ BIT_SCL_LOW │ ────┘       │
│        │                         bit_cnt < 7  └─────────────┘ bit_cnt=7    │
│        │                                              │                     │
│        │                                              ▼                     │
│   ┌────────┐   cmd_stop    ┌───────────┐        ┌───────────┐              │
│   │ STOP_2 │ ◄──────────── │  STOP_1   │ ◄───── │ ACK_phase │              │
│   └────────┘               └───────────┘        └───────────┘              │
│        │                                                                    │
│        └───────────────────────────────────────────────► IDLE              │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## FIFO Yapısı

### TX FIFO

```systemverilog
wbit_fifo #(
    .DATA_WIDTH(8),
    .FIFO_DEPTH(8)
) i_tx_fifo (
    .clk       (clk_i),
    .rst       (!rst_ni),
    .write_en  (tx_we),
    .read_en   (tx_re),
    .write_data(tx_wdata),
    .read_data (tx_rdata),
    .full      (tx_full),
    .empty     (tx_empty)
);
```

### RX FIFO

```systemverilog
wbit_fifo #(
    .DATA_WIDTH(8),
    .FIFO_DEPTH(8)
) i_rx_fifo (
    .clk       (clk_i),
    .rst       (!rst_ni),
    .write_en  (rx_we),
    .read_en   (rx_re),
    .write_data(rx_wdata),
    .read_data (rx_rdata),
    .full      (rx_full),
    .empty     (rx_empty)
);
```

---

## Clock Stretching

### Detection

```systemverilog
// SCL released but still low = slave stretching
if (scl_oe_q == 1'b0 && stretch_en && !i2c_scl_i) begin
    state_d = I2C_STRETCH;
end
```

### Stretch State

```
┌───────────────────────────────────────────────────────────────────────┐
│                      CLOCK STRETCHING                                  │
├───────────────────────────────────────────────────────────────────────┤
│                                                                        │
│ Master releases SCL (oe=0)                                            │
│         │                                                              │
│         ▼                                                              │
│     ┌───────┐ SCL still low (slave holding)                           │
│     │STRETCH│ ──────────────────────────────┐                         │
│     └───────┘                               │                          │
│         ▲                                   │                          │
│         │                                   ▼                          │
│         │                           Wait for SCL high                  │
│         │                                   │                          │
│         │◄──────────────────────────────────┘                          │
│                  i2c_scl_i = 1                                         │
│                                                                        │
└───────────────────────────────────────────────────────────────────────┘
```

---

## Kullanım Örneği

### C Header

```c
#define I2C_BASE       0x20003000

#define I2C_CTRL       (*(volatile uint32_t*)(I2C_BASE + 0x00))
#define I2C_STATUS     (*(volatile uint32_t*)(I2C_BASE + 0x04))
#define I2C_CMD        (*(volatile uint32_t*)(I2C_BASE + 0x08))
#define I2C_ADDR       (*(volatile uint32_t*)(I2C_BASE + 0x0C))
#define I2C_RDATA      (*(volatile uint32_t*)(I2C_BASE + 0x10))
#define I2C_WDATA      (*(volatile uint32_t*)(I2C_BASE + 0x14))

// Status bits
#define I2C_BUSY       (1 << 7)
#define I2C_ARB_LOST   (1 << 6)
#define I2C_ACK_ERR    (1 << 5)
#define I2C_TX_EMPTY   (1 << 4)
#define I2C_RX_EMPTY   (1 << 2)

// Command bits
#define I2C_CMD_START  (1 << 7)
#define I2C_CMD_STOP   (1 << 6)
#define I2C_CMD_READ   (1 << 5)
#define I2C_CMD_WRITE  (1 << 4)
#define I2C_CMD_NACK   (1 << 3)
```

### Write Byte to Slave

```c
int i2c_write_byte(uint8_t slave_addr, uint8_t reg, uint8_t data) {
    // Wait for not busy
    while (I2C_STATUS & I2C_BUSY);
    
    // Send slave address + W
    I2C_WDATA = (slave_addr << 1) | 0;
    I2C_CMD = I2C_CMD_START | I2C_CMD_WRITE;
    while (I2C_STATUS & I2C_BUSY);
    if (I2C_STATUS & I2C_ACK_ERR) return -1;
    
    // Send register address
    I2C_WDATA = reg;
    I2C_CMD = I2C_CMD_WRITE;
    while (I2C_STATUS & I2C_BUSY);
    
    // Send data with STOP
    I2C_WDATA = data;
    I2C_CMD = I2C_CMD_WRITE | I2C_CMD_STOP;
    while (I2C_STATUS & I2C_BUSY);
    
    return 0;
}
```

### Read Byte from Slave

```c
int i2c_read_byte(uint8_t slave_addr, uint8_t reg, uint8_t *data) {
    // Write register address
    I2C_WDATA = (slave_addr << 1) | 0;
    I2C_CMD = I2C_CMD_START | I2C_CMD_WRITE;
    while (I2C_STATUS & I2C_BUSY);
    
    I2C_WDATA = reg;
    I2C_CMD = I2C_CMD_WRITE;
    while (I2C_STATUS & I2C_BUSY);
    
    // Repeated START for read
    I2C_WDATA = (slave_addr << 1) | 1;
    I2C_CMD = I2C_CMD_START | I2C_CMD_WRITE;
    while (I2C_STATUS & I2C_BUSY);
    
    // Read with NACK and STOP
    I2C_CMD = I2C_CMD_READ | I2C_CMD_NACK | I2C_CMD_STOP;
    while (I2C_STATUS & I2C_BUSY);
    
    *data = I2C_RDATA & 0xFF;
    return 0;
}
```

---

## Özet

`i2c_master` modülü:

1. **3 Speed Modes**: 100k / 400k / 1M Hz
2. **FIFO Buffers**: 8-byte TX/RX
3. **Clock Stretching**: Slave-initiated wait
4. **Open-Drain**: External pull-up required
5. **Error Detection**: ARB_LOST, ACK_ERR
6. **Auto-ACK**: Configurable for reads
