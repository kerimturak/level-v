# SPI Master Controller - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Register Map](#register-map)
4. [SPI Modları](#spi-modları)
5. [State Machine](#state-machine)
6. [FIFO Yapısı](#fifo-yapısı)

---

## Genel Bakış

### Amaç

`spi_master` modülü, **8-bit SPI Master** controller olarak FIFO buffers ve 4 SPI mod desteği sağlar.

### Dosya Konumu

```
rtl/periph/spi/spi_master.sv
```

### Özellikler

- 8-bit data width
- 8-byte TX/RX FIFO buffers
- All 4 SPI modes (CPOL/CPHA combinations)
- Programmable clock divider
- Software-controlled chip select
- MSB-first transmission

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module spi_master
  import ceres_param::*;
(
    input  logic clk_i,
    input  logic rst_ni,

    // Register interface
    input  logic            stb_i,
    input  logic [     1:0] adr_i,       // 2-bit for 4 registers
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,

    // SPI Interface
    output logic spi_sck_o,
    output logic spi_mosi_o,
    input  logic spi_miso_i,
    output logic spi_cs_n_o
);
```

### SPI Signals

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        SPI INTERFACE                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Master                                      Slave                      │
│   ┌───────────┐                              ┌───────────┐              │
│   │           │──── SCK ────────────────────►│           │              │
│   │           │                              │           │              │
│   │           │──── MOSI ───────────────────►│           │              │
│   │  CERES    │                              │  Device   │              │
│   │           │◄─── MISO ────────────────────│           │              │
│   │           │                              │           │              │
│   │           │──── CS_N ───────────────────►│           │              │
│   └───────────┘                              └───────────┘              │
│                                                                          │
│   SCK:  Serial clock (master generated)                                 │
│   MOSI: Master Out, Slave In (data from master)                         │
│   MISO: Master In, Slave Out (data from slave)                          │
│   CS_N: Chip select (active low, software controlled)                   │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Register Map

| Offset | Register | Açıklama |
|--------|----------|----------|
| 0x00 | CTRL | Control register |
| 0x04 | STATUS | Status register (read-only) |
| 0x08 | RDATA | RX data (FIFO pop) |
| 0x0C | WDATA | TX data (FIFO push) |

### CTRL Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [31:16] │ sck_div │ SCK clock divider                                   │
│ [3]     │ cpol    │ Clock polarity (idle level)                         │
│ [2]     │ cpha    │ Clock phase (sample edge)                           │
│ [1]     │ cs_n    │ Chip select (direct control)                        │
│ [0]     │ spi_en  │ SPI enable                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### STATUS Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [3] │ tx_empty │ TX FIFO empty                                          │
│ [2] │ tx_full  │ TX FIFO full                                           │
│ [1] │ rx_empty │ RX FIFO empty                                          │
│ [0] │ rx_full  │ RX FIFO full                                           │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## SPI Modları

### CPOL ve CPHA Kombinasyonları

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          SPI MODES                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Mode 0 (CPOL=0, CPHA=0): Idle low, sample on rising edge              │
│   ─────────────────────────────────────────────────                      │
│        ┌───┐   ┌───┐   ┌───┐   ┌───┐                                    │
│   SCK ─┘   └───┘   └───┘   └───┘   └─                                   │
│        ▲       ▲       ▲       ▲    sample                              │
│   MOSI ─X───────X───────X───────X───                                    │
│              shift                                                       │
│                                                                          │
│   Mode 1 (CPOL=0, CPHA=1): Idle low, sample on falling edge             │
│   ─────────────────────────────────────────────────                      │
│        ┌───┐   ┌───┐   ┌───┐   ┌───┐                                    │
│   SCK ─┘   └───┘   └───┘   └───┘   └─                                   │
│            ▲       ▲       ▲       ▲  sample                            │
│   MOSI ───X───────X───────X───────X─                                    │
│         shift                                                            │
│                                                                          │
│   Mode 2 (CPOL=1, CPHA=0): Idle high, sample on falling edge            │
│   ─────────────────────────────────────────────────                      │
│   SCK ─┐   ┌───┐   ┌───┐   ┌───┐   ┌─                                   │
│        └───┘   └───┘   └───┘   └───┘                                    │
│        ▲       ▲       ▲       ▲    sample                              │
│   MOSI ─X───────X───────X───────X───                                    │
│                                                                          │
│   Mode 3 (CPOL=1, CPHA=1): Idle high, sample on rising edge             │
│   ─────────────────────────────────────────────────                      │
│   SCK ─┐   ┌───┐   ┌───┐   ┌───┐   ┌─                                   │
│        └───┘   └───┘   └───┘   └───┘                                    │
│            ▲       ▲       ▲       ▲  sample                            │
│   MOSI ───X───────X───────X───────X─                                    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### SCK Frequency Calculation

```
SCK_freq = clk_i / (2 * (sck_div + 1))

Example (50 MHz clock):
  1 MHz:  sck_div = 24  → 50M / (2*25) = 1 MHz
  5 MHz:  sck_div = 4   → 50M / (2*5)  = 5 MHz
  10 MHz: sck_div = 1   → 50M / (2*2)  = 12.5 MHz
```

---

## State Machine

### State Enum

```systemverilog
typedef enum logic [1:0] {
    SPI_IDLE,
    SPI_TRANSFER,
    SPI_DONE
} spi_state_t;
```

### State Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        SPI STATE MACHINE                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│          spi_en && !tx_empty && !cs_n                                   │
│   ┌───────────────────────────────────────────────────────┐             │
│   │                                                       │             │
│   ▼                                                       │             │
│ ┌──────────┐         ┌──────────────┐         ┌──────────┴─┐           │
│ │          │         │              │         │            │           │
│ │   IDLE   │ ──────► │   TRANSFER   │ ──────► │    DONE    │           │
│ │          │         │              │ bit=7   │            │           │
│ └──────────┘         └──────────────┘         └────────────┘           │
│      ▲                     │                        │                   │
│      │                     │                        │                   │
│      │                     │ bit < 7                │ tx_empty || cs_n  │
│      │                     └──────────────┐         │                   │
│      │                                    │         │                   │
│      │                                    ▼         ▼                   │
│      │                              ┌───────────────────┐               │
│      │                              │   Continue or     │               │
│      └──────────────────────────────│   return to IDLE  │               │
│                                     └───────────────────┘               │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Transfer Logic

```systemverilog
SPI_TRANSFER: begin
    if (sck_toggle) begin
        clk_cnt_q <= '0;
        sck_q <= ~sck_q;

        if (cpha == 1'b0) begin
            // Mode 0/2: Sample on first edge, shift on second
            if (sck_q == cpol) begin
                // First edge - sample
                shift_in_q <= {shift_in_q[6:0], spi_miso_i};
            end else begin
                // Second edge - shift
                shift_out_q <= {shift_out_q[6:0], 1'b0};
                bit_cnt_q <= bit_cnt_q + 1'b1;
            end
        end else begin
            // Mode 1/3: Shift on first edge, sample on second
            if (sck_q == cpol) begin
                // First edge - shift
                shift_out_q <= {shift_out_q[6:0], 1'b0};
            end else begin
                // Second edge - sample
                shift_in_q <= {shift_in_q[6:0], spi_miso_i};
                bit_cnt_q <= bit_cnt_q + 1'b1;
            end
        end
    end
end
```

---

## FIFO Yapısı

### TX/RX FIFO

```systemverilog
// TX FIFO
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

// RX FIFO
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

## Kullanım Örneği

### C Header

```c
#define SPI_BASE       0x20002000

#define SPI_CTRL       (*(volatile uint32_t*)(SPI_BASE + 0x00))
#define SPI_STATUS     (*(volatile uint32_t*)(SPI_BASE + 0x04))
#define SPI_RDATA      (*(volatile uint32_t*)(SPI_BASE + 0x08))
#define SPI_WDATA      (*(volatile uint32_t*)(SPI_BASE + 0x0C))

// CTRL bits
#define SPI_EN         (1 << 0)
#define SPI_CS_N       (1 << 1)
#define SPI_CPHA       (1 << 2)
#define SPI_CPOL       (1 << 3)

// STATUS bits
#define SPI_TX_EMPTY   (1 << 3)
#define SPI_TX_FULL    (1 << 2)
#define SPI_RX_EMPTY   (1 << 1)
#define SPI_RX_FULL    (1 << 0)
```

### Basic SPI Transfer

```c
void spi_init(void) {
    // 1 MHz, Mode 0, CS high, enabled
    SPI_CTRL = (24 << 16) | SPI_CS_N | SPI_EN;
}

uint8_t spi_transfer(uint8_t data) {
    // Assert CS
    SPI_CTRL &= ~SPI_CS_N;
    
    // Wait for TX not full, write data
    while (SPI_STATUS & SPI_TX_FULL);
    SPI_WDATA = data;
    
    // Wait for RX not empty, read data
    while (SPI_STATUS & SPI_RX_EMPTY);
    uint8_t rx = SPI_RDATA;
    
    // Deassert CS
    SPI_CTRL |= SPI_CS_N;
    
    return rx;
}
```

### SD Card Command

```c
uint8_t sd_command(uint8_t cmd, uint32_t arg) {
    uint8_t response;
    
    // Assert CS
    SPI_CTRL &= ~SPI_CS_N;
    
    // Send command (6 bytes)
    spi_transfer(0x40 | cmd);       // Command
    spi_transfer((arg >> 24) & 0xFF);
    spi_transfer((arg >> 16) & 0xFF);
    spi_transfer((arg >> 8) & 0xFF);
    spi_transfer(arg & 0xFF);
    spi_transfer(0x95);             // CRC (dummy for most commands)
    
    // Wait for response (R1)
    for (int i = 0; i < 10; i++) {
        response = spi_transfer(0xFF);
        if (!(response & 0x80)) break;
    }
    
    // Deassert CS
    SPI_CTRL |= SPI_CS_N;
    
    return response;
}
```

### Flash Read

```c
void flash_read(uint32_t addr, uint8_t *buf, int len) {
    // Assert CS
    SPI_CTRL &= ~SPI_CS_N;
    
    // Read command
    spi_transfer(0x03);
    spi_transfer((addr >> 16) & 0xFF);
    spi_transfer((addr >> 8) & 0xFF);
    spi_transfer(addr & 0xFF);
    
    // Read data
    for (int i = 0; i < len; i++) {
        buf[i] = spi_transfer(0xFF);
    }
    
    // Deassert CS
    SPI_CTRL |= SPI_CS_N;
}
```

---

## Timing Diyagramı

### SPI Transfer (Mode 0)

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └───

cs_n_reg   ────┐                                     ┌────
               └─────────────────────────────────────┘

sck_q                ┌───┐   ┌───┐   ┌───┐   ┌───┐
           ──────────┘   └───┘   └───┘   └───┘   └────

mosi_o     ──────────┤D7 ├───┤D6 ├───┤D5 ├───┤...├────
                     │   │   │   │   │   │

miso_i     ──────────┤D7 ├───┤D6 ├───┤D5 ├───┤...├────
                       ▲       ▲       ▲
                       │       │       │ sample
```

---

## Özet

`spi_master` modülü:

1. **8-bit Data**: Standard SPI width
2. **4 Modes**: All CPOL/CPHA combinations
3. **FIFO Buffers**: 8-byte TX/RX
4. **Software CS**: Direct control
5. **MSB First**: Standard bit order
6. **Programmable Clock**: Divider-based
