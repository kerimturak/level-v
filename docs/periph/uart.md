# UART Controller - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Yapısı](#modül-yapısı)
3. [Register Map](#register-map)
4. [TX Modülü](#tx-modülü)
5. [RX Modülü](#rx-modülü)
6. [Baud Rate Hesabı](#baud-rate-hesabı)

---

## Genel Bakış

### Amaç

`uart` modülü, **Full-duplex UART** controller olarak TX ve RX FIFO buffers ile asenkron seri iletişim sağlar.

### Dosya Konumları

```
rtl/periph/uart/
├── uart.sv          # Top-level wrapper
├── uart_tx.sv       # Transmit module
└── uart_rx.sv       # Receive module
```

### Özellikler

- Full-duplex operation
- 8-byte TX/RX FIFO buffers
- Programmable baud rate
- 8N1 frame format (8 data, no parity, 1 stop)
- LOG_UART simulation logging support
- Oversampling (16x) for RX

---

## Modül Yapısı

### Block Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                            UART CONTROLLER                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                         uart.sv (Top)                            │   │
│   │                                                                  │   │
│   │  ┌────────────────┐           ┌────────────────┐                │   │
│   │  │   Register     │           │    Control     │                │   │
│   │  │   Interface    │◄─────────►│    Logic       │                │   │
│   │  └────────────────┘           └────────────────┘                │   │
│   │         │                            │                           │   │
│   │         ▼                            ▼                           │   │
│   │  ┌────────────────────────────────────────────────────────────┐ │   │
│   │  │                                                             │ │   │
│   │  │  ┌─────────────────┐         ┌─────────────────┐           │ │   │
│   │  │  │    uart_tx.sv   │         │    uart_rx.sv   │           │ │   │
│   │  │  │                 │         │                 │           │ │   │
│   │  │  │  ┌───────────┐  │         │  ┌───────────┐  │           │ │   │
│   │  │  │  │  TX FIFO  │  │         │  │  RX FIFO  │  │           │ │   │
│   │  │  │  │  (8-byte) │  │         │  │  (8-byte) │  │           │ │   │
│   │  │  │  └─────┬─────┘  │         │  └─────▲─────┘  │           │ │   │
│   │  │  │        │        │         │        │        │           │ │   │
│   │  │  │  ┌─────▼─────┐  │         │  ┌─────┴─────┐  │           │ │   │
│   │  │  │  │ Shift Reg │  │         │  │ Shift Reg │  │           │ │   │
│   │  │  │  └─────┬─────┘  │         │  └─────▲─────┘  │           │ │   │
│   │  │  │        │        │         │        │        │           │ │   │
│   │  │  └────────┼────────┘         └────────┼────────┘           │ │   │
│   │  │           │                           │                     │ │   │
│   │  └───────────┼───────────────────────────┼─────────────────────┘ │   │
│   │              │                           │                       │   │
│   └──────────────┼───────────────────────────┼───────────────────────┘   │
│                  │                           │                           │
│                  ▼                           │                           │
│              uart_tx_o                   uart_rx_i                       │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Top-Level Port Tanımları

```systemverilog
module uart
  import ceres_param::*;
(
    input  logic clk_i,
    input  logic rst_ni,

    // Register interface
    input  logic             stb_i,
    input  logic [      1:0] adr_i,
    input  logic [      3:0] byte_sel_i,
    input  logic             we_i,
    input  logic [XLEN-1:0]  dat_i,
    output logic [XLEN-1:0]  dat_o,

    // UART Interface
    output logic uart_tx_o,
    input  logic uart_rx_i,

    // Interrupt
    output logic irq_o
);
```

---

## Register Map

| Offset | Register | Açıklama |
|--------|----------|----------|
| 0x00 | CTRL | Control register |
| 0x04 | STATUS | Status register |
| 0x08 | RDATA | RX data (FIFO pop) |
| 0x0C | WDATA | TX data (FIFO push) |

### CTRL Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [31:16] │ baud_div │ Baud rate divider value                            │
│ [0]     │ uart_en  │ UART enable                                        │
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

## TX Modülü

### uart_tx.sv Yapısı

```systemverilog
module uart_tx (
    input  logic       clk_i,
    input  logic       rst_ni,
    input  logic [7:0] data_i,
    input  logic       we_i,
    input  logic       en_i,
    input  logic [15:0] baud_div_i,
    output logic       tx_o,
    output logic       full_o,
    output logic       empty_o
);
```

### TX State Machine

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        TX STATE MACHINE                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   !fifo_empty && en                                                     │
│   ┌───────────────────────────────────────────────────────┐             │
│   │                                                       │             │
│   ▼                                                       │             │
│ ┌──────────┐         ┌──────────┐         ┌──────────────┴─┐           │
│ │          │         │          │         │                │           │
│ │   IDLE   │ ──────► │   LOAD   │ ──────► │    SENDING     │           │
│ │          │         │          │         │                │           │
│ │  tx = 1  │         │ load reg │         │ shift bits out │           │
│ └──────────┘         └──────────┘         └────────────────┘           │
│                                                   │                     │
│                                                   │ bit_cnt == 9        │
│                                                   │ (stop bit done)     │
│                                                   │                     │
│                                                   ▼                     │
│                                           ┌───────────────┐             │
│                                           │ Check FIFO    │             │
│                                           │ empty? → IDLE │             │
│                                           │ more? → LOAD  │             │
│                                           └───────────────┘             │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### TX Timing Diagram

```
                 ┌─── Start ─── Data Bits ─────────────── Stop ───┐
                 │                                                 │
                 │   D0   D1   D2   D3   D4   D5   D6   D7        │
                 │                                                 │
uart_tx_o  ──────┘ ─┐   ┌───┐   ┌───────────┐   ┌───┐   ┌─────────────
                    └───┘   └───┘           └───┘   └───┘
                 │                                                 │
                 ◄─────────────── 10 bits ─────────────────────────►
                 │                                                 │
              bit_tick                                          bit_tick
                 │◄──────── baud_div cycles ────────►│
                             (per bit)
```

### LOG_UART Simulation Feature

```systemverilog
`ifdef LOG_UART
    // Log transmitted characters to file
    integer log_file;
    initial log_file = $fopen("uart_tx.log", "w");

    always_ff @(posedge clk_i) begin
        if (tx_done) begin
            $fwrite(log_file, "%c", tx_data);
            $fflush(log_file);
        end
    end
`endif
```

---

## RX Modülü

### uart_rx.sv Yapısı

```systemverilog
module uart_rx (
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic        rx_i,
    input  logic        re_i,
    input  logic        en_i,
    input  logic [15:0] baud_div_i,
    output logic [7:0]  data_o,
    output logic        full_o,
    output logic        empty_o
);
```

### RX State Machine

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        RX STATE MACHINE                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   start bit (rx=0)                                                      │
│   ┌───────────────────────────────────────────────────────┐             │
│   │                                                       │             │
│   ▼                                                       │             │
│ ┌──────────┐         ┌──────────┐         ┌──────────────┴─┐           │
│ │          │         │  START   │         │                │           │
│ │   IDLE   │ ──────► │   DET    │ ──────► │   SAMPLING     │           │
│ │          │         │          │         │                │           │
│ │ wait rx=0│         │ verify   │         │ sample middle  │           │
│ └──────────┘         └──────────┘         └────────────────┘           │
│      ▲                                            │                     │
│      │                                            │ 8 bits + stop       │
│      │                                            │                     │
│      │                                            ▼                     │
│      │                                    ┌───────────────┐             │
│      └────────────────────────────────────│   Push FIFO   │             │
│                                           └───────────────┘             │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Oversampling (16x)

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        RX OVERSAMPLING                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Bit period divided into 16 samples:                                   │
│                                                                          │
│      0  1  2  3  4  5  6  7  8  9  10 11 12 13 14 15                    │
│      ├──┼──┼──┼──┼──┼──┼──┼──┼──┼──┼──┼──┼──┼──┼──┤                    │
│                              ▲                                          │
│                              │                                          │
│                          Sample at middle (7-8)                         │
│                                                                          │
│   Start bit detection:                                                   │
│   1. Detect falling edge (1→0)                                          │
│   2. Wait 8 samples (half bit)                                          │
│   3. Verify still low (valid start)                                     │
│   4. Sample data at middle of each bit                                  │
│                                                                          │
│   rx_i    ────┐     ┌─────────┐     ┌─────┐                             │
│               │     │         │     │     │                             │
│               └─────┘ D0=0    └─────┘ D1=1                              │
│                   ▲               ▲                                      │
│                   │               │                                      │
│                sample           sample                                   │
│               (middle)         (middle)                                  │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Edge Detection

```systemverilog
// 2-stage synchronizer + edge detect
logic [2:0] rx_sync;

always_ff @(posedge clk_i) begin
    rx_sync <= {rx_sync[1:0], rx_i};
end

wire rx_falling = rx_sync[2] & ~rx_sync[1];  // Start bit edge
wire rx_sampled = rx_sync[1];                 // Synchronized value
```

---

## Baud Rate Hesabı

### Divider Formula

```
baud_div = (clk_freq / baud_rate) - 1

Example (50 MHz clock):
  9600:   baud_div = 50000000 / 9600 - 1   = 5207
  19200:  baud_div = 50000000 / 19200 - 1  = 2603
  115200: baud_div = 50000000 / 115200 - 1 = 433
  921600: baud_div = 50000000 / 921600 - 1 = 53
```

### Common Baud Rates

| Baud Rate | Divider (50 MHz) | Actual Rate | Error |
|-----------|------------------|-------------|-------|
| 9600 | 5207 | 9600.6 | 0.006% |
| 19200 | 2603 | 19200.6 | 0.003% |
| 38400 | 1301 | 38417.4 | 0.045% |
| 57600 | 867 | 57603.7 | 0.006% |
| 115200 | 433 | 115207.4 | 0.006% |
| 230400 | 216 | 230414.7 | 0.006% |
| 460800 | 107 | 462962.9 | 0.47% |
| 921600 | 53 | 925925.9 | 0.47% |

---

## Kullanım Örneği

### C Header

```c
#define UART_BASE      0x20000000

#define UART_CTRL      (*(volatile uint32_t*)(UART_BASE + 0x00))
#define UART_STATUS    (*(volatile uint32_t*)(UART_BASE + 0x04))
#define UART_RDATA     (*(volatile uint32_t*)(UART_BASE + 0x08))
#define UART_WDATA     (*(volatile uint32_t*)(UART_BASE + 0x0C))

// CTRL bits
#define UART_EN        (1 << 0)

// STATUS bits
#define UART_TX_EMPTY  (1 << 3)
#define UART_TX_FULL   (1 << 2)
#define UART_RX_EMPTY  (1 << 1)
#define UART_RX_FULL   (1 << 0)

// Baud rate dividers (50 MHz)
#define BAUD_9600      5207
#define BAUD_115200    433
```

### Initialization

```c
void uart_init(uint32_t baud_div) {
    // Set baud rate and enable
    UART_CTRL = (baud_div << 16) | UART_EN;
}
```

### Send Character

```c
void uart_putc(char c) {
    // Wait for TX not full
    while (UART_STATUS & UART_TX_FULL);
    
    // Write character
    UART_WDATA = c;
}
```

### Receive Character

```c
char uart_getc(void) {
    // Wait for RX not empty
    while (UART_STATUS & UART_RX_EMPTY);
    
    // Read character
    return UART_RDATA;
}
```

### Print String

```c
void uart_puts(const char *s) {
    while (*s) {
        uart_putc(*s++);
    }
}
```

### Print Hex Number

```c
void uart_puthex(uint32_t val) {
    static const char hex[] = "0123456789ABCDEF";
    uart_puts("0x");
    for (int i = 28; i >= 0; i -= 4) {
        uart_putc(hex[(val >> i) & 0xF]);
    }
}
```

### Non-blocking Operations

```c
int uart_try_getc(void) {
    if (UART_STATUS & UART_RX_EMPTY)
        return -1;  // No data available
    return UART_RDATA;
}

int uart_try_putc(char c) {
    if (UART_STATUS & UART_TX_FULL)
        return -1;  // TX full
    UART_WDATA = c;
    return 0;
}
```

---

## Frame Format

### 8N1 Frame

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        8N1 FRAME FORMAT                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   IDLE     START   D0  D1  D2  D3  D4  D5  D6  D7   STOP   IDLE         │
│                                                                          │
│   ─────────┐   ┌───┬───┬───┬───┬───┬───┬───┬───┐   ┌─────────────       │
│            │   │   │   │   │   │   │   │   │   │   │                    │
│    HIGH    │ 0 │ LSB                     MSB │ 1 │    HIGH              │
│            │   │                             │   │                      │
│            └───┴───────────────────────────────┴───┘                    │
│                                                                          │
│   8N1 = 8 data bits, No parity, 1 stop bit                              │
│   Total: 1 start + 8 data + 1 stop = 10 bits per byte                   │
│                                                                          │
│   Effective throughput = Baud rate / 10                                 │
│   115200 baud → 11520 bytes/sec                                         │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Simulation Logging

### LOG_UART Feature

Compile ile `LOG_UART` tanımlandığında, TX çıkışı dosyaya loglanır:

```bash
# Enable logging
make run T=test_name LOG_UART=1

# Output file: build/logs/uart_tx.log
```

### Log Format

```
# uart_tx.log
Hello, World!
Test output: 0x12345678
```

---

## Özet

`uart` modülü:

1. **Full Duplex**: Independent TX and RX
2. **FIFO Buffers**: 8-byte each direction
3. **Programmable Baud**: Divider-based rate setting
4. **8N1 Format**: Standard frame format
5. **Oversampling**: 16x for reliable reception
6. **Simulation**: LOG_UART file output
7. **Low Latency**: FIFO-based transmission
