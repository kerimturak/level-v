# DMA Controller - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Register Map](#register-map)
4. [Channel Konfigürasyonu](#channel-konfigürasyonu)
5. [Transfer Modları](#transfer-modları)
6. [State Machine](#state-machine)
7. [Interrupt Sistemi](#interrupt-sistemi)

---

## Genel Bakış

### Amaç

`dma` modülü, **4 bağımsız DMA kanalı** ile memory-to-memory, peripheral-to-memory ve memory-to-peripheral transferlerini yönetir.

### Dosya Konumu

```
rtl/periph/dma/dma.sv
```

### Özellikler

- 4 bağımsız DMA kanalı
- Memory-to-memory transferleri
- Peripheral-to-memory / Memory-to-peripheral
- Konfigüre edilebilir burst boyutları (1, 4, 8, 16 word)
- Circular buffer modu
- Half-transfer ve transfer-complete interrupt'ları
- Kanal öncelik seviyeleri
- Source/destination increment modları
- Word, half-word ve byte transferleri

---

## Modül Arayüzü

### Parametreler

```systemverilog
module dma
  import ceres_param::*;
#(
    parameter int NUM_CHANNELS = 4,
    parameter int MAX_BURST    = 16
)
```

### Port Tanımları

```systemverilog
(
    input  logic                    clk_i,
    input  logic                    rst_ni,
    
    // Register Interface (slave)
    input  logic                    stb_i,
    input  logic [             5:0] adr_i,        // Word address [7:2]
    input  logic [             3:0] byte_sel_i,
    input  logic                    we_i,
    input  logic [            31:0] dat_i,
    output logic [            31:0] dat_o,
    
    // DMA Master Interface
    output logic                    dma_req_o,
    output logic [            31:0] dma_addr_o,
    output logic [            31:0] dma_wdata_o,
    output logic [             3:0] dma_wstrb_o,
    input  logic [            31:0] dma_rdata_i,
    input  logic                    dma_ack_i,
    
    // Peripheral DMA requests
    input  logic [NUM_CHANNELS-1:0] dreq_i,
    
    // Interrupt output
    output logic [NUM_CHANNELS-1:0] irq_o
);
```

---

## Register Map

### Per-Channel Registers (0x20 bytes per channel)

| Offset | Register | Açıklama |
|--------|----------|----------|
| 0x00 | CCR | Channel Control Register |
| 0x04 | CNDTR | Channel Number of Data to Transfer |
| 0x08 | CPAR | Channel Peripheral Address |
| 0x0C | CMAR | Channel Memory Address |
| 0x10 | CTCNT | Channel Transfer Count (read-only) |

### Global Registers

| Offset | Register | Açıklama |
|--------|----------|----------|
| 0x80 | ISR | Interrupt Status Register |
| 0x84 | IFCR | Interrupt Flag Clear Register |
| 0x88 | GCR | Global Control Register |

### CCR (Channel Control) Register

```
┌────────────────────────────────────────────────────────────────────────────┐
│ Bit   │ İsim    │ Açıklama                                                 │
├───────┼─────────┼────────────────────────────────────────────────────────────┤
│ [0]   │ EN      │ Channel enable                                           │
│ [1]   │ TCIE    │ Transfer complete interrupt enable                       │
│ [2]   │ HTIE    │ Half transfer interrupt enable                           │
│ [3]   │ TEIE    │ Transfer error interrupt enable                          │
│ [4]   │ DIR     │ Direction (0=P2M, 1=M2P)                                  │
│ [5]   │ CIRC    │ Circular mode                                             │
│ [6]   │ PINC    │ Peripheral increment mode                                │
│ [7]   │ MINC    │ Memory increment mode                                     │
│ [9:8] │ PSIZE   │ Peripheral size (00=byte, 01=half, 10=word)              │
│ [11:10]│ MSIZE  │ Memory size (00=byte, 01=half, 10=word)                  │
│ [13:12]│ PL     │ Priority level (00=low ... 11=very high)                 │
│ [14]  │ MEM2MEM │ Memory-to-memory mode                                     │
│ [17:15]│ BURST  │ Burst size (000=1, 001=4, 010=8, 011=16)                 │
└────────────────────────────────────────────────────────────────────────────┘
```

### ISR (Interrupt Status) Register

Her kanal için 4 bit:
- `[0]` GIF - Global interrupt flag
- `[1]` TCIF - Transfer complete interrupt flag
- `[2]` HTIF - Half transfer interrupt flag
- `[3]` TEIF - Transfer error interrupt flag

---

## Channel Konfigürasyonu

### Öncelik Sistemi

```systemverilog
// Priority encoding: 11=very high, 10=high, 01=medium, 00=low
assign ch_pl[i] = ccr[i][13:12];
```

### Arbitration

```systemverilog
// En yüksek öncelikli aktif kanalı bul
always_comb begin
    active_ch = '0;
    active_ch_valid = 1'b0;
    
    for (int p = 3; p >= 0; p--) begin  // Öncelik 3'ten 0'a
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            if (ch_request[i] && ch_pl[i] == p[1:0] && !active_ch_valid) begin
                active_ch = i;
                active_ch_valid = 1'b1;
            end
        end
    end
end
```

---

## Transfer Modları

### Memory-to-Memory

```
Source (Memory)  ──►  DMA Engine  ──►  Destination (Memory)
     CMAR                                    CPAR
```

### Peripheral-to-Memory (DIR=0)

```
Peripheral (CPAR)  ──►  DMA Engine  ──►  Memory (CMAR)
```

### Memory-to-Peripheral (DIR=1)

```
Memory (CMAR)  ──►  DMA Engine  ──►  Peripheral (CPAR)
```

### Circular Mode

```systemverilog
// Transfer complete'de reload
if (ctcnt[i] == 1) begin
    if (ch_circ[i]) begin
        ctcnt[i]     <= cndtr[i];     // Count reload
        cur_paddr[i] <= cpar[i];      // Peripheral address reload
        cur_maddr[i] <= cmar[i];      // Memory address reload
    end else begin
        ccr[i][0] <= 1'b0;            // Disable channel
    end
end
```

---

## State Machine

### State Diagram

```
┌──────────────────────────────────────────────────────────────────────┐
│                        DMA STATE MACHINE                              │
├──────────────────────────────────────────────────────────────────────┤
│                                                                       │
│    ┌─────────┐     active_ch_valid     ┌─────────────┐               │
│    │         │ ──────────────────────► │             │               │
│    │  IDLE   │                         │  READ_REQ   │               │
│    │         │ ◄────────────────────── │             │               │
│    └─────────┘        done             └──────┬──────┘               │
│         ▲                                     │                       │
│         │                                     │                       │
│         │            ┌─────────────┐          │                       │
│         │            │             │ ◄────────┘                       │
│         │            │  READ_WAIT  │                                  │
│         │            │             │ ─────────┐                       │
│         │            └─────────────┘          │ dma_ack_i             │
│         │                                     ▼                       │
│         │            ┌─────────────┐    ┌─────────────┐              │
│         │            │             │ ◄──│             │              │
│         └────────────│    DONE     │    │  WRITE_REQ  │              │
│                      │             │    │             │              │
│                      └─────────────┘    └──────┬──────┘              │
│                            ▲                   │                      │
│                            │                   ▼                      │
│                            │           ┌─────────────┐               │
│                            │           │             │               │
│                            └───────────│ WRITE_WAIT  │               │
│                              dma_ack_i │             │               │
│                                        └─────────────┘               │
│                                                                       │
└──────────────────────────────────────────────────────────────────────┘
```

### State Enum

```systemverilog
typedef enum logic [2:0] {
    DMA_IDLE,
    DMA_READ_REQ,
    DMA_READ_WAIT,
    DMA_WRITE_REQ,
    DMA_WRITE_WAIT,
    DMA_DONE
} dma_state_t;
```

---

## Interrupt Sistemi

### Interrupt Flags

```systemverilog
// Global interrupt flag = any flag set
assign gif[i] = tcif[i] | htif[i] | teif[i];

// Channel interrupt = enabled flags
assign irq_o[i] = (ch_tcie[i] & tcif[i]) | 
                  (ch_htie[i] & htif[i]) | 
                  (ch_teie[i] & teif[i]);
```

### Flag Generation

```systemverilog
// Half transfer: count reaches half of total
if (ctcnt[i] == (cndtr[i] >> 1)) begin
    htif[i] <= 1'b1;
end

// Transfer complete: count reaches 0
if (ctcnt[i] == 1) begin
    tcif[i] <= 1'b1;
end
```

### Flag Clear (IFCR)

```systemverilog
if (adr_i == 6'h21) begin  // IFCR address
    if (dat_i[i*4+1]) tcif[i] <= 1'b0;
    if (dat_i[i*4+2]) htif[i] <= 1'b0;
    if (dat_i[i*4+3]) teif[i] <= 1'b0;
end
```

---

## Kullanım Örneği

### C Header

```c
#define DMA_BASE       0x20009000

// Per-channel registers (channel 0-3)
#define DMA_CCR(n)     (*(volatile uint32_t*)(DMA_BASE + (n)*0x20 + 0x00))
#define DMA_CNDTR(n)   (*(volatile uint32_t*)(DMA_BASE + (n)*0x20 + 0x04))
#define DMA_CPAR(n)    (*(volatile uint32_t*)(DMA_BASE + (n)*0x20 + 0x08))
#define DMA_CMAR(n)    (*(volatile uint32_t*)(DMA_BASE + (n)*0x20 + 0x0C))
#define DMA_CTCNT(n)   (*(volatile uint32_t*)(DMA_BASE + (n)*0x20 + 0x10))

// Global registers
#define DMA_ISR        (*(volatile uint32_t*)(DMA_BASE + 0x80))
#define DMA_IFCR       (*(volatile uint32_t*)(DMA_BASE + 0x84))
#define DMA_GCR        (*(volatile uint32_t*)(DMA_BASE + 0x88))

// CCR bits
#define DMA_CCR_EN        (1 << 0)
#define DMA_CCR_TCIE      (1 << 1)
#define DMA_CCR_HTIE      (1 << 2)
#define DMA_CCR_DIR       (1 << 4)
#define DMA_CCR_CIRC      (1 << 5)
#define DMA_CCR_PINC      (1 << 6)
#define DMA_CCR_MINC      (1 << 7)
#define DMA_CCR_MEM2MEM   (1 << 14)
```

### Memory-to-Memory Transfer

```c
void dma_memcpy(uint32_t *dst, uint32_t *src, uint32_t count) {
    // Configure channel 0 for M2M
    DMA_CPAR(0) = (uint32_t)dst;
    DMA_CMAR(0) = (uint32_t)src;
    DMA_CNDTR(0) = count;
    
    DMA_CCR(0) = DMA_CCR_MEM2MEM |  // Memory-to-memory
                 DMA_CCR_MINC |     // Memory increment
                 DMA_CCR_PINC |     // Peripheral increment
                 (2 << 8) |         // PSIZE = word
                 (2 << 10) |        // MSIZE = word
                 DMA_CCR_EN;        // Enable
    
    // Wait for complete
    while (!(DMA_ISR & (1 << 1)));  // TCIF0
    DMA_IFCR = (1 << 1);            // Clear flag
}
```

---

## Özet

`dma` modülü:

1. **4 Kanal**: Bağımsız DMA kanalları
2. **3 Transfer Modu**: M2M, P2M, M2P
3. **Öncelik**: 4-level priority arbitration
4. **Circular**: Continuous buffer mode
5. **Interrupts**: TC, HT, TE flags
6. **Burst**: 1/4/8/16 word burst
