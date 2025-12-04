# Wishbone Interconnect Modülü - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Adres Çözümleme](#adres-çözümleme)
4. [Slave Haritası](#slave-haritası)
5. [Request/Response Yönlendirme](#requestresponse-yönlendirme)
6. [Hata Yönetimi](#hata-yönetimi)
7. [Zamanlama Diyagramları](#zamanlama-diyagramları)
8. [Doğrulama ve Test](#doğrulama-ve-test)

---

## Genel Bakış

### Amaç

`wb_interconnect` modülü, **Wishbone B4** uyumlu bir **1-to-N crossbar interconnect** yapısıdır. CPU'dan gelen bellek isteklerini adres tabanlı olarak uygun slave'e yönlendirir.

### Temel Özellikler

| Özellik | Değer |
|---------|-------|
| **Bus Standardı** | Wishbone B4 Pipelined |
| **Topoloji** | 1 Master → N Slave |
| **Adres Decode** | Tek cycle combinational |
| **Slave Sayısı** | 3 (RAM, CLINT, PBUS) |
| **Burst Desteği** | Evet (CTI/BTE) |
| **Error Handling** | Unmapped address error |

### Wishbone Interconnect Blok Diyagramı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                           WISHBONE INTERCONNECT                                  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────────────┐                                                           │
│   │   CPU Master    │                                                           │
│   │   (wb_m_i)      │                                                           │
│   └────────┬────────┘                                                           │
│            │                                                                     │
│            ▼                                                                     │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                        ADDRESS DECODER                                   │   │
│   │                                                                          │   │
│   │   addr[31:28] ────┬─────────────────────────────────────────────────────│   │
│   │                   │                                                      │   │
│   │         ┌─────────┴─────────┬──────────────┬──────────────┐             │   │
│   │         │                   │              │              │             │   │
│   │     0x8 (RAM)          0x3 (CLINT)    0x2 (PBUS)     Other            │   │
│   │         │                   │              │              │             │   │
│   │         ▼                   ▼              ▼              ▼             │   │
│   │   slave_sel[0]        slave_sel[1]   slave_sel[2]   addr_valid=0      │   │
│   │                                                      → ERROR           │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                     SLAVE INTERFACES                                     │   │
│   │                                                                          │   │
│   │   ┌──────────┐         ┌──────────┐         ┌──────────┐                │   │
│   │   │   RAM    │         │  CLINT   │         │   PBUS   │                │   │
│   │   │ Slave 0  │         │ Slave 1  │         │ Slave 2  │                │   │
│   │   │0x8xxxxxxx│         │0x3xxxxxxx│         │0x2xxxxxxx│                │   │
│   │   └──────────┘         └──────────┘         └──────────┘                │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module wb_interconnect #(
    parameter int NUM_SLAVES = 3
) (
    input  logic       clk_i,           // Sistem saati
    input  logic       rst_ni,          // Aktif-düşük reset

    // Wishbone Master interface (from CPU)
    input  wb_master_t wb_m_i,          // Master'dan gelen istek
    output wb_slave_t  wb_s_o,          // Master'a giden yanıt

    // Wishbone Slave interfaces
    output wb_master_t wb_m_o[NUM_SLAVES],  // Slave'lere giden istek
    input  wb_slave_t  wb_s_i[NUM_SLAVES]   // Slave'lerden gelen yanıt
);
```

### Wishbone Master Sinyalleri

```systemverilog
typedef struct packed {
    logic [WB_ADDR_WIDTH-1:0] adr;  // Adres
    logic [WB_DATA_WIDTH-1:0] dat;  // Yazma verisi
    logic [WB_SEL_WIDTH-1:0]  sel;  // Byte seçimi
    logic                     we;   // Write enable
    logic                     stb;  // Strobe
    logic                     cyc;  // Cycle
    logic [2:0]               cti;  // Cycle Type Identifier
    logic [1:0]               bte;  // Burst Type Extension
} wb_master_t;
```

### Wishbone Slave Sinyalleri

```systemverilog
typedef struct packed {
    logic [WB_DATA_WIDTH-1:0] dat;    // Okuma verisi
    logic                     ack;    // Acknowledge
    logic                     err;    // Error
    logic                     rty;    // Retry
    logic                     stall;  // Stall
} wb_slave_t;
```

---

## Adres Çözümleme

### Adres Decode Mantığı

```systemverilog
// Slave indeksleri
localparam SLAVE_RAM   = 0;
localparam SLAVE_CLINT = 1;
localparam SLAVE_PBUS  = 2;

logic [NUM_SLAVES-1:0] slave_sel;
logic                  addr_valid;

// Kombinasyonel adres decode
always_comb begin
    slave_sel  = '0;
    addr_valid = 1'b0;

    case (wb_m_i.adr[31:28])
        4'h8: begin  // RAM
            slave_sel[SLAVE_RAM] = 1'b1;
            addr_valid = 1'b1;
        end
        4'h3: begin  // CLINT
            slave_sel[SLAVE_CLINT] = 1'b1;
            addr_valid = 1'b1;
        end
        4'h2: begin  // Peripheral Bus
            slave_sel[SLAVE_PBUS] = 1'b1;
            addr_valid = 1'b1;
        end
        default: begin
            addr_valid = 1'b0;  // Geçersiz adres → Error
        end
    endcase
end
```

### Adres Alanları

| Slave | Adres Aralığı | Boyut | Açıklama |
|-------|---------------|-------|----------|
| RAM | 0x8000_0000 - 0xFFFF_FFFF | 2GB | Ana bellek |
| CLINT | 0x3000_0000 - 0x3FFF_FFFF | 256MB | Core-local interruptor |
| PBUS | 0x2000_0000 - 0x2FFF_FFFF | 256MB | Peripheral bus |

---

## Slave Haritası

### Slave 0: RAM (Main Memory)

```
Adres Aralığı: 0x8000_0000 - 0xFFFF_FFFF
Boyut: 2GB (tipik kullanım: 128KB - 1MB)

Özellikler:
- Cacheable
- Executable
- Read/Write

Kullanım:
- Program kodu
- Data
- Stack/Heap
```

### Slave 1: CLINT (Core Local Interruptor)

```
Adres Aralığı: 0x3000_0000 - 0x3000_FFFF
Boyut: 64KB

Özellikler:
- Uncacheable
- Non-executable
- Read/Write

Register Map:
- msip     @ 0x0000: Machine Software Interrupt Pending
- mtimecmp @ 0x4000: Machine Timer Compare
- mtime    @ 0xBFF8: Machine Timer
```

### Slave 2: PBUS (Peripheral Bus)

```
Adres Aralığı: 0x2000_0000 - 0x2FFF_FFFF
Boyut: 256MB

Özellikler:
- Uncacheable
- Non-executable
- Read/Write

Peripheral Offsets:
0x0000: UART0
0x1000: UART1
0x2000: SPI0
0x3000: I2C0
0x4000: GPIO
0x5000: PWM
0x6000: Timer
0x7000: PLIC
0x8000: Watchdog
0x9000: DMA
0xD000: VGA Control
```

---

## Request/Response Yönlendirme

### Request Tracking

Hangi slave'in aktif isteği olduğunu takip eder:

```systemverilog
logic [1:0] active_slave_q;
logic       req_pending_q;

always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        active_slave_q <= '0;
        req_pending_q  <= 1'b0;
    end else begin
        if (wb_m_i.cyc && wb_m_i.stb && !wb_s_o.stall) begin
            // Yeni istek kabul edildi
            for (int i = 0; i < NUM_SLAVES; i++) begin
                if (slave_sel[i]) begin
                    active_slave_q <= i[1:0];
                end
            end
            req_pending_q <= 1'b1;
        end else if (wb_s_o.ack || wb_s_o.err) begin
            // İstek tamamlandı
            if (wb_m_i.cti == WB_CTI_CLASSIC || wb_m_i.cti == WB_CTI_EOB) begin
                req_pending_q <= 1'b0;
            end
        end
    end
end
```

### Master → Slave Yönlendirme

```systemverilog
always_comb begin
    for (int i = 0; i < NUM_SLAVES; i++) begin
        // Tüm sinyalleri broadcast et
        wb_m_o[i].adr = wb_m_i.adr;
        wb_m_o[i].dat = wb_m_i.dat;
        wb_m_o[i].sel = wb_m_i.sel;
        wb_m_o[i].we  = wb_m_i.we;
        wb_m_o[i].cti = wb_m_i.cti;
        wb_m_o[i].bte = wb_m_i.bte;

        // Strobe ve cycle'ı slave seçimine göre gate'le
        wb_m_o[i].stb = wb_m_i.stb && slave_sel[i];
        wb_m_o[i].cyc = wb_m_i.cyc && 
                        (slave_sel[i] || (req_pending_q && active_slave_q == i[1:0]));
    end
end
```

### Slave → Master Yönlendirme

```systemverilog
always_comb begin
    // Varsayılan: yanıt yok
    wb_s_o.dat   = '0;
    wb_s_o.ack   = 1'b0;
    wb_s_o.err   = 1'b0;
    wb_s_o.rty   = 1'b0;
    wb_s_o.stall = 1'b0;

    if (!addr_valid && wb_m_i.cyc && wb_m_i.stb) begin
        // Geçersiz adres - error üret
        wb_s_o.err = 1'b1;
    end else begin
        // Seçili slave'den yanıt yönlendir
        for (int i = 0; i < NUM_SLAVES; i++) begin
            if (slave_sel[i] || (req_pending_q && active_slave_q == i[1:0])) begin
                wb_s_o.dat   = wb_s_i[i].dat;
                wb_s_o.ack   = wb_s_i[i].ack;
                wb_s_o.err   = wb_s_i[i].err;
                wb_s_o.rty   = wb_s_i[i].rty;
                wb_s_o.stall = wb_s_i[i].stall;
            end
        end
    end
end
```

---

## Hata Yönetimi

### Unmapped Address Error

Geçersiz adrese erişim durumunda interconnect otomatik olarak error üretir:

```systemverilog
if (!addr_valid && wb_m_i.cyc && wb_m_i.stb) begin
    wb_s_o.err = 1'b1;  // Error yanıtı
end
```

### Error Senaryoları

| Adres | Sonuç | Açıklama |
|-------|-------|----------|
| 0x0xxx_xxxx | ERROR | Debug module (not implemented) |
| 0x1xxx_xxxx | ERROR | Boot ROM (not implemented) |
| 0x4xxx_xxxx | ERROR | External memory (not implemented) |
| 0x5xxx_xxxx | ERROR | Rezerve |
| 0x6xxx_xxxx | ERROR | Rezerve |
| 0x7xxx_xxxx | ERROR | Rezerve |

---

## Zamanlama Diyagramları

### Başarılı RAM Okuma

```
clk      ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

wb_m_i   ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────
.cyc

wb_m_i   ────/‾‾‾‾\──────────────────────────────────
.stb

wb_m_i   ────┤0x8000_0000├───────────────────────────
.adr

slave_sel────┤RAM (sel[0]=1)├────────────────────────

wb_s_o   ────────────────────────────────/‾‾‾‾\──────
.ack                                     RAM ack

wb_s_o   ────────────────────────────────┤DATA├──────
.dat
```

### Burst Transfer (Cache Line)

```
clk      ____/‾\____/‾\____/‾\____/‾\____/‾\____

wb_m_i   ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────
.cyc

wb_m_i   ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────
.stb

wb_m_i   ────┤INCR├┤INCR├┤INCR├┤EOB ├──────────────
.cti

wb_m_i   ────┤ +0 ├┤ +4 ├┤ +8 ├┤ +C ├──────────────
.adr

wb_s_o   ────────/‾‾‾‾\────/‾‾‾‾\────/‾‾‾‾\────/‾‾‾‾\
.ack

wb_s_o   ────────┤ W0 ├────┤ W1 ├────┤ W2 ├────┤ W3 ├
.dat
```

### Invalid Address Error

```
clk      ____/‾‾‾‾\____/‾‾‾‾\____

wb_m_i   ────/‾‾‾‾\──────────────
.stb

wb_m_i   ────┤0x0000_0000├───────
.adr        (invalid!)

addr_valid───┤ 0 ├───────────────

wb_s_o   ────/‾‾‾‾\──────────────
.err            │
             Error!
```

---

## Doğrulama ve Test

### Assertion'lar

```systemverilog
// Tek slave seçili olmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
    addr_valid |-> $onehot(slave_sel)
) else $error("Only one slave should be selected");

// Geçersiz adres error üretmeli
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (!addr_valid && wb_m_i.cyc && wb_m_i.stb) |-> wb_s_o.err
) else $error("Invalid address should generate error");

// ACK ve ERR aynı anda olamaz
assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(wb_s_o.ack && wb_s_o.err)
) else $error("ACK and ERR cannot be active simultaneously");
```

### Test Senaryoları

1. **Adres Decode**
   - Her slave aralığına erişim
   - Boundary adresleri test

2. **Error Generation**
   - Geçersiz adres erişimi
   - Reserved bölgelere erişim

3. **Burst Transfer**
   - Cache line burst
   - CTI/BTE kombinasyonları

4. **Stall Handling**
   - Slave stall durumu
   - Master bekleme

---

## Özet

`wb_interconnect` modülü:

1. **Simple 1-to-N Routing**: Tek master, çoklu slave
2. **Address-based Selection**: 4-bit üst adres decode
3. **Wishbone B4 Compliant**: Pipelined, burst destekli
4. **Error Handling**: Unmapped address protection
5. **Low Latency**: Combinational decode

Bu modül, CERES SoC'da CPU ile bellek/peripheral arasındaki bağlantıyı sağlar.
