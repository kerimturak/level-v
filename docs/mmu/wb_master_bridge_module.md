# Wishbone Master Bridge Modülü - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [State Machine](#state-machine)
4. [Transfer Modları](#transfer-modları)
5. [Burst İşlemleri](#burst-işlemleri)
6. [Stall ve Error Handling](#stall-ve-error-handling)
7. [Timing ve Latency](#timing-ve-latency)
8. [Doğrulama ve Debug](#doğrulama-ve-debug)

---

## Genel Bakış

### Amaç

`wb_master_bridge` modülü, CPU'nun iç bellek arayüzü (iomem) ile **Wishbone B4** bus protokolü arasında köprü görevi yapar. Basit request/response arayüzünü Wishbone pipelined protokolüne dönüştürür.

### Temel Özellikler

| Özellik | Değer |
|---------|-------|
| **Giriş Protokolü** | iomem (ready/valid) |
| **Çıkış Protokolü** | Wishbone B4 Pipelined |
| **Burst Desteği** | Incrementing (4-beat) |
| **Address Alignment** | 4-byte (word aligned) |
| **Byte Enable** | 4-bit select |
| **Error Handling** | Pass-through |

### Blok Diyagramı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          WISHBONE MASTER BRIDGE                                  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────────────┐                              ┌─────────────────┐          │
│   │   iomem_i       │                              │   wb_m_o        │          │
│   │   (CPU side)    │                              │   (Bus side)    │          │
│   │                 │                              │                 │          │
│   │  .valid    ────┼──────────────────────────────┼──→ .stb         │          │
│   │  .addr     ────┼──────────────────────────────┼──→ .adr         │          │
│   │  .wdata    ────┼──────────────────────────────┼──→ .dat         │          │
│   │  .we       ────┼──────────────────────────────┼──→ .we          │          │
│   │  .sel      ────┼──────────────────────────────┼──→ .sel         │          │
│   │  .burst    ────┼──────────────────────────────┼──→ .cti/.bte    │          │
│   │                 │                              │                 │          │
│   │  .ready   ◄────┼──────────────────────────────┼─── .ack/.stall  │          │
│   │  .rdata   ◄────┼──────────────────────────────┼─── .dat         │          │
│   │  .err     ◄────┼──────────────────────────────┼─── .err         │          │
│   └─────────────────┘                              └─────────────────┘          │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                          STATE MACHINE                                   │   │
│   │                                                                          │   │
│   │                    ┌─────────────────┐                                   │   │
│   │         ┌─────────►│      IDLE       │◄──────────────┐                  │   │
│   │         │          └────────┬────────┘               │                  │   │
│   │         │                   │ valid                  │                  │   │
│   │         │                   ▼                        │                  │   │
│   │         │          ┌─────────────────┐               │                  │   │
│   │     ack │          │     REQUEST     │               │                  │   │
│   │  (single)          └────────┬────────┘               │                  │   │
│   │         │                   │ burst?                 │ last + ack       │   │
│   │         │         ┌─────────┴─────────┐              │                  │   │
│   │         │         │                   │              │                  │   │
│   │         │         ▼                   ▼              │                  │   │
│   │    ┌────┴────┐         ┌─────────────────┐           │                  │   │
│   │    │ WAIT_   │         │     BURST       │───────────┘                  │   │
│   │    │ ACK     │         │ (count beats)   │                              │   │
│   │    └─────────┘         └─────────────────┘                              │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module wb_master_bridge
  import ceres_param::*;
(
    input  logic       clk_i,        // Sistem saati
    input  logic       rst_ni,       // Aktif-düşük reset

    // iomem arayüzü (CPU tarafı)
    input  iomem_req_t iomem_i,      // İstek
    output iomem_rsp_t iomem_o,      // Yanıt

    // Wishbone master interface
    output wb_master_t wb_m_o,       // Bus'a giden sinyaller
    input  wb_slave_t  wb_s_i        // Bus'tan gelen sinyaller
);
```

### iomem Request Yapısı

```systemverilog
typedef struct packed {
    logic                     valid;   // İstek geçerli
    logic [XLEN-1:0]          addr;    // Adres
    logic [XLEN-1:0]          wdata;   // Yazma verisi
    logic                     we;      // Write enable
    logic [WB_SEL_WIDTH-1:0]  sel;     // Byte seçimi
    logic                     burst;   // Burst modu
    logic [1:0]               burst_cnt; // Burst sayacı (0-3)
} iomem_req_t;
```

### iomem Response Yapısı

```systemverilog
typedef struct packed {
    logic                ready;   // Transfer tamamlandı
    logic [XLEN-1:0]     rdata;   // Okuma verisi
    logic                err;     // Error
} iomem_rsp_t;
```

---

## State Machine

### State Tanımları

```systemverilog
typedef enum logic [1:0] {
    IDLE,       // Boşta, istek bekliyor
    REQUEST,    // İstek gönderildi, yanıt bekliyor
    BURST,      // Burst modunda, beat'leri sayıyor
    WAIT_ACK    // Son ACK bekleniyor
} state_e;

state_e state_q, state_d;
```

### State Geçişleri

```systemverilog
always_comb begin
    state_d = state_q;

    case (state_q)
        IDLE: begin
            if (iomem_i.valid) begin
                if (iomem_i.burst) begin
                    state_d = BURST;
                end else begin
                    state_d = REQUEST;
                end
            end
        end

        REQUEST: begin
            if (wb_s_i.ack || wb_s_i.err) begin
                state_d = IDLE;
            end
        end

        BURST: begin
            if (wb_s_i.ack || wb_s_i.err) begin
                if (burst_cnt_q == WB_BURST_LEN - 1) begin
                    state_d = IDLE;  // Son beat
                end
                // Else: burst devam
            end
        end

        WAIT_ACK: begin
            if (wb_s_i.ack || wb_s_i.err) begin
                state_d = IDLE;
            end
        end
    endcase
end
```

### State Machine Diyagramı

```
                    ┌─────────────────────────────────────────────┐
                    │                                             │
                    ▼                                             │
             ┌──────────┐                                         │
    ──reset──►   IDLE   │                                         │
             └────┬─────┘                                         │
                  │                                               │
                  │ valid                                         │
                  ▼                                               │
          ┌───────────────┐                                       │
          │  burst mode?  │                                       │
          └───────┬───────┘                                       │
                  │                                               │
         ┌────────┴────────┐                                      │
         │ yes             │ no                                   │
         ▼                 ▼                                      │
   ┌──────────┐      ┌──────────┐                                │
   │  BURST   │      │ REQUEST  │                                │
   └────┬─────┘      └────┬─────┘                                │
        │                 │                                       │
        │                 │ ack/err ───────────────────────────────►
        │                 │
        │ count beats     │
        │                 │
        ▼                 │
   ┌──────────┐          │
   │  last    │──────────┘
   │  beat?   │
   └──────────┘
```

---

## Transfer Modları

### Single Transfer (Classic)

Tek word okuma/yazma işlemi:

```systemverilog
// CTI = Classic (single transfer)
wb_m_o.cti = WB_CTI_CLASSIC;  // 3'b000
wb_m_o.bte = 2'b00;           // Linear (don't care)
```

**Zamanlama:**

```
clk    ____/‾\____/‾\____/‾\____

iomem  ────/‾‾‾‾\────────────────
.valid

wb_m   ────/‾‾‾‾‾‾‾‾\────────────
.cyc

wb_m   ────/‾‾‾‾\────────────────
.stb

wb_s   ────────────/‾\───────────
.ack

iomem  ────────────/‾\───────────
.ready
```

### Burst Transfer (Incrementing)

Cache line fetch için 4-beat burst:

```systemverilog
// Burst sırasında CTI değişimi
case (burst_cnt_q)
    2'b00, 2'b01, 2'b10: begin
        wb_m_o.cti = WB_CTI_INCR;  // 3'b010 - Incrementing
    end
    2'b11: begin
        wb_m_o.cti = WB_CTI_EOB;   // 3'b111 - End of Burst
    end
endcase

wb_m_o.bte = 2'b00;  // Linear burst
```

**Zamanlama:**

```
clk      ____/‾\____/‾\____/‾\____/‾\____/‾\____

iomem    ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────────
.valid

wb_m.cyc ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──────

wb_m.stb ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──────

wb_m.cti ────┤INCR├┤INCR├┤INCR├┤EOB ├───────────

wb_m.adr ────┤ +0 ├┤ +4 ├┤ +8 ├┤ +C ├───────────

wb_s.ack ────────/‾\────/‾\────/‾\────/‾\────────

burst_cnt────┤ 0  ├┤ 1  ├┤ 2  ├┤ 3  ├───────────

iomem    ────────/‾\────/‾\────/‾\────/‾\────────
.ready          W0    W1    W2    W3
```

---

## Burst İşlemleri

### Burst Counter

```systemverilog
logic [1:0] burst_cnt_q, burst_cnt_d;
logic [XLEN-1:0] burst_addr_q, burst_addr_d;

// Burst counter güncelleme
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        burst_cnt_q  <= '0;
        burst_addr_q <= '0;
    end else begin
        burst_cnt_q  <= burst_cnt_d;
        burst_addr_q <= burst_addr_d;
    end
end

always_comb begin
    burst_cnt_d  = burst_cnt_q;
    burst_addr_d = burst_addr_q;

    case (state_q)
        IDLE: begin
            if (iomem_i.valid && iomem_i.burst) begin
                burst_cnt_d  = '0;
                burst_addr_d = iomem_i.addr;
            end
        end

        BURST: begin
            if (wb_s_i.ack && !wb_s_i.stall) begin
                burst_cnt_d  = burst_cnt_q + 1'b1;
                burst_addr_d = burst_addr_q + 4;  // Word increment
            end
        end
    endcase
end
```

### Adres Hesaplama

```systemverilog
// Burst modunda adres otomatik artar
always_comb begin
    if (state_q == BURST) begin
        wb_m_o.adr = burst_addr_q;
    end else begin
        wb_m_o.adr = iomem_i.addr;
    end
end
```

### Burst Length

```systemverilog
// Cache line boyutu: 128 bit = 4 x 32-bit word
localparam WB_BURST_LEN = 4;

// Burst tamamlandığında
logic burst_done;
assign burst_done = (burst_cnt_q == WB_BURST_LEN - 1) && wb_s_i.ack;
```

---

## Stall ve Error Handling

### Stall Yönetimi

Wishbone B4 pipelined modunda slave stall sinyali ile flow control yapabilir:

```systemverilog
// Stall durumunda istek tutulur
logic stalled_q;

always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        stalled_q <= 1'b0;
    end else begin
        stalled_q <= wb_s_i.stall && wb_m_o.cyc;
    end
end

// Strobe sadece stall yokken
assign wb_m_o.stb = (state_q == REQUEST || state_q == BURST) && !stalled_q;
```

**Stall Timing:**

```
clk      ____/‾\____/‾\____/‾\____/‾\____

wb_m.stb ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────────

wb_s.stall────────/‾‾‾‾\────────────────
                    │
                  Hold!

wb_s.ack ────────────────────/‾\────────
```

### Error Handling

```systemverilog
// Error sinyali doğrudan geçirilir
assign iomem_o.err = wb_s_i.err;

// Error durumunda işlem sonlanır
always_comb begin
    if (wb_s_i.err) begin
        state_d = IDLE;
        // Burst da dahil tüm işlem iptal
    end
end
```

---

## Timing ve Latency

### Latency Değerleri

| İşlem | Latency (cycles) | Açıklama |
|-------|------------------|----------|
| Single Read | 2-3 | Request + ACK |
| Single Write | 2-3 | Request + ACK |
| Burst Read (4) | 5-8 | 4 beat + overhead |
| Burst Write (4) | 5-8 | 4 beat + overhead |
| Stalled Request | +N | Stall süresi |

### Throughput

**Burst modunda:**
- Best case: 1 word/cycle (back-to-back ACK)
- Typical: 0.8 word/cycle (occasional stall)

**Single modunda:**
- 0.33-0.5 word/cycle (overhead)

### Pipeline Diyagramı

```
Cycle:    0     1     2     3     4     5     6
          │     │     │     │     │     │     │
          ▼     ▼     ▼     ▼     ▼     ▼     ▼

Burst:   REQ0──REQ1──REQ2──REQ3
              │     │     │     │
         ACK0──ACK1──ACK2──ACK3
              │     │     │     │
         DAT0  DAT1  DAT2  DAT3


Single:  REQ0────────ACK0
                     │
                    DAT0

              REQ1────────ACK1
                          │
                         DAT1
```

---

## Doğrulama ve Debug

### Wishbone Protokol Assertion'ları

```systemverilog
// STB sadece CYC aktifken assert edilmeli
assert property (@(posedge clk_i) disable iff (!rst_ni)
    wb_m_o.stb |-> wb_m_o.cyc
) else $error("STB requires CYC");

// ACK geldikten sonra STB düşmeli (single mode)
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (wb_s_i.ack && wb_m_o.cti == WB_CTI_CLASSIC) |=> !wb_m_o.stb
) else $error("STB should deassert after ACK in classic mode");

// Burst CTI geçişleri doğru olmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (wb_m_o.cti == WB_CTI_EOB && wb_s_i.ack) |=> !wb_m_o.cyc
) else $error("CYC should deassert after EOB+ACK");

// Error ve ACK aynı anda olamaz
assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(wb_s_i.ack && wb_s_i.err)
) else $error("ACK and ERR conflict");
```

### Debug Sinyalleri

```systemverilog
`ifdef DEBUG_WB_BRIDGE
    // State machine debug
    always_ff @(posedge clk_i) begin
        if (state_q != state_d) begin
            $display("[WB_BRIDGE] State: %s -> %s @ %0t",
                     state_q.name(), state_d.name(), $time);
        end

        if (wb_s_i.ack) begin
            $display("[WB_BRIDGE] ACK addr=0x%08x data=0x%08x @ %0t",
                     wb_m_o.adr, wb_s_i.dat, $time);
        end

        if (wb_s_i.err) begin
            $display("[WB_BRIDGE] ERROR addr=0x%08x @ %0t",
                     wb_m_o.adr, $time);
        end
    end
`endif
```

### Test Senaryoları

1. **Single Transfer**
   - Read/Write tüm byte enable kombinasyonları
   - Back-to-back single transfer

2. **Burst Transfer**
   - 4-beat burst read
   - 4-beat burst write
   - Stalled burst

3. **Error Conditions**
   - Error during single transfer
   - Error during burst (mid-burst abort)

4. **Stall Scenarios**
   - Continuous stall
   - Intermittent stall
   - Stall at burst boundary

---

## Özet

`wb_master_bridge` modülü:

1. **Protocol Conversion**: iomem ↔ Wishbone B4
2. **Burst Support**: 4-beat incrementing burst
3. **Pipelined Operation**: Low latency transfers
4. **Error Handling**: Pass-through error signaling
5. **Flow Control**: Stall signal support

Bu modül, CPU çekirdeğini Wishbone tabanlı SoC bus'ına bağlayan kritik bir bileşendir.
