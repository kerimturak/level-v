# Memory Arbiter Modülü - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Arbitrasyon Mantığı](#arbitrasyon-mantığı)
4. [State Machine](#state-machine)
5. [Veri Yolları](#veri-yolları)
6. [Zamanlama Diyagramları](#zamanlama-diyagramları)
7. [Performans Analizi](#performans-analizi)
8. [Doğrulama ve Test](#doğrulama-ve-test)

---

## Genel Bakış

### Amaç

`memory_arbiter` modülü, I-Cache ve D-Cache arasında bellek erişimi arbitrasyonu sağlar. Von Neumann mimarisinde tek bellek arayüzü üzerinden her iki cache'in isteklerini yönetir.

### Temel Özellikler

| Özellik | Değer |
|---------|-------|
| **Arbitrasyon Tipi** | Round-robin |
| **Öncelik** | Eşit (fair scheduling) |
| **Latching** | İstekler register'lanır |
| **Pipeline** | Single-stage |
| **Burst Desteği** | Evet (cache line) |

### Memory Arbiter Blok Diyagramı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              MEMORY ARBITER                                      │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────────┐                                   ┌─────────────┐             │
│   │   I-Cache   │                                   │   D-Cache   │             │
│   │   Request   │                                   │   Request   │             │
│   └──────┬──────┘                                   └──────┬──────┘             │
│          │                                                 │                     │
│          ▼                                                 ▼                     │
│   ┌─────────────┐                                   ┌─────────────┐             │
│   │   icache_   │                                   │   dcache_   │             │
│   │   req_reg   │                                   │   req_reg   │             │
│   │  (latch)    │                                   │  (latch)    │             │
│   └──────┬──────┘                                   └──────┬──────┘             │
│          │                                                 │                     │
│          └──────────────────┬──────────────────────────────┘                     │
│                             │                                                    │
│                             ▼                                                    │
│                    ┌─────────────────┐                                          │
│                    │   ROUND-ROBIN   │                                          │
│                    │   STATE MACHINE │                                          │
│                    │  ┌───────────┐  │                                          │
│                    │  │   IDLE    │──┼──▶ İstek bekle                           │
│                    │  │   ICACHE  │──┼──▶ I-Cache servisi                       │
│                    │  │   DCACHE  │──┼──▶ D-Cache servisi                       │
│                    │  └───────────┘  │                                          │
│                    └────────┬────────┘                                          │
│                             │                                                    │
│                             ▼                                                    │
│                    ┌─────────────────┐                                          │
│                    │    iomem_req    │                                          │
│                    │      (out)      │                                          │
│                    └────────┬────────┘                                          │
│                             │                                                    │
│                             ▼                                                    │
│                    ┌─────────────────┐                                          │
│                    │   Wishbone Bus  │                                          │
│                    │   (to memory)   │                                          │
│                    └─────────────────┘                                          │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module memory_arbiter (
    input  logic       clk_i,           // Sistem saati
    input  logic       rst_ni,          // Aktif-düşük reset
    
    // I-Cache arayüzü
    input  ilowX_req_t icache_req_i,    // I-Cache isteği
    output ilowX_res_t icache_res_o,    // I-Cache yanıtı
    
    // D-Cache arayüzü
    input  dlowX_req_t dcache_req_i,    // D-Cache isteği
    output dlowX_res_t dcache_res_o,    // D-Cache yanıtı
    
    // Bellek arayüzü
    input  iomem_res_t iomem_res_i,     // Bellek yanıtı
    output iomem_req_t iomem_req_o      // Bellek isteği
);
```

### Port Açıklamaları

| Port | Yön | Tip | Açıklama |
|------|-----|-----|----------|
| `clk_i` | Giriş | logic | Sistem saati |
| `rst_ni` | Giriş | logic | Aktif-düşük reset |
| `icache_req_i` | Giriş | ilowX_req_t | I-Cache bellek isteği |
| `icache_res_o` | Çıkış | ilowX_res_t | I-Cache bellek yanıtı |
| `dcache_req_i` | Giriş | dlowX_req_t | D-Cache bellek isteği |
| `dcache_res_o` | Çıkış | dlowX_res_t | D-Cache bellek yanıtı |
| `iomem_res_i` | Giriş | iomem_res_t | Alt seviye bellek yanıtı |
| `iomem_req_o` | Çıkış | iomem_req_t | Alt seviye bellek isteği |

### İstek/Yanıt Yapıları

```systemverilog
// I-Cache İstek Yapısı
typedef struct packed {
    logic [XLEN-1:0] addr;      // Bellek adresi
    logic            valid;     // İstek geçerli
    logic            ready;     // Cache hazır
    logic            uncached;  // Uncached erişim
} ilowX_req_t;

// I-Cache Yanıt Yapısı
typedef struct packed {
    logic [BLK_SIZE-1:0] blk;   // Cache line verisi
    logic                valid; // Yanıt geçerli
    logic                ready; // Arbiter hazır
} ilowX_res_t;

// D-Cache İstek Yapısı
typedef struct packed {
    logic [XLEN-1:0]    addr;      // Bellek adresi
    logic [BLK_SIZE-1:0] data;     // Yazma verisi
    logic               valid;     // İstek geçerli
    logic               rw;        // 0: Read, 1: Write
    logic [1:0]         rw_size;   // 01:byte, 10:half, 11:word
    logic               uncached;  // Uncached erişim
} dlowX_req_t;

// D-Cache Yanıt Yapısı
typedef struct packed {
    logic [BLK_SIZE-1:0] data;  // Okuma verisi
    logic                valid; // Yanıt geçerli
    logic                ready; // Arbiter hazır
} dlowX_res_t;
```

---

## Arbitrasyon Mantığı

### Round-Robin State Machine

```systemverilog
typedef enum logic [1:0] {
    IDLE,     // Boşta, istek bekliyor
    ICACHE,   // I-Cache servis ediliyor
    DCACHE    // D-Cache servis ediliyor
} round_e;

round_e round;
```

### İstek Latching

İstekler register'lanarak tek cycle'lık pulse'ların kaybedilmesi önlenir:

```systemverilog
// Latching registers
ilowX_req_t icache_req_reg;
dlowX_req_t dcache_req_reg;

always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
        icache_req_reg <= '{default: 0};
        dcache_req_reg <= '{default: 0};
    end else begin
        // Yeni istekleri latch'le (varsa)
        if (!icache_req_reg.valid && icache_req_i.valid) 
            icache_req_reg <= icache_req_i;
        if (!dcache_req_reg.valid && dcache_req_i.valid) 
            dcache_req_reg <= dcache_req_i;
    end
end
```

### State Geçişleri

```systemverilog
always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
        round <= IDLE;
    end else begin
        if (iomem_res_i.valid || round == IDLE) begin
            case (round)
                ICACHE: begin
                    icache_req_reg.valid <= 1'b0;  // İstek işlendi
                    round <= dcache_req_reg.valid ? DCACHE : 
                             icache_req_reg.valid && !iomem_res_i.valid ? ICACHE : 
                             IDLE;
                end
                
                DCACHE: begin
                    dcache_req_reg.valid <= 1'b0;  // İstek işlendi
                    round <= icache_req_reg.valid ? ICACHE : 
                             dcache_req_reg.valid && !iomem_res_i.valid ? DCACHE : 
                             IDLE;
                end
                
                IDLE: begin
                    if (icache_req_reg.valid) 
                        round <= ICACHE;
                    else if (dcache_req_reg.valid) 
                        round <= DCACHE;
                    else 
                        round <= IDLE;
                end
            endcase
        end
    end
end
```

---

## State Machine

### State Diagram

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                         ROUND-ROBIN STATE MACHINE                                │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│                          ┌──────────────────────┐                               │
│                          │                      │                               │
│                          │        IDLE          │                               │
│                          │  (İstek bekliyor)    │                               │
│                          │                      │                               │
│                          └───────────┬──────────┘                               │
│                                      │                                          │
│                        ┌─────────────┼─────────────┐                            │
│                        │             │             │                            │
│            icache_valid│             │             │dcache_valid                │
│           (icache önce)│             │             │(dcache önce)               │
│                        ▼             │             ▼                            │
│              ┌──────────────┐        │        ┌──────────────┐                  │
│              │              │        │        │              │                  │
│              │   ICACHE     │        │        │   DCACHE     │                  │
│              │  Servis      │◀───────┴───────▶│  Servis      │                  │
│              │              │  dcache_valid   │              │                  │
│              └──────┬───────┘  icache_valid   └───────┬──────┘                  │
│                     │                                 │                          │
│         iomem_valid │                                 │ iomem_valid              │
│                     │                                 │                          │
│                     └─────────────────────────────────┘                          │
│                                      │                                          │
│                                      ▼                                          │
│                             Diğer istek varsa                                    │
│                             → Round switch                                       │
│                             Yoksa → IDLE                                         │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### State Açıklamaları

| State | Açıklama |
|-------|----------|
| **IDLE** | Beklemede, yeni istek gelince ICACHE veya DCACHE'e geçiş |
| **ICACHE** | I-Cache isteği servis ediliyor, tamamlanınca DCACHE veya IDLE'a |
| **DCACHE** | D-Cache isteği servis ediliyor, tamamlanınca ICACHE veya IDLE'a |

---

## Veri Yolları

### İstek Yönlendirme

```systemverilog
always_comb begin
    if (round == DCACHE) begin
        iomem_req_o.addr  = dcache_req_reg.addr;
        iomem_req_o.valid = dcache_req_reg.valid;
    end else begin
        // ICACHE veya IDLE durumunda I-Cache öncelikli
        iomem_req_o.addr  = icache_req_reg.addr;
        iomem_req_o.valid = icache_req_reg.valid;
    end
    
    iomem_req_o.data = dcache_req_reg.data;  // D-Cache yazma verisi
end
```

### Yazma Maskesi (D-Cache)

```systemverilog
always_comb begin
    iomem_req_o.rw = '0;
    
    if (round == DCACHE && dcache_req_reg.valid && dcache_req_reg.rw) begin
        if (dcache_req_reg.uncached) begin
            // Uncached write: rw_size'a göre byte enable
            case (dcache_req_reg.rw_size)
                2'b01:   iomem_req_o.rw = 'b1    << dcache_req_reg.addr[BOFFSET-1:0]; // Byte
                2'b10:   iomem_req_o.rw = 'b11   << dcache_req_reg.addr[BOFFSET-1:0]; // Halfword
                default: iomem_req_o.rw = 'b1111 << dcache_req_reg.addr[BOFFSET-1:0]; // Word
            endcase
        end else begin
            // Cached write: tam cache line
            case (dcache_req_reg.rw_size)
                2'b01:   iomem_req_o.rw = 'b1    << dcache_req_reg.addr[BOFFSET-1:0];
                2'b10:   iomem_req_o.rw = 'b11   << dcache_req_reg.addr[BOFFSET-1:0];
                default: iomem_req_o.rw = '1;  // Tüm line
            endcase
        end
    end
end
```

### Yanıt Yönlendirme

```systemverilog
always_comb begin
    // I-Cache yanıtı
    icache_res_o.valid = (round == ICACHE) && iomem_res_i.valid;
    icache_res_o.ready = 1'b1;
    icache_res_o.blk   = iomem_res_i.data;

    // D-Cache yanıtı
    dcache_res_o.valid = (round == DCACHE) && iomem_res_i.valid;
    dcache_res_o.ready = 1'b1;
    dcache_res_o.data  = iomem_res_i.data;
end
```

---

## Zamanlama Diyagramları

### Tek I-Cache İsteği

```
clk      ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____ ... ____/‾‾‾‾\____

icache   ────/‾‾‾‾\─────────────────────────────────────────────
req.valid

round    ────┤IDLE ├────┤ICACHE├──────────────────┤IDLE ├──────

iomem    ────────────────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\─────────────────────
req.valid                Memory access

iomem    ─────────────────────────────────────────/‾‾‾‾\────────
res.valid                                         Done!

icache   ─────────────────────────────────────────/‾‾‾‾\────────
res.valid
```

### I-Cache ve D-Cache Çakışması

```
clk      ____/‾\____/‾\____/‾\____ ... ____/‾\____ ... ____/‾\____

icache   ────/‾‾‾‾\───────────────────────────────────────────────
req.valid

dcache   ──────────/‾‾‾‾\─────────────────────────────────────────
req.valid

round    ────┤IDLE├┤ICACHE├────────────────┤DCACHE├───────┤IDLE├──

iomem_req────────────/‾‾‾‾‾‾‾‾‾‾\────────────/‾‾‾‾‾‾‾‾‾‾\─────────
             icache addr        dcache addr

icache   ──────────────────────────────────/‾‾‾‾\─────────────────
res.valid                                   I done

dcache   ────────────────────────────────────────────────/‾‾‾‾\───
res.valid                                                D done
```

### Round-Robin Fairness

```
clk      ____/‾\____/‾\____/‾\____/‾\____/‾\____ ... 

         Sürekli icache ve dcache istekleri

round    ──┤IC├────┤DC├────┤IC├────┤DC├────┤IC├── ...
           ↑       ↑       ↑       ↑       ↑
           │       │       │       │       │
        icache  dcache  icache  dcache  icache
        servis  servis  servis  servis  servis

         Fair scheduling: alternating access
```

---

## Performans Analizi

### Gecikme Analizi

| Senaryo | Gecikme |
|---------|---------|
| Tek istek (IDLE → servic) | 0 cycle overhead |
| Çakışan istekler | İlk: 0, İkinci: +memory_latency |
| Sürekli çakışma | Ortalama 2× memory latency |

### Bant Genişliği

```
Peak Bandwidth (no contention):
    BW = BLK_SIZE / memory_latency
    BW = 128 bit / 10 cycle = 12.8 bits/cycle @ 50MHz

Effective Bandwidth (with contention):
    BW_eff = BW / 2 (worst case: 50% utilization per cache)
```

### Fairness Garantisi

- Round-robin sayesinde starvation yok
- Her istek en fazla 1 başka isteği bekler
- Uzun vadede eşit erişim fırsatı

---

## Doğrulama ve Test

### Assertion'lar

```systemverilog
// Aynı anda tek cache servis edilmeli
assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(icache_res_o.valid && dcache_res_o.valid)
) else $error("Both caches cannot have valid response simultaneously");

// IDLE'da istek varsa geçiş olmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (round == IDLE && (icache_req_reg.valid || dcache_req_reg.valid)) |=> 
    (round != IDLE)
) else $error("Should transition from IDLE when request pending");

// Round-robin fairness: sürekli isteklerde dönüşümlü servis
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (round == ICACHE && iomem_res_i.valid && dcache_req_reg.valid) |=> 
    (round == DCACHE)
) else $error("Should switch to DCACHE after ICACHE when DCACHE pending");
```

### Test Senaryoları

1. **Tek Cache Erişimi**
   - Sadece I-Cache istekleri
   - Sadece D-Cache istekleri

2. **Çakışan İstekler**
   - Aynı cycle'da her iki istek
   - Alternating istekler

3. **Starvation Testi**
   - Bir cache sürekli istek, diğer tek istek
   - Her ikisi de servis edilmeli

4. **Uncached Write**
   - D-Cache uncached write
   - Byte/halfword/word write

---

## Özet

`memory_arbiter` modülü:

1. **Fair Scheduling**: Round-robin ile starvation önlenir
2. **Request Latching**: Pulse kayıpları önlenir
3. **Flexible Write**: Byte/halfword/word write desteği
4. **Simple Design**: Minimal karmaşıklık, kolay debug
5. **Low Latency**: Contention yoksa ek gecikme yok

Bu modül, Von Neumann mimarisinde I-Cache ve D-Cache arasında verimli bellek paylaşımı sağlar.
