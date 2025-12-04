# Physical Memory Attributes (PMA) Modülü - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Bellek Haritası](#bellek-haritası)
4. [Region Tanımları](#region-tanımları)
5. [Erişim Kontrolü](#erişim-kontrolü)
6. [Cache Politikası](#cache-politikası)
7. [MMIO Regulator](#mmio-regulator)
8. [Peripheral Erişimi](#peripheral-erişimi)
9. [Doğrulama ve Test](#doğrulama-ve-test)

---

## Genel Bakış

### Amaç

`pma` (Physical Memory Attributes) modülü, bellek adres alanının fiziksel özelliklerini tanımlar. Her bellek bölgesi için cache'lenebilirlik, çalıştırılabilirlik ve erişim izinlerini belirler.

### Temel Özellikler

| Özellik | Değer |
|---------|-------|
| **Region Sayısı** | 20 |
| **Adres Genişliği** | 32-bit |
| **Decode Yöntemi** | Paralel match |
| **Latency** | 0 cycle (combinational) |
| **Default Politika** | Error on unmapped |

### PMA Blok Diyagramı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                         PHYSICAL MEMORY ATTRIBUTES (PMA)                         │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                          ADDRESS INPUT                                   │   │
│   │                                                                          │   │
│   │              i_addr[31:0]                                                │   │
│   │                   │                                                      │   │
│   └───────────────────┼──────────────────────────────────────────────────────┘   │
│                       │                                                          │
│                       ▼                                                          │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                    PARALLEL REGION MATCHER                               │   │
│   │                                                                          │   │
│   │  ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐         ┌────────┐        │   │
│   │  │Region 0│ │Region 1│ │Region 2│ │Region 3│   ...   │Region19│        │   │
│   │  │  RAM   │ │ CLINT  │ │ UART0  │ │ UART1  │         │  VGA   │        │   │
│   │  └───┬────┘ └───┬────┘ └───┬────┘ └───┬────┘         └───┬────┘        │   │
│   │      │          │          │          │                  │              │   │
│   │      ▼          ▼          ▼          ▼                  ▼              │   │
│   │  ┌──────────────────────────────────────────────────────────────────┐  │   │
│   │  │                     PRIORITY ENCODER                              │  │   │
│   │  │              (First match wins - low index priority)              │  │   │
│   │  └──────────────────────────────────────────────────────────────────┘  │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                        OUTPUT ATTRIBUTES                                 │   │
│   │                                                                          │   │
│   │    o_cacheable ─────────► Cache'lenebilir mi?                           │   │
│   │    o_executable ────────► Çalıştırılabilir mi?                          │   │
│   │    o_mmio ──────────────► Memory-mapped I/O mu?                         │   │
│   │    o_access_fault ──────► Erişim hatası mı?                             │   │
│   │    o_region_idx ────────► Eşleşen region indeksi                        │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module pma
  import ceres_param::*;
#(
    parameter int NUM_REGIONS = PMA_NUM_REGIONS  // 20
) (
    // Address inputs
    input  logic [XLEN-1:0]           i_addr,        // Kontrol edilecek adres
    input  logic                      i_req,         // İstek geçerli
    input  logic                      i_we,          // Write enable

    // Memory type outputs
    output logic                      o_cacheable,   // Cache'lenebilir
    output logic                      o_executable,  // Çalıştırılabilir
    output logic                      o_mmio,        // Memory-mapped I/O
    output logic                      o_atomic_ok,   // Atomic destekli

    // Access control outputs
    output logic                      o_read_ok,     // Okuma izni
    output logic                      o_write_ok,    // Yazma izni
    output logic                      o_access_fault,// Erişim hatası

    // Debug outputs
    output logic [$clog2(NUM_REGIONS)-1:0] o_region_idx  // Eşleşen region
);
```

---

## Bellek Haritası

### Tam Bellek Haritası

```
┌────────────────────────────────────────────────────────────────────────────────┐
│                          CERES SOC MEMORY MAP                                   │
├────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  0xFFFF_FFFF ┬─────────────────────────────────────────────────────────────────│
│              │                                                                  │
│              │                       RAM                                        │
│              │                   (Cacheable)                                    │
│              │                  (Executable)                                    │
│              │                    (2 GB)                                        │
│              │                                                                  │
│  0x8000_0000 ┼─────────────────────────────────────────────────────────────────│
│              │              Reserved (Error)                                    │
│  0x4000_0000 ┼─────────────────────────────────────────────────────────────────│
│              │                                                                  │
│              │                     CLINT                                        │
│              │              Core Local Interruptor                              │
│              │                (Uncacheable)                                     │
│              │                   (64 KB)                                        │
│              │                                                                  │
│  0x3000_0000 ┼─────────────────────────────────────────────────────────────────│
│              │              Reserved (Error)                                    │
│  0x2010_0000 ┼─────────────────────────────────────────────────────────────────│
│              │                                                                  │
│              │               VGA Framebuffer                                    │
│              │                  (256 KB)                                        │
│              │                                                                  │
│  0x200D_0000 ┼─────────────────────────────────────────────────────────────────│
│              │                 VGA Control                                      │
│  0x2009_0000 ┼───────────────── DMA ─────────────────────────────────────────│
│  0x2008_0000 ┼───────────────── WDT ─────────────────────────────────────────│
│  0x2007_0000 ┼───────────────── PLIC ────────────────────────────────────────│
│  0x2006_0000 ┼───────────────── Timer ───────────────────────────────────────│
│  0x2005_0000 ┼───────────────── PWM ─────────────────────────────────────────│
│  0x2004_0000 ┼───────────────── GPIO ────────────────────────────────────────│
│  0x2003_0000 ┼───────────────── I2C0 ────────────────────────────────────────│
│  0x2002_0000 ┼───────────────── SPI0 ────────────────────────────────────────│
│  0x2001_0000 ┼───────────────── UART1 ───────────────────────────────────────│
│  0x2000_0000 ┼───────────────── UART0 ───────────────────────────────────────│
│              │              Reserved (Error)                                    │
│  0x0000_0000 ┴─────────────────────────────────────────────────────────────────│
│                                                                                 │
└────────────────────────────────────────────────────────────────────────────────┘
```

---

## Region Tanımları

### Region Yapısı

```systemverilog
typedef struct packed {
    logic [XLEN-1:0] base_addr;    // Başlangıç adresi
    logic [XLEN-1:0] addr_mask;    // Adres maskesi
    logic            cacheable;    // Cache'lenebilir
    logic            executable;   // Çalıştırılabilir
    logic            readable;     // Okunabilir
    logic            writable;     // Yazılabilir
    logic            atomic;       // Atomic destekli
    logic            mmio;         // Memory-mapped I/O
} pma_region_t;
```

### Tüm Region Tanımları

```systemverilog
localparam pma_region_t [NUM_REGIONS-1:0] PMA_REGIONS = '{
    // Region 0: RAM (Main Memory)
    '{
        base_addr:  32'h8000_0000,
        addr_mask:  32'h8000_0000,  // 0x8xxx_xxxx matches
        cacheable:  1'b1,
        executable: 1'b1,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b1,
        mmio:       1'b0
    },

    // Region 1: CLINT
    '{
        base_addr:  32'h3000_0000,
        addr_mask:  32'hFFFF_0000,  // 64KB
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // Region 2: UART0
    '{
        base_addr:  32'h2000_0000,
        addr_mask:  32'hFFFF_F000,  // 4KB
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // Region 3: UART1
    '{
        base_addr:  32'h2000_1000,
        addr_mask:  32'hFFFF_F000,
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // Region 4: SPI0
    '{
        base_addr:  32'h2000_2000,
        addr_mask:  32'hFFFF_F000,
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // Region 5: I2C0
    '{
        base_addr:  32'h2000_3000,
        addr_mask:  32'hFFFF_F000,
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // Region 6: GPIO
    '{
        base_addr:  32'h2000_4000,
        addr_mask:  32'hFFFF_F000,
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // Region 7: PWM
    '{
        base_addr:  32'h2000_5000,
        addr_mask:  32'hFFFF_F000,
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // Region 8: Timer
    '{
        base_addr:  32'h2000_6000,
        addr_mask:  32'hFFFF_F000,
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // Region 9: PLIC
    '{
        base_addr:  32'h2000_7000,
        addr_mask:  32'hFFFF_F000,
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // Region 10: Watchdog
    '{
        base_addr:  32'h2000_8000,
        addr_mask:  32'hFFFF_F000,
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // Region 11: DMA
    '{
        base_addr:  32'h2000_9000,
        addr_mask:  32'hFFFF_F000,
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // ... (VGA Control, VGA Framebuffer, Reserved regions)

    // Region 18: VGA Control
    '{
        base_addr:  32'h200D_0000,
        addr_mask:  32'hFFFF_F000,
        cacheable:  1'b0,
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    },

    // Region 19: VGA Framebuffer
    '{
        base_addr:  32'h2010_0000,
        addr_mask:  32'hFFFC_0000,  // 256KB
        cacheable:  1'b0,           // Write-through preferred
        executable: 1'b0,
        readable:   1'b1,
        writable:   1'b1,
        atomic:     1'b0,
        mmio:       1'b1
    }
};
```

### Region Özet Tablosu

| # | Bölge | Base | Size | C | X | R | W | A | MMIO |
|---|-------|------|------|---|---|---|---|---|------|
| 0 | RAM | 0x8000_0000 | 2GB | ✓ | ✓ | ✓ | ✓ | ✓ | - |
| 1 | CLINT | 0x3000_0000 | 64KB | - | - | ✓ | ✓ | - | ✓ |
| 2 | UART0 | 0x2000_0000 | 4KB | - | - | ✓ | ✓ | - | ✓ |
| 3 | UART1 | 0x2000_1000 | 4KB | - | - | ✓ | ✓ | - | ✓ |
| 4 | SPI0 | 0x2000_2000 | 4KB | - | - | ✓ | ✓ | - | ✓ |
| 5 | I2C0 | 0x2000_3000 | 4KB | - | - | ✓ | ✓ | - | ✓ |
| 6 | GPIO | 0x2000_4000 | 4KB | - | - | ✓ | ✓ | - | ✓ |
| 7 | PWM | 0x2000_5000 | 4KB | - | - | ✓ | ✓ | - | ✓ |
| 8 | Timer | 0x2000_6000 | 4KB | - | - | ✓ | ✓ | - | ✓ |
| 9 | PLIC | 0x2000_7000 | 4KB | - | - | ✓ | ✓ | - | ✓ |
| 10 | WDT | 0x2000_8000 | 4KB | - | - | ✓ | ✓ | - | ✓ |
| 11 | DMA | 0x2000_9000 | 4KB | - | - | ✓ | ✓ | - | ✓ |
| 18 | VGA Ctrl | 0x200D_0000 | 4KB | - | - | ✓ | ✓ | - | ✓ |
| 19 | VGA FB | 0x2010_0000 | 256KB | - | - | ✓ | ✓ | - | ✓ |

**Açıklamalar:** C=Cacheable, X=Executable, R=Readable, W=Writable, A=Atomic

---

## Erişim Kontrolü

### Region Eşleştirme

```systemverilog
logic [NUM_REGIONS-1:0] region_match;

// Paralel region eşleştirme
generate
    for (genvar i = 0; i < NUM_REGIONS; i++) begin : g_match
        assign region_match[i] = 
            (i_addr & PMA_REGIONS[i].addr_mask) == 
            (PMA_REGIONS[i].base_addr & PMA_REGIONS[i].addr_mask);
    end
endgenerate
```

### Priority Encoder

```systemverilog
// İlk eşleşen region (düşük indeks öncelikli)
logic [$clog2(NUM_REGIONS)-1:0] matched_region;
logic                           region_found;

always_comb begin
    matched_region = '0;
    region_found   = 1'b0;

    for (int i = 0; i < NUM_REGIONS; i++) begin
        if (region_match[i] && !region_found) begin
            matched_region = i[$clog2(NUM_REGIONS)-1:0];
            region_found   = 1'b1;
        end
    end
end
```

### Erişim İzni Kontrolü

```systemverilog
always_comb begin
    if (region_found) begin
        o_cacheable   = PMA_REGIONS[matched_region].cacheable;
        o_executable  = PMA_REGIONS[matched_region].executable;
        o_mmio        = PMA_REGIONS[matched_region].mmio;
        o_atomic_ok   = PMA_REGIONS[matched_region].atomic;
        o_read_ok     = PMA_REGIONS[matched_region].readable;
        o_write_ok    = PMA_REGIONS[matched_region].writable;

        // Erişim kontrolü
        if (i_we && !PMA_REGIONS[matched_region].writable) begin
            o_access_fault = 1'b1;  // Yazma izni yok
        end else if (!i_we && !PMA_REGIONS[matched_region].readable) begin
            o_access_fault = 1'b1;  // Okuma izni yok
        end else begin
            o_access_fault = 1'b0;
        end
    end else begin
        // Eşleşen region yok - unmapped
        o_cacheable    = 1'b0;
        o_executable   = 1'b0;
        o_mmio         = 1'b0;
        o_atomic_ok    = 1'b0;
        o_read_ok      = 1'b0;
        o_write_ok     = 1'b0;
        o_access_fault = i_req;  // Unmapped access = fault
    end
end
```

---

## Cache Politikası

### Cacheable Bölgeler

Sadece RAM bölgesi cache'lenebilir:

```systemverilog
// Region 0: RAM - Cacheable
// Tüm peripherals: Non-cacheable (MMIO)

// I-Cache: executable && cacheable kontrolü
// D-Cache: cacheable kontrolü (MMIO bypass)
```

### Cache Davranışı

| Bölge | I-Cache | D-Cache | Politika |
|-------|---------|---------|----------|
| RAM | Hit/Miss | Hit/Miss | Write-back, Write-allocate |
| CLINT | Bypass | Bypass | Direct access |
| UART | Bypass | Bypass | Direct access |
| GPIO | Bypass | Bypass | Direct access |
| VGA FB | Bypass | Bypass | Direct access |

### MMIO Erişim Kuralları

```
MMIO Bölgeleri için:
1. Cache bypass - her erişim direkt belleğe
2. Side-effect var - okuma bile state değiştirebilir
3. Sıralı erişim - out-of-order yok
4. Tek erişim - burst yok (genellikle)
```

---

## MMIO Regulator

### Side-Effect Yönetimi

MMIO erişimlerinde side-effect'ler olabilir:

```systemverilog
// MMIO check - cache bypass gerekli mi?
assign o_mmio = region_found && PMA_REGIONS[matched_region].mmio;

// Cache kontrolünde kullanım:
// if (pma_mmio) begin
//     // Cache bypass, direkt bus erişimi
// end else begin
//     // Normal cache erişimi
// end
```

### Atomic Erişim

RAM bölgesi atomic işlemleri destekler:

```systemverilog
// Atomic destekli bölgeler
// LR/SC, AMO instructions

assign o_atomic_ok = region_found && PMA_REGIONS[matched_region].atomic;

// Atomic desteği olmayan bölgede AMO:
// → Store/AMO access fault (exception)
```

---

## Peripheral Erişimi

### Peripheral Adres Hesaplama

```systemverilog
// Peripheral offset hesaplama
localparam PERIPH_BASE = 32'h2000_0000;
localparam PERIPH_SLOT = 12;  // 4KB per peripheral

function automatic logic [3:0] get_periph_id(logic [31:0] addr);
    return addr[PERIPH_SLOT+3:PERIPH_SLOT];  // bits [15:12]
endfunction

// Peripheral IDs
localparam PERIPH_UART0  = 4'h0;  // 0x2000_0xxx
localparam PERIPH_UART1  = 4'h1;  // 0x2000_1xxx
localparam PERIPH_SPI0   = 4'h2;  // 0x2000_2xxx
localparam PERIPH_I2C0   = 4'h3;  // 0x2000_3xxx
localparam PERIPH_GPIO   = 4'h4;  // 0x2000_4xxx
localparam PERIPH_PWM    = 4'h5;  // 0x2000_5xxx
localparam PERIPH_TIMER  = 4'h6;  // 0x2000_6xxx
localparam PERIPH_PLIC   = 4'h7;  // 0x2000_7xxx
localparam PERIPH_WDT    = 4'h8;  // 0x2000_8xxx
localparam PERIPH_DMA    = 4'h9;  // 0x2000_9xxx
localparam PERIPH_VGA_C  = 4'hD;  // 0x200D_xxxx
```

### Peripheral Register Offset

```systemverilog
// Register offset (peripheral içi)
function automatic logic [11:0] get_reg_offset(logic [31:0] addr);
    return addr[11:0];
endfunction

// Örnek: UART0 TX register
// Adres: 0x2000_0000 + 0x000 = 0x2000_0000
// periph_id = 0, reg_offset = 0
```

---

## Doğrulama ve Test

### Assertion'lar

```systemverilog
// En fazla bir region eşleşmeli
assert property (@(posedge clk_i) disable iff (!rst_ni)
    region_found |-> $onehot(region_match)
) else $warning("Multiple PMA region match");

// RAM bölgesi cacheable olmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (region_match[0]) |-> o_cacheable
) else $error("RAM should be cacheable");

// MMIO bölgeleri non-cacheable olmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
    o_mmio |-> !o_cacheable
) else $error("MMIO should not be cacheable");

// Executable sadece RAM'de
assert property (@(posedge clk_i) disable iff (!rst_ni)
    o_executable |-> (matched_region == 0)
) else $error("Only RAM should be executable");
```

### Test Senaryoları

1. **Region Eşleştirme**
   - Her region için boundary test
   - Overlapping region kontrolü

2. **Erişim İzni**
   - Read-only bölgeye yazma
   - Execute-only bölgeden okuma

3. **Cache Politikası**
   - Cacheable bölge testi
   - MMIO bypass testi

4. **Unmapped Erişim**
   - Reserved bölgeye erişim
   - Fault generation

### Debug Log

```systemverilog
`ifdef DEBUG_PMA
    always_comb begin
        if (i_req) begin
            $display("[PMA] addr=0x%08x region=%0d cache=%b exec=%b mmio=%b fault=%b",
                     i_addr, matched_region, o_cacheable, o_executable,
                     o_mmio, o_access_fault);
        end
    end
`endif
```

---

## Özet

PMA modülü:

1. **20 Region**: RAM + CLINT + 18 peripheral
2. **Paralel Match**: Tek cycle adres decode
3. **Cache Control**: Cacheable/MMIO belirleme
4. **Access Control**: Read/Write/Execute izinleri
5. **Fault Detection**: Unmapped erişim koruması

Bu modül, CERES SoC'da bellek koruma ve cache politikası yönetiminin temelini oluşturur.
