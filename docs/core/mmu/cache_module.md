# Cache Modülü - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Önbellek Mimarisi](#önbellek-mimarisi)
4. [PLRU Eviction Algoritması](#plru-eviction-algoritması)
5. [I-Cache Davranışı](#i-cache-davranışı)
6. [D-Cache Davranışı](#d-cache-davranışı)
7. [FENCE.I Dirty Writeback](#fencei-dirty-writeback)
8. [Bellek Yapıları](#bellek-yapıları)
9. [Zamanlama Diyagramları](#zamanlama-diyagramları)
10. [Performans Analizi](#performans-analizi)
11. [Doğrulama ve Test](#doğrulama-ve-test)

---

## Genel Bakış

### Amaç

`cache` modülü, CERES RISC-V işlemcisi için **parametrik**, **set-associative** önbellek uygulamasıdır. Tek bir modül hem **I-Cache** (Instruction Cache) hem de **D-Cache** (Data Cache) olarak konfigüre edilebilir.

### Temel Özellikler

| Özellik | Değer |
|---------|-------|
| **Associativity** | Parametrik (varsayılan 8-way) |
| **Kapasite** | Parametrik (varsayılan 8KB) |
| **Blok Boyutu** | 128-bit (4 x 32-bit word) |
| **Eviction Policy** | Pseudo-LRU (Tree-based PLRU) |
| **Write Policy** | Write-back, Write-allocate (D-Cache) |
| **Unified/Split** | Split (ayrı I-Cache ve D-Cache) |
| **FENCE.I Desteği** | Dirty writeback state machine |

### Cache Blok Diyagramı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                                    CACHE                                         │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌──────────────────────────────────────────────────────────────────────────┐  │
│   │                           ADDRESS DECODE                                  │  │
│   │   ┌────────────┬────────────┬────────────┐                               │  │
│   │   │    TAG     │   INDEX    │   OFFSET   │                               │  │
│   │   │  [31:IDX+B]│[IDX+B-1:B] │  [B-1:0]   │                               │  │
│   │   └────────────┴────────────┴────────────┘                               │  │
│   └──────────────────────────────────────────────────────────────────────────┘  │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                         MEMORY ARRAYS                                    │   │
│   │                                                                          │   │
│   │   ┌─────────────┐   ┌─────────────┐   ┌─────────────┐   ┌───────────┐   │   │
│   │   │  Tag Array  │   │ Data Array  │   │ Valid Array │   │PLRU Array │   │   │
│   │   │  (NUM_WAY)  │   │  (NUM_WAY)  │   │  (NUM_WAY)  │   │(NUM_WAY-1)│   │   │
│   │   └──────┬──────┘   └──────┬──────┘   └──────┬──────┘   └─────┬─────┘   │   │
│   │          │                 │                 │                │          │   │
│   │          ▼                 ▼                 ▼                ▼          │   │
│   │   ┌─────────────────────────────────────────────────────────────────┐   │   │
│   │   │                    HIT/MISS DETECTION                            │   │   │
│   │   │   Tag Match && Valid → Hit                                       │   │   │
│   │   │   !Match || !Valid  → Miss                                       │   │   │
│   │   └─────────────────────────────────────────────────────────────────┘   │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                    D-CACHE SPECIFIC (IS_ICACHE=0)                        │   │
│   │   ┌─────────────┐   ┌─────────────────────────────────────────────────┐ │   │
│   │   │ Dirty Array │   │         FENCE.I Writeback FSM                   │ │   │
│   │   │  (NUM_WAY)  │   │  IDLE → SCAN → CHECK → WRITEBACK → MARK_CLEAN   │ │   │
│   │   └─────────────┘   └─────────────────────────────────────────────────┘ │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module cache
  import ceres_param::*;
#(
    parameter      IS_ICACHE   = 1,           // 1: I-Cache, 0: D-Cache
    parameter type cache_req_t = logic,       // Cache istek tipi
    parameter type cache_res_t = logic,       // Cache yanıt tipi
    parameter type lowX_res_t  = logic,       // Alt seviye yanıt tipi
    parameter type lowX_req_t  = logic,       // Alt seviye istek tipi
    parameter      CACHE_SIZE  = 1024,        // Cache boyutu (byte)
    parameter      BLK_SIZE    = ceres_param::BLK_SIZE, // Blok boyutu (bit)
    parameter      XLEN        = ceres_param::XLEN,     // Veri genişliği
    parameter      NUM_WAY     = 4            // Associativity
) (
    input  logic       clk_i,          // Sistem saati
    input  logic       rst_ni,         // Aktif-düşük reset
    input  logic       flush_i,        // Cache flush sinyali
    input  cache_req_t cache_req_i,    // Cache isteği
    output cache_res_t cache_res_o,    // Cache yanıtı
    input  lowX_res_t  lowX_res_i,     // Alt seviye yanıtı
    output lowX_req_t  lowX_req_o,     // Alt seviye isteği
    output logic       fencei_stall_o  // FENCE.I stall sinyali
);
```

### Port Açıklamaları

| Port | Yön | Genişlik | Açıklama |
|------|-----|----------|----------|
| `clk_i` | Giriş | 1 bit | Sistem saati |
| `rst_ni` | Giriş | 1 bit | Aktif-düşük asenkron reset |
| `flush_i` | Giriş | 1 bit | Cache flush tetikleyici (FENCE.I) |
| `cache_req_i` | Giriş | Struct | Cache erişim isteği |
| `cache_res_o` | Çıkış | Struct | Cache yanıtı |
| `lowX_res_i` | Giriş | Struct | Bellek yanıtı |
| `lowX_req_o` | Çıkış | Struct | Bellek isteği |
| `fencei_stall_o` | Çıkış | 1 bit | FENCE.I dirty writeback stall |

### Yerel Parametreler

```systemverilog
localparam NUM_SET    = (CACHE_SIZE / BLK_SIZE) / NUM_WAY;  // Set sayısı
localparam IDX_WIDTH  = $clog2(NUM_SET);                     // Index bit genişliği
localparam BOFFSET    = $clog2(BLK_SIZE / 8);                // Blok offset bit
localparam WOFFSET    = $clog2(BLK_SIZE / 32);               // Word offset bit
localparam TAG_SIZE   = XLEN - IDX_WIDTH - BOFFSET;          // Tag bit genişliği
```

### Varsayılan Konfigürasyon (8KB, 8-way)

| Parametre | Değer | Hesaplama |
|-----------|-------|-----------|
| CACHE_SIZE | 8192 byte | 8KB |
| BLK_SIZE | 128 bit | 16 byte cache line |
| NUM_WAY | 8 | 8-way set associative |
| NUM_SET | 64 | 8192 / 16 / 8 |
| IDX_WIDTH | 6 bit | log2(64) |
| BOFFSET | 4 bit | log2(128/8) |
| TAG_SIZE | 22 bit | 32 - 6 - 4 |

---

## Önbellek Mimarisi

### Adres Çözümleme

```
32-bit Adres Yapısı:
┌─────────────────────────────────────────────────────────────────┐
│  31        31-IDX_WIDTH   IDX_WIDTH+BOFFSET-1   BOFFSET-1    0  │
│  ┌──────────────────────┬────────────────────┬───────────────┐  │
│  │         TAG          │       INDEX        │    OFFSET     │  │
│  │      (22 bit)        │      (6 bit)       │   (4 bit)     │  │
│  └──────────────────────┴────────────────────┴───────────────┘  │
└─────────────────────────────────────────────────────────────────┘

Örnek: Adres 0x8000_1234
- TAG:    0x200004  (bits [31:10])
- INDEX:  0x12      (bits [9:4])
- OFFSET: 0x4       (bits [3:0])
```

### Set-Associative Yapısı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                           8-WAY SET ASSOCIATIVE CACHE                            │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│         Way 0      Way 1      Way 2      Way 3      Way 4      Way 5      ...   │
│       ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐        │
│ Set 0 │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│        │
│       ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤        │
│ Set 1 │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│        │
│       ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤        │
│ Set 2 │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│        │
│       ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤        │
│  ...  │  ...   │ │  ...   │ │  ...   │ │  ...   │ │  ...   │ │  ...   │        │
│       ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤ ├────────┤        │
│Set 63 │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│ │V|T|Data│        │
│       └────────┘ └────────┘ └────────┘ └────────┘ └────────┘ └────────┘        │
│                                                                                  │
│   V = Valid bit (1 bit)                                                          │
│   T = Tag (22 bit)                                                               │
│   Data = Cache line (128 bit = 4 words)                                          │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Cache Line Yapısı

```
128-bit Cache Line (4 x 32-bit words):
┌────────────────┬────────────────┬────────────────┬────────────────┐
│    Word 3      │    Word 2      │    Word 1      │    Word 0      │
│   [127:96]     │   [95:64]      │   [63:32]      │   [31:0]       │
├────────────────┴────────────────┴────────────────┴────────────────┤
│                      Offset [3:0]                                  │
│   0x0 → Word 0    0x4 → Word 1    0x8 → Word 2    0xC → Word 3    │
└───────────────────────────────────────────────────────────────────┘
```

---

## PLRU Eviction Algoritması

### Tree-based Pseudo-LRU

PLRU (Pseudo Least Recently Used), tam LRU'nun donanım maliyetini azaltmak için kullanılan bir yaklaşımdır. 8-way cache için 7 bitlik bir tree yapısı kullanılır.

```
                    PLRU Tree Yapısı (8-way için)
                    ─────────────────────────────
                    
                           [0]
                          /    \
                        /        \
                      /            \
                    [1]            [2]
                   /   \          /   \
                  /     \        /     \
                [3]     [4]    [5]     [6]
               / \     / \    / \     / \
              W0  W1  W2  W3 W4  W5  W6  W7

    Node değeri:
    - 0 = Sol tarafa git (LRU sol tarafta)
    - 1 = Sağ tarafa git (LRU sağ tarafta)
    
    Erişim sonrası:
    - Erişilen way'e giden path'teki tüm node'lar ters yöne işaret eder
```

### PLRU Node Güncelleme Fonksiyonu

```systemverilog
function automatic [NUM_WAY-2:0] update_node(
    input logic [NUM_WAY-2:0] node_in, 
    input logic [NUM_WAY-1:0] hit_vec
);
    logic [NUM_WAY-2:0] node_tmp;
    int idx_base, shift;
    node_tmp = node_in;
    
    for (int unsigned i = 0; i < NUM_WAY; i++) begin
        if (hit_vec[i]) begin
            for (int unsigned lvl = 0; lvl < $clog2(NUM_WAY); lvl++) begin
                idx_base = (2 ** lvl) - 1;
                shift = $clog2(NUM_WAY) - lvl;
                // Erişilen way'e giden path'i ters yöne çevir
                node_tmp[idx_base + (i >> shift)] = ((i >> (shift - 1)) & 1) == 0;
            end
        end
    end
    return node_tmp;
endfunction
```

### PLRU Evict Way Hesaplama

```systemverilog
function automatic [NUM_WAY-1:0] compute_evict_way(
    input logic [NUM_WAY-2:0] node_in
);
    logic [NUM_WAY-1:0] way;
    int idx_base, shift;
    
    for (int unsigned i = 0; i < NUM_WAY; i++) begin
        logic en;
        en = 1'b1;
        for (int unsigned lvl = 0; lvl < $clog2(NUM_WAY); lvl++) begin
            idx_base = (2 ** lvl) - 1;
            shift = $clog2(NUM_WAY) - lvl;
            // Tree'yi takip ederek LRU way'i bul
            if (((i >> (shift - 1)) & 32'b1) == 32'b1) 
                en &= node_in[idx_base + (i >> shift)];
            else 
                en &= ~node_in[idx_base + (i >> shift)];
        end
        way[i] = en;
    end
    return way;
endfunction
```

### PLRU Örneği

```
Başlangıç: node = 7'b0000000 (tüm yönler sol)
           Evict Way = Way 0

Way 5'e erişim:
- Path: Root(0) → Sağ(2) → Sol(5) → Way 5
- Güncelleme: node[0]=0, node[2]=0, node[5]=1
- Yeni node = 7'b0100000
- Yeni Evict Way = Way 0 (hala)

Way 0'a erişim:
- Path: Root(0) → Sol(1) → Sol(3) → Way 0
- Güncelleme: node[0]=1, node[1]=1, node[3]=1
- Yeni node = 7'b0101011
- Yeni Evict Way = Way 4
```

---

## I-Cache Davranışı

### I-Cache Özellikleri

| Özellik | Değer |
|---------|-------|
| IS_ICACHE | 1 |
| Write Desteği | Hayır (read-only) |
| Dirty Bit | Yok |
| Writeback | Yok |
| FENCE.I Stall | Her zaman 0 |

### I-Cache Mantığı

```systemverilog
if (IS_ICACHE) begin : icache_impl
    // I-Cache'de dirty writeback yok
    assign fencei_stall_o = 1'b0;

    always_comb begin
        // Node array güncelleme (hit veya refill durumunda)
        nsram.rw_en = cache_wr_en || cache_hit;
        nsram.wnode = flush ? '0 : updated_node;
        nsram.idx   = cache_idx;

        // Tag array güncelleme (miss + refill durumunda)
        tsram.way   = '0;
        tsram.idx   = cache_idx;
        tsram.wtag  = flush ? '0 : {1'b1, cache_req_q.addr[XLEN-1:IDX_WIDTH+BOFFSET]};
        for (int i = 0; i < NUM_WAY; i++) 
            tsram.way[i] = flush ? '1 : cache_wr_way[i] && cache_wr_en;

        // Data array güncelleme (refill durumunda)
        dsram.way   = '0;
        dsram.idx   = cache_idx;
        dsram.wdata = lowX_res_i.blk;
        for (int i = 0; i < NUM_WAY; i++) 
            dsram.way[i] = cache_wr_way[i] && cache_wr_en;
    end

    // LowX arayüzü ve cache yanıtı
    always_comb begin
        lowX_req_o.valid    = !lookup_ack && cache_miss;
        lowX_req_o.ready    = !flush;
        lowX_req_o.addr     = cache_req_q.addr;
        lowX_req_o.uncached = cache_req_q.uncached;
        
        cache_res_o.miss  = cache_miss;
        cache_res_o.valid = cache_req_i.ready && 
                           (cache_hit || (cache_miss && lowX_req_o.ready && lowX_res_i.valid));
        cache_res_o.ready = (!cache_miss || lowX_res_i.valid) && !flush;
        cache_res_o.blk   = (cache_miss && lowX_res_i.valid) ? lowX_res_i.blk : cache_select_data;
    end
end
```

### I-Cache Hit/Miss Akışı

```
I-Cache Hit (1 cycle):
┌────────┐    ┌────────┐    ┌────────┐
│  Req   │───▶│Tag Cmp │───▶│  Data  │
│ (addr) │    │  Hit!  │    │ Return │
└────────┘    └────────┘    └────────┘

I-Cache Miss (~10 cycles):
┌────────┐    ┌────────┐    ┌─────────────┐    ┌────────┐    ┌────────┐
│  Req   │───▶│Tag Cmp │───▶│   Memory    │───▶│ Refill │───▶│  Data  │
│ (addr) │    │ Miss!  │    │   Fetch     │    │  Cache │    │ Return │
└────────┘    └────────┘    └─────────────┘    └────────┘    └────────┘
                                  ↑
                           ~10 cycle gecikme
```

---

## D-Cache Davranışı

### D-Cache Özellikleri

| Özellik | Değer |
|---------|-------|
| IS_ICACHE | 0 |
| Write Desteği | Evet (read/write) |
| Write Policy | Write-back, Write-allocate |
| Dirty Bit | Evet (per-way) |
| Writeback | Eviction ve FENCE.I'da |
| FENCE.I Stall | Dirty line varsa aktif |

### D-Cache Dirty Array

```systemverilog
// Register-tabanlı dirty array (SRAM değil)
// FENCE.I için tek cycle'da tüm dirty bitlerine erişim gerekli
logic [NUM_WAY-1:0] dirty_reg[NUM_SET];

always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
        for (int i = 0; i < NUM_SET; i++) 
            dirty_reg[i] <= '0;
    end else begin
        for (int w = 0; w < NUM_WAY; w++) begin
            if (drsram.way[w]) begin
                dirty_reg[drsram.idx][w] <= drsram.wdirty;
            end
        end
    end
end

// Kombinasyonel okuma (anında erişim)
always_comb begin
    for (int w = 0; w < NUM_WAY; w++) begin
        drsram.rdirty[w] = dirty_reg[drsram.idx][w];
    end
end
```

### D-Cache Write İşlemi

```systemverilog
// Veri maskeleme (byte/halfword/word write)
always_comb begin
    mask_data   = cache_hit ? cache_select_data : lowX_res_i.data;
    data_wr_pre = mask_data;
    
    case (cache_req_q.rw_size)
        2'b11: data_wr_pre[cache_req_q.addr[BOFFSET-1:2]*32+:32] = cache_req_q.data; // Word
        2'b10: data_wr_pre[cache_req_q.addr[BOFFSET-1:1]*16+:16] = cache_req_q.data[15:0]; // Halfword
        2'b01: data_wr_pre[cache_req_q.addr[BOFFSET-1:0]*8+:8]   = cache_req_q.data[7:0];  // Byte
        2'b00: data_wr_pre = '0;
    endcase
end
```

### D-Cache Writeback Mantığı

```systemverilog
// Eviction durumunda dirty line writeback
write_back = cache_miss && (|(drsram.rdirty & evict_way & cache_valid_vec));

// Writeback adresi ve verisi
always_comb begin
    evict_tag  = '0;
    evict_data = '0;
    for (int i = 0; i < NUM_WAY; i++) begin
        if (evict_way[i]) begin
            evict_tag  = tsram.rtag[i][TAG_SIZE-1:0];
            evict_data = dsram.rdata[i];
        end
    end
end
```

---

## FENCE.I Dirty Writeback

### FENCE.I State Machine

FENCE.I komutu çalıştığında D-Cache'deki tüm dirty line'lar belleğe yazılmalıdır. Bu işlem bir state machine ile yönetilir.

```systemverilog
typedef enum logic [2:0] {
    FI_IDLE,            // Normal işlem
    FI_SCAN,            // Set'leri tara
    FI_CHECK_WAY,       // Her way'i kontrol et
    FI_WRITEBACK_REQ,   // Writeback isteği gönder
    FI_WRITEBACK_WAIT,  // Writeback tamamlanmasını bekle
    FI_MARK_CLEAN,      // Line'ı temiz işaretle
    FI_NEXT_WAY,        // Sonraki way'e geç
    FI_DONE             // Writeback tamamlandı
} fencei_state_e;
```

### FENCE.I Akış Diyagramı

```
┌──────────────────────────────────────────────────────────────────────────────────┐
│                         FENCE.I DIRTY WRITEBACK FSM                              │
├──────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│                              ┌──────────┐                                        │
│              flush_i ───────▶│  FI_IDLE │                                        │
│              rising edge     └────┬─────┘                                        │
│                                   │                                              │
│                                   ▼                                              │
│                              ┌──────────┐                                        │
│                              │ FI_SCAN  │◀─────────────────────────┐            │
│                              │(BRAM lat)│                          │            │
│                              └────┬─────┘                          │            │
│                                   │                                │            │
│                                   ▼                                │            │
│                           ┌─────────────┐                          │            │
│                           │FI_CHECK_WAY │                          │            │
│                           │ dirty[way]? │                          │            │
│                           └──────┬──────┘                          │            │
│                          ┌───────┴───────┐                         │            │
│                          │               │                         │            │
│                     dirty=1         dirty=0                        │            │
│                          │               │                         │            │
│                          ▼               │                         │            │
│                   ┌─────────────┐        │                         │            │
│                   │FI_WRITEBACK │        │                         │            │
│                   │    _REQ     │        │                         │            │
│                   └──────┬──────┘        │                         │            │
│                          │               │                         │            │
│                          ▼               │                         │            │
│                   ┌─────────────┐        │                         │            │
│                   │FI_WRITEBACK │        │                         │            │
│                   │   _WAIT     │        │                         │            │
│                   └──────┬──────┘        │                         │            │
│                          │               │                         │            │
│                          ▼               │                         │            │
│                   ┌─────────────┐        │                         │            │
│                   │FI_MARK_CLEAN│        │                         │            │
│                   └──────┬──────┘        │                         │            │
│                          │               │                         │            │
│                          └───────┬───────┘                         │            │
│                                  │                                 │            │
│                                  ▼                                 │            │
│                           ┌─────────────┐                          │            │
│                           │ FI_NEXT_WAY │                          │            │
│                           └──────┬──────┘                          │            │
│                          ┌───────┴───────┐                         │            │
│                          │               │                         │            │
│                     way<NUM_WAY-1   way=NUM_WAY-1                  │            │
│                          │               │                         │            │
│                          │        ┌──────┴──────┐                  │            │
│                          │        │             │                  │            │
│                          │   set<NUM_SET-1  set=NUM_SET-1          │            │
│                          │        │             │                  │            │
│                          │        │             ▼                  │            │
│                          │        │       ┌──────────┐             │            │
│                          │        │       │ FI_DONE  │────▶ flush_i=0 ──▶ IDLE  │
│                          │        │       └──────────┘             │            │
│                          │        │                                │            │
│                          ▼        └────────────────────────────────┘            │
│                     CHECK_WAY                                                    │
│                     (next way)                                                   │
│                                                                                  │
└──────────────────────────────────────────────────────────────────────────────────┘
```

### FENCE.I State Machine Kodu

```systemverilog
always_comb begin
    fi_state_d       = fi_state_q;
    fi_set_idx_d     = fi_set_idx_q;
    fi_way_idx_d     = fi_way_idx_q;
    fi_active        = 1'b0;
    fi_writeback_req = 1'b0;
    fi_mark_clean    = 1'b0;

    unique case (fi_state_q)
        FI_IDLE: begin
            if (fi_start) begin
                fi_state_d   = FI_SCAN;
                fi_set_idx_d = '0;
                fi_way_idx_d = '0;
                fi_active    = 1'b1;
            end
        end

        FI_SCAN: begin
            fi_active  = 1'b1;
            fi_state_d = FI_CHECK_WAY;  // BRAM latency için bekle
        end

        FI_CHECK_WAY: begin
            fi_active = 1'b1;
            if (fi_has_dirty) begin
                fi_state_d = FI_WRITEBACK_REQ;
            end else begin
                fi_state_d = FI_NEXT_WAY;
            end
        end

        FI_WRITEBACK_REQ: begin
            fi_active = 1'b1;
            fi_writeback_req = 1'b1;
            if (lowX_res_i.ready) begin
                fi_state_d = FI_WRITEBACK_WAIT;
            end
        end

        FI_WRITEBACK_WAIT: begin
            fi_active = 1'b1;
            fi_writeback_req = 1'b1;
            if (lowX_res_i.valid) begin
                fi_state_d = FI_MARK_CLEAN;
            end
        end

        FI_MARK_CLEAN: begin
            fi_active = 1'b1;
            fi_mark_clean = 1'b1;
            fi_state_d = FI_NEXT_WAY;
        end

        FI_NEXT_WAY: begin
            fi_active = 1'b1;
            if (fi_way_idx_q == NUM_WAY - 1) begin
                if (fi_set_idx_q == NUM_SET - 1) begin
                    fi_state_d = FI_DONE;
                end else begin
                    fi_set_idx_d = fi_set_idx_q + 1'b1;
                    fi_way_idx_d = '0;
                    fi_state_d   = FI_SCAN;
                end
            end else begin
                fi_way_idx_d = fi_way_idx_q + 1'b1;
                fi_state_d   = FI_CHECK_WAY;
            end
        end

        FI_DONE: begin
            fi_active = 1'b0;  // Stall serbest bırak
            if (!flush_i) begin
                fi_state_d = FI_IDLE;
            end
        end
    endcase
end

assign fencei_stall_o = fi_active;
```

### FENCE.I Önemli Notlar

1. **Tag Invalidation Yok**: FENCE.I sadece dirty writeback yapar, cache line'ları invalidate etmez
2. **Stall Süresi**: Dirty line sayısına bağlı (worst case: NUM_SET × NUM_WAY × memory_latency)
3. **Pipeline Etkisi**: `fencei_stall_o` aktifken tüm pipeline durur

---

## Bellek Yapıları

### Tag Array

```systemverilog
typedef struct packed {
    logic [IDX_WIDTH-1:0]           idx;    // Index
    logic [NUM_WAY-1:0]             way;    // Way seçimi
    logic [TAG_SIZE:0]              wtag;   // Yazılacak tag + valid
    logic [NUM_WAY-1:0][TAG_SIZE:0] rtag;   // Okunan tag'ler
} tsram_t;
```

### Data Array

```systemverilog
typedef struct packed {
    logic [IDX_WIDTH-1:0]             idx;    // Index
    logic [NUM_WAY-1:0]               way;    // Way seçimi
    logic [BLK_SIZE-1:0]              wdata;  // Yazılacak veri
    logic [NUM_WAY-1:0][BLK_SIZE-1:0] rdata;  // Okunan veriler
} dsram_t;
```

### Node Array (PLRU)

```systemverilog
typedef struct packed {
    logic [IDX_WIDTH-1:0] idx;    // Index
    logic                 rw_en;  // R/W enable
    logic [NUM_WAY-2:0]   wnode;  // Yazılacak PLRU state
    logic [NUM_WAY-2:0]   rnode;  // Okunan PLRU state
} nsram_t;
```

### Dirty Array (D-Cache Only)

```systemverilog
typedef struct packed {
    logic [IDX_WIDTH-1:0] idx;      // Index
    logic [NUM_WAY-1:0]   way;      // Way seçimi
    logic                 rw_en;    // R/W enable
    logic                 wdirty;   // Yazılacak dirty bit
    logic [NUM_WAY-1:0]   rdirty;   // Okunan dirty bit'ler
} drsram_t;
```

---

## Zamanlama Diyagramları

### Cache Hit (1 Cycle)

```
clk     ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

req     ────/‾‾‾‾‾‾‾‾‾\──────────────────
valid

hit     ─────────────/‾‾‾‾‾‾‾‾‾\─────────

data    ─────────────┤ VALID  ├──────────
                      │ DATA   │

res     ─────────────/‾‾‾‾‾‾‾‾‾\─────────
valid
```

### Cache Miss + Refill (~10 Cycles)

```
clk     ____/‾\____/‾\____/‾\____ ... ____/‾\____/‾\____

req     ────/‾‾‾‾\───────────────────────────────────────
valid

miss    ─────────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──────────────

lowX    ─────────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──────────────
req            Memory fetch in progress...

lowX    ───────────────────────────────────/‾‾‾‾\────────
valid                                      │data│

res     ───────────────────────────────────/‾‾‾‾\────────
valid                                      │hit!│
```

### D-Cache Write-back Eviction

```
clk     ____/‾\____/‾\____/‾\____/‾\____ ... ____/‾\____

miss    ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──────

evict   ────/‾‾‾‾‾‾‾‾‾‾‾\────────────────────────────────
dirty        │writeback │

lowX    ────/‾‾‾‾‾‾‾‾‾‾‾\────────────────────────────────
wr_req       │evict data│

lowX    ─────────────────/‾‾‾‾\──────────────────────────
wr_ack               │done│

lowX    ─────────────────────/‾‾‾‾‾‾‾‾‾‾‾\───────────────
rd_req                   │fetch new│

lowX    ───────────────────────────────────/‾‾‾‾\────────
rd_ack                                 │data│
```

### FENCE.I Dirty Writeback

```
clk     ____/‾\____/‾\____/‾\____/‾\____ ... ____/‾\____

flush_i ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\──

stall   ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────────

state   IDLE│SCAN│CHK│WB_REQ│WB_WAIT│MARK│NEXT│...│DONE│

        ↑    ↑    ↑    ↑      ↑       ↑    ↑        ↑
        │    │    │    │      │       │    │        │
     start  bram  dirty? request wait  clear next  all
             lat   yes          mem    bit  set/   done
                                            way
```

---

## Performans Analizi

### Cache Hit Rate

| Workload | Tipik I-Cache Hit Rate | Tipik D-Cache Hit Rate |
|----------|------------------------|------------------------|
| Coremark | >95% | >90% |
| Dhrystone | >98% | >95% |
| General | >90% | >85% |

### Gecikme Analizi

| İşlem | Gecikme (cycle) | Açıklama |
|-------|-----------------|----------|
| Cache Hit | 1 | Tek cycle okuma |
| Cache Miss (clean) | ~10 | Memory latency |
| Cache Miss (dirty) | ~20 | Writeback + Refill |
| FENCE.I (best) | 2 | Dirty line yok |
| FENCE.I (worst) | NUM_SET × NUM_WAY × 10 | Tüm line'lar dirty |

### Alan Kullanımı (8KB, 8-way)

| Bileşen | Boyut | Hesaplama |
|---------|-------|-----------|
| Data Array | 8KB × 8 way = 64Kb | BLK_SIZE × NUM_SET × NUM_WAY |
| Tag Array | (22+1) × 64 × 8 = 11776 bit | (TAG_SIZE+1) × NUM_SET × NUM_WAY |
| Node Array | 7 × 64 = 448 bit | (NUM_WAY-1) × NUM_SET |
| Dirty Array | 8 × 64 = 512 bit | NUM_WAY × NUM_SET |
| **Toplam** | ~76KB | Data + Tag + Node + Dirty |

---

## Doğrulama ve Test

### Assertion'lar

```systemverilog
// Hit ve miss aynı anda olamaz
assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(cache_hit && cache_miss)
) else $error("Hit and miss cannot be active simultaneously");

// PLRU evict way one-hot olmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
    $onehot(evict_way)
) else $error("Evict way must be one-hot encoded");

// D-Cache: FENCE.I sırasında normal erişim kapalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
    fi_active |-> !cache_res_o.valid
) else $error("Cache should not respond during FENCE.I");

// Miss durumunda lowX request aktif olmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (cache_miss && !lookup_ack) |-> lowX_req_o.valid
) else $error("Memory request should be active on cache miss");
```

### Test Senaryoları

1. **Basic Hit/Miss**
   - Aynı adrese ardışık erişim (hit)
   - Farklı set'lere erişim (cold miss)
   - Aynı set'e 9 farklı adres (capacity miss)

2. **PLRU Eviction**
   - 8 way'i sırayla doldur
   - 9. erişimde PLRU eviction doğrula
   - Erişim paterni sonrası evict way kontrolü

3. **D-Cache Write-back**
   - Write miss → allocate → write
   - Eviction sırasında dirty writeback
   - Clean line eviction (no writeback)

4. **FENCE.I**
   - Dirty line yok → hızlı tamamlanma
   - Tek dirty line → writeback
   - Tüm line'lar dirty → full writeback

5. **Uncached Access**
   - Peripheral adresleri (uncached)
   - RAM adresleri (cached)

### Coverage Noktaları

```systemverilog
covergroup cache_cg @(posedge clk_i);
    // Hit/Miss coverage
    hit_miss: coverpoint {cache_hit, cache_miss} {
        bins hit  = {2'b10};
        bins miss = {2'b01};
        bins idle = {2'b00};
    }
    
    // Way selection coverage
    way_sel: coverpoint cache_wr_way {
        bins way[] = {[0:NUM_WAY-1]};
    }
    
    // D-Cache write size coverage
    write_size: coverpoint cache_req_i.rw_size iff (cache_req_i.rw) {
        bins byte_wr = {2'b01};
        bins half_wr = {2'b10};
        bins word_wr = {2'b11};
    }
    
    // FENCE.I state coverage
    fencei_state: coverpoint fi_state_q {
        bins all_states[] = {[FI_IDLE:FI_DONE]};
    }
endgroup
```

---

## Özet

`cache` modülü, CERES RISC-V işlemcisi için kritik bir performans bileşenidir:

1. **Parametrik Tasarım**: Kapasite, associativity ve blok boyutu ayarlanabilir
2. **Unified Modül**: Tek modül I-Cache ve D-Cache olarak kullanılabilir
3. **PLRU Eviction**: Düşük maliyetli, etkili eviction policy
4. **Write-back Policy**: D-Cache için minimum bellek trafiği
5. **FENCE.I Desteği**: Dirty writeback state machine
6. **Uncached Bypass**: Peripheral erişimleri için cache bypass

Bu tasarım, tipik embedded workload'lar için >90% hit rate sağlarken, FPGA kaynak kullanımını optimize eder.
