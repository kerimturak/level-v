# ALIGN BUFFER Modülü - Teknik Döküman

## Genel Bakış

`align_buffer.sv` modülü, instruction cache'ten gelen 128-bit cache line'ları 32-bit RISC-V instruction'lara hizalar. Misaligned instruction access'leri (cache line boundary'sini geçen instruction'lar) handle eder ve compressed instruction desteği sağlar. Modül, even/odd bank mimarisi kullanarak 16-bit parcel'lar üzerinden işlem yapar.

## Temel Sorumluluklar

1. **Instruction Alignment**: 128-bit cache line'dan 32-bit instruction extraction
2. **Misaligned Access Handling**: Cache line boundary'sini geçen instruction'ları işler
3. **Double Miss Management**: İki farklı cache line'a ihtiyaç duyulduğunda fetch orchestration
4. **Parcel-Based Architecture**: Even/odd bank sistemi ile 16-bit parcel organization
5. **Combinational Loop Prevention**: Verilator uyumluluğu için split_var directive'leri

## Mimari Parametreler

| Parametre | Default (ceres_param) | Açıklama |
|-----------|----------------------|----------|
| `CACHE_SIZE` | ABUFF_SIZE | Align buffer cache boyutu (bit) |
| `BLK_SIZE` | BLK_SIZE | Cache line boyutu (bit) - genelde 128 |
| `XLEN` | 32 | Register genişliği |
| `NUM_WAY` | ABUFF_WAY | Way sayısı (future expansion için) |

### Türetilmiş Parametreler

```systemverilog
localparam NUM_SET = (CACHE_SIZE / (BLK_SIZE * NUM_WAY));
localparam IDX_WIDTH = $clog2(NUM_SET);
localparam OFFSET_WIDTH = $clog2(BLK_SIZE / 8);
localparam TAG_SIZE = XLEN - IDX_WIDTH - OFFSET_WIDTH;
localparam NUM_WORDS = BLK_SIZE / 32;  // 128-bit line: 4 words
localparam NUM_PARCELS = NUM_WORDS * 2;  // Her word 2 parcel (16-bit)
```

**Örnek (128-bit cache line):**
- `BLK_SIZE = 128 bit`
- `NUM_WORDS = 4` (32-bit words)
- `NUM_PARCELS = 8` (16-bit parcels)
- `OFFSET_WIDTH = 4` (16 byte / 8 = 4 bit)

## Port Tanımları

### Giriş Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `flush_i` | logic | Pipeline flush sinyali |
| `buff_req_i` | abuff_req_t | Fetch'ten gelen buffer request |
| `lowX_res_i` | blowX_res_t | Lower-level cache/memory'den response |

**abuff_req_t yapısı:**
```systemverilog
typedef struct packed {
  logic         valid;     // Request geçerli mi?
  logic         ready;     // Buffer hazır mı?
  logic [XLEN-1:0] addr;   // Fetch adresi
  logic         uncached;  // Uncached access (MMIO)
} abuff_req_t;
```

### Çıkış Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `buff_res_o` | abuff_res_t | Fetch'e giden buffer response |
| `lowX_req_o` | blowX_req_t | Lower-level cache/memory'ye request |

**abuff_res_t yapısı:**
```systemverilog
typedef struct packed {
  logic         valid;          // Response geçerli mi?
  logic         ready;          // Buffer sonraki request'e hazır mı?
  logic         miss;           // Cache miss oluştu mu?
  logic         waiting_second; // Double miss - ikinci response bekleniyor
  logic [31:0]  blk;            // Hizalanmış 32-bit instruction
} abuff_res_t;
```

## Even/Odd Bank Mimarisi

### Memory Layout

128-bit cache line, 8 adet 16-bit parcel'a bölünür:

```
Cache Line (128-bit):
+--------+--------+--------+--------+--------+--------+--------+--------+
| Word 3 | Word 2 | Word 1 | Word 0 |
| O3 E3  | O2 E2  | O1 E1  | O0 E0  |
+--------+--------+--------+--------+--------+--------+--------+--------+
Address:  +E  +C    +A  +8    +6  +4    +2  +0

E (Even): Lower 16-bits of each word
O (Odd):  Upper 16-bits of each word
```

**Bank Organizasyonu:**
- **Even Bank (ebram)**: E0, E1, E2, E3 (her word'ün alt 16-bit'i)
- **Odd Bank (obram)**: O0, O1, O2, O3 (her word'ün üst 16-bit'i)

### Adres Mapping

```systemverilog
Adres:      [TAG | INDEX | OFFSET]
            [31:IDX_WIDTH+OFFSET_WIDTH] [IDX_WIDTH+OFFSET_WIDTH-1:OFFSET_WIDTH] [OFFSET_WIDTH-1:0]

Örnek (128-bit line, 64 set):
  TAG:      [31:10]  (22-bit)
  INDEX:    [9:4]    (6-bit, 64 set)
  OFFSET:   [3:0]    (4-bit, 16 byte)
  
OFFSET breakdown:
  [3:2] -> word_sel  (4 word içinden seçim)
  [1]   -> half_sel  (word içinde hangi half: 0=lower, 1=upper)
  [0]   -> byte_sel  (16-bit parcel içinde hangi byte - kullanılmıyor)
```

## İşlem Akışı

### 1. Address Parsing

```systemverilog
half_sel = buff_req_i.addr[1];        // Word içinde hangi half
word_sel = buff_req_i.addr[OFFSET_WIDTH-1:2];  // Cache line içinde hangi word
unalign  = &{word_sel, half_sel};     // Cache line boundary cross?

odd.rd_idx = buff_req_i.addr[IDX_WIDTH+OFFSET_WIDTH-1:OFFSET_WIDTH];
{overflow, even.rd_idx} = odd.rd_idx + {{(IDX_WIDTH-1){1'b0}}, unalign};
```

**Unalign Detection:**
- `unalign = 1` olduğunda instruction cache line boundary'sini geçer
- Örnek: addr[3:1] = `111` → word_sel=3, half_sel=1 → son parcel → unalign=1
- Overflow oluşursa even bank'ın index'i bir sonraki cache line'ı işaret eder

### 2. Tag Comparison & Hit/Miss Detection

```systemverilog
odd.wr_tag = {1'b1, buff_req_i.addr[XLEN-1:IDX_WIDTH+OFFSET_WIDTH]};
even.wr_tag = overflow ? {1'b1, tag_plus1} : odd.wr_tag;

even.rd_tag = tag_ram[even.rd_idx];
odd.rd_tag  = tag_ram[odd.rd_idx];

even.valid = even.rd_tag[TAG_SIZE];  // MSB: valid bit
odd.valid  = odd.rd_tag[TAG_SIZE];

even.match = (even.rd_tag[TAG_SIZE-1:0] == even.wr_tag[TAG_SIZE-1:0]);
odd.match  = (odd.rd_tag[TAG_SIZE-1:0] == odd.wr_tag[TAG_SIZE-1:0]);

even.miss = buff_req_i.valid && !(even.valid && even.match);
odd.miss  = buff_req_i.valid && !(odd.valid && odd.match);
```

**Miss State:**
```
miss_state = {odd.miss, even.miss}
2'b00 -> Both banks HIT
2'b01 -> Even miss, Odd hit
2'b10 -> Odd miss, Even hit
2'b11 -> Both banks MISS (double miss possible)
```

### 3. Parcel Selection

**Cache Hit Path:**
```systemverilog
// Even bank: lower 16-bits of word
case (parcel_idx[WORD_SEL_WIDTH-1:0])
  2'd0: even.parcel = even.rd_parcel[0];
  2'd1: even.parcel = even.rd_parcel[1];
  2'd2: even.parcel = even.rd_parcel[2];
  2'd3: even.parcel = even.rd_parcel[3];
endcase

// Odd bank: upper 16-bits of word
case (word_sel)
  2'd0: odd.parcel = odd.rd_parcel[0];
  2'd1: odd.parcel = odd.rd_parcel[1];
  2'd2: odd.parcel = odd.rd_parcel[2];
  2'd3: odd.parcel = odd.rd_parcel[3];
endcase
```

**Memory Response Path (Miss):**
```systemverilog
// Odd bank: upper 16-bit of selected word from memory
case (word_sel)
  2'd0: odd.deviceX_parcel = lowX_res_i.blk[31:16];
  2'd1: odd.deviceX_parcel = lowX_res_i.blk[63:48];
  2'd2: odd.deviceX_parcel = lowX_res_i.blk[95:80];
  2'd3: odd.deviceX_parcel = lowX_res_i.blk[127:112];
endcase

// Even bank: unalign durumunda ilk parcel, değilse odd ile aynı
even.deviceX_parcel = unalign ? lowX_res_i.blk[15:0] : odd.deviceX_parcel;
```

### 4. Instruction Assembly

**Case Analysis:**

#### Case 1: Word-Aligned (half_sel=0, addr[1]=0)
```
Instruction: [addr: lower16] [addr+2: upper16]
Output: {odd.parcel, even.parcel}

Örnek: addr=0x80000000
  even.parcel = E0 (cache[0x0:0x1])
  odd.parcel  = O0 (cache[0x2:0x3])
  inst = {O0, E0} = cache[0x0:0x3]
```

#### Case 2: Half-Word Offset (half_sel=1, addr[1]=1)
```
Instruction: [addr: lower16] [addr+2: upper16 from next word]
Output: {even.parcel, odd.parcel}

Örnek: addr=0x80000002
  odd.parcel  = O0 (cache[0x2:0x3])
  even.parcel = E1 (cache[0x4:0x5])
  inst = {E1, O0} = cache[0x2:0x5]
```

#### Case 3: Unaligned (cache line boundary cross, addr[3:1]=111)
```
Instruction spans two cache lines
Output: {even.parcel(next_line), odd.parcel(current_line)}

Örnek: addr=0x8000000E
  odd.parcel  = O3 (current line[0xE:0xF])
  even.parcel = E0 (next line[0x0:0x1])
  inst = {E0_next, O3_current}
```

### 5. Double Miss State Machine

**Problem:**
Unaligned access durumunda iki cache line'a ihtiyaç duyulur. Her iki line de miss ise iki memory response gerekir. İlk response'dan sonra valid sinyali tetiklenmemeli (instruction henüz tamamlanmadı).

**Çözüm:**
```systemverilog
// Ignore valid for one cycle after first response
always_ff @(posedge clk_i) begin
  if ((miss_state == 2'b11) && lowX_res_i.valid && unalign)
    ignore_valid_q <= 1'b1;
  else
    ignore_valid_q <= 1'b0;
end

// Track that we're waiting for second response
always_ff @(posedge clk_i) begin
  if ((miss_state == 2'b11) && masked_valid && unalign)
    waiting_second_q <= 1'b1;
  else if (waiting_second_q && masked_valid)
    waiting_second_q <= 1'b0;
end

masked_valid = lowX_res_i.valid && !ignore_valid_q;
```

**Timeline:**
```
Cycle N:   First request (odd bank line)
Cycle N+X: First response → ignore_valid_q=1, waiting_second_q=1
Cycle N+X+1: Second request (even bank line)
Cycle N+Y: Second response → instruction valid!
```

### 6. Output Valid Generation

```systemverilog
buff_res_o.valid = 
  &hit_state ||  // Both banks hit (same cycle)
  (|miss_state && !half_sel && masked_valid) ||  // Word-aligned single miss
  (!(&miss_state) && half_sel && masked_valid) ||  // Half-word partial hit
  (waiting_second_q && masked_valid);  // Double miss second response
```

**Valid Conditions:**
1. **Dual Hit**: Her iki bank da hit → instruction aynı cycle hazır
2. **Single Miss (word-aligned)**: Tek memory response yeterli
3. **Single Miss (half-word, partial hit)**: Bir bank hit, diğeri miss → tek response
4. **Double Miss**: İki response gerekli, ikinci response geldiğinde valid

## Request Generation Logic

```systemverilog
if (waiting_second_q && !masked_valid)
  lowX_req_o.valid = !buff_req_i.uncached;  // Second request
else if (&miss_state)
  lowX_req_o.valid = !masked_valid && !buff_req_i.uncached;  // First request
else if (|miss_state)
  lowX_req_o.valid = !masked_valid && !waiting_second_q && !buff_req_i.uncached;  // Single miss
else
  lowX_req_o.valid = 1'b0;  // Both hit
```

### Address Calculation

```systemverilog
base_addr = buff_req_i.addr & ~(BLOCK_BYTES - 1);  // Cache line aligned

if (waiting_second_q)
  lowX_req_o.addr = base_addr + BLOCK_BYTES;  // Even bank line
else
  case ({unalign, odd.miss, even.miss})
    3'b101:  lowX_req_o.addr = base_addr + BLOCK_BYTES;  // Even miss only
    3'b111:  lowX_req_o.addr = base_addr;  // Double miss: odd first
    default: lowX_req_o.addr = base_addr;  // Same line
  endcase
```

## Verilator Optimizations

### Split_Var Directive

```systemverilog
bank_t even /*verilator split_var*/, odd /*verilator split_var*/;
logic miss_state /*verilator split_var*/;
logic word_sel /*verilator split_var*/;
```

**Amaç:**
- Verilator'ın 2-state simulation'ında combinational loop detection'ı iyileştirme
- Even/odd struct'ları arasındaki circular dependency'yi kırmak
- `UNOPTFLAT` warning'lerini önlemek

**Detaylı Açıklama:**
- `docs/verilator/bugs/002_combinational_loop_instruction_corruption.md` dökümanına bakınız
- Circular logic olmadan Verilator signal evaluation order hatasına düşebilir
- Split_var, struct member'ları ayrı variable'lar gibi treat eder

## Timing Analysis

### Critical Paths

1. **Tag Comparison Path:**
   ```
   buff_req_i.addr → tag_ram read → tag compare → hit/miss detection → output mux
   ```
   - Combinational path, single cycle
   - Tag RAM read genelde asenkron (BRAM primitive kullanımında dikkat)

2. **Parcel Selection Path:**
   ```
   word_sel/half_sel → bank select → parcel mux → instruction assembly
   ```
   - Multiplexer cascade'i, timing critical olabilir
   - Case statement ile optimize edilmiş

3. **Double Miss FSM Path:**
   ```
   lowX_res_i.valid → ignore_valid_q → masked_valid → FSM transition
   ```
   - Sequential logic, register to register
   - Timing constraint: single cycle state transition

### Performance Metrics

| Durum | Latency | Throughput |
|-------|---------|------------|
| **Dual Hit** | 1 cycle | 1 inst/cycle |
| **Single Miss (aligned)** | N+1 cycles | 1 inst/N cycles |
| **Single Miss (half-word)** | N+1 cycles | 1 inst/N cycles |
| **Double Miss (unalign)** | 2N+2 cycles | 1 inst/2N cycles |

*N = Memory access latency (cache line fetch)*

## Exception Handling

Align buffer'ın kendi exception'ı yoktur, ancak fetch modülü tarafından üretilen exception'ları propagate eder:

- **Instruction Access Fault**: PMA modülünden gelen `grand=0` → fetch modülü handle eder
- **Instruction Misaligned**: PC alignment check → fetch modülü handle eder
- **Uncached Access**: `buff_req_i.uncached=1` durumunda cache bypass

## Debug Support

### Signal Monitoring

```systemverilog
// Simülasyonda monitor edilmesi gereken sinyaller:
- miss_state        // Cache miss durumu (2'b00/01/10/11)
- unalign           // Cache line boundary cross
- waiting_second_q  // Double miss FSM state
- masked_valid      // Effective valid signal
- buff_res_o.valid  // Final instruction valid
- buff_res_o.blk    // Assembled instruction
```

### Waveform Analysis

```
Signal Flow for Double Miss:
  1. buff_req_i.valid = 1, unalign = 1, miss_state = 2'b11
  2. lowX_req_o.valid = 1 (first request, odd bank line)
  3. lowX_res_i.valid = 1 (first response)
  4. ignore_valid_q = 1 (suppress first valid)
  5. waiting_second_q = 1 (FSM transition)
  6. lowX_req_o.valid = 1 (second request, even bank line)
  7. lowX_res_i.valid = 1 (second response)
  8. buff_res_o.valid = 1 (final instruction ready)
```

## Assertions (Önerilen)

```systemverilog
// Double miss durumunda ikinci request gönderilmeli
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (waiting_second_q && !masked_valid) |-> lowX_req_o.valid);

// Valid response'da instruction sıfır olmamalı (NOP hariç)
assert property (@(posedge clk_i) disable iff (!rst_ni)
  buff_res_o.valid |-> (buff_res_o.blk inside {32'h00000013, [32'h1:32'hFFFFFFFF]}));

// Unalign olmadan double miss olmamalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (miss_state == 2'b11) |-> unalign);

// Flush sırasında waiting_second temizlenmeli
assert property (@(posedge clk_i) disable iff (!rst_ni)
  flush_i |=> !waiting_second_q);
```

## Gelecek İyileştirmeler

1. **Way-Associative Support**: Şu an tek way, gelecekte set-associative expansion
2. **Prefetching**: Sequential access pattern'lerde proactive fetch
3. **Streaming Buffer**: Consecutive miss'lerde burst fetch
4. **Tag RAM Optimization**: BRAM primitive kullanımı ile timing iyileştirmesi
5. **Adaptive Banking**: Compressed instruction yoğunluğuna göre dinamik bank allocation

---

## 🚀 Prefetcher Implementasyon Planı

### Prefetcher Türleri ve Karşılaştırması

| # | Prefetcher Türü | Karmaşıklık | Alan | Beklenen Kazanım | Kullanım Alanı |
|---|----------------|-------------|------|------------------|----------------|
| 1 | **Next-Line** | ⭐ Düşük | ~50 FF | %5-10 hit artışı | Baseline, sıralı erişim |
| 2 | **Stride** | ⭐⭐ Orta | ~1-2KB | %10-20 hit artışı | Array/loop erişimleri |
| 3 | **Stream** | ⭐⭐ Orta | ~512B-1KB | %15-25 hit artışı | Sequential I-fetch |
| 4 | **Markov** | ⭐⭐⭐ Orta-Yüksek | ~4-8KB | %15-30 hit artışı | Irregular patterns |
| 5 | **Neural/Perceptron** | ⭐⭐⭐⭐ Yüksek | ~2-4KB | %20-35 hit artışı | Kompleks patterns |
| 6 | **Hibrit** | ⭐⭐⭐ Orta-Yüksek | ~2-4KB | %20-30 hit artışı | Tüm workload'lar |

### Aşamalı Implementasyon Planı

| Aşama | Prefetcher | Hedef | Tahmini Süre | Durum |
|-------|-----------|-------|--------------|-------|
| 1 | Next-Line (I-Cache) | Baseline kurulumu | 1-2 gün | ⏳ Planlandı |
| 2 | Stride (D-Cache) | Array/loop erişimleri | 3-5 gün | 📋 Beklemede |
| 3 | Stream (I-Cache) | Sequential fetch | 3-5 gün | 📋 Beklemede |
| 4 | Hibrit/Neural | Maksimum performans | 1-2 hafta | 📋 Beklemede |

---

### 1️⃣ Next-Line Prefetcher (Aşama 1 - Başlangıç)

**Çalışma Prensibi:**
- Cache miss olduğunda, bir sonraki cache line'ı da prefetch et
- Özellikle sıralı erişim pattern'leri için etkili
- Minimum alan ve karmaşıklık ile temel prefetching sağlar

```systemverilog
module next_line_prefetcher #(
    parameter XLEN     = 32,
    parameter BLK_SIZE = 128  // Cache line size in bits
)(
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             cache_miss_i,
    input  logic [XLEN-1:0]  miss_addr_i,
    input  logic             prefetch_ack_i,  // Prefetch kabul edildi
    output logic             prefetch_valid_o,
    output logic [XLEN-1:0]  prefetch_addr_o
);

    localparam LINE_BYTES = BLK_SIZE / 8;  // 16 bytes for 128-bit line
    localparam OFFSET_BITS = $clog2(LINE_BYTES);

    // Prefetch state
    logic prefetch_pending_q;
    logic [XLEN-1:0] prefetch_addr_q;

    // Next line address calculation (cache line aligned)
    logic [XLEN-1:0] next_line_addr;
    assign next_line_addr = {miss_addr_i[XLEN-1:OFFSET_BITS], {OFFSET_BITS{1'b0}}} + LINE_BYTES;

    // Prefetch output
    assign prefetch_valid_o = prefetch_pending_q;
    assign prefetch_addr_o = prefetch_addr_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            prefetch_pending_q <= 1'b0;
            prefetch_addr_q <= '0;
        end else begin
            if (cache_miss_i && !prefetch_pending_q) begin
                // Yeni miss - next line'ı prefetch et
                prefetch_pending_q <= 1'b1;
                prefetch_addr_q <= next_line_addr;
            end else if (prefetch_ack_i) begin
                // Prefetch kabul edildi
                prefetch_pending_q <= 1'b0;
            end
        end
    end

endmodule
```

**Entegrasyon Noktası:** `align_buffer.sv` veya `cache.sv` içinde miss sinyali ile tetiklenir.

---

### 2️⃣ Stride Prefetcher (Aşama 2)

**Çalışma Prensibi:**
- Her PC için erişim pattern'ini izler
- Stride (adres farkı) tekrar ederse, sonraki adresi prefetch eder
- Array traversal, matrix işlemleri için çok etkili

```systemverilog
module stride_prefetcher #(
    parameter XLEN        = 32,
    parameter TABLE_SIZE  = 64,
    parameter STRIDE_BITS = 12,
    parameter BLK_SIZE    = 128
)(
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             access_valid_i,
    input  logic [XLEN-1:0]  access_pc_i,
    input  logic [XLEN-1:0]  access_addr_i,
    input  logic             cache_hit_i,
    input  logic             prefetch_ack_i,
    output logic             prefetch_valid_o,
    output logic [XLEN-1:0]  prefetch_addr_o,
    output logic [1:0]       prefetch_confidence_o
);

    typedef struct packed {
        logic [XLEN-1:0]        last_addr;
        logic signed [STRIDE_BITS-1:0] stride;
        logic [1:0]             state;  // 0: initial, 1: transient, 2: steady, 3: no-pred
        logic                   valid;
    } stride_entry_t;

    stride_entry_t table [TABLE_SIZE];

    // PC-indexed lookup
    logic [$clog2(TABLE_SIZE)-1:0] idx;
    assign idx = access_pc_i[$clog2(TABLE_SIZE)+1:2];

    // Current stride calculation
    logic signed [STRIDE_BITS-1:0] current_stride;
    assign current_stride = access_addr_i - table[idx].last_addr;

    // Prefetch decision: steady state (confidence >= 2)
    assign prefetch_valid_o = access_valid_i && 
                              table[idx].valid && 
                              (table[idx].state >= 2'd2);
    assign prefetch_addr_o = access_addr_i + 
                             {{(XLEN-STRIDE_BITS){table[idx].stride[STRIDE_BITS-1]}}, 
                              table[idx].stride};
    assign prefetch_confidence_o = table[idx].state;

    // State machine update
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            for (int i = 0; i < TABLE_SIZE; i++) begin
                table[i] <= '0;
            end
        end else if (access_valid_i) begin
            if (!table[idx].valid) begin
                // İlk erişim - entry oluştur
                table[idx].last_addr <= access_addr_i;
                table[idx].stride <= '0;
                table[idx].state <= 2'd0;
                table[idx].valid <= 1'b1;
            end else begin
                // Mevcut entry güncelle
                table[idx].last_addr <= access_addr_i;
                
                if (current_stride == table[idx].stride) begin
                    // Stride match - confidence artır
                    if (table[idx].state < 2'd3)
                        table[idx].state <= table[idx].state + 1;
                end else begin
                    // Stride mismatch - yeni stride kaydet, confidence sıfırla
                    table[idx].stride <= current_stride;
                    table[idx].state <= 2'd1;
                end
            end
        end
    end

endmodule
```

---

### 3️⃣ Stream Prefetcher (Aşama 3 - I-Cache için İdeal)

**Çalışma Prensibi:**
- Belirli sayıda ardışık miss tespit edilince "stream" başlar
- Stream yönünde birden fazla cache line prefetch edilir
- Özellikle sequential instruction fetch için mükemmel

```systemverilog
module stream_prefetcher #(
    parameter XLEN           = 32,
    parameter NUM_STREAMS    = 4,
    parameter PREFETCH_DEGREE = 4,  // Kaç line önceden prefetch
    parameter BLK_SIZE       = 128
)(
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             cache_miss_i,
    input  logic [XLEN-1:0]  miss_addr_i,
    input  logic             prefetch_ack_i,
    output logic             prefetch_valid_o,
    output logic [XLEN-1:0]  prefetch_addr_o
);

    localparam LINE_BYTES = BLK_SIZE / 8;
    localparam OFFSET_BITS = $clog2(LINE_BYTES);

    typedef struct packed {
        logic [XLEN-1:0] start_addr;
        logic [XLEN-1:0] current_addr;
        logic            direction;  // 0: ascending, 1: descending
        logic [2:0]      confidence;
        logic [2:0]      prefetch_count;
        logic            valid;
    } stream_t;

    stream_t streams [NUM_STREAMS];
    logic [$clog2(NUM_STREAMS)-1:0] alloc_ptr;
    logic [$clog2(NUM_STREAMS)-1:0] active_stream;
    logic stream_found;

    // Stream matching logic
    always_comb begin
        stream_found = 1'b0;
        active_stream = '0;
        
        for (int i = 0; i < NUM_STREAMS; i++) begin
            if (streams[i].valid) begin
                // Check if miss is in this stream's range
                logic [XLEN-1:0] expected_addr;
                expected_addr = streams[i].direction ? 
                               streams[i].current_addr - LINE_BYTES :
                               streams[i].current_addr + LINE_BYTES;
                
                if (miss_addr_i[XLEN-1:OFFSET_BITS] == expected_addr[XLEN-1:OFFSET_BITS]) begin
                    stream_found = 1'b1;
                    active_stream = i[$clog2(NUM_STREAMS)-1:0];
                end
            end
        end
    end

    // Prefetch output from active stream
    assign prefetch_valid_o = stream_found && 
                              (streams[active_stream].confidence >= 3'd2) &&
                              (streams[active_stream].prefetch_count < PREFETCH_DEGREE);
    assign prefetch_addr_o = streams[active_stream].direction ?
                             streams[active_stream].current_addr - (LINE_BYTES * (streams[active_stream].prefetch_count + 1)) :
                             streams[active_stream].current_addr + (LINE_BYTES * (streams[active_stream].prefetch_count + 1));

    // Stream management state machine
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            for (int i = 0; i < NUM_STREAMS; i++) begin
                streams[i] <= '0;
            end
            alloc_ptr <= '0;
        end else if (cache_miss_i) begin
            if (stream_found) begin
                // Mevcut stream güncelle
                streams[active_stream].current_addr <= miss_addr_i;
                if (streams[active_stream].confidence < 3'd7)
                    streams[active_stream].confidence <= streams[active_stream].confidence + 1;
            end else begin
                // Yeni stream alloc
                streams[alloc_ptr].start_addr <= miss_addr_i;
                streams[alloc_ptr].current_addr <= miss_addr_i;
                streams[alloc_ptr].direction <= 1'b0;  // Default ascending
                streams[alloc_ptr].confidence <= 3'd1;
                streams[alloc_ptr].prefetch_count <= '0;
                streams[alloc_ptr].valid <= 1'b1;
                alloc_ptr <= alloc_ptr + 1;
            end
        end
        
        if (prefetch_ack_i && stream_found) begin
            streams[active_stream].prefetch_count <= streams[active_stream].prefetch_count + 1;
        end
    end

endmodule
```

---

### 📐 Parametrik Prefetcher Wrapper (Seçim için)

Tüm prefetcher'ları parametrik olarak seçmek için wrapper modül:

```systemverilog
module prefetcher_wrapper #(
    parameter XLEN           = 32,
    parameter BLK_SIZE       = 128,
    parameter PREFETCH_TYPE  = 0,  // 0: None, 1: NextLine, 2: Stride, 3: Stream, 4: Hybrid
    // Stride parameters
    parameter STRIDE_TABLE   = 64,
    parameter STRIDE_BITS    = 12,
    // Stream parameters
    parameter NUM_STREAMS    = 4,
    parameter PREFETCH_DEGREE = 4
)(
    input  logic             clk_i,
    input  logic             rst_ni,
    // Cache interface
    input  logic             cache_miss_i,
    input  logic             cache_hit_i,
    input  logic [XLEN-1:0]  access_addr_i,
    input  logic [XLEN-1:0]  access_pc_i,
    input  logic             access_valid_i,
    // Prefetch interface
    input  logic             prefetch_ack_i,
    output logic             prefetch_valid_o,
    output logic [XLEN-1:0]  prefetch_addr_o
);

    generate
        if (PREFETCH_TYPE == 0) begin : gen_no_prefetch
            // No prefetching
            assign prefetch_valid_o = 1'b0;
            assign prefetch_addr_o = '0;
            
        end else if (PREFETCH_TYPE == 1) begin : gen_next_line
            // Next-Line Prefetcher
            next_line_prefetcher #(
                .XLEN(XLEN),
                .BLK_SIZE(BLK_SIZE)
            ) u_next_line (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .cache_miss_i(cache_miss_i),
                .miss_addr_i(access_addr_i),
                .prefetch_ack_i(prefetch_ack_i),
                .prefetch_valid_o(prefetch_valid_o),
                .prefetch_addr_o(prefetch_addr_o)
            );
            
        end else if (PREFETCH_TYPE == 2) begin : gen_stride
            // Stride Prefetcher
            stride_prefetcher #(
                .XLEN(XLEN),
                .TABLE_SIZE(STRIDE_TABLE),
                .STRIDE_BITS(STRIDE_BITS),
                .BLK_SIZE(BLK_SIZE)
            ) u_stride (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .access_valid_i(access_valid_i),
                .access_pc_i(access_pc_i),
                .access_addr_i(access_addr_i),
                .cache_hit_i(cache_hit_i),
                .prefetch_ack_i(prefetch_ack_i),
                .prefetch_valid_o(prefetch_valid_o),
                .prefetch_addr_o(prefetch_addr_o),
                .prefetch_confidence_o()  // Optional
            );
            
        end else if (PREFETCH_TYPE == 3) begin : gen_stream
            // Stream Prefetcher
            stream_prefetcher #(
                .XLEN(XLEN),
                .NUM_STREAMS(NUM_STREAMS),
                .PREFETCH_DEGREE(PREFETCH_DEGREE),
                .BLK_SIZE(BLK_SIZE)
            ) u_stream (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .cache_miss_i(cache_miss_i),
                .miss_addr_i(access_addr_i),
                .prefetch_ack_i(prefetch_ack_i),
                .prefetch_valid_o(prefetch_valid_o),
                .prefetch_addr_o(prefetch_addr_o)
            );
            
        end else if (PREFETCH_TYPE == 4) begin : gen_hybrid
            // Hybrid: Stride + Stream with arbiter
            logic stride_valid, stream_valid;
            logic [XLEN-1:0] stride_addr, stream_addr;
            
            stride_prefetcher #(.XLEN(XLEN), .TABLE_SIZE(STRIDE_TABLE)) u_stride (
                .clk_i(clk_i), .rst_ni(rst_ni),
                .access_valid_i(access_valid_i),
                .access_pc_i(access_pc_i),
                .access_addr_i(access_addr_i),
                .cache_hit_i(cache_hit_i),
                .prefetch_ack_i(prefetch_ack_i && stride_valid),
                .prefetch_valid_o(stride_valid),
                .prefetch_addr_o(stride_addr),
                .prefetch_confidence_o()
            );
            
            stream_prefetcher #(.XLEN(XLEN), .NUM_STREAMS(NUM_STREAMS)) u_stream (
                .clk_i(clk_i), .rst_ni(rst_ni),
                .cache_miss_i(cache_miss_i),
                .miss_addr_i(access_addr_i),
                .prefetch_ack_i(prefetch_ack_i && stream_valid && !stride_valid),
                .prefetch_valid_o(stream_valid),
                .prefetch_addr_o(stream_addr)
            );
            
            // Stride has priority
            assign prefetch_valid_o = stride_valid | stream_valid;
            assign prefetch_addr_o = stride_valid ? stride_addr : stream_addr;
        end
    endgenerate

endmodule
```

---

### 🔧 Entegrasyon Mimarisi

```
┌─────────────────────────────────────────────────────────────────┐
│                         CPU Core                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────┐     ┌──────────────────┐    ┌─────────────────┐   │
│  │  Fetch   │────►│   Align Buffer   │───►│  Prefetcher     │   │
│  │  Stage   │     │   (align_buffer) │    │  (PREFETCH_TYPE)│   │
│  └──────────┘     └────────┬─────────┘    └────────┬────────┘   │
│                            │                       │             │
│                            ▼                       ▼             │
│                   ┌──────────────────────────────────────┐      │
│                   │           I-Cache                     │      │
│                   │   cache_req: demand + prefetch        │      │
│                   └──────────────────────────────────────┘      │
│                            │                                     │
│                            ▼                                     │
│                   ┌──────────────────────────────────────┐      │
│                   │        Memory Arbiter                 │      │
│                   │   Priority: Demand > Prefetch         │      │
│                   └──────────────────────────────────────┘      │
│                                                                  │
│  ┌──────────┐     ┌──────────────────┐    ┌─────────────────┐   │
│  │ Memory   │────►│     D-Cache      │───►│  Stride         │   │
│  │  Stage   │     │                  │    │  Prefetcher     │   │
│  └──────────┘     └──────────────────┘    └─────────────────┘   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### ceres_param.sv'ye Eklenecek Parametreler

```systemverilog
// ============================================================================
// PREFETCHER PARAMETERS
// ============================================================================
localparam int PREFETCH_TYPE = 1;        // 0:None, 1:NextLine, 2:Stride, 3:Stream, 4:Hybrid
localparam int STRIDE_TABLE_SIZE = 64;   // Stride prefetcher table entries
localparam int STRIDE_BITS = 12;         // Stride bit width
localparam int NUM_STREAMS = 4;          // Stream prefetcher stream count
localparam int PREFETCH_DEGREE = 4;      // How many lines ahead to prefetch
```

## İlgili Modüller

1. **fetch.sv**: Ana fetch modülü (align buffer'ı kullanır)
2. **cache.sv**: Instruction cache (align buffer'a response verir)
3. **compressed_decoder.sv**: 16-bit compressed instruction decode (fetch sonrası)

## Referanslar

1. RISC-V Unprivileged ISA Specification - Instruction Fetch
2. "Cache and Memory Hierarchy Design: A Performance-Directed Approach" - Steven A. Przybylski
3. "Computer Architecture: A Quantitative Approach" - Hennessy & Patterson, Chapter 2 (Memory Hierarchy)
4. Verilator Manual - Split_Var Directive

---

**Son Güncelleme:** 4 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
