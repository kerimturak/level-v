# FETCH Modülü - Teknik Döküman

## Genel Bakış

`fetch.sv` modülü, RISC-V işlemci çekirdeğinin ilk aşamasıdır (Stage 01). Program Counter (PC) yönetiminden, instruction cache'e erişimden, dallanma tahminlerinden ve exception tespitinden sorumludur. Bu modül, pipelined bir mimaride instruction akışını başlatır ve downstream aşamalarına (decode, execute, vb.) instruction sağlar.

## Temel Sorumluluklar

1. **Program Counter (PC) Yönetimi**: Sequential, branch, jump ve exception durumlarında PC'nin doğru güncellenmesi
2. **Instruction Fetch**: Instruction cache üzerinden instruction'ların alınması
3. **Branch Prediction**: GSHARE algoritması ile dallanma tahmini
4. **Misaligned Instruction Handling**: Align buffer ile hizasız instruction'ların işlenmesi
5. **Exception Detection**: Parametrik önceliğe sahip exception tespiti
6. **Compressed Instruction Support**: RV32C (16-bit) instruction'ların decode edilmesi

## Port Tanımları

### Giriş Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `stall_i` | stall_e | Pipeline stall sinyali (NO_STALL/STALL enum) |
| `flush_i` | logic | Pipeline flush sinyali (misprediction/exception durumunda) |
| `flush_pc_i` | [XLEN-1:0] | Flush durumunda yeni PC değeri |
| `lx_ires_i` | ilowX_res_t | Lower-level memory hierarchy'den instruction response |
| `pc_target_i` | [XLEN-1:0] | Execute aşamasından gelen gerçek branch/jump hedefi |
| `ex_mtvec_i` | [XLEN-1:0] | Machine trap vector (exception handler adresi) |
| `trap_active_i` | logic | Trap handler aktif mi? |
| `misa_c_i` | logic | C extension (compressed instructions) etkin mi? |
| `tdata1_i` | [XLEN-1:0] | Trigger data 1 (debug breakpoint config) |
| `tdata2_i` | [XLEN-1:0] | Trigger data 2 (breakpoint address) |
| `tcontrol_i` | [XLEN-1:0] | Trigger control (mte bit[3] trigger'ları aktive eder) |
| `spec_hit_i` | logic | Branch prediction doğru mu? (1=doğru, 0=misprediction) |
| `de_info_i` | pipe_info_t | Decode aşamasından pipeline info |
| `ex_info_i` | pipe_info_t | Execute aşamasından pipeline info |

### Çıkış Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `spec_o` | predict_info_t | Prediction bilgisi (tahmin edilen PC, taken/not-taken) |
| `lx_ireq_o` | ilowX_req_t | Lower-level memory hierarchy'ye instruction request |
| `pc_o` | [XLEN-1:0] | Mevcut program counter |
| `pc_incr_o` | [XLEN-1:0] | Sequential PC (pc+2 veya pc+4) |
| `inst_o` | [XLEN-1:0] | Fetch edilen instruction (decode'a gönderilir) |
| `imiss_stall_o` | logic | Instruction cache miss stall sinyali |
| `exc_type_o` | exc_type_e | Tespit edilen exception tipi |
| `instr_type_o` | instr_type_e | Instruction tipi (decode yardımcı) |

## Mimari Bloklar

### 1. Program Counter (PC) Register

```systemverilog
always_ff @(posedge clk_i) begin
  if (!rst_ni) begin
    pc <= RESET_VECTOR;
  end else if (pc_en) begin
    pc <= pc_next;
  end
end
```

**Özellikler:**
- Reset durumunda `RESET_VECTOR` adresine atanır (parametrik, genelde `0x80000000`)
- `pc_en` aktif olduğunda `pc_next` değeri yazılır
- Stall durumunda PC güncellenmez (statik kalır)

### 2. PC Next Logic (Öncelik Sırası)

PC'nin bir sonraki değerinin belirlenmesinde aşağıdaki öncelik sırası uygulanır:

```
1. flush_i         → flush_pc_i        (En yüksek öncelik - pipeline flush)
2. trap_active_i   → ex_mtvec_i        (Exception handler)
3. !spec_hit_i     → pc_target_i       (Misprediction recovery)
4. spec_o.taken    → spec_o.pc         (Branch prediction taken)
5. Default         → pc_incr_o         (Sequential fetch - PC+2/+4)
```

**Detaylı Açıklama:**
- **Flush**: Decode/Execute aşamalarından gelen flush sinyali (örn. fence.i)
- **Trap**: Exception/interrupt oluştuğunda trap handler'a (mtvec) atlanır
- **Misprediction**: Execute aşamasında branch prediction yanlışsa düzeltme yapılır
- **Branch Taken**: Prediction taken ise tahmin edilen adrese atla
- **Sequential**: Normal durum, bir sonraki instruction'ı fetch et

### 3. PC Increment Calculation

```systemverilog
pc_incr_o = (buff_res.valid && is_comp) ? (pc_o + 32'd2) : (pc_o + 32'd4);
```

- **Compressed Instruction** (16-bit, C extension): PC + 2
- **Normal Instruction** (32-bit): PC + 4
- Compressed instruction tespiti `compressed_decoder` modülünden gelir

### 4. Fetch Valid Logic

Instruction fetch'in geçerliliği aşağıdaki durumlarda belirlenir:

```systemverilog
if (flush_i) 
  fetch_valid = 1'b0;  // Flush sırasında fetch geçersiz
else if (spec_hit_i)
  fetch_valid = !trap_active_i;  // Speculation doğruysa trap kontrolü
else
  fetch_valid = !trap_active_i;  // Speculation yanlışsa execute exception kontrolü
```

**Mantık:**
- **Flush sırasında**: Hiçbir instruction geçerli değil
- **Speculation hit**: Normal exception kontrolü
- **Speculation miss**: Execute aşamasındaki exception'lar dışında fetch geçerli (çünkü pipeline zaten flush edilecek)

### 5. Exception Detection & Parametric Priority

RISC-V Privileged Specification Section 3.1.15'e uygun parametrik öncelik sistemi:

```systemverilog
// Exception detection flags
has_debug_breakpoint   = fetch_valid && tcontrol_i[3] && tdata1_i[2] && (pc_o == tdata2_i);
has_instr_misaligned   = fetch_valid && (misa_c_i ? pc_o[0] : (pc_o[1:0] != 2'b00));
has_instr_access_fault = fetch_valid && !grand;
has_illegal_instr      = fetch_valid && illegal_instr && buff_res.valid;
has_ebreak             = fetch_valid && (instr_type_o == ebreak);
has_ecall              = fetch_valid && (instr_type_o == ecall);
```

**Öncelik Sırası** (ceres_param.sv'den yapılandırılabilir):
1. **BREAKPOINT** (Hardware debug breakpoint): `EXC_PRIORITY_DEBUG_BREAKPOINT`
2. **INSTR_MISALIGNED** (Hizasız PC): `EXC_PRIORITY_INSTR_MISALIGNED`
3. **INSTR_ACCESS_FAULT** (PMA ihlali): `EXC_PRIORITY_INSTR_ACCESS_FAULT`
4. **ILLEGAL_INSTRUCTION**: `EXC_PRIORITY_ILLEGAL`
5. **EBREAK** (Breakpoint instruction): `EXC_PRIORITY_EBREAK`
6. **ECALL** (Environment call): `EXC_PRIORITY_ECALL`

**Parametrik Kontrol:**
- Her exception tipi için `ceres_param.sv` içinde öncelik seviyesi tanımlanır
- `check_exc_priority()` fonksiyonu ile etkinlik kontrolü yapılır
- Bu sayede RISC-V specification'ın farklı versiyonlarına uyum sağlanabilir

### 6. Instruction Cache Miss Handling

```systemverilog
imiss_stall_o = (buff_req.valid && !buff_res.valid);
```

**Stall Durumu:**
- Align buffer'a geçerli bir istek yapılmış ancak henüz cevap gelmemiş
- Bu durumda pipeline stall edilir (hazard_unit tarafından)
- Ready-valid handshake tam kurulmamış (align_buffer request'i registerlemiyor)

**TODO Notu:** Kodda belirtildiği üzere, gelecekte tam handshake protokolü uygulanabilir

### 7. Buffer to Cache Request Gating

Align buffer'dan gelen sürekli valid sinyali, icache'e tek cycle'lık handshake'e dönüştürülür:

```systemverilog
icache_req.valid = abuff_icache_req.valid && !buf_lookup_ack;

always_ff @(posedge clk_i) begin
  if (buff_lowX_res.valid) 
    buf_lookup_ack <= 1'b0;  // Response geldi, yeni request'e izin ver
  else if (buff_res.waiting_second && buf_lookup_ack)
    buf_lookup_ack <= 1'b0;  // Double miss: ikinci request için clear et
  else if (icache_req.valid && buff_lowX_res.ready && !buf_lookup_ack)
    buf_lookup_ack <= 1'b1;  // Request kabul edildi, ack set et
end
```

**Amaç:**
- Align buffer cache miss sırasında valid=1 tutar
- Bu sürekli valid, icache'e her cycle yeni request göndermemeli
- `buf_lookup_ack` flag'i ile request zaten gönderilmişse suppress edilir
- Response geldiğinde veya double miss durumunda flag temizlenir

## Alt Modüller

### 1. PMA (Physical Memory Attributes)

```systemverilog
pma i_pma (
  .addr_i      (pc_o),
  .uncached_o  (uncached),
  .memregion_o (memregion),
  .grand_o     (grand)
);
```

**İşlev:**
- PC adresinin bellek özelliklerini belirler
- **uncached**: Instruction cache'lenmeyecek mi? (MMIO bölgesi)
- **grand**: Erişim izni var mı? (yoksa INSTR_ACCESS_FAULT)
- **memregion**: Bellek bölgesi tipi (henüz kullanılmıyor)

### 2. GSHARE Branch Predictor

```systemverilog
gshare_bp i_gshare_bp (
  .clk_i         (clk_i),
  .rst_ni        (rst_ni),
  .spec_hit_i    (spec_hit_i),
  .pc_target_i   (pc_target_i),
  .inst_i        (inst_o),
  .stall_i       (!pc_en),
  .pc_i          (pc_o),
  .pc_incr_i     (pc_incr_o),
  .fetch_valid_i (buff_res.valid),
  .spec_o        (spec_o),
  .de_info_i     (de_info_i),
  .ex_info_i     (ex_info_i)
);
```

**İşlev:**
- Dallanma tahmini (branch prediction) yapar
- GSHARE algoritması: Global History Register (GHR) ⊕ PC → Pattern History Table (PHT)
- RAS (Return Address Stack) ile return instruction'ları tahmin eder
- BTB (Branch Target Buffer) ile branch hedef adreslerini cache'ler
- Detaylı açıklama için `gshare_bp_module.md` dökümanına bakınız

### 3. Align Buffer

```systemverilog
align_buffer i_align_buffer (
  .clk_i      (clk_i),
  .rst_ni     (rst_ni),
  .flush_i    (flush_i),
  .buff_req_i (buff_req),
  .buff_res_o (buff_res),
  .lowX_res_i (buff_lowX_res),
  .lowX_req_o (abuff_icache_req)
);
```

**İşlev:**
- Instruction cache'ten gelen 128-bit cache line'ları 32-bit instruction'lara hizalar
- Misaligned access desteği (instruction cache line boundary'sini geçen instruction'lar)
- Double miss handling (iki farklı cache line'dan fetch gerektiğinde)
- Even/Odd bank mimarisi ile 16-bit parcel'lar şeklinde organize edilir
- Detaylı açıklama için `align_buffer_module.md` dökümanına bakınız

### 4. Instruction Cache

```systemverilog
cache #(
  .IS_ICACHE   (1),
  .cache_req_t (icache_req_t),
  .cache_res_t (icache_res_t),
  .lowX_req_t  (ilowX_req_t),
  .lowX_res_t  (ilowX_res_t),
  .CACHE_SIZE  (IC_CAPACITY),
  .BLK_SIZE    (BLK_SIZE),
  .XLEN        (XLEN),
  .NUM_WAY     (IC_WAY)
) i_icache (
  .clk_i          (clk_i),
  .rst_ni         (rst_ni),
  .flush_i        (flush_i),
  .cache_req_i    (icache_req),
  .cache_res_o    (icache_res),
  .lowX_res_i     (lx_ires_i),
  .lowX_req_o     (lx_ireq_o),
  .fencei_stall_o (icache_fencei_stall)
);
```

**İşlev:**
- Instruction'ları cache'ler (set-associative veya direct-mapped)
- Cache miss durumunda lower-level memory'den (L2/Memory) fetch yapar
- Parametrik: boyut, way sayısı, block size
- `fencei_stall_o` instruction cache için her zaman 0 (data cache'te kullanılır)

### 5. Compressed Decoder

```systemverilog
compressed_decoder i_compressed_decoder (
  .instr_i         (buff_res.blk),
  .instr_o         (inst_o),
  .is_compressed_o (is_comp),
  .illegal_instr_o (illegal_instr)
);
```

**İşlev:**
- 16-bit compressed instruction'ları (RV32C) 32-bit normal instruction'lara decode eder
- C0, C1, C2 quadrant'larını işler
- Illegal compressed instruction tespiti yapar
- RISC-V C extension specification'a tam uyumlu
- Detaylı açıklama için `compressed_decoder_module.md` dökümanına bakınız

## Timing Diagram

```
Cycle 0: Reset
         PC = RESET_VECTOR (0x80000000)

Cycle 1: Sequential Fetch
         PC = 0x80000000
         Request to Align Buffer & ICache
         
Cycle 2: Align Buffer Response
         inst_o = 0x00000013 (NOP)
         is_comp = 0 (32-bit instruction)
         pc_incr_o = PC + 4 = 0x80000004
         
Cycle 3: Sequential Fetch
         PC = 0x80000004
         
Cycle 4: Branch Instruction Fetch
         inst_o = 0x00C0006F (JAL)
         spec_o.taken = 1
         spec_o.pc = PC + 0xC = 0x80000010
         
Cycle 5: Branch Target Fetch
         PC = 0x80000010 (predicted)
         
Cycle N: Branch Resolution (in Execute stage)
         spec_hit_i = 1 (correct prediction)
         
Cycle M: Misprediction Case
         spec_hit_i = 0
         pc_next = pc_target_i (actual target from EX)
         flush_i = 1 (flush decode/fetch stages)
```

## Performance Considerations

### 1. Cache Miss Handling
- **Single-cycle hit**: Align buffer + ICache hit → inst_o geçerli aynı cycle
- **Multi-cycle miss**: ICache'ten lower-level memory'ye istek, cevap gelene kadar stall
- **Double miss** (misaligned, boundary cross): İki cache line fetch gerekir, alignment buffer bunu handle eder

### 2. Branch Prediction Impact
- **Correct prediction**: Pipeline akışı kesintisiz
- **Misprediction**: 3-4 cycle penalty (flush + re-fetch)
- GSHARE prediction accuracy: ~85-95% (kod tipine göre)

### 3. Compressed Instruction Benefit
- **Code density**: %25-30 daha küçük binary boyutu
- **Performance**: PC increment bazen +2 (compressed), bazen +4
- **Decode latency**: Aynı cycle (combinational decoder)

## Exception Handling Flow

```
1. Exception Detection (Fetch Stage)
   ↓
2. exc_type_o signal → Pipeline
   ↓
3. Propagate to Execute (Writeback'e kadar)
   ↓
4. Writeback: trap_active_i = 1
   ↓
5. Fetch: pc_next = ex_mtvec_i (trap handler)
   ↓
6. Trap Handler Execution
```

**Önemli Noktalar:**
- Exception'lar fetch'te tespit edilir ama commit edilmez (writeback'te commit)
- Speculation miss durumunda fetch exception'ları flush edilir
- Trap handler PC'si `mtvec` CSR'den gelir (vectored veya direct mode)

## Debug & Verification

### Commit Tracer Support

```systemverilog
`ifdef COMMIT_TRACER
  always_comb begin
    fe_tracer_o.inst = '0;
    if ((stall_i == NO_STALL) && buff_res.valid) begin
      if (is_comp)
        fe_tracer_o.inst = {16'b0, buff_res.blk[15:0]};
      else
        fe_tracer_o.inst = buff_res.blk;
    end
  end
`endif
```

**Amaç:**
- Simülasyonda/doğrulamada her instruction'ı trace etmek
- Compressed/normal instruction ayrımı
- Valid cycle'larda aktif

### Assertions (Önerilen)

```systemverilog
// PC alignment kontrolü (C extension varsa 2-byte, yoksa 4-byte)
assert property (@(posedge clk_i) disable iff (!rst_ni)
  misa_c_i |-> pc_o[0] == 1'b0 else pc_o[1:0] == 2'b00);

// Flush sırasında fetch valid olmamalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
  flush_i |-> !fetch_valid);

// Misprediction sırasında PC düzeltmesi yapılmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
  !spec_hit_i && (ex_info_i.bjtype != NO_BJ) |=> pc_o == $past(pc_target_i));
```

## Parametre Yapılandırması

### RESET_VECTOR
```systemverilog
parameter RESET_VECTOR = ceres_param::RESET_VECTOR
```
- Default: `0x80000000`
- RISC-V convention: machine mode reset vector
- SoC'ye göre değiştirilebilir

### Cache Parameters (indirect - ceres_param.sv)
- `IC_CAPACITY`: Instruction cache boyutu (örn. 16 KB)
- `IC_WAY`: Way sayısı (1=direct-mapped, 2/4/8=set-associative)
- `BLK_SIZE`: Cache line boyutu (genelde 128 bit = 16 byte)

### Predictor Parameters (indirect - ceres_param.sv)
- `GHR_SIZE`: Global History Register boyutu (örn. 8-bit)
- `PHT_SIZE`: Pattern History Table entry sayısı (örn. 256)
- `BTB_SIZE`: Branch Target Buffer entry sayısı (örn. 128)
- `RAS_SIZE`: Return Address Stack derinliği (örn. 8)

## İlgili Modüller

1. **align_buffer.sv**: Instruction hizalama ve misaligned access handling
2. **gshare_bp.sv**: Dallanma tahmini ve BTB yönetimi
3. **compressed_decoder.sv**: RV32C instruction decode
4. **ras.sv**: Return address stack (function call/return prediction)
5. **cache.sv**: Generic cache implementation (instruction/data cache için ortak)
6. **pma.sv**: Physical memory attributes checker

## Gelecek İyileştirmeler (TODO)

1. **Full Handshake Protocol**: Align buffer request'i registerlayarak ready-valid handshake'i tam kurulabilir
2. **Prefetcher**: Sequential access pattern'leri tespit edip proactive fetch
3. **Multiple Outstanding Requests**: Cache miss sırasında diğer instruction'ları fetch etmeye devam et
4. **Fusion Support**: Sık kullanılan instruction pair'lerini tek micro-op olarak işle
5. **Advanced Prediction**: Perceptron-based veya TAGE predictor entegrasyonu

## Referanslar

1. RISC-V Unprivileged ISA Specification v20191213
2. RISC-V Privileged Specification v1.12
3. RISC-V "C" Standard Extension (Compressed Instructions)
4. "A Case for (Partially) TAgged GEometric History Length Branch Prediction" - André Seznec, 2006
5. "The GShare Predictor" - Scott McFarling, 1993

---

**Son Güncelleme:** 4 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
