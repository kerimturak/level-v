# GSHARE BRANCH PREDICTOR Modülü - Teknik Döküman

## Genel Bakış

`gshare_bp.sv` modülü, RISC-V işlemcisinde gelişmiş dallanma tahmini (branch prediction) yapar. GSHARE (Global History with Shared indexing) algoritmasını, Tournament predictor ile, RAS (Return Address Stack), BTB (Branch Target Buffer), IBTC (Indirect Branch Target Cache) ve Loop predictor ile birleştirerek yüksek doğruluk oranı sağlar.

## Branch Prediction Neden Önemli?

Modern pipeline'lı işlemcilerde:
- Branch resolution Execute aşamasında olur (3-4 cycle sonra)
- Yanlış tahmin → **Pipeline flush** → 3-4 cycle penalty
- Doğru tahmin → Pipeline akışı kesintisiz

**Örnek:**
- 100M instruction, %20 branch
- Misprediction rate %10 → 2M misprediction
- Penalty 4 cycle → **8M cycle loss** (~8% performance kaybı)

## Temel Mimariler

### 1. GSHARE (Primary Predictor)
- **Global History Register (GHR)**: Son N branch sonuçlarını tutar
- **Pattern History Table (PHT)**: PC ⊕ GHR ile index'lenen 2-bit saturating counter'lar
- **Avantaj**: Global branch pattern correlation

### 2. Bimodal Predictor (Secondary)
- **Pattern History Table**: Sadece PC ile index'lenen 2-bit counter'lar
- **Avantaj**: Basit, local pattern'lerde iyi

### 3. Tournament Predictor (Meta)
- **Choice Table**: GSHARE vs Bimodal seçimi
- Hangisi daha başarılıysa onu kullan
- **Accuracy:** %90-95 (kod tipine göre)

### 4. Return Address Stack (RAS)
- **Function Return Prediction**: `ret` instruction'ları için
- Stack-based, LIFO
- **Accuracy:** %95-99

### 5. Branch Target Buffer (BTB)
- **Target Address Cache**: Branch hedef adreslerini cache'ler
- Tag + Target pair
- BTB miss → Static prediction (BTFN)

### 6. Indirect Branch Target Cache (IBTC)
- **JALR Prediction**: Indirect jump'lar için
- PC → Target mapping
- RAS'ın cover etmediği indirect jump'ları handle eder

### 7. Loop Predictor
- **Loop Iteration Tracking**: Döngü iterasyon sayısını tahmin eder
- Trip count learning
- Backward branch detection

## Port Tanımları

### Giriş Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `spec_hit_i` | logic | Prediction doğru mu? (1=doğru, 0=misprediction) |
| `stall_i` | logic | Pipeline stall sinyali |
| `inst_i` | inst_t | Fetch edilen instruction |
| `pc_target_i` | [XLEN-1:0] | Execute'dan gelen gerçek branch hedefi |
| `pc_i` | [XLEN-1:0] | Mevcut program counter |
| `pc_incr_i` | [XLEN-1:0] | PC + 4 (sequential) |
| `fetch_valid_i` | logic | Fetch geçerli mi? |
| `de_info_i` | pipe_info_t | Decode pipeline info |
| `ex_info_i` | pipe_info_t | Execute pipeline info |

### Çıkış Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `spec_o` | predict_info_t | Prediction bilgisi (pc, taken, spectype) |

**predict_info_t yapısı:**
```systemverilog
typedef struct packed {
  logic [XLEN-1:0] pc;        // Tahmin edilen hedef PC
  logic            taken;     // Branch taken mı?
  spec_type_e      spectype;  // Prediction tipi (BRANCH/JUMP/RAS/NO_SPEC)
} predict_info_t;
```

## Veri Yapıları

### Global History Register (GHR)

```systemverilog
logic [GHR_SIZE-1:0] ghr;        // Committed GHR (EX feedback)
logic [GHR_SIZE-1:0] ghr_spec;   // Speculative GHR (prediction)
```

**Boyut:** `GHR_SIZE = 8-16 bit` (ceres_param.sv'den)

**Güncelleme:**
- **Speculative:** Her prediction'da shift left, tahmin sonucu append
- **Committed:** Execute'da branch resolve olduğunda shift left, gerçek sonuç append

**Örnek (GHR_SIZE=8):**
```
Initial:    GHR = 8'b00000000
Branch 1 (taken):     GHR_spec = 8'b00000001
Branch 2 (not-taken): GHR_spec = 8'b00000010
Misprediction → GHR restore + correct outcome
```

### Pattern History Table (PHT)

```systemverilog
logic [1:0] pht [PHT_SIZE];      // GSHARE PHT
logic [1:0] bimodal [PHT_SIZE];  // Bimodal PHT
```

**Boyut:** `PHT_SIZE = 256-1024` (2^8 to 2^10)

**2-Bit Saturating Counter:**
```
State | Value | Prediction
------|-------|------------
SNT   | 2'b00 | Strongly Not-Taken
WNT   | 2'b01 | Weakly Not-Taken
WT    | 2'b10 | Weakly Taken
ST    | 2'b11 | Strongly Taken

Transition (on taken):
  2'b00 → 2'b01 → 2'b10 → 2'b11 (saturate)

Transition (on not-taken):
  2'b11 → 2'b10 → 2'b01 → 2'b00 (saturate)
```

**Index Calculation:**
```systemverilog
// GSHARE: XOR for correlation
pht_idx = pc[PC_BITS:1] ^ ghr_spec[GHR_SIZE-1:0];

// Bimodal: PC only
bimodal_idx = pc[PC_BITS:1];
```

### Choice Table (Tournament)

```systemverilog
logic [1:0] choice [PHT_SIZE];
```

**Selection:**
- `choice[1] == 1` → Use GSHARE prediction
- `choice[1] == 0` → Use Bimodal prediction

**Update Logic:**
```systemverilog
if (pht[idx][1] != bimodal[idx][1]) begin  // Disagreement
  if (pht[idx][1] == actual_outcome) begin
    // GSHARE correct → increase choice
    if (choice[idx] < 2'b11) choice[idx] <= choice[idx] + 1;
  end else begin
    // Bimodal correct → decrease choice
    if (choice[idx] > 2'b00) choice[idx] <= choice[idx] - 1;
  end
end
```

### Branch Target Buffer (BTB)

```systemverilog
logic btb_valid [BTB_SIZE];
logic [TAG_WIDTH-1:0] btb_tag [BTB_SIZE];
logic [XLEN-1:0] btb_target [BTB_SIZE];
```

**Boyut:** `BTB_SIZE = 128-512`

**Lookup:**
```systemverilog
btb_idx = pc[BTB_IDX_BITS:1];
btb_hit = btb_valid[btb_idx] && (btb_tag[btb_idx] == pc[XLEN-1:BTB_IDX_BITS+2]);
predicted_target = btb_target[btb_idx];
```

**Update (on branch resolution):**
```systemverilog
btb_valid[btb_wr_idx]  <= 1'b1;
btb_tag[btb_wr_idx]    <= ex_pc[XLEN-1:BTB_IDX_BITS+2];
btb_target[btb_wr_idx] <= actual_target;
```

### Indirect Branch Target Cache (IBTC)

```systemverilog
logic ibtc_valid [IBTC_SIZE];
logic [TAG_WIDTH-1:0] ibtc_tag [IBTC_SIZE];
logic [XLEN-1:0] ibtc_target [IBTC_SIZE];
```

**Boyut:** `IBTC_SIZE = 32-128`

**Kullanım:**
- JALR instruction'ları için (RAS'ın cover etmedikleri)
- Örnek: Computed jumps, virtual function calls, switch-case jump tables

**Lookup:**
```systemverilog
ibtc_idx = pc[IBTC_IDX_BITS:1];
ibtc_hit = ibtc_valid[ibtc_idx] && (ibtc_tag[ibtc_idx] == pc[XLEN-1:IBTC_IDX_BITS+2]);
predicted_target = ibtc_target[ibtc_idx];
```

### Loop Predictor

```systemverilog
logic [7:0] loop_count [LOOP_SIZE];  // Current iteration
logic [7:0] loop_trip [LOOP_SIZE];   // Max iterations seen
logic loop_valid [LOOP_SIZE];
logic [TAG_WIDTH-1:0] loop_tag [LOOP_SIZE];
```

**Boyut:** `LOOP_SIZE = 32-64`

**İşlem:**
1. Backward branch tespit edilir (`$signed(target - pc) < 0`)
2. Loop entry: `loop_count = 1`
3. Her iteration: `loop_count++`
4. Loop exit: `loop_trip = loop_count`, `loop_count = 0`
5. Prediction: `loop_count >= loop_trip - 1` → predict exit

**Örnek:**
```c
for (int i = 0; i < 10; i++) {  // Loop trip count = 10
  // ...
}
```
- İlk 9 iteration: Predict TAKEN (loop continue)
- 10. iteration: Predict NOT-TAKEN (loop exit)

## Prediction Logic (Öncelik Sırası)

```systemverilog
if (popped.valid) 
  spec_o = RAS prediction;
else if (j_type)
  spec_o = JAL prediction (PC + imm);
else if (jr_type && ibtc_hit)
  spec_o = JALR prediction (IBTC target);
else if (b_type) begin
  if (loop_hit && is_backward_branch)
    spec_o = Loop predictor;
  else if (btb_hit)
    spec_o = Tournament predictor (GSHARE/Bimodal);
  else if (is_backward_branch)
    spec_o = Static BTFN (predict TAKEN);
  else
    spec_o = Static BTFN (predict NOT-TAKEN);
end
else
  spec_o = Sequential (PC + 4);
```

### 1. RAS Prediction (En Yüksek Öncelik)

```systemverilog
if (popped.valid) begin
  spec_o.pc       = popped.data;       // RAS'tan pop edilen return address
  spec_o.taken    = 1'b1;
  spec_o.spectype = RAS;
end
```

**Koşul:** `jr_type && (rd_addr == x1 || rd_addr == x5) && (rs1_addr == x1 || rs1_addr == x5)`

### 2. JAL Prediction (Unconditional Jump)

```systemverilog
if (j_type) begin
  spec_o.pc       = pc_i + imm;        // PC-relative jump
  spec_o.taken    = 1'b1;
  spec_o.spectype = JUMP;
end
```

**Doğruluk:** %100 (unconditional, target deterministik)

### 3. JALR with IBTC Prediction

```systemverilog
if (jr_type && ibtc_hit) begin
  spec_o.pc       = ibtc_predicted_target;
  spec_o.taken    = 1'b1;
  spec_o.spectype = JUMP;
end
```

**IBTC Miss:** Sequential fetch devam eder (target bilinmiyor)

### 4. Conditional Branch Prediction

#### 4a. Loop Predictor (Backward Branch)

```systemverilog
if (loop_hit && is_backward_branch) begin
  if (loop_pred_exit) begin
    spec_o.pc       = pc_incr_i;     // Predict loop exit
    spec_o.taken    = 1'b0;
  end else begin
    spec_o.pc       = btb_hit ? btb_predicted_target : branch_target_calc;
    spec_o.taken    = 1'b1;
  end
  spec_o.spectype = BRANCH;
end
```

#### 4b. Tournament Predictor (BTB Hit)

```systemverilog
if (btb_hit) begin
  use_gshare = choice[bimodal_idx][1];
  final_taken = use_gshare ? pht[pht_idx][1] : bimodal[bimodal_idx][1];
  
  if (final_taken) begin
    spec_o.pc       = btb_predicted_target;
    spec_o.taken    = 1'b1;
  end else begin
    spec_o.pc       = pc_incr_i;
    spec_o.taken    = 1'b0;
  end
  spec_o.spectype = BRANCH;
end
```

#### 4c. Static BTFN (BTB Miss)

**Backward-Taken, Forward-Not-Taken Heuristic:**

```systemverilog
if (is_backward_branch) begin
  spec_o.pc       = branch_target_calc;  // Predict TAKEN (likely loop)
  spec_o.taken    = 1'b1;
end else begin
  spec_o.pc       = pc_incr_i;           // Predict NOT-TAKEN
  spec_o.taken    = 1'b0;
end
```

**Rationale:**
- Backward branch'ler genelde loop'tur → TAKEN
- Forward branch'ler genelde if-statement → NOT-TAKEN (early exit daha az frequent)

## GHR Update Mechanism

### Speculative Update (Prediction Phase)

```systemverilog
always_ff @(posedge clk_i) begin
  if (!rst_ni)
    ghr_spec <= '0;
  else if (!stall_i) begin
    if (spec_miss) begin
      // Misprediction → restore committed GHR + correct outcome
      ghr_spec <= {ghr[GHR_SIZE-2:0], ex_was_taken};
    end else if (fetch_valid_i && b_type) begin
      // Speculatively update GHR
      ghr_spec <= {ghr_spec[GHR_SIZE-2:0], spec_o.taken};
    end
  end
end
```

### Committed Update (Execute Feedback)

```systemverilog
always_ff @(posedge clk_i) begin
  if (ex_is_branch) begin
    ghr <= {ghr[GHR_SIZE-2:0], ex_was_taken};
  end
end
```

**Dual GHR Neden?**
- **ghr_spec**: Prediction için kullanılır (fetch stage)
- **ghr**: Committed (execute feedback), recovery için
- Misprediction'da `ghr_spec` restore edilir

## Predictor Update (Training)

### PHT Update (2-Bit Saturating Counter)

```systemverilog
if (ex_was_taken) begin
  if (pht[pht_wr_idx] < 2'b11) 
    pht[pht_wr_idx] <= pht[pht_wr_idx] + 1;
end else begin
  if (pht[pht_wr_idx] > 2'b00) 
    pht[pht_wr_idx] <= pht[pht_wr_idx] - 1;
end
```

### Choice Update (Tournament)

```systemverilog
if (pht[pht_wr_idx][1] != bimodal[bimodal_wr_idx][1]) begin
  if (pht[pht_wr_idx][1] == ex_was_taken) begin
    // GSHARE correct
    if (choice[bimodal_wr_idx] < 2'b11) 
      choice[bimodal_wr_idx] <= choice[bimodal_wr_idx] + 1;
  end else begin
    // Bimodal correct
    if (choice[bimodal_wr_idx] > 2'b00) 
      choice[bimodal_wr_idx] <= choice[bimodal_wr_idx] - 1;
  end
end
```

**Update sadece disagreement varsa:** Predictionlar aynıysa seçim değişmez (her ikisi de doğru/yanlış)

### BTB Update

```systemverilog
btb_valid[btb_wr_idx]  <= 1'b1;
btb_tag[btb_wr_idx]    <= ex_info_i.pc[XLEN-1:$clog2(BTB_SIZE)+2];
btb_target[btb_wr_idx] <= pc_target_i;
```

**Her branch resolution'da:** BTB her zaman update edilir (hit/miss fark etmez)

### Loop Predictor Update

```systemverilog
if ($signed(pc_target_i - ex_info_i.pc) < 0) begin  // Backward branch
  if (ex_was_taken) begin
    if (loop_valid[lp_wr_idx] && loop_tag[lp_wr_idx] == ex_pc_tag) begin
      loop_count[lp_wr_idx] <= loop_count[lp_wr_idx] + 1;  // Iteration
    end else begin
      loop_valid[lp_wr_idx] <= 1'b1;  // New loop entry
      loop_tag[lp_wr_idx]   <= ex_pc_tag;
      loop_count[lp_wr_idx] <= 8'd1;
    end
  end else begin
    if (loop_valid[lp_wr_idx] && loop_tag[lp_wr_idx] == ex_pc_tag) begin
      loop_trip[lp_wr_idx]  <= loop_count[lp_wr_idx];  // Record trip count
      loop_count[lp_wr_idx] <= 8'd0;  // Reset for next loop
    end
  end
end
```

## Branch Prediction Logger (Optional)

`+define+LOG_BP` ile etkinleştirilir.

### İstatistikler

```systemverilog
logic [63:0] total_branches;
logic [63:0] correct_predictions;
logic [63:0] mispredictions;
logic [63:0] ras_predictions, ras_correct;
logic [63:0] jal_count, jal_correct;
logic [63:0] jalr_count, jalr_correct;
logic [63:0] ibtc_predictions, ibtc_correct;
logic [63:0] btb_hits, btb_misses;
```

### Çıktı Formatı

```
╔══════════════════════════════════════════════════════════════╗
║          GSHARE Branch Predictor - Final Statistics          ║
╠══════════════════════════════════════════════════════════════╣
║  Total Control Transfers : 1000000                          ║
║  Correct Predictions     : 920000    (92.00%)              ║
║  Mispredictions          : 80000     (8.00%)               ║
╠══════════════════════════════════════════════════════════════╣
║  JAL (Direct Jump)                                           ║
║    Total                 : 150000                           ║
║    Correct               : 150000    (100.00%)             ║
╠══════════════════════════════════════════════════════════════╣
║  JALR (Indirect Jump)                                        ║
║    Total                 : 50000                            ║
║    Correct               : 47000     (94.00%)              ║
║    - RAS Predictions     : 40000     (98.00% accurate)     ║
║    - IBTC Predictions    : 7000      (85.71% accurate)     ║
╠══════════════════════════════════════════════════════════════╣
║  Conditional Branch (BEQ/BNE/BLT/BGE/BLTU/BGEU)               ║
║    Total                 : 800000                           ║
║    Correct               : 723000    (90.38%)              ║
║    Mispredicted          : 77000     (9.62%)               ║
╚══════════════════════════════════════════════════════════════╝
```

## Performance Analysis

### Typical Accuracy (Benchmark Dependent)

| Predictor | Accuracy | Misprediction Rate |
|-----------|----------|-------------------|
| Static (Always Not-Taken) | ~60% | ~40% |
| Bimodal (2-bit counter) | ~82-85% | ~15-18% |
| GSHARE (8-bit GHR) | ~87-92% | ~8-13% |
| Tournament (GSHARE+Bimodal) | ~90-95% | ~5-10% |
| Tournament + RAS + BTB + Loop | ~92-96% | ~4-8% |

### Pipeline Impact

**Örnek (Coremark benchmark):**
- Total instructions: 10M
- Branch instructions: 2M (20%)
- Misprediction rate: 5%
- Mispredictions: 100K
- Penalty: 4 cycles
- **Total penalty:** 400K cycles (~4% slowdown)

**Improvement:**
- Static predictor (15% misprediction) → 600K cycles lost (~6%)
- **Improvement:** 200K cycles saved (33% reduction in penalty)

## Timing Considerations

### Critical Paths

1. **Prediction Path (Fetch Stage):**
   ```
   PC → BTB lookup → PHT lookup → Tournament select → Mux → spec_o.pc
   ```
   - Timing critical (single cycle)
   - BTB/PHT genelde BRAM/SRAM → asenkron read

2. **Update Path (Execute Stage):**
   ```
   ex_info_i → PHT update → Choice update → BTB update
   ```
   - Sequential logic, less critical

### Area Overhead

**Örnek Configuration:**
- PHT: 256 entries × 2-bit × 2 (GSHARE+Bimodal) = 1 Kbit
- Choice: 256 entries × 2-bit = 512 bit
- BTB: 128 entries × (22-bit tag + 32-bit target) = 6.75 Kbit
- IBTC: 32 entries × (22-bit tag + 32-bit target) = 1.69 Kbit
- Loop: 32 entries × (22-bit tag + 8-bit count + 8-bit trip + 1-bit valid) = 1.22 Kbit
- GHR: 8-bit × 2 (spec + committed) = 16 bit

**Total:** ~11 Kbit (~1.4 KB)

## Verification

### Test Scenarios

1. **Sequential Code:** Prediction accuracy ~100% (no branches)
2. **Simple Loops:** Loop predictor accuracy ~95%
3. **Nested Loops:** GSHARE correlation accuracy ~90%
4. **Function Calls:** RAS accuracy ~98%
5. **Switch-Case:** IBTC accuracy ~85% (after warmup)
6. **Random Branches:** Tournament accuracy ~75-80%

### Assertions (Önerilen)

```systemverilog
// Speculation hit durumunda GHR update yapılmamalı (already updated)
assert property (@(posedge clk_i) disable iff (!rst_ni)
  spec_hit_i && ex_is_branch |-> $stable(ghr));

// Misprediction durumunda GHR restore edilmeli
assert property (@(posedge clk_i) disable iff (!rst_ni)
  !spec_hit_i && ex_is_branch |=> ghr_spec == {$past(ghr[GHR_SIZE-2:0]), $past(ex_was_taken)});

// BTB update her branch'te yapılmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
  ex_is_branch |=> btb_valid[$past(btb_wr_idx)]);
```

## Gelecek İyileştirmeler

1. **TAGE Predictor**: Tagged Geometric History Length (daha yüksek accuracy)
2. **Perceptron Predictor**: Neural network-based prediction
3. **BTB Associativity**: Multi-way BTB (alias reduction)
4. **Loop Predictor Enhancement**: Nested loop support
5. **Prefetch Integration**: Predicted path'i proactive fetch et
6. **Power Optimization**: Gated clock, selective update

## İlgili Modüller

1. **fetch.sv**: Branch predictor'ı kullanır
2. **ras.sv**: Return Address Stack implementation
3. **hazard_unit.sv**: Misprediction handling
4. **execute.sv**: Branch resolution feedback

## Referanslar

1. "The GShare Predictor" - Scott McFarling, 1993
2. "A Case for (Partially) TAged GEometric History Length Branch Prediction" - André Seznec, 2006 (TAGE)
3. "Dynamic Branch Prediction with Perceptrons" - Daniel A. Jiménez, Calvin Lin, 2001
4. "Branch Prediction" - Computer Architecture: A Quantitative Approach - Hennessy & Patterson
5. RISC-V Unprivileged ISA Specification - Control Transfer Instructions

---

**Son Güncelleme:** 4 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
