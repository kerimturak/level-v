---
title: "Hazard Detection Unit"
description: "Pipeline hazard tespiti ve çözümü"
date: 2025-12-01
draft: false
weight: 350
---

# Hazard Detection Unit: hazard_unit.sv

Pipeline'daki veri hazarlarını (data hazards) ve kontrol hazarlarını tespit edip çözer.

---

## 📋 Hazard Types

### 1. RAW (Read-After-Write) Hazard

**Problem**: Bir register yazılırken, başka bir instruction aynı register'ı okuyor.

```
Cycle 0: ADD x3, x1, x2    ; Write x3
Cycle 1: SUB x5, x3, x4    ; Read x3 (BEFORE write completes!)
         ↑ x3 değeri henüz güncellenmedi

Timeline (5-stage pipeline):
Cycle  IF    ID    EX    MEM   WB
────────────────────────────────
 0     ADD    -     -     -     -
 1     SUB    ADD   -     -     -    ← x3 yazılmadı!
 2     -      SUB   ADD   -     -
 3     -      -     SUB   ADD   -
 4     -      -     -     SUB   ADD   ← x3 yazıldı
```

**Çözüm**: 
- **Forwarding** (Data Forwarding): MEM veya WB aşamasındaki veriyi direkt kullan
- **Stalling** (Load-Use Hazard): Pipeline'ı durdur

### 2. Load-Use Hazard

**Problem**: Load instruction'dan veri, hemen sonraki instruction'da kullanılıyor.

```
LW x3, 0(x5)     ; Load x3 from memory
ADD x7, x3, x4   ; x3'ü 1 cycle sonra kullan

Problem: Load veri MEM stage'de tamamlanıyor, fakat ADD
         EX stage'de x3 değerine ihtiyaç duyuyor!

Timing:
Cycle  IF    ID    EX      MEM   WB
────────────────────────────────────
 0     LW    -     -       -     -
 1     ADD   LW    -       -     -    ← ADD EX'de, data MEM'de
 2     -     ADD   LW      -     -
 3     -     -     ADD     LW    -
 4     -     -     -       ADD   LW

x3 data: LW MEM (Cycle 2) → WB (Cycle 4)
         ADD EX (Cycle 2)  ← BEFORE x3 ready!
```

**Çözüm**: **Stall** - Pipeline'ı 1 cycle beklet

### 3. Control Hazard

**Problem**: Branch instruction PC'yi değiştirse, önceki instruction'lar hala pipeline'da.

```
BEQ x1, x2, offset  ; Branch taken
ADD x3, x4, x5      ; Should NOT execute
SUB x6, x7, x8      ; Should NOT execute

Problem: ADD ve SUB fetch edildikten sonra branch karşılaştırması yapılıyor!

Timeline:
Cycle  IF      ID    EX    MEM   WB
────────────────────────────────────
 0     BEQ     -     -     -     -
 1     ADD     BEQ   -     -     -    ← Branch taken detected!
 2     SUB     ADD   BEQ   -     -
 3     -       SUB   ADD   BEQ   -    ← Flush ADD & SUB
 4     -       -     SUB   ADD   BEQ
```

**Çözüm**: **Flush** - Fetch edilen hatalı instruction'ları sil

---

## 🏗️ Architecture

### Interface

```systemverilog
module hazard_unit (
    // Decode stage register addresses
    input  logic [4:0] r1_addr_de_i,       // RS1 (Decode)
    input  logic [4:0] r2_addr_de_i,       // RS2 (Decode)
    
    // Execute stage register addresses
    input  logic [4:0] r1_addr_ex_i,       // RS1 (Execute)
    input  logic [4:0] r2_addr_ex_i,       // RS2 (Execute)
    input  logic [4:0] rd_addr_ex_i,       // RD (Execute)
    input  logic       pc_sel_ex_i,        // Branch taken (Execute)
    input  logic       rslt_sel_ex_0,      // Load instruction (Execute)
    
    // Memory stage register addresses
    input  logic [4:0] rd_addr_me_i,       // RD (Memory)
    input  logic       rf_rw_me_i,         // Register write enable (Memory)
    
    // WriteBack stage register addresses
    input  logic       rf_rw_wb_i,         // Register write enable (WriteBack)
    input  logic [4:0] rd_addr_wb_i,       // RD (WriteBack)
    
    // Outputs
    output logic       stall_fe_o,         // Stall Fetch
    output logic       stall_de_o,         // Stall Decode
    output logic       flush_de_o,         // Flush Decode
    output logic       flush_ex_o,         // Flush Execute
    output logic [1:0] fwd_a_ex_o,         // Forward source A (Execute)
    output logic [1:0] fwd_b_ex_o,         // Forward source B (Execute)
    output logic       fwd_a_de_o,         // Forward source A (Decode)
    output logic       fwd_b_de_o          // Forward source B (Decode)
);
```

---

## 🔄 Data Forwarding

### Forwarding Priority

**Execute Stage Operand A**:

```systemverilog
if (rf_rw_me_i && (r1_addr_ex_i == rd_addr_me_i) && (r1_addr_ex_i != 0)) begin
    fwd_a_ex_o = 2'b10;  // Forward from MEM stage (highest priority)
end else if (rf_rw_wb_i && (r1_addr_ex_i == rd_addr_wb_i) && (r1_addr_ex_i != 0)) begin
    fwd_a_ex_o = 2'b01;  // Forward from WB stage
end else begin
    fwd_a_ex_o = 2'b00;  // Use register file data (no forward)
end
```

**Why MEM before WB?**

```
Example: Two consecutive ADD instructions
─────────────────────────────────────────
ADD x3, x1, x2    ; Write x3
ADD x5, x3, x4    ; Read x3

Timeline:
Cycle  IF    ID    EX    MEM   WB
────────────────────────────────
 0     ADD   -     -     -     -
 1     ADD   ADD   -     -     -
 2     -     ADD   ADD   -     -
 3     -     -     ADD   ADD   -
 4     -     -     -     ADD   ADD

Cycle 2, ADD (second) EX stage:
  ├─ x3 updated in MEM stage (first ADD, cycle 2)
  ├─ x3 also being updated in WB (first ADD, cycle 1 result)
  └─ Use MEM value (most recent) → fwd_a = 2'b10
```

### Forwarding Sources (2-bit)

| Encoding | Source | Latency | Priority |
|----------|--------|---------|----------|
| 2'b00 | Register File | 1 cycle | Lowest |
| 2'b01 | WriteBack Stage | 0 cycles | Medium |
| 2'b10 | Memory Stage | 0 cycles | Highest |

### Decode Stage Forwarding

```systemverilog
fwd_a_de_o = rf_rw_wb_i && (r1_addr_de_i == rd_addr_wb_i) && (r1_addr_de_i != 0);
fwd_b_de_o = rf_rw_wb_i && (r2_addr_de_i == rd_addr_wb_i) && (r2_addr_de_i != 0);
```

**Decode'den WB'ye only**: Decode stage'de sadece WB'den forward edebiliriz çünkü:
- MEM/EX stage'deki veriler henüz execute edilmemiş olabilir
- WB verisi kesindir (geçmiş sonuç)

---

## 🛑 Load-Use Hazard Stalling

### Detection

```systemverilog
lw_stall = rslt_sel_ex_0 && 
           ((r1_addr_de_i == rd_addr_ex_i) || (r2_addr_de_i == rd_addr_ex_i));
```

**Condition**:
1. `rslt_sel_ex_0 = 1`: EX stage'deki instruction bir Load (LW, LH, LB, vb.)
2. RS1 veya RS2: Decode stage'deki instruction, Load'un destination register'ını okuyor

```
Example:
─────
LW x3, 0(x5)     ; EX stage, rd_addr_ex_i = 5 (x5'e yazılıyor)
ADD x5, x1, x2   ; DE stage, r1_addr_de_i = 5 (x5'i okuyor)

Detection:
├─ rslt_sel_ex_0 = 1 (Load instruction)
├─ r1_addr_de_i (5) == rd_addr_ex_i (5) ✓
└─ lw_stall = 1

Pipeline:
Cycle  IF    ID    EX    MEM   WB
────────────────────────────────
 0     LW    -     -     -     -
 1     ADD   LW    -     -     -
 2     -     ADD   LW    -     -    ← Stall!
 3     -     ADD   -     LW    -    ← x3 loading
 4     -     -     ADD   -     LW   ← x3 available to ADD
```

### Stall Propagation

```systemverilog
stall_fe_o = lw_stall;  // Fetch stage stalls
stall_de_o = lw_stall;  // Decode stage stalls
```

Effect:
- **Fetch**: Pipeline'a yeni instruction almaz
- **Decode**: Aynı instruction'ı tutmaya devam eder
- Result: Instruction'lar 1 cycle gecikmeli execute edilir

---

## 🧹 Pipeline Flushing

### Branch Resolution Flush

```systemverilog
flush_de_o = pc_sel_ex_i;  // Branch taken → Flush Decode
flush_ex_o = lw_stall || pc_sel_ex_i;  // Flush Execute
```

**Why Flush?**

```
BEQ x1, x2, target  ; Branch taken (EX stage)
└─ pc_sel_ex_i = 1

Instructions fetched after BEQ (now invalid):
├─ Decode stage: Wrong instruction
├─ Execute stage: Wrong instruction
└─ Must be flushed!
```

### Load-Use + Branch Flush Conflict

```
Cycle 0: LW x3, 0(x5)      ; Fetch
Cycle 1: BEQ x1, x2, ...   ; Fetch  (branch taken!)
         LW at EX stage, Stall = 1

Flushing:
├─ flush_ex_o = lw_stall || pc_sel_ex_i
├─ = 1 || 1 = 1
└─ Flush both: Load stall AND branch flush
```

---

## 📊 Example Scenario

### Scenario: Load-Use + Branch

```systemverilog
// Code:
LW   x3, 0(x5)        ; addr=0
ADD  x3, x3, x4       ; uses x3 (hazard!)
BEQ  x1, x2, label    ; branch taken

Timeline:
─────────────────────────────────────
Cycle  IF      ID        EX    MEM   WB
─────────────────────────────────────
  0    LW      -         -     -     -
  1    ADD     LW        -     -     -
  2    BEQ     ADD       LW    -     -   ← lw_stall=1, stall_de=1
  3    -       ADD       -     LW    -   ← stall continues
  4    -       -         ADD   -     LW  ← Branch check in EX
                                         ← pc_sel_ex = 1 (branch taken)
  5    -       -         -     ADD   -   ← flush_de=1, flush_ex=1
  6    <new PC> -        -     -     ADD ← Branch destination fetched
```

**Result**:
- Load-Use stall prevents ADD from executing immediately
- Branch flush clears incorrect instructions
- Correct instruction from branch target fetches next cycle

---

## 🎯 x0 Special Handling

```systemverilog
// Never forward or stall for x0 (always zero)
if (r1_addr_ex_i != 0) begin  // Only if not x0
    fwd_a_ex_o = 2'b10;
end
```

**Why?** x0 is always 0 (read-only), writing to it is ignored:
- No data hazard to x0
- Always safe to read x0 from register file

---

## 📈 Latency Impact

| Operation | Stall Cycles | Total Latency |
|-----------|--------------|---------------|
| ADD (no hazard) | 0 | 3 (IF→ID→EX) |
| ADD (forwarded) | 0 | 3 |
| ADD (LW + use) | 1 | 4 |
| Branch taken | 0 | 3 |
| Branch + Load stall | 1 | 4 |

---

## 🔧 Implementation Details

### Zero Check (x0)

```systemverilog
// Always check: (r1_addr == rd) && (r1_addr != 0)
// This prevents x0 from causing false hazards
```

### Register Addresses

```
5-bit register address:
├─ 0: x0 (zero register)
├─ 1-5: x1-x5
├─ ...
└─ 31: x31
```

### Result Source (rslt_sel_ex_0)

```
rslt_sel_ex_0 = 1: Load instruction
  └─ Data comes from Memory (next cycle), not this cycle
  
rslt_sel_ex_0 = 0: Non-load instruction
  └─ Data available this cycle (ALU result)
```

---

## 📚 Integration with Pipeline

### Hazard Unit connects to:

1. **Register File** (Decode): Read addresses rs1, rs2
2. **Pipeline Registers** (EX, MEM, WB): Register destinations
3. **ALU/CSR** (Execute): Branch decision (pc_sel)
4. **Stall Generator**: Stall signals to pipeline control
5. **Forwarding Mux** (Execute, Decode): Forwarding selection

### Control Flow

```
Hazard Unit detects hazard
         ↓
If RAW: Set fwd_*_o (forwarding selector)
         ↓
If Load-Use: Set stall_fe_o, stall_de_o
         ↓
If Branch: Set flush_de_o, flush_ex_o
         ↓
Pipeline Control applies these signals
         ↓
Stall: Hold current instructions, don't fetch new
Flush: Clear pipeline stages of wrong instructions
Forward: Route data from later stages to earlier stages
```

---

## 🎯 Summary

| Hazard | Symptom | Solution | Cost |
|--------|---------|----------|------|
| RAW | Register read before write | Forwarding | 0 cycles |
| Load-Use | Load data needed next cycle | Stall | 1 cycle |
| Control | Branch changes PC | Flush | 3 cycles |

**Hazard Unit Output Priority**:
1. Detect stalls first (Load-Use)
2. Detect branch flushes
3. Set forwarding paths
4. Combine results

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025

