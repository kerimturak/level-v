---
title: "Fetch Stage (Stage 1) - RTL"
description: "Instruction Fetch aşamasının detaylı RTL implementasyonu"
date: 2025-12-01
draft: false
weight: 310
---

# Fetch Stage (Stage 1) - Detaylı RTL Implementasyonu

Ceres RISC-V'nin birinci aşaması olan Fetch Stage, talimatları bellek/cache'den alıp, PC (Program Counter) yönetimini gerçekleştirir.

---

## 📁 Dosya Konumu

```
rtl/core/stage01_fetch/
├── fetch.sv                  # Main fetch module (344 satır)
├── align_buffer.sv           # Instruction alignment buffer
├── compressed_decoder.sv     # RV32C decoder
├── gshare_bp.sv              # Gshare branch predictor
└── ras.sv                    # Return Address Stack
```

---

## 🎯 Amaç

Fetch Stage'in temel görevleri:

1. **Program Counter (PC) Yönetimi**: PC'yi güncelle, exception'lara ve dallanmalara yanıt ver
2. **Instruction Fetch**: I-Cache'den instruction al
3. **Instruction Alignment**: Sıkıştırılmış (16-bit) instruction'ları hizala
4. **Branch Prediction**: Şartlı dallanmaları tahmin et
5. **Exception Detection**: İçeride oluşan exception'ları tespit et (DEBUG breakpoint, MISALIGNED, vb.)

---

## 🏗️ Modül Hiyerarşisi

```
fetch.sv (Ana Fetch Modülü)
├─→ align_buffer.sv
│   └─→ compressed_decoder.sv
├─→ gshare_bp.sv (Branch Predictor)
├─→ ras.sv (Return Address Stack)
└─→ I-Cache Interface
```

---

## 📊 Modülün Arayüzü

### Girişler (Inputs)

```systemverilog
input  logic                       clk_i,         // Clock
input  logic                       rst_ni,        // Active-low reset
input  stall_e                     stall_i,       // Pipeline stall cause
input  logic                       flush_i,       // Pipeline flush
input  logic            [XLEN-1:0] flush_pc_i,   // Flush target address
input  ilowX_res_t                 lx_ires_i,    // I-Cache response
input  logic            [XLEN-1:0] pc_target_i,  // Branch target (from WB)
input  logic            [XLEN-1:0] ex_mtvec_i,   // Exception handler address
input  logic                       trap_active_i, // Exception active
input  logic                       misa_c_i,     // C extension enabled
input  logic            [XLEN-1:0] tdata1_i,     // Trigger control
input  logic            [XLEN-1:0] tdata2_i,     // Breakpoint address
input  logic                       spec_hit_i,   // Speculation hit/miss
input  pipe_info_t                 de_info_i,    // Decode stage info
input  pipe_info_t                 ex_info_i,    // Execute stage info
```

### Çıkışlar (Outputs)

```systemverilog
output predict_info_t              spec_o,        // Branch prediction output
output ilowX_req_t                 lx_ireq_o,    // I-Cache request
output logic            [XLEN-1:0] pc_o,         // Current PC
output logic            [XLEN-1:0] pc_incr_o,    // PC + increment
output logic            [XLEN-1:0] inst_o,       // Instruction
output logic                       imiss_stall_o, // I-Cache miss stall
output exc_type_e                  exc_type_o,   // Exception type
output instr_type_e                instr_type_o  // Instruction type
```

---

## 🔄 PC Yönetimi

### PC Register Güncellemesi

```systemverilog
always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
        pc <= RESET_VECTOR;  // 0x8000_0000
    end else if (pc_en) begin
        pc <= pc_next;  // PC güncelleme
    end
end
```

**PC Reset Değeri**: `0x8000_0000` (parametrik, `RESET_VECTOR`)

### PC Enable Logic

```systemverilog
always_comb begin
    // PC üç durumda güncellenir:
    // 1. trap_active_i = 1: Exception durumu
    // 2. stall_i == NO_STALL: Normal fetch
    // 3. flush_i = 1: Pipeline flush (exception recovery)
    
    pc_en = trap_active_i || (stall_i == NO_STALL) || flush_i;
end
```

**PC Enable Koşulları**:
- ✓ Exception aktif: PC → MTVEC
- ✓ Stall yok (NO_STALL): PC normal güncellenme
- ✓ Flush aktif: PC → flush_pc_i

### PC Increment Hesaplama

```systemverilog
// Compressed instruction: +2, Normal: +4
pc_incr_o = (buff_res.valid && is_comp) ? (pc + 32'd2) : (pc + 32'd4);
```

**Önemli**: RV32C (Compressed) extension'da instruction'lar 16-bit olabilir.

---

## 📋 Next PC Selection Logic

Next PC'nin belirlenmesinde **öncelik sırası** vardır:

```systemverilog
always_comb begin
    if (flush_i) begin
        // 1. HIGHEST: Pipeline flush (exception recovery)
        pc_next = flush_pc_i;
    end else if (trap_active_i) begin
        // 2. Exception active - handler'a git
        pc_next = ex_mtvec_i;  // MTVEC CSR
    end else if (!spec_hit_i) begin
        // 3. Speculation miss (branch misprediction)
        pc_next = pc_target_i;  // Correct target from WB
    end else if (spec_o.taken) begin
        // 4. Branch prediction taken
        pc_next = spec_o.pc;  // Predicted target
    end else begin
        // 5. LOWEST: Sequential fetch
        pc_next = pc_incr_o;  // PC + 2/4
    end
end
```

**Öncelik**:
1. **Flush** (Exception recovery)
2. **Trap** (Exception handler)
3. **Misprediction** (Correct target)
4. **Prediction Hit** (Predicted target)
5. **Sequential** (PC + 2/4)

---

## 🎯 Fetch Valid Logic

```systemverilog
always_comb begin
    if (flush_i) begin
        fetch_valid = 1'b0;  // Flush sırasında fetch geçersiz
    end else if (spec_hit_i) begin
        fetch_valid = !trap_active_i;  // Normal exception kontrol
    end else begin
        fetch_valid = !trap_active_i;  // Misprediction recovery
    end
end
```

**Fetch Valid Durumları**:
- ✗ Flush aktif: Geçersiz (pipeline flushing)
- ✓ Speculation hit & no trap: Geçerli
- ✓ Speculation miss & no trap: Geçerli
- ✗ Trap aktif: Geçersiz

---

## 📖 Instruction Detection

### Compressed vs Normal Detection

```systemverilog
// Instruction ilk 2 bitine bakarak compressed olup olmadığını belirle
is_comp = (inst_o[1:0] != 2'b11);  // 11 ile bitiş = normal (32-bit)
```

**RV32C Encoding**:
- `xx00`: QUADRANT 0 (Compressed)
- `xx01`: QUADRANT 1 (Compressed)
- `xx10`: QUADRANT 2 (Compressed)
- `xx11`: Normal 32-bit (00-11 opcode bölümü)

### Instruction Type Tanımlama

```systemverilog
instr_type_o = resolved_instr_type(inst_o);  // ceres_param.sv fonksiyonu
```

**Örnek**: 
- Opcode = `7'b00100_11` (I-type) → `i_addi`, `i_slti`, vb.
- Opcode = `7'b01100_11` (R-type) → `r_add`, `r_sub`, vb.

---

## 🔍 Exception Detection @ Fetch

Fetch aşamasında 6 tip exception tespit edilir:

### 1. Debug Breakpoint
```systemverilog
has_debug_breakpoint = fetch_valid && tdata1_i[2] && (pc_o == tdata2_i);
```

**Koşul**: 
- Fetch geçerli
- Trigger control enabled (`tdata1[2] = 1`)
- PC == breakpoint address (`tdata2`)

**Priority**: `EXC_PRIORITY_DEBUG_BREAKPOINT` (varsayılan: PRIORITY_1)

### 2. Instruction Misaligned
```systemverilog
has_instr_misaligned = fetch_valid && (misa_c_i ? pc_o[0] : (pc_o[1:0] != 2'b00));
```

**Koşul**:
- Fetch geçerli
- C extension disabled: `pc[1:0] != 0`
- C extension enabled: `pc[0] != 0`

**Priority**: `EXC_PRIORITY_INSTR_MISALIGNED` (varsayılan: PRIORITY_2)

### 3. Instruction Access Fault
```systemverilog
has_instr_access_fault = fetch_valid && !grand;
```

**Koşul**: 
- Fetch geçerli
- Memory access denied (`!grand` = no memory grant)

**Priority**: `EXC_PRIORITY_INSTR_ACCESS_FAULT` (varsayılan: PRIORITY_3)

### 4. Illegal Instruction
```systemverilog
has_illegal_instr = fetch_valid && illegal_instr && buff_res.valid;
```

**Koşul**:
- Fetch geçerli
- Instruction recognized as illegal (control unit check)
- Buffer has valid response

**Priority**: `EXC_PRIORITY_ILLEGAL` (varsayılan: PRIORITY_4)

### 5. EBREAK
```systemverilog
has_ebreak = fetch_valid && (instr_type_o == ebreak);
```

**Koşul**: Instruction type = `ebreak`

**Priority**: `EXC_PRIORITY_EBREAK` (varsayılan: PRIORITY_5)

### 6. ECALL
```systemverilog
has_ecall = fetch_valid && (instr_type_o == ecall);
```

**Koşul**: Instruction type = `ecall`

**Priority**: `EXC_PRIORITY_ECALL` (varsayılan: PRIORITY_6)

### Exception Priority Selection

```systemverilog
// Tüm exception'lar tespit edilir, fakat sadece en yüksek priority
// olanı seçilir:

always_comb begin
    exc_type_o = NO_EXCEPTION;
    
    if (has_debug_breakpoint && check_exc_priority(EXC_PRIORITY_DEBUG_BREAKPOINT, PRIORITY_7)) begin
        exc_type_o = BREAKPOINT;
    end else if (has_instr_misaligned && check_exc_priority(EXC_PRIORITY_INSTR_MISALIGNED, PRIORITY_7)) begin
        exc_type_o = INSTR_MISALIGNED;
    end else if (has_instr_access_fault && check_exc_priority(EXC_PRIORITY_INSTR_ACCESS_FAULT, PRIORITY_7)) begin
        exc_type_o = INSTR_ACCESS_FAULT;
    // ... diğer exception'lar
    end
end

// Priority check fonksiyonu (ceres_param.sv):
function automatic logic check_exc_priority(input exc_priority_t exc_pri, input exc_priority_t min_pri);
    return (exc_pri <= min_pri) && (exc_pri != PRIORITY_DISABLED);
endfunction
```

---

## 🌳 Branch Prediction

### Gshare Predictor

Gshare Branch Predictor (`gshare_bp.sv`):

```systemverilog
predict_info_t spec_o;  // Output prediction

// Prediction structure:
typedef struct packed {
    logic [XLEN-1:0]  pc;      // Predicted target
    logic             taken;   // Prediction: taken/not taken
    logic [XLEN-1:0]  hist;    // History for later update
    logic             valid;   // Valid prediction
} predict_info_t;
```

### Return Address Stack (RAS)

RAS (`ras.sv`) size = 8 entries:

```systemverilog
localparam RAS_SIZE = 8;

typedef struct packed {
    logic            valid;     // Entry valid
    logic [XLEN-1:0] data;      // Return address
} ras_t;
```

**Kullanımı**:
- `JAL` (Jump and Link): Push return address
- `JALR` (Jump and Link Register): Pop or use predicted

---

## 🔗 Align Buffer & Compressed Decoder

### Align Buffer (`align_buffer.sv`)

16-bit ve 32-bit instruction'ları hizalar:

```systemverilog
// Request from cache
ilowX_req_t cache_req;

// Response with aligned instructions
typedef struct packed {
    logic [XLEN-1:0]  instr;     // 32-bit aligned instruction
    logic             valid;     // Valid instruction
    logic [XLEN-1:0]  addr;      // Instruction address
} abuff_res_t;
```

### Compressed Decoder (`compressed_decoder.sv`)

RV32C compressed instruction'ları 32-bit'e decode eder:

```systemverilog
// Input: 16-bit compressed instruction
logic [15:0]  comp_instr;

// Output: 32-bit expanded form
logic [31:0]  expanded_instr;

// Example: c.addi x1, 1 → addi x1, x1, 1
```

---

## 🎛️ I-Cache Interface

### I-Cache Request

```systemverilog
typedef struct packed {
    logic [XLEN-1:0]  addr;     // Fetch address
    logic             valid;    // Request valid
} ilowX_req_t;
```

### I-Cache Response

```systemverilog
typedef struct packed {
    logic [XLEN-1:0]  data;     // Instruction data
    logic             valid;    // Data valid
    logic             ready;    // Ready for next request
} ilowX_res_t;
```

### Cache Miss Handling

```systemverilog
assign imiss_stall_o = (!lx_ires_i.valid) && lx_ireq_o.valid;

// I-Cache miss → stall_cause = IMISS_STALL
```

---

## 💾 Dataflow Örneği

### Normal Instruction Fetch

```
Cycle 1:
    PC = 0x8000_0000
    lx_ireq_o = {addr: 0x8000_0000, valid: 1}
    
Cycle 2 (I-Cache hit):
    lx_ires_i = {data: 0x93, valid: 1}  // addi x1, x0, 1
    inst_o = 0x93
    pc_o = 0x8000_0000
    pc_incr_o = 0x8000_0004
    pc_next = 0x8000_0004
    
Cycle 3:
    PC = 0x8000_0004
    (next instruction fetch)
```

### Branch Taken

```
Cycle 3:
    beq x1, x0, 100  // Branch to 0x8000_0064
    spec_o.taken = 1
    spec_o.pc = 0x8000_0064
    pc_next = 0x8000_0064
    
Cycle 4:
    PC = 0x8000_0064
    (branch target instruction)
```

### Exception (DEBUG Breakpoint)

```
Cycle 2:
    has_debug_breakpoint = 1
    exc_type_o = BREAKPOINT
    
Cycle 3:
    trap_active_i = 1
    pc_next = ex_mtvec_i  // Handler address
    
Cycle 4:
    PC = ex_mtvec_i
    (exception handler)
```

---

## 🎨 Stall Handling

```systemverilog
// PC only updates when:
// 1. trap_active = true, OR
// 2. stall_i == NO_STALL, OR
// 3. flush_i = true

// Common stalls:
stall_e stall_reasons = {
    NO_STALL = 0,           // Normal
    LOAD_RAW_STALL = 1,     // Load-use hazard (from decode)
    IMISS_STALL = 2,        // I-Cache miss
    DMISS_STALL = 3,        // D-Cache miss
    ALU_STALL = 4,          // MUL/DIV latency
    FENCEI_STALL = 5        // FENCE.I memory barrier
};

// Fetch stage responds to ALL stall reasons
if (stall_i != NO_STALL) begin
    pc_en = 1'b0;  // PC doesn't advance
    // But new instruction request may still be issued
end
```

---

## 📊 Durum Diyagramı

```
FETCH STAGE STATE MACHINE:

┌─────────────────┐
│  IDLE/RESET     │
│  PC ← VECTOR    │
└────────┬────────┘
         │
         ▼
┌─────────────────────────┐
│  FETCH WAIT             │
│  • Issue I-Cache req    │
│  • Branch predict       │
│  • Exception detect     │
└────────┬────────────────┘
         │
    ┌────┴────┐
    │          │
    ▼          ▼
NORMAL    STALL/EXCEPTION
FETCH     
    │          │
    │    (pc_en = 0)
    │
    ▼
┌──────────────────────────┐
│  OUTPUT VALID            │
│  • inst_o valid          │
│  • exc_type_o set        │
│  • Branch spec output    │
└──────────────────────────┘
```

---

## 🔧 Configuration Parameters (ceres_param.sv)

```systemverilog
localparam RESET_VECTOR = 32'h8000_0000;  // Boot address
localparam RAS_SIZE = 8;                   // Return Address Stack
localparam IC_WAY = 8;                     // I-Cache ways
localparam IC_CAPACITY = 32 * (2**10) * 8; // I-Cache size
localparam misa_c_i = 1'b1;                // C extension enabled
```

---

## 📈 Timing & Latency

| Operation | Latency | Notes |
|-----------|---------|-------|
| Normal fetch | 1 cycle | I-Cache hit |
| I-Cache miss | 1-10+ cycles | Depends on memory |
| Branch prediction | 0 (comb) | Gshare predictor |
| Compressed decode | 0 (comb) | Part of fetch |
| Exception handling | 1 cycle | Pipeline flush + MTVEC |

---

## 🐛 Debug & Troubleshooting

### I-Cache Miss Debugging

```bash
# Trace shows imiss_stall_o = 1
# → Check lx_ires_i.valid
# → Check cache hit/miss rates
```

### Branch Misprediction

```bash
# spec_hit_i = 0
# → Branch was mispredicted
# → pc_target_i used for recovery
# → Next cycle: pc_next = pc_target_i
```

### Exception Not Taken

```bash
# Verify:
# 1. has_debug_breakpoint = 1 AND tdata1[2] = 1
# 2. pc_o == tdata2_i
# 3. check_exc_priority returns true
```

---

## 🎓 Sonraki Adımlar

- [Align Buffer (Detay)](./fetch_align_buffer.md)
- [Branch Predictor (Gshare)](./fetch_gshare.md)
- [Return Address Stack](./fetch_ras.md)
- [Decode Stage](./decode_stage.md)

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025

