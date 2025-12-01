---
title: "CPU Top Module - RTL"
description: "CPU Top module'ün pipeline orchestration ve kontrol mantığı"
date: 2025-12-01
draft: false
weight: 300
---

# CPU Top Module - Pipeline Orchestration

`cpu.sv` (698 satır) Ceres RISC-V processor'ünün kalbidir. Tüm pipeline aşamalarını koordine eder, veri transfer'ını kontrol eder ve hazard yönetimini gerçekleştirir.

---

## 📁 Dosya Konumu

```
rtl/core/cpu.sv
```

---

## 🎯 Temel Amaçlar

1. **Pipeline Orchestration**: 5 aşamayı senkronize etmek
2. **Data Flow Control**: Register'lar arasında veri taşıma
3. **Hazard Detection**: Data, Structural, Control hazard'ları tespit etmek
4. **Forward Unit**: Data bypass (forwarding) sağlamak
5. **Exception Handling**: Trap'ları yönetmek
6. **Stall Management**: Pipeline stall'ları kontrol etmek
7. **Memory Interface**: I/D cache'ye erişimi koordine etmek

---

## 🏗️ Genel Yapı

```
cpu.sv (Top)
├─ fetch.sv        (Stage 1)
├─ decode.sv       (Stage 2)
├─ execution.sv    (Stage 3)
├─ memory.sv       (Stage 4)
├─ writeback.sv    (Stage 5)
├─ hazard_unit.sv  (Control)
└─ (Tüm sub-modules)
```

---

## 📋 Module Interface

### Girişler

```systemverilog
input  logic       clk_i,          // Clock
input  logic       rst_ni,         // Active-low reset
input  iomem_req_t iomem_res_i,   // I/O memory response
input  logic       uart_rx_i,      // UART receive (periph)
```

### Çıkışlar

```systemverilog
output iomem_req_t iomem_req_o,    // I/O memory request
output logic       uart_tx_o,      // UART transmit (periph)
```

---

## 🔄 Pipeline Architecture

### 5-Stage Pipeline

```
┌─────┐     ┌─────┐     ┌─────┐     ┌─────┐     ┌─────┐
│ IF  │ --> │ ID  │ --> │ EX  │ --> │ MEM │ --> │ WB  │
│Stage│     │Stage│     │Stage│     │Stage│     │Stage│
└─────┘     └─────┘     └─────┘     └─────┘     └─────┘
  (1)         (2)         (3)         (4)         (5)
```

### Pipeline Registers

CPU, stage'ler arasında veriyi taşımak için **pipe register'lar** kullanır:

#### Pipe Register 1 (IF → ID)
```systemverilog
pipe1_t pipe1;  // Fetch sonuçlarını Decode'a gönder

typedef struct packed {
    logic [XLEN-1:0]  pc;          // Program Counter
    logic [XLEN-1:0]  inst;        // Instruction
    exc_type_e        exc_type;    // Exception
    instr_type_e      instr_type;  // Instruction type
    predict_info_t    spec;        // Branch prediction
    // ... diğer alanlar
} pipe1_t;
```

#### Pipe Register 2 (ID → EX)
```systemverilog
pipe2_t pipe2;  // Decode sonuçlarını Execute'a gönder

typedef struct packed {
    logic [XLEN-1:0]  pc;          // PC
    logic [XLEN-1:0]  r1_data;     // RS1 value
    logic [XLEN-1:0]  r2_data;     // RS2 value
    logic [XLEN-1:0]  imm;         // Immediate
    ctrl_t            ctrl;        // Control signals
    exc_type_e        exc_type;    // Exception
    // ... kontrol ve data sinyalleri
} pipe2_t;
```

#### Pipe Register 3 (EX → MEM)
```systemverilog
pipe3_t pipe3;  // Execute sonuçlarını Memory'e gönder
```

#### Pipe Register 4 (MEM → WB)
```systemverilog
pipe4_t pipe4;  // Memory sonuçlarını WB'e gönder
```

---

## 🎛️ Control Signals

### Stall Nedenleri (stall_e)

```systemverilog
typedef enum logic [2:0] {
    NO_STALL = 0,           // Normal operation
    LOAD_RAW_STALL = 1,     // Load-Use data hazard
    IMISS_STALL = 2,        // Instruction cache miss
    DMISS_STALL = 3,        // Data cache miss
    ALU_STALL = 4,          // ALU latency (MUL/DIV)
    FENCEI_STALL = 5        // FENCE.I memory barrier
} stall_e;
```

**Stall Priority** (en yüksek → en düşük):
1. FENCEI_STALL (Memory barrier - en ciddi)
2. ALU_STALL (MUL/DIV latency)
3. DMISS_STALL (Data cache miss)
4. IMISS_STALL (Instruction cache miss)
5. LOAD_RAW_STALL (Data hazard)

### Pipeline Enable/Disable

```systemverilog
// Her stage'in enable sinyali:
logic fe_enable;    // Fetch enable
logic de_enable;    // Decode enable
logic ex_enable;    // Execute enable
logic mem_enable;   // Memory enable
logic wb_enable;    // Write-back enable

// Stall → stage disable
fe_enable = !stall || trap;  // Flush sırasında enable
de_enable = fe_enable;
ex_enable = de_enable;
// ... vb.
```

---

## 🔀 Data Forwarding Unit

### Forwarding Paths

Forwarding, Load-Use RAW (Read-After-Write) hazard'ını azaltır:

```
Hazard:
    Cycle 1: lw x1, 0(x2)     (ID → EX → MEM → WB)
    Cycle 2: add x3, x1, x4   (IF → ID) *HAZARD* x1 henüz yazılmadı

Solution: Forward x1 from EX directly to ID
```

### Forward Multiplexers

```systemverilog
// Decode stage for RS1
always_comb begin
    if (ex_fwd_a[1]) begin
        // Forward from EX stage ALU result
        de_r1_data_actual = ex_alu_result;
    end else if (ex_fwd_a[0]) begin
        // Forward from WB stage
        de_r1_data_actual = wb_data;
    end else begin
        // No forward, use register file value
        de_r1_data_actual = de_r1_data;
    end
end

logic [1:0] ex_fwd_a;  // {from_wb, from_ex}
logic [1:0] ex_fwd_b;  // {from_wb, from_ex}
```

### Forward Flags

```systemverilog
// Forward from EX → ID
logic ex_fwd_a, ex_fwd_b;  // 2-bit each

// Forward from WB → ID
logic wb_fwd_a, wb_fwd_b;  // 1-bit each

// Hazard unit determines forwarding based on:
// 1. EX stage rd_addr == ID stage rs1/rs2
// 2. WB stage rd_addr == ID stage rs1/rs2
// 3. Write enable flags
```

---

## 🚫 Hazard Detection

### 1. Data Hazard (RAW - Read After Write)

```systemverilog
// Load-Use Hazard
logic load_use_hazard;
assign load_use_hazard = (ex_ctrl.mem_read) &&     // EX is a load
                         ((ex_rd_addr == de_rs1) || // and dest matches RS1
                          (ex_rd_addr == de_rs2));  // or RS2

if (load_use_hazard) begin
    stall_cause = LOAD_RAW_STALL;
    // Pipeline stalls for 1 cycle to wait for data
end
```

### 2. Structural Hazard

```systemverilog
// Register file write conflict
// All writes go through WB → no conflict (single-port read, WB writes)

// Memory access conflict handled by arbiter
// Multiple stage cache access → handled by memory arbiter
```

### 3. Control Hazard

```systemverilog
// Branch prediction speculation
logic spec_hit;  // Prediction was correct

if (!spec_hit) begin
    // Misprediction → flush pipeline
    flush_i = 1'b1;
    flush_pc_i = pc_target_i;  // Correct target from WB
    
    // Flush all in-flight instructions
    de_flush = 1'b1;
    ex_flush = 1'b1;
    mem_flush = 1'b1;
end
```

---

## 🔴 Exception Handling

### Exception Propagation Through Pipeline

Exception'lar pipeline'da ilerler:

```
Stage 1 (IF):
    exc_type_o → pipe1.exc_type
    
Stage 2 (ID):
    pipe1.exc_type + dec_exc → pipe2.exc_type
    
Stage 3 (EX):
    pipe2.exc_type + ex_exc → pipe3.exc_type
    
Stage 4 (MEM):
    pipe3.exc_type + mem_exc → pipe4.exc_type
    
Stage 5 (WB):
    pipe4.exc_type → Trap handler
    
PC ← MTVEC (Exception handler address)
```

### Exception Priority Management

```systemverilog
// Her stage'de exception prioritize edilir
// Parametrik exception priority sistemi (ceres_param.sv)

typedef enum logic [4:0] {
    PRIORITY_1,        // Highest
    PRIORITY_2,
    // ...
    PRIORITY_7,        // Lowest
    PRIORITY_DISABLED
} exc_priority_t;

// Örnek:
localparam EXC_PRIORITY_DEBUG = PRIORITY_1;       // En yüksek
localparam EXC_PRIORITY_MISALIGNED = PRIORITY_2;
localparam EXC_PRIORITY_ILLEGAL = PRIORITY_4;
localparam EXC_PRIORITY_ECALL = PRIORITY_6;       // En düşük
```

### Exception Handler

```systemverilog
if (trap_active) begin
    // Pipeline flush
    flush_i = 1'b1;
    
    // Set exception code in MCAUSE CSR
    ex_trap_cause = exc_type;
    
    // Save PC in MEPC CSR
    ex_trap_mepc = pc_at_exception;
    
    // Jump to handler
    pc_next = ex_mtvec;  // Machine Trap Vector
end
```

---

## 🔄 Pipeline Timing

### Clock-by-Clock Example: `add x3, x1, x2`

```
Cycle 1 (IF):
    ├─ PC = 0x8000_0000
    ├─ lx_ireq_o = {addr: 0x8000_0000, valid: 1}
    └─ (waiting for I-Cache)

Cycle 2 (IF hits, ID begins):
    ├─ lx_ires_i = {data: 0x38_0_3_15_33, valid: 1}  // add x3, x1, x2
    ├─ pipe1.inst = 0x38_0_3_15_33
    ├─ pipe1.pc = 0x8000_0000
    ├─ lx_ireq_o = {addr: 0x8000_0004, valid: 1}  (next fetch)
    └─ (decode begins)

Cycle 3 (ID continues, EX begins):
    ├─ pipe2.instr_type = r_add
    ├─ pipe2.r1_data = reg_file[1]  // x1 value
    ├─ pipe2.r2_data = reg_file[2]  // x2 value
    ├─ pipe1.inst = next_instruction
    └─ (execute begins)

Cycle 4 (EX continues, MEM begins):
    ├─ ex_alu_result = pipe2.r1_data + pipe2.r2_data
    ├─ pipe3.alu_result = result
    ├─ lx_dreq_o = (no memory access for ADD)
    └─ (memory stage, but no operation)

Cycle 5 (MEM continues, WB begins):
    ├─ pipe4.alu_result = ex_alu_result
    ├─ rf_wr_en = 1
    ├─ rf_wr_addr = 3  // x3
    └─ (write-back stage)

Cycle 6 (WB completes):
    ├─ reg_file[3] <= pipe4.alu_result  // x3 = x1 + x2
    └─ (result written)
```

---

## 💾 Memory Interface

### Instruction Memory (I-Cache)

```systemverilog
// CPU → I-Cache
ilowX_req_t lx_ireq_o;  // Instruction request
// CPU ← I-Cache
ilowX_res_t lx_ires_i;  // Instruction response

// Used by: fetch.sv
```

### Data Memory (D-Cache)

```systemverilog
// CPU → D-Cache
dlowX_req_t lx_dreq_o;  // Data request
// CPU ← D-Cache
dlowX_res_t lx_dres_i;  // Data response

// Used by: memory.sv
```

### I/O Memory Interface

```systemverilog
// CPU → Peripherals
iomem_req_t iomem_req_o;  // I/O request
// CPU ← Peripherals
iomem_res_t iomem_res_i;  // I/O response

// Used by: memory.sv (for peripheral access)
```

---

## 🔌 Sub-Module Instantiation

### Fetch Modülü

```systemverilog
fetch #(
    .RESET_VECTOR(RESET_VECTOR)
) i_fetch (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .stall_i(stall_cause),
    .flush_i(flush_i),
    .flush_pc_i(flush_pc),
    .pc_target_i(pc_target),
    .ex_mtvec_i(ex_mtvec),
    .trap_active_i(trap_active),
    // ...outputs...
    .lx_ireq_o(lx_ireq),
    .inst_o(fe_inst),
    .pc_o(fe_pc),
    .exc_type_o(fe_exc_type),
    // ...
);
```

### Decode Modülü

```systemverilog
decode i_decode (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .inst_i(pipe1.inst),
    .instr_type_i(pipe1.instr_type),
    .fwd_a_i(de_fwd_a),
    .fwd_b_i(de_fwd_b),
    .wb_data_i(wb_data),
    // ...
    .r1_data_o(de_r1_data),
    .r2_data_o(de_r2_data),
    .ctrl_o(de_ctrl),
    .exc_type_o(de_exc_type),
    // ...
);
```

### Execution Modülü

```systemverilog
execution i_execution (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .stall_i(stall_cause),
    .fwd_a_i(ex_fwd_a),
    .fwd_b_i(ex_fwd_b),
    .alu_result_i(pipe2.alu_result),
    .r1_data_i(pipe2.r1_data),
    .r2_data_i(pipe2.r2_data),
    // ...
    .alu_result_o(ex_alu_result),
    .pc_target_o(ex_pc_target),
    .exc_type_o(ex_exc_type),
    // ...
);
```

---

## 📊 State Machine

```
┌──────────────────────┐
│   RESET STATE        │
│ rst_ni = 0           │
│ PC ← RESET_VECTOR    │
│ All pipes flush      │
└────────┬─────────────┘
         │
    rst_ni = 1
         │
         ▼
┌──────────────────────┐
│   NORMAL OPERATION   │
│ • Fetch instruction  │
│ • Decode             │
│ • Execute            │
│ • Memory access      │
│ • Write-back         │
└────────┬─────────────┘
         │
    ┌────┴────┬────────────┐
    │          │            │
    ▼          ▼            ▼
 NORMAL     STALL      EXCEPTION
 FLOW       (pc_en=0)  (flush=1)
    │          │            │
    └────┬─────┴────────┬───┘
         │              │
         └──────────────┘
              │
         PC UPDATE
              │
              ▼
         NEXT CYCLE
```

---

## 🎨 Waveform Signals (Important)

| Signal | 宽度 | 설명 | 例 |
|--------|------|------|-----|
| clk_i | 1 | System clock | Toggle 1:1 |
| rst_ni | 1 | Reset (active low) | 0 → 1 |
| stall_cause | 3 | Pipeline stall | NO_STALL (0) |
| flush_i | 1 | Pipeline flush | 1 on exception |
| fe_pc | 32 | Fetch PC | 0x8000_0000 |
| fe_inst | 32 | Fetched instruction | 0x93 (addi) |
| de_r1_data | 32 | Register rs1 | 0x00000005 |
| de_r2_data | 32 | Register rs2 | 0x00000003 |
| ex_alu_result | 32 | ALU result | 0x00000008 |
| mem_addr | 32 | Memory address | 0x80000100 |
| mem_wdata | 32 | Write data | 0x12345678 |
| wb_rd_addr | 5 | Destination register | 5'b00011 (x3) |
| wb_rd_data | 32 | Write-back data | 0x00000042 |

---

## 🔧 Makefile Integration

```makefile
# Verilator compilation
verilator --trace -cc rtl/core/cpu.sv --top cpu \
    -I rtl/include \
    -I rtl/pkg

# Generate VCD waveform
vvp build/obj_dir/Vcpu__ALL.a -o cpu.vvp
vvp cpu.vvp -lxt
```

---

## 🎓 Sonraki Adımlar

- [Hazard Unit](../units/hazard_unit.md)
- [Decode Stage](./decode_stage.md)
- [Execute Stage](./execute_stage.md)
- [Memory Stage](./memory_stage.md)

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025

