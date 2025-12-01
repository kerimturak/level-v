---
title: "Decode Stage - stage02_decode"
description: "Instruction Decode (ID) aşaması - kontrol sinyalleri ve hazırlık"
date: 2025-12-01
draft: false
weight: 320
---

# Decode Stage: stage02_decode

Decode aşaması (`stage02_decode/`), Fetch'ten gelen 32-bit instruction'ı deşifre eder ve:
- Kontrol sinyalleri oluşturur (ALU işlemi, register yazma, vb.)
- Register dosyasından operand değerlerini okur
- Immediate değerleri genişletir
- Hazırlık işlemleri yapar

---

## 📁 Modüller

Decode aşaması 4 modülden oluşur:

| Modül | Satır | Görev |
|-------|-------|-------|
| `decode.sv` | 66 | ID pipeline aşamasının orchestration'ı |
| `control_unit.sv` | 345 | Instruction decode ve kontrol sinyalleri |
| `reg_file.sv` | 40 | 32 adet 32-bit register (x0-x31) |
| `extend.sv` | 50 | Immediate değer genişletme |

---

## 🏗️ Block Diagram

```
┌─────────────────────────────────────────────┐
│        Decode Stage (ID)                    │
├─────────────────────────────────────────────┤
│                                             │
│  ┌──────────────┐                          │
│  │ From Fetch   │                          │
│  │ (inst_i)     │                          │
│  └────────┬─────┘                          │
│           │                                 │
│           ▼                                 │
│  ┌──────────────────────────────────────┐  │
│  │  Control Unit                        │  │
│  │  (instruction decode)                │  │
│  │  - Opcode analysis                   │  │
│  │  - ALU operation selection           │  │
│  │  - Control signals generation        │  │
│  │  - Exception detection               │  │
│  └──┬────────────────┬────────────────┬──  │
│     │                │                │    │
│     ▼                ▼                │    │
│  ┌────────────┐ ┌───────────────┐   │    │
│  │ Register   │ │ Extend        │   │    │
│  │ File       │ │ (Immediate)   │   │    │
│  │ (Read)     │ │               │   │    │
│  │ r1, r2     │ │ I-type,S-type │   │    │
│  │            │ │ U-type, etc.  │   │    │
│  └─┬──────────┘ └────────┬──────┘   │    │
│    │                     │          │    │
│    └─────────┬───────────┴──────────┘    │
│              │                           │
│              ▼                           │
│  ┌─────────────────────────────────────┐ │
│  │  To Execute Stage                   │ │
│  │  - r1_data_o, r2_data_o             │ │
│  │  - Control signals (ctrl_o)         │ │
│  │  - Immediate (imm_o)                │ │
│  │  - Exception type (exc_type_o)      │ │
│  └─────────────────────────────────────┘ │
│                                          │
└──────────────────────────────────────────┘
```

---

## 📊 Data Structures

### Control Signals Struct (ctrl_t)

```systemverilog
typedef struct packed {
    logic [1:0]  result_src;      // WB source selection
    logic [6:0]  alu_ctrl;        // ALU operation
    logic        alu_in1_sel;     // ALU input 1 selection
    logic        alu_in2_sel;     // ALU input 2 selection
    logic        rf_rw_en;        // Register file write enable
    logic        wr_en;           // Data cache write enable
    logic        dcache_valid;    // Data cache request valid
    logic [1:0]  rw_size;         // Read/Write size (byte/half/word)
    logic        csr_or_data;     // CSR vs data selection
    logic        rd_csr;          // Read CSR
    logic        wr_csr;          // Write CSR
    logic [2:0]  imm_sel;         // Immediate type selector
    logic [3:0]  pc_sel;          // PC selection (branch type)
    logic [11:0] csr_idx;         // CSR index
    exc_type_e   exc_type;        // Exception type
} ctrl_t;
```

### Instruction Type Enum

```systemverilog
typedef enum logic [5:0] {
    // R-type
    r_add, r_sub, r_sll, r_slt, r_sltu, r_xor, r_srl, r_sra, r_or, r_and,
    // Multiply/Divide
    r_mul, r_mulh, r_mulhsu, r_mulhu, r_div, r_divu, r_rem, r_remu,
    // I-type
    i_addi, i_slti, i_sltiu, i_xori, i_ori, i_andi, i_slli, i_srli, i_srai,
    // I-type Load
    i_lb, i_lh, i_lw, i_lbu, i_lhu,
    // I-type Jump
    i_jalr,
    // S-type Store
    s_sb, s_sh, s_sw,
    // B-type Branch
    b_beq, b_bne, b_blt, b_bge, b_bltu, b_bgeu,
    // U-type
    u_lui, u_auipc,
    // J-type
    u_jal,
    // CSR
    CSR_RW, CSR_RS, CSR_RC, CSR_RWI, CSR_RSI, CSR_RCI
} instr_type_e;
```

---

## 🔧 Decode.sv - Orchestration

### Interface

```systemverilog
module decode
  import ceres_param::*;
(
    // Clock & Reset
    input  logic                   clk_i,
    input  logic                   rst_ni,
    
    // Instruction & Forwarding
    input  inst_t                  inst_i,        // From Fetch
    input  logic                   fwd_a_i,       // Forward signal A
    input  logic                   fwd_b_i,       // Forward signal B
    input  logic        [XLEN-1:0] wb_data_i,     // Write-back data
    
    // Register file write
    input  logic        [     4:0] rd_addr_i,     // Write address
    input  logic                   rf_rw_en_i,    // Write enable
    
    // Instruction type (from Fetch)
    input  instr_type_e            instr_type_i,  // Decoded type
    
    // Outputs
    output logic        [XLEN-1:0] r1_data_o,     // Source 1 data
    output logic        [XLEN-1:0] r2_data_o,     // Source 2 data
    output ctrl_t                  ctrl_o,        // Control signals
    output logic        [XLEN-1:0] imm_o,         // Immediate value
    output exc_type_e              exc_type_o     // Exception type
);
```

### Data Forwarding Logic

```systemverilog
always_comb begin
    // If forwarding enabled, use WB data instead of register file
    r1_data_o  = fwd_a_i ? wb_data_i : r1_data;
    r2_data_o  = fwd_b_i ? wb_data_i : r2_data;
    
    // Pass through exception from control unit
    exc_type_o = ctrl_o.exc_type;
end
```

**Forwarding İlişkisi**:
- `fwd_a_i = 1`: Register 1 yerine WB data'sı kullan (RAW hazard çözümü)
- `fwd_b_i = 1`: Register 2 yerine WB data'sı kullan

---

## 🎛️ Control Unit - Instruction Decode

### Görevler

1. **Opcode Analysis**: Instruction type'ı belirle
2. **ALU Operation**: Hangi ALU işlemi yapılacak?
3. **Register Writes**: Register dosyasına yazma olacak mı?
4. **Memory Operations**: Load/Store mı?
5. **PC Selection**: Branch mı?
6. **Exception Detection**: İllegal instruction mı?

### Opcode Routing

```systemverilog
case (inst_i.opcode)
    op_r_type: begin           // ADD, SUB, SLL, SLT, ...
        ctrl_o.rf_rw_en    = 1'b1;     // Register yazma
        ctrl_o.alu_in2_sel = 1'b0;     // ALU input 2 = register
        ctrl_o.wr_en       = 1'b0;     // Memory yazma yok
        ctrl_o.imm_sel     = NO_IMM;   // Immediate yok
    end
    
    op_i_type: begin           // ADDI, SLLI, SLTI, ...
        ctrl_o.rf_rw_en    = 1'b1;
        ctrl_o.alu_in2_sel = 1'b1;     // ALU input 2 = immediate
        ctrl_o.imm_sel     = I_IMM;    // 12-bit signed immediate
    end
    
    op_i_type_load: begin      // LW, LH, LB, ...
        ctrl_o.rf_rw_en    = 1'b1;     // Register yazma
        ctrl_o.wr_en       = 1'b0;     // Memory yazma yok
        ctrl_o.result_src  = 2'b01;    // WB source = memory data
        ctrl_o.dcache_valid = 1'b1;    // Data cache request
        ctrl_o.imm_sel     = I_IMM;
    end
    
    op_s_type: begin           // SW, SH, SB, ...
        ctrl_o.rf_rw_en    = 1'b0;     // Register yazma yok
        ctrl_o.wr_en       = 1'b1;     // Memory yazma var
        ctrl_o.dcache_valid = 1'b1;
        ctrl_o.imm_sel     = S_IMM;    // 12-bit signed (store offset)
    end
    
    op_b_type: begin           // BEQ, BNE, BLT, ...
        ctrl_o.rf_rw_en    = 1'b0;     // Register yazma yok
        ctrl_o.imm_sel     = B_IMM;    // 13-bit branch offset
        ctrl_o.pc_sel      = (BEQ/BNE/BLT/...);  // Branch type
    end
    
    op_u_type: begin           // LUI, AUIPC
        ctrl_o.rf_rw_en    = 1'b1;
        ctrl_o.imm_sel     = U_IMM;    // 20-bit upper immediate
    end
    
    op_j_type: begin           // JAL
        ctrl_o.rf_rw_en    = 1'b1;     // rd = PC + 4 (return address)
        ctrl_o.result_src  = 2'b10;    // WB source = PC + 4
        ctrl_o.imm_sel     = J_IMM;    // 20-bit branch offset
    end
    
    op_i_type_jump: begin      // JALR
        ctrl_o.rf_rw_en    = 1'b1;
        ctrl_o.alu_in1_sel = 2'b1;     // ALU input 1 = PC (for link)
        ctrl_o.imm_sel     = I_IMM;
        ctrl_o.pc_sel      = JALR;
    end
endcase
```

### ALU Operation Selection

```systemverilog
case (instr_type_i)
    // Arithmetic
    r_add, i_addi, i_lw, s_sw: ctrl_o.alu_ctrl = OP_ADD;
    r_sub:                      ctrl_o.alu_ctrl = OP_SUB;
    
    // Logical
    r_and, i_andi:              ctrl_o.alu_ctrl = OP_AND;
    r_or,  i_ori:               ctrl_o.alu_ctrl = OP_OR;
    r_xor, i_xori:              ctrl_o.alu_ctrl = OP_XOR;
    
    // Shifts
    r_sll, i_slli:              ctrl_o.alu_ctrl = OP_SLL;
    r_srl, i_srli:              ctrl_o.alu_ctrl = OP_SRL;
    r_sra, i_srai:              ctrl_o.alu_ctrl = OP_SRA;
    
    // Comparisons
    r_slt,  i_slti:             ctrl_o.alu_ctrl = OP_SLT;
    r_sltu, i_sltiu:            ctrl_o.alu_ctrl = OP_SLTU;
    
    // Multiply/Divide
    r_mul:                      ctrl_o.alu_ctrl = OP_MUL;
    r_div:                      ctrl_o.alu_ctrl = OP_DIV;
    
    // CSR
    CSR_RW, CSR_RWI:            ctrl_o.alu_ctrl = OP_CSRRW;
    CSR_RS, CSR_RSI:            ctrl_o.alu_ctrl = OP_CSRRS;
    CSR_RC, CSR_RCI:            ctrl_o.alu_ctrl = OP_CSRRC;
    
    default:                    ctrl_o.alu_ctrl = OP_ADD;
endcase
```

### Exception Detection

```systemverilog
// Örnek 1: İllegal Shift
if (illegal_shift) begin
    ctrl_o.exc_type = ILLEGAL_INSTRUCTION;
end

// Örnek 2: Desteklenmeyen CSR
else if (instr_is_csr && !csr_supported) begin
    ctrl_o.exc_type = ILLEGAL_INSTRUCTION;
end

// Örnek 3: Read-only CSR'ye yazma
else if (instr_is_csr && csr_read_only && csr_write_intent) begin
    ctrl_o.exc_type = ILLEGAL_INSTRUCTION;
end
```

---

## 💾 Register File - reg_file.sv

### Purpose

32 adet 32-bit register (x0-x31) saklar ve:
- **Asynchronous Read**: Bir cycle'da 2 register oku
- **Synchronous Write**: Clock edge'te 1 register yaz
- **x0 Special**: Her zaman 0'dır

### Interface

```systemverilog
module reg_file #(
    parameter XLEN = 32
) (
    // Clock & Reset
    input  logic            clk_i,
    input  logic            rst_ni,
    
    // Write Port
    input  logic            rw_en_i,           // Write enable
    input  logic [     4:0] waddr_i,           // Write address
    input  logic [XLEN-1:0] wdata_i,           // Write data
    
    // Read Ports (Asynchronous)
    input  logic [     4:0] r1_addr_i,         // Read address 1
    input  logic [     4:0] r2_addr_i,         // Read address 2
    output logic [XLEN-1:0] r1_data_o,         // Read data 1
    output logic [XLEN-1:0] r2_data_o          // Read data 2
);
```

### Implementation

```systemverilog
logic [XLEN-1:0] registers[31:0];  // 32 × 32-bit registers

// Asynchronous Read (combinational)
always_comb begin : register_read
    r1_data_o = registers[r1_addr_i];  // x0 → 0 (by default)
    r2_data_o = registers[r2_addr_i];
end

// Synchronous Write (sequential)
always_ff @(posedge clk_i) begin : register_write
    if (!rst_ni) begin
        registers <= '{default: 0};  // Reset all to 0
    end else if (rw_en_i && waddr_i != 5'b0) begin
        registers[waddr_i] <= wdata_i;  // x0 yazma engellenir!
    end
end
```

### Register Naming (ABI)

| x0 | x1 | x2 | x3 | x4 | x5-x7 | x8 | x9 | x10-x11 | x12-x17 | x18-x27 | x28-x31 |
|----|----|----|----|----|-------|----|----|---------|---------|---------|---------|
| zero | ra | sp | gp | tp | t0-t2 | s0 | s1 | a0-a1 | a2-a7 | s2-s11 | t3-t6 |

---

## 🔢 Immediate Generation - extend.sv

### Purpose

Instruction'daki immediate bits'i XLEN (32-bit) genişletir.

### Immediate Types

```systemverilog
typedef enum logic [2:0] {
    I_IMM,      // I-type: 12-bit signed
    S_IMM,      // S-type: 12-bit signed (store)
    B_IMM,      // B-type: 13-bit signed (branch)
    U_IMM,      // U-type: 20-bit upper
    J_IMM,      // J-type: 20-bit signed (jump)
    I_USIMM,    // I-type: 12-bit unsigned (shift amount)
    CSR_IMM     // CSR immediate (5-bit zimm)
} imm_e;
```

### Immediate Extraction & Sign Extension

```systemverilog
always_comb begin : immediate_generator
    case (sel_i)
        // I-type: bits[31:20] sign-extended
        I_IMM: imm_o = {{20{imm_i[31]}}, imm_i[31:20]};
        
        // I-type unsigned: bits[31:20] zero-extended (shifts)
        I_USIMM: imm_o = {{20{1'b0}}, imm_i[31:20]};
        
        // S-type: bits[31:25] || bits[11:7] sign-extended
        S_IMM: imm_o = {{20{imm_i[31]}}, imm_i[31:25], imm_i[11:7]};
        
        // B-type: bits[31,7] || bits[30:25,11:8] || 1'b0 (branch offset)
        B_IMM: imm_o = {{20{imm_i[31]}}, imm_i[7], imm_i[30:25], imm_i[11:8], 1'b0};
        
        // U-type: bits[31:12] || 12'b0 (upper immediate)
        U_IMM: imm_o = {imm_i[31:12], 12'b0};
        
        // J-type: bits[31,19:12,20,30:21] || 1'b0 (jump offset)
        J_IMM: imm_o = {{12{imm_i[31]}}, imm_i[19:12], imm_i[20], imm_i[30:21], 1'b0};
        
        // CSR immediate: 5-bit zimm (register index)
        CSR_IMM: imm_o = {27'b0, imm_i[19:15]};
        
        default: imm_o = '0;
    endcase
end
```

### Instruction Format Reference

```
I-type:  [31:20] = imm[11:0]
         imm = {{20{inst[31]}}, inst[31:20]}

S-type:  [31:25] = imm[11:5], [11:7] = imm[4:0]
         imm = {{20{inst[31]}}, inst[31:25], inst[11:7]}

B-type:  [31] = imm[12], [30:25] = imm[10:5]
         [11:8] = imm[4:1], [7] = imm[11]
         imm = {{20{inst[31]}}, inst[7], inst[30:25], inst[11:8], 1'b0}

U-type:  [31:12] = imm[31:12]
         imm = {inst[31:12], 12'b0}

J-type:  [31] = imm[20], [19:12] = imm[19:12]
         [20] = imm[11], [30:21] = imm[10:1]
         imm = {{12{inst[31]}}, inst[19:12], inst[20], inst[30:21], 1'b0}
```

---

## 📈 Dataflow Example

### Örnek: `ADD x3, x1, x2`

```
Hex: 0x00208233
     opcode=0x33 (R-type ADD)
     rd=x3 (bits[11:7]=0b00011)
     funct3=0b000
     rs1=x1 (bits[19:15]=0b00001)
     rs2=x2 (bits[24:20]=0b00010)
     funct7=0b0000000

IF → ID (Cycle N):
├─ Instruction: 0x00208233
└─ Decode detects: R-type ADD

Control Unit (Cycle N):
├─ instr_type_i = r_add
├─ ctrl_o.alu_ctrl = OP_ADD
├─ ctrl_o.rf_rw_en = 1 (x3 yazılacak)
├─ ctrl_o.alu_in2_sel = 0 (rs2 kullan)
├─ ctrl_o.imm_sel = NO_IMM
└─ ctrl_o.exc_type = NO_EXCEPTION

Register File (Cycle N):
├─ Read x1 → r1_data = (x1 değeri)
├─ Read x2 → r2_data = (x2 değeri)
└─ Asynchronous, immediate result

Output (Cycle N):
├─ r1_data_o = value of x1
├─ r2_data_o = value of x2
├─ ctrl_o = {ADD, write enable, ...}
├─ imm_o = 0 (unused)
└─ exc_type_o = NO_EXCEPTION
```

### Örnek: `ADDI x5, x6, 100`

```
Hex: 0x06430293
     opcode=0x13 (I-type)
     rd=x5, rs1=x6, imm=100

Decode (Cycle N):
├─ instr_type_i = i_addi
├─ ALU operation: OP_ADD
├─ alu_in2_sel = 1 (immediate kullan)
├─ imm_sel = I_IMM
└─ rf_rw_en = 1

Register File (Cycle N):
├─ Read x6 → r1_data_o = (x6 değeri)
└─ r2_data_o = (unused for this instruction)

Extend (Cycle N):
├─ Input: 0x064 (bits[31:20])
├─ Sign extend: 0x00000064
└─ imm_o = 100

Output (Cycle N):
├─ r1_data_o = value of x6
├─ imm_o = 100
├─ ctrl_o = {OP_ADD, alu_in2_sel=1, ...}
└─ Execute will compute: x5 = x6 + 100
```

### Örnek: `LW x8, 0(x7)` (Load Word)

```
Hex: 0x00038403
     opcode=0x03 (Load)
     rd=x8, rs1=x7, offset=0

Control Unit (Cycle N):
├─ instr_type_i = i_lw
├─ ctrl_o.result_src = 2'b01 (memory data select)
├─ ctrl_o.dcache_valid = 1 (data cache request)
├─ ctrl_o.rw_size = 2'b11 (32-bit word)
├─ ctrl_o.rf_rw_en = 1 (x8 yazılacak)
└─ ctrl_o.wr_en = 0 (memory yazma yok)

Register File (Cycle N):
├─ Read x7 → r1_data_o = (x7 değeri = base address)
└─ r2_data_o = (unused)

Extend (Cycle N):
├─ Extract bits[31:20] = 0x000
├─ Sign extend: 0x00000000
└─ imm_o = 0

Output (Cycle N):
├─ r1_data_o = base address (x7)
├─ imm_o = 0 (offset)
├─ ctrl_o = {memory read, result_src=MEM, ...}
└─ Execute: compute address = x7 + 0, send to data cache
```

---

## 🔄 Pipeline Integration

### Data Flow (Decode → Execute)

```
Decode Stage Output (End of Cycle N)
    ↓
┌─────────────────────────────────────┐
│ Pipe Register 2 (pipe2_t)           │
│ ├─ r1_data, r2_data                 │
│ ├─ ctrl (control signals)           │
│ ├─ imm (immediate)                  │
│ ├─ rd_addr (destination register)   │
│ ├─ pc_next (for branch links)       │
│ └─ exception (exc_type)             │
└────────────┬────────────────────────┘
             │
         Pipeline Register
         (synchronized by clock)
             │
             ▼
    Execute Stage (Cycle N+1)
```

### Timing (3-stage pipeline example)

```
Cycle  Fetch  Decode  Execute
────────────────────────────
 0      IF1    -       -
 1      IF2    ID1     -
 2      IF3    ID2     EX1
 3      -      ID3     EX2
 ...
```

---

## 🎯 Summary

| Aspect | Details |
|--------|---------|
| **Purpose** | Instruction decode, register read, immediate generation |
| **Key Outputs** | 2 register operands, immediate value, control signals |
| **Latency** | 1 cycle (combinational + register read) |
| **Exception Detection** | Illegal instruction, CSR violations |
| **Forwarding Support** | Yes (data bypassing for RAW hazards) |
| **Register Count** | 32 × 32-bit (RISC-V standard) |

---

## 📚 Sonraki Adımlar

- [Execute Stage](./EXECUTE_STAGE.md)
- [Memory Stage](./MEMORY_STAGE.md)
- [Register Forwarding](./forwarding.md)

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025

