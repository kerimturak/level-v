---
title: "Execute Stage - stage03_execute"
description: "ALU işlemleri, CSR yönetimi, Multiply/Divide"
date: 2025-12-01
draft: false
weight: 330
---

# Execute Stage: stage03_execute

Execute aşaması (`stage03_execute/`), tüm komput işlemlerini gerçekleştirir:
- **Aritmetik ve Mantıksal İşlemler** (ALU)
- **Kontrol & Status Registers** (CSR)
- **Çarpma (Multiply)** - Multi-cycle işlem
- **Bölme (Divide)** - Multi-cycle işlem

---

## 📁 Modüller

| Modül | Satır | Görev |
|-------|-------|-------|
| `execution.sv` | 173 | Execute aşaması orchestration'ı |
| `alu.sv` | 376 | ALU operasyonları (ADD, SUB, SHL, vb.) |
| `cs_reg_file.sv` | 425 | CSR yönetimi (mstatus, mepc, mcause, vb.) |
| `mul_div/` | - | Multiply/Divide alt-modülleri |

---

## 🏗️ Block Diagram

```
┌──────────────────────────────────────────────┐
│      Execute Stage (EX)                      │
├──────────────────────────────────────────────┤
│                                              │
│  ┌───────────────────────────────────────┐  │
│  │  Data Forwarding & Operand Selection  │  │
│  │  ├─ fwd_a_i: ALU result / WB data     │  │
│  │  ├─ fwd_b_i: ALU result / WB data     │  │
│  │  └─ operand_a, operand_b ready       │  │
│  └────────┬───────────────────────────────┘  │
│           │                                   │
│  ┌────────▼───────────────────────────────┐  │
│  │  ALU (Arithmetic Logic Unit)           │  │
│  │  ├─ Basic: ADD, SUB, AND, OR, XOR     │  │
│  │  ├─ Shift: SLL, SRL, SRA              │  │
│  │  ├─ Compare: SLT, SLTU                │  │
│  │  ├─ Multiply: MUL, MULH, ...          │  │
│  │  └─ Divide: DIV, DIVU, REM, REMU     │  │
│  └────────┬──────────────────────────────┘  │
│           │                                   │
│  ┌────────▼──────────────┐   ┌───────────┐ │
│  │  CSR Register File    │   │ PC Target │ │
│  │  ├─ Read CSR values   │   │ Calc      │ │
│  │  ├─ Write on CSR ops  │   │ (branches)│ │
│  │  └─ Exception updates │   │           │ │
│  └───────────────────────┘   └───────────┘ │
│                                              │
│  ┌──────────────────────────────────────┐  │
│  │  To Memory Stage                     │  │
│  │  ├─ alu_result_o                     │  │
│  │  ├─ write_data_o (store data)        │  │
│  │  ├─ pc_target_o (for branches)       │  │
│  │  └─ exc_type_o (exceptions)          │  │
│  └──────────────────────────────────────┘  │
│                                              │
└──────────────────────────────────────────────┘
```

---

## 💾 ALU Module - alu.sv

### Purpose

ALU, tüm aritmetik, mantıksal, çarpma ve bölme işlemlerini gerçekleştirir.

### Interface

```systemverilog
module alu
  import ceres_param::*;
(
    input  logic               clk_i,
    input  logic               rst_ni,
    
    // Operands
    input  logic    [XLEN-1:0] alu_a_i,       // Operand A
    input  logic    [XLEN-1:0] alu_b_i,       // Operand B
    input  logic    [XLEN-1:0] csr_rdata_i,   // CSR read data (for CSR ops)
    
    // Operation selection
    input  alu_op_e            op_sel_i,      // Operation selector
    
    // Outputs
    output logic    [XLEN-1:0] alu_o,         // Result
    output logic               zero_o,        // Result is zero
    output logic               slt_o,         // Signed less-than
    output logic               sltu_o,        // Unsigned less-than
    output logic               alu_stall_o    // Stall (for MUL/DIV)
);
```

### ALU Operations (alu_op_e)

```systemverilog
typedef enum logic [6:0] {
    // Basic Arithmetic
    OP_ADD,        // Addition
    OP_SUB,        // Subtraction
    
    // Logical
    OP_AND,        // AND
    OP_OR,         // OR
    OP_XOR,        // XOR
    
    // Shifts
    OP_SLL,        // Shift Left Logical
    OP_SRL,        // Shift Right Logical
    OP_SRA,        // Shift Right Arithmetic
    
    // Comparisons
    OP_SLT,        // Set if Less Than (signed)
    OP_SLTU,       // Set if Less Than Unsigned
    
    // Special
    OP_LUI,        // Load Upper Immediate
    
    // Multiply (multi-cycle)
    OP_MUL,        // Multiply (lower 32-bits)
    OP_MULH,       // Multiply High (signed × signed)
    OP_MULHSU,     // Multiply High (signed × unsigned)
    OP_MULHU,      // Multiply High (unsigned × unsigned)
    
    // Divide (multi-cycle)
    OP_DIV,        // Divide (signed)
    OP_DIVU,       // Divide (unsigned)
    OP_REM,        // Remainder (signed)
    OP_REMU,       // Remainder (unsigned)
    
    // CSR Operations
    OP_CSRRW,      // CSR Read/Write
    OP_CSRRS,      // CSR Read/Set Bits
    OP_CSRRC,      // CSR Read/Clear Bits
    OP_CSRRWI,     // CSR Read/Write Immediate
    OP_CSRRSI,     // CSR Read/Set Bits Immediate
    OP_CSRRCI       // CSR Read/Clear Bits Immediate
} alu_op_e;
```

### ALU Results Structure

```systemverilog
typedef struct packed {
    logic [XLEN-1:0]   ADD;        // Addition result
    logic [XLEN-1:0]   SUB;        // Subtraction result
    logic [XLEN-1:0]   AND;        // AND result
    logic [XLEN-1:0]   OR;         // OR result
    logic [XLEN-1:0]   XOR;        // XOR result
    logic [XLEN-1:0]   SLL;        // Shift left result
    logic [XLEN-1:0]   SRL;        // Shift right logical
    logic [XLEN-1:0]   SRA;        // Shift right arithmetic
    logic [XLEN-1:0]   SLT;        // Signed comparison result
    logic [XLEN-1:0]   SLTU;       // Unsigned comparison result
    logic [XLEN-1:0]   LUI;        // Upper immediate
    logic [XLEN-1:0]   DIV;        // Division quotient
    logic [XLEN-1:0]   DIVU;       // Unsigned division
    logic [XLEN-1:0]   REM;        // Division remainder
    logic [XLEN-1:0]   REMU;       // Unsigned remainder
    logic [XLEN-1:0]   MUL;        // Multiply low
    logic [2*XLEN-1:0] MULH;       // Multiply high (signed)
    logic [2*XLEN-1:0] MULHSU;     // Multiply high (mixed)
    logic [2*XLEN-1:0] MULHU;      // Multiply high (unsigned)
} result_t;
```

### Temel ALU Operasyonları

```systemverilog
// Aritmetik
rslt.ADD  = alu_a_i + alu_b_i;
rslt.SUB  = alu_a_i - alu_b_i;

// Mantıksal
rslt.AND  = alu_a_i & alu_b_i;
rslt.OR   = alu_a_i | alu_b_i;
rslt.XOR  = alu_a_i ^ alu_b_i;

// Kaymalar (shift amount = alu_b_i[4:0] for RV32)
rslt.SLL  = alu_a_i << alu_b_i[4:0];
rslt.SRL  = alu_a_i >> alu_b_i[4:0];
rslt.SRA  = $signed(alu_a_i) >>> alu_b_i[4:0];

// Karşılaştırmalar
rslt.SLT  = {31'b0, $signed(alu_a_i) < $signed(alu_b_i)};
rslt.SLTU = {31'b0, alu_a_i < alu_b_i};

// LUI (upper immediate)
rslt.LUI  = {alu_b_i[19:0], 12'b0};
```

### Multiply Operation

```systemverilog
// 32×32 multiplier (Wallace tree or similar)
// Output: 64-bit product

if (mul_type) begin
    case (op_sel_i)
        // MUL: Signed × Signed → Lower 32 bits
        OP_MUL: begin
            mul_op_A = abs_A;
            mul_op_B = abs_B;
            mul_sign = alu_a_i[31] ^ alu_b_i[31];  // Sign of result
            // product[31:0] → alu_result
        end
        
        // MULH: Signed × Signed → Upper 32 bits
        OP_MULH: begin
            mul_op_A = abs_A;
            mul_op_B = abs_B;
            mul_sign = alu_a_i[31] ^ alu_b_i[31];
            // product[63:32] → alu_result
        end
        
        // MULHSU: Signed × Unsigned → Upper 32 bits
        OP_MULHSU: begin
            mul_op_A = abs_A;           // |rs1|
            mul_op_B = alu_b_i;         // rs2 (unsigned)
            mul_sign = alu_a_i[31];     // Sign of result = sign(rs1)
        end
        
        // MULHU: Unsigned × Unsigned → Upper 32 bits
        OP_MULHU: begin
            mul_op_A = alu_a_i;         // No sign correction
            mul_op_B = alu_b_i;
            mul_sign = 1'b0;            // Always positive
        end
    endcase
    
    // Sign correction on result
    unsigned_prod = mul_op_A * mul_op_B;
    product = mul_sign ? (~unsigned_prod + 1) : unsigned_prod;
end
```

### Divide Operation

```systemverilog
// Non-restoring or radix-2 divider

if (div_type) begin
    case (op_sel_i)
        // DIV: Signed ÷ Signed
        OP_DIV: begin
            div_op_A = abs_A;
            div_op_B = abs_B;
            div_sign_quot = alu_a_i[31] ^ alu_b_i[31];  // Sign of quotient
            div_sign_rem  = alu_a_i[31];                // Sign of remainder
        end
        
        // DIVU: Unsigned ÷ Unsigned
        OP_DIVU: begin
            div_op_A = alu_a_i;
            div_op_B = alu_b_i;
            div_sign_quot = 1'b0;
            div_sign_rem  = 1'b0;
        end
        
        // REM: Signed remainder
        OP_REM: begin
            div_op_A = abs_A;
            div_op_B = abs_B;
            div_sign_rem  = alu_a_i[31];
        end
        
        // REMU: Unsigned remainder
        OP_REMU: begin
            div_op_A = alu_a_i;
            div_op_B = alu_b_i;
            div_sign_rem = 1'b0;
        end
    endcase
    
    // Execute division
    unsigned_quo = div_op_A / div_op_B;
    unsigned_rem = div_op_A % div_op_B;
    
    // Sign correction
    quotient = div_sign_quot ? (~unsigned_quo + 1) : unsigned_quo;
    remainder = div_sign_rem ? (~unsigned_rem + 1) : unsigned_rem;
end
```

### Multi-Cycle Stall

```systemverilog
// ALU stalls when MUL or DIV operations are in progress
always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
        alu_stall_q <= 1'b0;
    end else if (mul_start || div_start) begin
        alu_stall_q <= 1'b1;  // Start stalling
    end else if (mul_done || div_done) begin
        alu_stall_q <= 1'b0;  // Stop stalling
    end
end

assign alu_stall_o = alu_stall_q;
```

---

## 🔧 CSR Module - cs_reg_file.sv

### Purpose

RISC-V Machine Mode CSR'ları (Control & Status Registers) yönetir.

### CSR Address Map

```
// Machine Information
0xF11: mvendorid   (R)    Vendor ID
0xF12: marchid     (R)    Architecture ID
0xF13: mimpid      (R)    Implementation ID
0xF14: mhartid     (R)    Hart ID
0xF15: mconfigptr  (R)    Configuration Pointer

// Trap Setup
0x300: mstatus     (RW)   Machine Status
0x301: misa        (RW)   ISA and Extensions
0x304: mie         (RW)   Machine Interrupt Enable
0x305: mtvec       (RW)   Machine Trap Vector
0x306: mcounteren  (RW)   Counter Enable

// Trap Handling
0x340: mscratch    (RW)   Scratch Register
0x341: mepc        (RW)   Exception PC
0x342: mcause      (RW)   Exception Cause
0x343: mtval       (RW)   Exception Value
0x344: mip         (RW)   Machine Interrupt Pending

// Counters
0xB00: mcycle      (RW)   Cycle Counter
0xB02: minstret    (RW)   Instruction Counter
0xB80: mcycleh     (RW)   Cycle Counter High (RV32)
0xB82: minstreth   (RW)   Instruction Counter High (RV32)

// Debug/Trigger
0x7A0: tselect     (RW)   Trigger Select
0x7A1: tdata1      (RW)   Trigger Data 1
0x7A2: tdata2      (RW)   Trigger Data 2
0x7A3: tdata3      (RW)   Trigger Data 3
```

### CSR Operations

```systemverilog
// CSRRW: CSR Read/Write
// rd = csr; csr = rs1
always_comb begin
    if (wr_en_i && instr_type_i == CSR_RW) begin
        csr_wdata = csr_wdata_i;  // Direct write
    end
end

// CSRRS: CSR Read/Set Bits
// rd = csr; csr = csr | rs1
csr_wdata = csr_rdata_o | csr_wdata_i;

// CSRRC: CSR Read/Clear Bits
// rd = csr; csr = csr & ~rs1
csr_wdata = csr_rdata_o & ~csr_wdata_i;

// Immediate variants: CSRRWI, CSRRSI, CSRRCI use zimm (5-bit immediate)
```

### mstatus Register

```
Field   | Bits | R/W | Purpose
--------|------|-----|----------
MIE     | 3    | RW  | Machine Interrupt Enable
MPIE    | 7    | RW  | Machine Prior Interrupt Enable
MPP     | 12:11 | RW | Machine Prior Privilege Mode
FS      | 14:13 | RW | Floating-point Status
XS      | 16:15 | RW | Extension Status
MPRV    | 17   | RW  | Modify Privilege on Mem Access
SUM     | 18   | RW  | Permit Supervisor to Access User Memory
MXR     | 19   | RW  | Make eXecutable Readable
SD      | 31   | R   | State Dirty (FS or XS changed)

Example:
├─ MIE = 1: Interrupts enabled
├─ MPIE = 1: Interrupts were enabled before trap
├─ MPP = 11 (Machine mode)
└─ On MRET: restore MIE from MPIE
```

### Exception Handling in CSR

```systemverilog
// On exception:
if (trap_active_i) begin
    // 1. Save current state
    mepc_q     <= trap_mepc_i;     // Exception PC
    mcause_q   <= trap_cause_i;    // Exception cause
    mtval_q    <= trap_tval_i;     // Exception value (addr/instr)
    
    // 2. Update mstatus
    mstatus.MPIE <= mstatus.MIE;   // Save interrupt enable
    mstatus.MIE  <= 1'b0;          // Disable interrupts
    mstatus.MPP  <= 2'b11;         // Assert Machine mode
    
    // 3. PC → mtvec + trap_cause offset
    pc_next = mtvec + (trap_cause * 4);  // Vectored mode
end

// On MRET (return from exception):
if (instr_type_i == mret) begin
    mstatus.MIE  <= mstatus.MPIE;  // Restore interrupt enable
    mstatus.MPIE <= 1'b1;          // Set to 1
    pc_next = mepc;
end
```

### Exception Causes

```systemverilog
typedef enum logic [31:0] {
    EXC_INSTR_MISALIGNED   = 32'h00000000,
    EXC_INSTR_FAULT        = 32'h00000001,
    EXC_ILLEGAL_INSTR      = 32'h00000002,
    EXC_BREAKPOINT         = 32'h00000003,
    EXC_LOAD_MISALIGNED    = 32'h00000004,
    EXC_LOAD_FAULT         = 32'h00000005,
    EXC_STORE_MISALIGNED   = 32'h00000006,
    EXC_STORE_FAULT        = 32'h00000007,
    EXC_ECALL_U            = 32'h00000008,
    EXC_ECALL_S            = 32'h00000009,
    EXC_ECALL_M            = 32'h0000000B,
    EXC_INSTR_PAGE_FAULT   = 32'h0000000C,
    EXC_LOAD_PAGE_FAULT    = 32'h0000000D,
    EXC_STORE_PAGE_FAULT   = 32'h0000000F
} exc_cause_e;
```

---

## 🏃 Execution Module - execution.sv

### Purpose

Execute aşamasının orchestration'ı ve data forwarding.

### Interface

```systemverilog
module execution #(
    parameter XLEN = 32
) (
    input  logic                   clk_i,
    input  logic                   rst_ni,
    
    // Data from Decode stage
    input  logic        [XLEN-1:0] r1_data_i,         // Register 1
    input  logic        [XLEN-1:0] r2_data_i,         // Register 2
    input  logic        [XLEN-1:0] imm_i,             // Immediate
    input  logic        [XLEN-1:0] pc_i,              // Current PC
    input  logic        [XLEN-1:0] pc_incr_i,         // PC+4
    
    // Control signals
    input  logic        [     1:0] alu_in1_sel_i,     // Operand 1 select
    input  logic                   alu_in2_sel_i,     // Operand 2 select
    input  alu_op_e                alu_ctrl_i,        // ALU operation
    input  pc_sel_e                pc_sel_i,          // Branch type
    input  instr_type_e            instr_type_i,      // Instruction type
    
    // CSR operations
    input  logic                   rd_csr_i,          // Read CSR
    input  logic                   wr_csr_i,          // Write CSR
    input  logic        [    11:0] csr_idx_i,         // CSR index
    
    // Data forwarding
    input  logic        [     1:0] fwd_a_i,           // Forward source 1
    input  logic        [     1:0] fwd_b_i,           // Forward source 2
    input  logic        [XLEN-1:0] alu_result_i,      // Previous ALU result
    input  logic        [XLEN-1:0] wb_data_i,         // Write-back data
    
    // Exception inputs
    input  logic                   trap_active_i,     // Exception active
    input  logic        [XLEN-1:0] trap_cause_i,      // Exception cause
    input  logic        [XLEN-1:0] trap_tval_i,       // Exception value
    input  logic        [XLEN-1:0] trap_mepc_i,       // Exception PC
    
    // Outputs to Memory stage
    output logic        [XLEN-1:0] alu_result_o,      // ALU result
    output logic        [XLEN-1:0] write_data_o,      // Store data
    output logic        [XLEN-1:0] pc_target_o,       // Branch target
    output logic                   pc_sel_o,          // Take branch
    output logic                   alu_stall_o,       // Stall (MUL/DIV)
    output exc_type_e              exc_type_o,        // Exception type
    
    // CSR outputs (for traps)
    output logic        [XLEN-1:0] mtvec_o,           // Trap vector
    output logic        [XLEN-1:0] mepc_o             // Exception PC
);
```

### Data Forwarding Selection

```systemverilog
always_comb begin
    // Select operand A
    case (fwd_a_i)
        2'b00: data_a = r1_data_i;        // From register
        2'b01: data_a = wb_data_i;        // From WB stage
        2'b10: data_a = alu_result_i;     // From previous EX
        default: data_a = r1_data_i;
    endcase
    
    // Select operand B
    case (fwd_b_i)
        2'b00: data_b = r2_data_i;        // From register
        2'b01: data_b = wb_data_i;        // From WB stage
        2'b10: data_b = alu_result_i;     // From previous EX
        default: data_b = r2_data_i;
    endcase
end
```

### ALU Operand Selection

```systemverilog
// ALU Input 1
case (alu_in1_sel_i)
    2'b00: operand_a = data_a;           // rs1 (from register)
    2'b01: operand_a = pc_incr_i;        // PC+4 (for link instructions)
    2'b10: operand_a = pc_i;             // PC (for AUIPC)
    2'b11: operand_a = data_a;           // rs1 (default)
endcase

// ALU Input 2
operand_b = alu_in2_sel_i ? imm_i : data_b;
```

### Branch Resolution

```systemverilog
// Evaluate branch conditions
ex_zero  = (alu_result == 0);            // Zero flag
ex_slt   = (signed_alu_result < 0);      // Signed less-than
ex_sltu  = (alu_result < data_a);        // Unsigned less-than

// PC selection based on branch type
always_comb begin
    pc_sel_o = 1'b0;  // Default: no branch
    
    if ((pc_sel_i == BEQ) && ex_zero)           pc_sel_o = 1'b1;
    if ((pc_sel_i == BNE) && !ex_zero)          pc_sel_o = 1'b1;
    if ((pc_sel_i == BLT) && ex_slt)            pc_sel_o = 1'b1;
    if ((pc_sel_i == BGE) && (!ex_slt || ex_zero)) pc_sel_o = 1'b1;
    if ((pc_sel_i == BLTU) && ex_sltu)          pc_sel_o = 1'b1;
    if ((pc_sel_i == BGEU) && (!ex_sltu || ex_zero)) pc_sel_o = 1'b1;
    if ((pc_sel_i == JALR) || (pc_sel_i == JAL)) pc_sel_o = 1'b1;
    if (instr_type_i == mret)                   pc_sel_o = 1'b1;
end

// Target calculation
case (pc_sel_i)
    JALR: pc_target_o = (data_a + imm_i) & ~32'b1;  // Clear LSB
    default: pc_target_o = pc_i + signed_imm;
endcase

// Handle MRET specially
if (instr_type_i == mret)
    pc_target_o = mepc;  // Return to exception PC
```

### Misaligned Check

```systemverilog
// Check for instruction misalignment on branch/jump
if (pc_sel_o && pc_target_o[0])
    exc_type_o = INSTR_MISALIGNED;
else
    exc_type_o = NO_EXCEPTION;
```

---

## 📊 Dataflow Example

### Örnek 1: `ADD x3, x1, x2`

```
Decode Output:
├─ r1_data_i = 100
├─ r2_data_i = 200
├─ alu_ctrl_i = OP_ADD
├─ alu_in1_sel_i = 2'b00 (rs1)
└─ alu_in2_sel_i = 1'b0 (rs2)

Execute (Cycle N):
├─ operand_a = 100
├─ operand_b = 200
├─ ALU: 100 + 200 = 300
├─ pc_sel_o = 0 (no branch)
└─ alu_result_o = 300

Memory Stage (Cycle N+1):
└─ Register x3 ← 300
```

### Örnek 2: `BEQ x5, x6, offset`

```
Decode Output:
├─ r1_data_i = 10
├─ r2_data_i = 10
├─ pc_sel_i = BEQ
├─ imm_i = offset (e.g., 20)
└─ pc_i = 0x1000, pc_incr_i = 0x1004

Execute (Cycle N):
├─ ALU: 10 - 10 = 0 (for comparison)
├─ ex_zero = 1 (result is zero)
├─ Branch condition: (BEQ && ex_zero) = 1
├─ pc_target_o = 0x1000 + 20 = 0x1014
├─ pc_sel_o = 1 (take branch)
└─ Exception: NONE

Fetch (Cycle N+1):
└─ PC ← 0x1014 (branch taken)
```

### Örnek 3: `MUL x7, x8, x9` (Multi-cycle)

```
Decode Output (Cycle N):
├─ r1_data_i = 200
├─ r2_data_i = 300
├─ alu_ctrl_i = OP_MUL
└─ imm_i = 0

Execute (Cycle N):
├─ mul_start = 1
├─ alu_stall_o = 1 (STALL pipeline)
└─ Multiplier start: 200 × 300

Execute (Cycle N+1):
├─ mul_busy = 1 (still computing)
├─ alu_stall_o = 1 (continue stall)
└─ Multiplier: computing...

Execute (Cycle N+2):
├─ mul_done = 1
├─ alu_stall_o = 0 (resume)
└─ alu_result_o = 60000 (lower 32 bits)

Memory Stage (Cycle N+3):
└─ Register x7 ← 60000
```

### Örnek 4: `CSRW mstatus, x10`

```
Decode Output:
├─ r1_data_i = 0x1800 (new mstatus value)
├─ csr_idx_i = 12'h300 (mstatus)
├─ wr_csr_i = 1
└─ instr_type_i = CSR_RW

Execute (Cycle N):
├─ CSR write: mstatus ← 0x1800
├─ csr_rdata = (old mstatus value)
├─ alu_result_o = csr_rdata (read before write)
└─ CSR updated

Execute (Cycle N+1):
└─ Effect: Interrupts enabled/disabled based on new mstatus
```

---

## 📈 Timing & Stalling

### Multi-cycle Latency

| Operation | Latency | Cause |
|-----------|---------|-------|
| ADD, SUB, Logic | 1 cycle | Combinational ALU |
| Shift | 1 cycle | Barrel shifter |
| Comparison | 1 cycle | ALU flags |
| LUI | 1 cycle | Pass-through |
| MUL | 3-4 cycles | Wallace tree multiply |
| MULH | 3-4 cycles | Extract high bits |
| DIV | 30-40 cycles | Non-restoring divider |
| REM | 30-40 cycles | Part of divide |
| CSR read | 1 cycle | Register file read |
| CSR write | 1 cycle | Register file write |

### Stall Generation

```
Normal (1-cycle ops):
Cycle: IF  | ID  | EX  | MEM | WB  |
              |R→ EX
              
MUL (3-cycle):
Cycle: IF  | ID  | EX~EX~EX | MEM | WB  |
              |    STALL STALL

DIV (30-cycle):
Cycle: IF  | ID  | EX~~~~~~~~~~...~~~ | MEM | WB |
              |    STALL for 29 cycles
```

---

## 🎯 Summary

| Aspect | Details |
|--------|---------|
| **Operations** | Arithmetic, Logical, Shifts, Compare, MUL, DIV, CSR |
| **Latency** | 1 cycle (basic), 3-4 (MUL), 30-40 (DIV) |
| **Forwarding** | 2-bit per operand (register, WB data, ALU result) |
| **CSR Count** | 20+ registers (mstatus, mepc, mcause, etc.) |
| **Exception Handling** | Trap detection, PC calculation, CSR updates |
| **Stalling** | ALU stalls pipeline for MUL/DIV |

---

## 📚 Sonraki Adımlar

- [Memory Stage](./MEMORY_STAGE.md)
- [CSR Deep Dive](./csr_guide.md)
- [Multiply/Divide Units](./mul_div.md)

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025

