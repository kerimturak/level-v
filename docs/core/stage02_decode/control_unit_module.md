# CONTROL UNIT Modülü - Teknik Döküman

## Genel Bakış

`control_unit.sv` modülü, RISC-V instruction'ını decode ederek execute aşaması için gereken tüm control signal'lerini üretir. Combinational logic ile çalışır ve instruction type'a göre ALU operation, memory access, register write, CSR access ve branch/jump kontrollerini belirler.

## Temel Sorumluluklar

1. **ALU Control Generation**: ALU operation type belirleme (ADD, SUB, XOR, etc.)
2. **Memory Control**: Load/store size, sign extension, cache valid
3. **Register File Control**: Write enable, result source selection
4. **Branch/Jump Control**: PC selection (sequential, branch, jump)
5. **CSR Control**: CSR read/write, immediate vs register operand
6. **Exception Detection**: Illegal instruction, illegal shift, illegal CSR access

## Port Tanımları

### Giriş Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `inst_i` | inst_t | Parsed instruction (opcode, rs1, rs2, rd, funct3, funct7) |
| `instr_type_i` | instr_type_e | Instruction type (fetch'ten gelen ön-decode bilgisi) |

### Çıkış Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `ctrl_o` | ctrl_t | Control signal bundle (tüm execute control'ları) |

**ctrl_t yapısı (detaylı):**
```systemverilog
typedef struct packed {
  alu_ctrl_e   alu_ctrl;      // ALU operation (ADD/SUB/XOR/...)
  logic [1:0]  alu_in1_sel;   // ALU input 1: 0=rs1, 1=imm, 2=PC
  logic        alu_in2_sel;   // ALU input 2: 0=rs2, 1=imm
  logic        rf_rw_en;      // Register file write enable
  logic        wr_en;         // Memory write enable
  logic        ld_op_sign;    // Load sign extension enable
  logic [1:0]  rw_size;       // Memory size: 01=byte, 10=half, 11=word
  logic [1:0]  result_src;    // Result mux: 00=ALU, 01=Mem, 10=PC+4
  pc_sel_e     pc_sel;        // Branch/Jump type: BEQ/BNE/.../JAL/JALR
  logic        dcache_valid;  // Data cache access valid
  logic        csr_or_data;   // Result from CSR or ALU
  logic        rd_csr;        // CSR read enable
  logic        wr_csr;        // CSR write enable
  logic [11:0] csr_idx;       // CSR address
  imm_e        imm_sel;       // Immediate type: I_IMM/S_IMM/B_IMM/...
  exc_type_e   exc_type;      // Exception type
} ctrl_t;
```

## Exception Detection Logic

### 1. Illegal Shift Detection

```systemverilog
logic illegal_shift;

if (instr_type_i == i_slli || instr_type_i == i_srli || instr_type_i == i_srai) begin
  if (inst_i[25]) begin  // RV32: imm[5] must be zero
    illegal_shift = 1'b1;
  end
end
```

**RISC-V RV32I Kısıtı:**
- Shift amount 5-bit (0-31)
- RV64'te 6-bit olabilir ama RV32'de imm[5] = inst_i[25] her zaman 0 olmalı
- Aksi halde ILLEGAL_INSTRUCTION exception

**Örnek:**
```assembly
slli x1, x2, 32  # Illegal! (shift amount > 31 for RV32)
```

### 2. CSR Illegal Detection

```systemverilog
logic csr_supported;
logic csr_write_intent;
logic instr_is_csr;
logic csr_read_only;

// CSR instruction mı?
instr_is_csr = (instr_type_i == CSR_RW) || (instr_type_i == CSR_RWI) || 
               (instr_type_i == CSR_RS) || (instr_type_i == CSR_RSI) || 
               (instr_type_i == CSR_RC) || (instr_type_i == CSR_RCI);

// CSR core tarafından destekleniyor mu?
csr_supported = is_supported_csr(inst_i[31:20]);

// Read-only CSR mı? (bits [11:10] == 2'b11)
csr_read_only = (inst_i[31:30] == 2'b11);

// Yazma niyeti var mı?
csr_write_intent =
   (instr_type_i == CSR_RW)  ||
   (instr_type_i == CSR_RWI) ||
   ((instr_type_i == CSR_RS  || instr_type_i == CSR_RC)  && inst_i.r1_addr != 5'd0) ||
   ((instr_type_i == CSR_RSI || instr_type_i == CSR_RCI) && inst_i[19:15] != 5'd0);
```

**CSR Exception Conditions:**
1. **Unsupported CSR**: `!csr_supported` → ILLEGAL_INSTRUCTION
2. **Read-Only Write Attempt**: `csr_read_only && csr_write_intent` → ILLEGAL_INSTRUCTION

**RISC-V CSR Address Convention:**
- `csr[11:10] == 2'b11` → Read-only CSR (örn. mvendorid, marchid, cycle)
- `csr[11:10] == 2'b00` → Read-write CSR (örn. mstatus, mtvec)

**Örnek:**
```assembly
csrw cycle, x1   # Illegal! (cycle is read-only, address 0xC00, bits[11:10]=11)
```

### 3. Exception Priority

```systemverilog
ctrl_o.exc_type = NO_EXCEPTION;

if (illegal_shift) 
  ctrl_o.exc_type = ILLEGAL_INSTRUCTION;
else if (instr_is_csr && !csr_supported)
  ctrl_o.exc_type = ILLEGAL_INSTRUCTION;
else if (instr_is_csr && csr_read_only && csr_write_intent)
  ctrl_o.exc_type = ILLEGAL_INSTRUCTION;
```

**Priority Order:**
1. Illegal shift (highest)
2. Unsupported CSR
3. Read-only CSR write (lowest)

## ALU Control Generation

```systemverilog
case (instr_type_i)
  r_add, i_lb, i_lh, i_lw, i_lbu, i_lhu, i_addi, s_sb, s_sh, s_sw, 
  b_beq, b_bne, b_blt, b_bge, b_bltu, b_bgeu, u_jal, i_jalr: 
    ctrl_o.alu_ctrl = OP_ADD;
  
  r_sub:           ctrl_o.alu_ctrl = OP_SUB;
  r_sll, i_slli:   ctrl_o.alu_ctrl = OP_SLL;
  r_slt, i_slti:   ctrl_o.alu_ctrl = OP_SLT;
  r_sltu, i_sltiu: ctrl_o.alu_ctrl = OP_SLTU;
  r_xor, i_xori:   ctrl_o.alu_ctrl = OP_XOR;
  r_srl, i_srli:   ctrl_o.alu_ctrl = OP_SRL;
  r_sra, i_srai:   ctrl_o.alu_ctrl = OP_SRA;
  r_or, i_ori:     ctrl_o.alu_ctrl = OP_OR;
  r_and, i_andi:   ctrl_o.alu_ctrl = OP_AND;
  
  // M extension
  r_mul:           ctrl_o.alu_ctrl = OP_MUL;
  r_mulh:          ctrl_o.alu_ctrl = OP_MULH;
  r_mulhsu:        ctrl_o.alu_ctrl = OP_MULHSU;
  r_mulhu:         ctrl_o.alu_ctrl = OP_MULHU;
  r_div:           ctrl_o.alu_ctrl = OP_DIV;
  r_divu:          ctrl_o.alu_ctrl = OP_DIVU;
  r_rem:           ctrl_o.alu_ctrl = OP_REM;
  r_remu:          ctrl_o.alu_ctrl = OP_REMU;
  
  u_lui:           ctrl_o.alu_ctrl = OP_LUI;
  
  // CSR instructions
  CSR_RW:          ctrl_o.alu_ctrl = OP_CSRRW;
  CSR_RS:          ctrl_o.alu_ctrl = OP_CSRRS;
  CSR_RC:          ctrl_o.alu_ctrl = OP_CSRRC;
  CSR_RWI:         ctrl_o.alu_ctrl = OP_CSRRWI;
  CSR_RSI:         ctrl_o.alu_ctrl = OP_CSRRSI;
  CSR_RCI:         ctrl_o.alu_ctrl = OP_CSRRCI;
  
  default:         ctrl_o.alu_ctrl = OP_ADD;
endcase
```

**Not:** Load/Store/Branch instruction'ları da OP_ADD kullanır (address calculation için)

## Branch/Jump Control

```systemverilog
case (instr_type_i)
  b_beq:   ctrl_o.pc_sel = BEQ;
  b_bne:   ctrl_o.pc_sel = BNE;
  b_blt:   ctrl_o.pc_sel = BLT;
  b_bge:   ctrl_o.pc_sel = BGE;
  b_bltu:  ctrl_o.pc_sel = BLTU;
  b_bgeu:  ctrl_o.pc_sel = BGEU;
  i_jalr:  ctrl_o.pc_sel = JALR;
  u_jal:   ctrl_o.pc_sel = JAL;
  default: ctrl_o.pc_sel = NO_BJ;
endcase
```

**pc_sel_e enum:**
```systemverilog
typedef enum logic [3:0] {
  NO_BJ,   // Sequential (PC + 4)
  BEQ,     // Branch if equal
  BNE,     // Branch if not equal
  BLT,     // Branch if less than (signed)
  BGE,     // Branch if greater or equal (signed)
  BLTU,    // Branch if less than (unsigned)
  BGEU,    // Branch if greater or equal (unsigned)
  JAL,     // Jump and link
  JALR     // Jump and link register
} pc_sel_e;
```

## Opcode-Based Control Generation

Control unit, instruction'ın opcode'una göre case-statement ile control signal'lerini üretir:

### R-Type (Register-Register)

```systemverilog
op_r_type: begin
  ctrl_o.rf_rw_en     = 1'b1;      // Write to rd
  ctrl_o.csr_or_data  = 1'b0;      // ALU result (not CSR)
  ctrl_o.imm_sel      = NO_IMM;    // No immediate
  ctrl_o.alu_in2_sel  = 1'b0;      // ALU input 2 = rs2
  ctrl_o.wr_en        = 1'b0;      // No memory write
  ctrl_o.result_src   = 2'b00;     // Result from ALU
  ctrl_o.dcache_valid = 1'b0;      // No data cache access
end
```

**Örnek:** `add x1, x2, x3` → ALU: x2 + x3 → x1

### I-Type (Immediate ALU)

```systemverilog
op_i_type: begin
  ctrl_o.rf_rw_en = 1'b1;
  if (instr_type_i == i_slli || instr_type_i == i_srli || instr_type_i == i_srai) begin
    ctrl_o.imm_sel = I_USIMM;  // Unsigned immediate (shift amount)
  end else begin
    ctrl_o.imm_sel = I_IMM;    // Signed immediate
  end
  ctrl_o.alu_in2_sel  = 1'b1;  // ALU input 2 = imm
  ctrl_o.wr_en        = 1'b0;
  ctrl_o.result_src   = 2'b00;
  ctrl_o.dcache_valid = 1'b0;
end
```

**Örnek:** `addi x1, x2, 12` → ALU: x2 + 12 → x1

### I-Type Load

```systemverilog
op_i_type_load: begin
  ctrl_o.rf_rw_en     = 1'b1;
  ctrl_o.imm_sel      = I_IMM;
  ctrl_o.alu_in2_sel  = 1'b1;      // ALU: rs1 + offset
  ctrl_o.wr_en        = 1'b0;      // Read (not write)
  ctrl_o.result_src   = 2'b01;     // Result from memory
  ctrl_o.dcache_valid = 1'b1;      // Data cache access
  
  case (instr_type_i)
    i_lb, i_lbu: ctrl_o.rw_size = 2'b01;  // Byte
    i_lh, i_lhu: ctrl_o.rw_size = 2'b10;  // Halfword
    i_lw:        ctrl_o.rw_size = 2'b11;  // Word
  endcase
  
  // Sign extension control
  ctrl_o.ld_op_sign = !(instr_type_i == i_lhu || instr_type_i == i_lbu);
end
```

**Örnek:** `lw x1, 8(x2)` → Memory[x2 + 8] → x1

### S-Type (Store)

```systemverilog
op_s_type: begin
  ctrl_o.rf_rw_en     = 1'b0;      // No register write
  ctrl_o.imm_sel      = S_IMM;
  ctrl_o.alu_in2_sel  = 1'b1;      // ALU: rs1 + offset
  ctrl_o.wr_en        = 1'b1;      // Memory write
  ctrl_o.dcache_valid = 1'b1;
  
  case (instr_type_i)
    s_sb:    ctrl_o.rw_size = 2'b01;  // Byte
    s_sh:    ctrl_o.rw_size = 2'b10;  // Halfword
    s_sw:    ctrl_o.rw_size = 2'b11;  // Word
  endcase
  
  ctrl_o.result_src = 2'b00;  // Don't care (no writeback)
end
```

**Örnek:** `sw x3, 8(x2)` → x3 → Memory[x2 + 8]

### B-Type (Branch)

```systemverilog
op_b_type: begin
  ctrl_o.rf_rw_en     = 1'b0;      // No register write
  ctrl_o.imm_sel      = B_IMM;     // 13-bit branch offset
  ctrl_o.alu_in2_sel  = 1'b0;      // rs2 (for comparison)
  ctrl_o.wr_en        = 1'b0;
  ctrl_o.result_src   = 2'b00;
  ctrl_o.dcache_valid = 1'b0;
end
```

**Örnek:** `beq x1, x2, offset` → if (x1 == x2) PC = PC + offset

### JAL (Jump and Link)

```systemverilog
op_u_type_jump: begin  // u_jal
  ctrl_o.rf_rw_en     = 1'b1;      // Write PC+4 to rd
  ctrl_o.imm_sel      = J_IMM;     // 21-bit jump offset
  ctrl_o.alu_in2_sel  = 1'b0;      // Don't care
  ctrl_o.wr_en        = 1'b0;
  ctrl_o.result_src   = 2'b10;     // Result = PC+4
  ctrl_o.dcache_valid = 1'b0;
end
```

**Örnek:** `jal x1, offset` → x1 = PC+4, PC = PC + offset

### JALR (Jump and Link Register)

```systemverilog
op_i_type_jump: begin  // i_jalr
  ctrl_o.rf_rw_en     = 1'b1;      // Write PC+4 to rd
  ctrl_o.alu_in1_sel  = 2'b1;      // ALU input 1 = imm (for PC calc)
  ctrl_o.imm_sel      = I_IMM;     // 12-bit offset
  ctrl_o.alu_in2_sel  = 1'b1;      // ALU input 2 = imm
  ctrl_o.wr_en        = 1'b0;
  ctrl_o.result_src   = 2'b10;     // Result = PC+4
  ctrl_o.dcache_valid = 1'b0;
end
```

**Örnek:** `jalr x1, 0(x2)` → x1 = PC+4, PC = x2 + 0

### AUIPC (Add Upper Immediate to PC)

```systemverilog
op_u_type_auipc: begin
  ctrl_o.rf_rw_en     = 1'b1;
  ctrl_o.alu_in1_sel  = 2'd2;      // ALU input 1 = PC
  ctrl_o.imm_sel      = U_IMM;     // 20-bit upper immediate
  ctrl_o.alu_in2_sel  = 1'b1;      // ALU input 2 = imm
  ctrl_o.wr_en        = 1'b0;
  ctrl_o.result_src   = 2'b00;     // Result from ALU
  ctrl_o.dcache_valid = 1'b0;
end
```

**Örnek:** `auipc x1, 0x12345` → x1 = PC + (0x12345 << 12)

### LUI (Load Upper Immediate)

```systemverilog
op_u_type_load: begin
  ctrl_o.rf_rw_en     = 1'b1;
  ctrl_o.imm_sel      = U_IMM;
  ctrl_o.alu_in2_sel  = 1'b1;
  ctrl_o.wr_en        = 1'b0;
  ctrl_o.result_src   = 2'b00;
  ctrl_o.dcache_valid = 1'b0;
end
```

**Örnek:** `lui x1, 0x12345` → x1 = 0x12345000

### CSR Instructions

#### CSRRW (CSR Read/Write)

```systemverilog
CSR_RW: begin
  ctrl_o.rf_rw_en     = (inst_i.rd_addr != 0);  // Write CSR to rd (if rd!=x0)
  ctrl_o.csr_or_data  = 1'b1;                   // Result from CSR
  ctrl_o.rd_csr       = (inst_i.rd_addr != 0);  // Read CSR (if rd!=x0)
  ctrl_o.wr_csr       = 1'b1;                   // Always write CSR
  ctrl_o.csr_idx      = inst_i[31:20];
  ctrl_o.imm_sel      = NO_IMM;
  ctrl_o.alu_in2_sel  = 1'b0;                   // rs1 value
end
```

**Semantic:** `rd = CSR[csr]; CSR[csr] = rs1;`

#### CSRRS/CSRRC (CSR Read and Set/Clear)

```systemverilog
CSR_RS, CSR_RC: begin
  ctrl_o.rf_rw_en     = (inst_i.rd_addr != 0);
  ctrl_o.csr_or_data  = 1'b1;
  ctrl_o.rd_csr       = 1'b1;                   // Always read CSR
  ctrl_o.wr_csr       = (inst_i.r1_addr != 0);  // Write only if rs1!=x0
  ctrl_o.csr_idx      = inst_i[31:20];
  ctrl_o.imm_sel      = NO_IMM;
  ctrl_o.alu_in2_sel  = 1'b0;
end
```

**Semantic:** 
- CSRRS: `rd = CSR[csr]; if (rs1!=x0) CSR[csr] |= rs1;`
- CSRRC: `rd = CSR[csr]; if (rs1!=x0) CSR[csr] &= ~rs1;`

#### CSRRWI/CSRRSI/CSRRCI (CSR Immediate)

```systemverilog
CSR_RWI, CSR_RSI, CSR_RCI: begin
  ctrl_o.csr_or_data  = 1'b1;
  ctrl_o.csr_idx      = inst_i[31:20];
  ctrl_o.imm_sel      = CSR_IMM;      // 5-bit zero-extended immediate
  ctrl_o.alu_in2_sel  = 1'b1;         // zimm (immediate)
  
  // CSRRWI: always write, read if rd!=x0
  // CSRRSI/CSRRCI: write if zimm!=0, always read
  if (instr_type_i == CSR_RWI) begin
    ctrl_o.rf_rw_en = (inst_i.rd_addr != 0);
    ctrl_o.rd_csr   = (inst_i.rd_addr != 0);
    ctrl_o.wr_csr   = 1'b1;
  end else begin  // CSR_RSI, CSR_RCI
    ctrl_o.rf_rw_en = (inst_i.rd_addr != 0);
    ctrl_o.rd_csr   = 1'b1;
    ctrl_o.wr_csr   = (inst_i[19:15] != 5'd0);
  end
end
```

### System Instructions

```systemverilog
mret, ecall, ebreak, wfi: begin
  ctrl_o.rf_rw_en     = 1'b0;   // No register write
  ctrl_o.wr_csr       = 1'b0;
  ctrl_o.rd_csr       = 1'b0;
  ctrl_o.csr_idx      = 12'h000;
  ctrl_o.csr_or_data  = 1'b0;
  ctrl_o.imm_sel      = NO_IMM;
  ctrl_o.alu_in2_sel  = 1'b0;
  ctrl_o.wr_en        = 1'b0;
  ctrl_o.result_src   = 2'b00;
  ctrl_o.dcache_valid = 1'b0;
end
```

**Not:** Bu instruction'lar execute aşamasında özel handling gerektirir

## Control Signal Encoding

### alu_in1_sel

| Value | Source | Kullanım |
|-------|--------|----------|
| 2'b00 | rs1 | Normal ALU operations |
| 2'b01 | imm | JALR (PC calculation için immediate) |
| 2'b10 | PC | AUIPC (PC + immediate) |

### alu_in2_sel

| Value | Source | Kullanım |
|-------|--------|----------|
| 1'b0 | rs2 | R-type, branch comparison |
| 1'b1 | imm | I-type, load/store, AUIPC |

### result_src

| Value | Source | Kullanım |
|-------|--------|----------|
| 2'b00 | ALU result | Arithmetic/logic instructions |
| 2'b01 | Memory data | Load instructions |
| 2'b10 | PC + 4 | JAL/JALR (return address) |

### rw_size

| Value | Size | Byte Count |
|-------|------|------------|
| 2'b01 | Byte | 1 byte |
| 2'b10 | Halfword | 2 bytes |
| 2'b11 | Word | 4 bytes |

## Timing & Synthesis

### Critical Paths

1. **Opcode Decode:**
   ```
   inst_i.opcode → case statement → ctrl_o signals
   ```
   - Delay: ~4-6 logic levels (case priority encoder)

2. **CSR Exception Detection:**
   ```
   inst_i[31:20] → is_supported_csr() → csr_supported → exc_type
   ```
   - Delay: ~5-7 logic levels (lookup table + logic)

3. **Immediate Selection:**
   ```
   instr_type_i → imm_sel case → ctrl_o.imm_sel
   ```
   - Delay: ~3-4 logic levels

**Total Combinational Delay:** ~7-10 logic levels (tipik olarak tek cycle içinde)

### Area Optimization

- **Case statement sharing:** Birden fazla instruction type aynı control signal'i paylaşır
- **Default values:** Unused signal'ler için default assignment (synthesis optimization)
- **Function reuse:** `is_supported_csr()` fonksiyonu CSR lookup için

## Verification Strategy

### Test Cases

1. **All Instruction Types:**
   - R-type: add, sub, and, or, xor, sll, srl, sra, slt, sltu
   - I-type: addi, slti, sltiu, xori, ori, andi, slli, srli, srai
   - Load: lb, lh, lw, lbu, lhu
   - Store: sb, sh, sw
   - Branch: beq, bne, blt, bge, bltu, bgeu
   - Jump: jal, jalr
   - Upper: lui, auipc
   - CSR: csrrw, csrrs, csrrc, csrrwi, csrrsi, csrrci
   - System: ecall, ebreak, mret, wfi

2. **Exception Detection:**
   - Illegal shift (RV32 shift amount > 31)
   - Unsupported CSR access
   - Read-only CSR write attempt

3. **Edge Cases:**
   - x0 register (no write)
   - CSR immediate = 0 (no write for CSRSI/CSRCI)
   - rd = x0 for CSR (no register write)

### Assertions

```systemverilog
// R-type instruction'lar register write yapmalı
assert property (@(posedge clk_i)
  (inst_i.opcode == op_r_type) |-> ctrl_o.rf_rw_en);

// Store instruction'lar memory write yapmalı
assert property (@(posedge clk_i)
  (inst_i.opcode == op_s_type) |-> ctrl_o.wr_en);

// Load instruction'lar data cache access yapmalı
assert property (@(posedge clk_i)
  (inst_i.opcode == op_i_type_load) |-> ctrl_o.dcache_valid);

// Branch instruction'lar register write yapmamalı
assert property (@(posedge clk_i)
  (inst_i.opcode == op_b_type) |-> !ctrl_o.rf_rw_en);
```

## İlgili Modüller

1. **decode.sv**: Control unit'i kullanır
2. **execute.sv**: Control signal'lere göre işlem yapar
3. **csr_file.sv**: CSR control signal'lerini işler
4. **alu.sv**: ALU control'e göre operation seçer

## Referanslar

1. RISC-V Unprivileged ISA Specification v20191213 - Instruction Encoding
2. RISC-V Privileged Specification v1.12 - CSR Specifications
3. "Computer Organization and Design: RISC-V Edition" - Patterson & Hennessy, Chapter 4

---

**Son Güncelleme:** 5 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
