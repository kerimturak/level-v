# COMPRESSED DECODER Modülü - Teknik Döküman

## Genel Bakış

`compressed_decoder.sv` modülü, RISC-V C Extension (RV32C) specification'a uygun olarak 16-bit compressed instruction'ları 32-bit standart RISC-V instruction'lara decode eder. Modül tamamen combinational logic ile çalışır ve illegal instruction detection yapar.

## RISC-V C Extension Özellikleri

### Avantajları
- **Code Density**: %25-30 daha küçük binary boyutu
- **Performance**: Daha az instruction fetch (cache efficiency)
- **Backward Compatibility**: Normal 32-bit instruction'larla mix edilebilir

### Compressed Instruction Format

16-bit compressed instruction'lar 4 quadrant'a ayrılır:

```
Instruction[1:0] | Quadrant | Açıklama
-----------------|----------|----------
     2'b00       |    C0    | Load/Store, Stack operations
     2'b01       |    C1    | Control flow, ALU immediate
     2'b10       |    C2    | Stack operations, Register moves
     2'b11       |    --    | Normal 32-bit instruction (not compressed)
```

## Port Tanımları

| Port | Yön | Tip | Açıklama |
|------|-----|-----|----------|
| `instr_i` | Input | [31:0] | Giriş instruction (16-bit compressed veya 32-bit normal) |
| `instr_o` | Output | [31:0] | Çıkış instruction (her zaman 32-bit decoded) |
| `is_compressed_o` | Output | logic | Giriş compressed instruction mıydı? (1=compressed, 0=normal) |
| `illegal_instr_o` | Output | logic | Illegal instruction tespit edildi mi? |

**Not:** 
- 16-bit compressed instruction'lar `instr_i[15:0]` içinde gelir
- `instr_i[31:16]` compressed instruction'lar için don't care
- Normal 32-bit instruction'lar doğrudan `instr_o` ya aktarılır

## Instruction Decode Flow

```
instr_i[1:0] (quadrant) → Quadrant Decoder (C0/C1/C2)
                              ↓
                        Compressed Format Parse
                              ↓
                        32-bit Instruction Generation
                              ↓
                        Illegal Check
                              ↓
                    instr_o + is_compressed_o + illegal_instr_o
```

## Opcode & Funct Definitions

### RV32I Base Opcodes

```systemverilog
localparam logic [6:0] OPCODE_LOAD   = 7'h03;  // Load instructions
localparam logic [6:0] OPCODE_STORE  = 7'h23;  // Store instructions
localparam logic [6:0] OPCODE_BRANCH = 7'h63;  // Branch instructions
localparam logic [6:0] OPCODE_JALR   = 7'h67;  // JALR (indirect jump)
localparam logic [6:0] OPCODE_JAL    = 7'h6f;  // JAL (direct jump)
localparam logic [6:0] OPCODE_OPIMM  = 7'h13;  // ALU immediate operations
localparam logic [6:0] OPCODE_OP     = 7'h33;  // ALU register operations
localparam logic [6:0] OPCODE_LUI    = 7'h37;  // Load Upper Immediate
localparam logic [6:0] OPCODE_SYSTEM = 7'h73;  // System instructions (EBREAK)
```

### Register Encoding

```systemverilog
localparam logic [4:0] REG_ZERO = 5'h00;  // x0 (zero register)
localparam logic [4:0] REG_RA   = 5'h01;  // x1 (return address)
localparam logic [4:0] REG_SP   = 5'h02;  // x2 (stack pointer)
```

## Field Extraction

### Full Registers (C2 Quadrant)
```systemverilog
rd_rs1_full = instr_i[11:7];  // 5-bit, full register set (x0-x31)
rs2_full    = instr_i[6:2];
```

### Compressed Registers (C0/C1 Quadrant)
```systemverilog
rd_prime  = {2'b01, instr_i[4:2]};  // x8-x15 (8 + [2:0])
rs1_prime = {2'b01, instr_i[9:7]};
rs2_prime = {2'b01, instr_i[4:2]};
```

**Compressed Register Mapping:**
- 3-bit encoded → 5-bit actual
- Sadece x8-x15 erişilebilir (register window)
- x8 = s0/fp, x9 = s1, ..., x15 = a5

## Immediate Extraction Functions

### 1. C.ADDI4SPN (Stack Pointer Immediate)
```systemverilog
function automatic logic [11:0] get_imm_addi4spn();
  return {2'b0, instr_i[10:7], instr_i[12:11], instr_i[5], instr_i[6], 2'b00};
endfunction
```
- **Format:** nzuimm[5:4|9:6|2|3] scaled by 4
- **Range:** 4-1020 (non-zero, 4-byte aligned)
- **Usage:** `addi rd', x2, nzuimm`

### 2. C.LW / C.SW (Load/Store Word Immediate)
```systemverilog
function automatic logic [11:0] get_imm_lw_sw();
  return {5'b0, instr_i[5], instr_i[12:10], instr_i[6], 2'b00};
endfunction
```
- **Format:** uimm[5:3|2|6] scaled by 4
- **Range:** 0-124 (4-byte aligned)

### 3. C.ADDI / C.LI (Immediate)
```systemverilog
function automatic logic [11:0] get_imm_ci();
  return {{6{instr_i[12]}}, instr_i[12], instr_i[6:2]};
endfunction
```
- **Format:** imm[5] sign-extended | imm[4:0]
- **Range:** -32 to +31 (signed 6-bit)

### 4. C.LUI (Load Upper Immediate)
```systemverilog
function automatic logic [19:0] get_imm_lui();
  return {{14{instr_i[12]}}, instr_i[12], instr_i[6:2]};
endfunction
```
- **Format:** nzimm[17] sign-extended | imm[16:12]
- **Range:** -131072 to +131068 (upper 20 bits)

### 5. C.ADDI16SP (Stack Adjust)
```systemverilog
function automatic logic [11:0] get_imm_addi16sp();
  return {{3{instr_i[12]}}, instr_i[4:3], instr_i[5], instr_i[2], instr_i[6], 4'b0};
endfunction
```
- **Format:** nzimm[9] | imm[4|6|8:7|5] scaled by 16
- **Range:** -512 to +496 (16-byte aligned, non-zero)

### 6. C.J / C.JAL (Jump Offset)
```systemverilog
function automatic logic [31:0] gen_c_jal(input logic [4:0] rd);
  return {instr_i[12], instr_i[8], instr_i[10:9], instr_i[6], instr_i[7], 
          instr_i[2], instr_i[11], instr_i[5:3], {9{instr_i[12]}}, rd, OPCODE_JAL};
endfunction
```
- **Format:** offset[11|4|9:8|10|6|7|3:1|5]
- **Range:** -2048 to +2046 (2-byte aligned)

### 7. C.BEQZ / C.BNEZ (Branch Offset)
```systemverilog
function automatic logic [31:0] gen_c_branch(input logic [2:0] f3);
  return {{4{instr_i[12]}}, instr_i[6:5], instr_i[2], REG_ZERO, rs1_prime, 
          f3, instr_i[11:10], instr_i[4:3], instr_i[12], OPCODE_BRANCH};
endfunction
```
- **Format:** offset[8|4:3|7:6|2:1|5]
- **Range:** -256 to +254 (2-byte aligned)

### 8. C.LWSP / C.SWSP (Stack Load/Store)
```systemverilog
// C.LWSP
get_imm_lwsp() = {4'b0, instr_i[3:2], instr_i[12], instr_i[6:4], 2'b00};

// C.SWSP
get_imm_swsp() = {4'b0, instr_i[8:7], instr_i[12:9], 2'b00};
```
- **Range:** 0-252 (4-byte aligned)

## Instruction Generation Functions

### R-Type
```systemverilog
function automatic logic [31:0] gen_r_type(
  input logic [6:0] funct7, 
  input logic [4:0] rs2, 
  input logic [4:0] rs1, 
  input logic [2:0] f3, 
  input logic [4:0] rd, 
  input logic [6:0] opcode
);
  return {funct7, rs2, rs1, f3, rd, opcode};
endfunction
```

### I-Type
```systemverilog
function automatic logic [31:0] gen_i_type(
  input logic [11:0] imm, 
  input logic [4:0] rs1, 
  input logic [2:0] f3, 
  input logic [4:0] rd, 
  input logic [6:0] opcode
);
  return {imm, rs1, f3, rd, opcode};
endfunction
```

### S-Type
```systemverilog
function automatic logic [31:0] gen_s_type(
  input logic [11:0] imm, 
  input logic [4:0] rs2, 
  input logic [4:0] rs1, 
  input logic [2:0] f3, 
  input logic [6:0] opcode
);
  return {imm[11:5], rs2, rs1, f3, imm[4:0], opcode};
endfunction
```

### U-Type
```systemverilog
function automatic logic [31:0] gen_u_type(
  input logic [19:0] imm, 
  input logic [4:0] rd, 
  input logic [6:0] opcode
);
  return {imm, rd, opcode};
endfunction
```

## Quadrant Decoders

### C0 Quadrant (opcode[1:0] = 2'b00)

| funct3 | Instruction | Expansion | Açıklama |
|--------|-------------|-----------|----------|
| 3'b000 | C.ADDI4SPN | `addi rd', x2, nzuimm` | Stack pointer offset add |
| 3'b010 | C.LW | `lw rd', offset(rs1')` | Load word |
| 3'b110 | C.SW | `sw rs2', offset(rs1')` | Store word |
| Others | -- | -- | **Illegal** |

**Illegal Conditions:**
- `C.ADDI4SPN`: nzuimm = 0 (reserved)
- `funct3 ∉ {000, 010, 110}`: Illegal

**Örnek:**
```
C.LW x10, 8(x9)  [Compressed]
→ lw x10, 8(x9)  [Expanded]

Binary (C format): 0x4588
  funct3=010, rs1'=001(x9), offset=8, rd'=010(x10)
```

### C1 Quadrant (opcode[1:0] = 2'b01)

| funct3 | Instruction | Expansion | Açıklama |
|--------|-------------|-----------|----------|
| 3'b000 | C.ADDI / C.NOP | `addi rd, rd, imm` | Add immediate |
| 3'b001 | C.JAL (RV32C) | `jal x1, offset` | Jump and link |
| 3'b010 | C.LI | `addi rd, x0, imm` | Load immediate |
| 3'b011 | C.LUI / C.ADDI16SP | `lui rd, imm` / `addi x2, x2, nzimm` | Load upper / SP adjust |
| 3'b100 | C.SRLI/C.SRAI/C.ANDI/C.SUB/... | Various ALU ops | Arithmetic/Logic |
| 3'b101 | C.J | `jal x0, offset` | Jump (no link) |
| 3'b110 | C.BEQZ | `beq rs1', x0, offset` | Branch if equal zero |
| 3'b111 | C.BNEZ | `bne rs1', x0, offset` | Branch if not equal zero |

**C.ADDI (funct3=000):**
```systemverilog
c1_instr = gen_i_type(get_imm_ci(), rd_rs1_full, FUNCT3_ADD, rd_rs1_full, OPCODE_OPIMM);
// rd=x0 → C.NOP (valid)
// imm=0 with rd!=0 → HINT (valid, treated as NOP)
```

**C.LUI / C.ADDI16SP (funct3=011):**
```systemverilog
if (rd_rs1_full == REG_SP)
  c1_instr = gen_i_type(get_imm_addi16sp(), REG_SP, FUNCT3_ADD, REG_SP, OPCODE_OPIMM);
else
  c1_instr = gen_u_type(get_imm_lui(), rd_rs1_full, OPCODE_LUI);

// Illegal: nzimm = 0
if ({instr_i[12], instr_i[6:2]} == 6'b0) c1_illegal = 1'b1;
```

**C.SRLI / C.SRAI / C.ANDI (funct3=100):**
```systemverilog
case (instr_i[11:10])
  2'b00: // C.SRLI: srli rd', rd', shamt
    c1_instr = gen_i_type({7'b0, get_shamt()}, rs1_prime, FUNCT3_SRL, rs1_prime, OPCODE_OPIMM);
    // Illegal: shamt[5]=1 (RV32) or shamt=0
  
  2'b01: // C.SRAI: srai rd', rd', shamt
    c1_instr = gen_i_type({7'b0100000, get_shamt()}, rs1_prime, FUNCT3_SRL, rs1_prime, OPCODE_OPIMM);
  
  2'b10: // C.ANDI: andi rd', rd', imm
    c1_instr = gen_i_type(get_imm_ci(), rs1_prime, FUNCT3_AND, rs1_prime, OPCODE_OPIMM);
  
  2'b11: // C.SUB/C.XOR/C.OR/C.AND
    case ({instr_i[12], instr_i[6:5]})
      3'b000: c1_instr = gen_r_type(FUNCT7_SUB, rs2_prime, rs1_prime, FUNCT3_ADD, rs1_prime, OPCODE_OP);  // C.SUB
      3'b001: c1_instr = gen_r_type(FUNCT7_ZERO, rs2_prime, rs1_prime, FUNCT3_XOR, rs1_prime, OPCODE_OP); // C.XOR
      3'b010: c1_instr = gen_r_type(FUNCT7_ZERO, rs2_prime, rs1_prime, FUNCT3_OR, rs1_prime, OPCODE_OP);  // C.OR
      3'b011: c1_instr = gen_r_type(FUNCT7_ZERO, rs2_prime, rs1_prime, FUNCT3_AND, rs1_prime, OPCODE_OP); // C.AND
      default: c1_illegal = 1'b1;  // RV64C only (SUBW/ADDW)
    endcase
endcase
```

### C2 Quadrant (opcode[1:0] = 2'b10)

| funct3 | Instruction | Expansion | Açıklama |
|--------|-------------|-----------|----------|
| 3'b000 | C.SLLI | `slli rd, rd, shamt` | Shift left logical immediate |
| 3'b010 | C.LWSP | `lw rd, offset(x2)` | Load word from stack |
| 3'b100 | C.MV / C.JR / C.JALR / C.ADD / C.EBREAK | Multiple | Control/Move/Add |
| 3'b110 | C.SWSP | `sw rs2, offset(x2)` | Store word to stack |
| Others | -- | -- | **Illegal** |

**C.SLLI (funct3=000):**
```systemverilog
c2_instr = gen_i_type({7'b0, get_shamt()}, rd_rs1_full, FUNCT3_SLL, rd_rs1_full, OPCODE_OPIMM);
// Illegal: shamt[5]=1 (RV32) or shamt=0
// rd=x0 → HINT (valid, treated as NOP)
```

**C.LWSP (funct3=010):**
```systemverilog
c2_instr = gen_i_type(get_imm_lwsp(), REG_SP, FUNCT3_LW, rd_rs1_full, OPCODE_LOAD);
// Illegal: rd = x0 (reserved)
```

**C.MV / C.JR / C.JALR / C.ADD / C.EBREAK (funct3=100):**
```systemverilog
if (!instr_i[12]) begin
  if (rs2_full == REG_ZERO) begin
    // C.JR: jalr x0, rs1, 0
    c2_instr = gen_i_type(12'b0, rd_rs1_full, FUNCT3_ADD, REG_ZERO, OPCODE_JALR);
    // Illegal: rs1=x0
  end else begin
    // C.MV: add rd, x0, rs2
    c2_instr = gen_r_type(FUNCT7_ZERO, rs2_full, REG_ZERO, FUNCT3_ADD, rd_rs1_full, OPCODE_OP);
  end
end else begin
  if (rd_rs1_full == REG_ZERO && rs2_full == REG_ZERO) begin
    // C.EBREAK
    c2_instr = 32'h00100073;
  end else if (rs2_full == REG_ZERO) begin
    // C.JALR: jalr x1, rs1, 0
    c2_instr = gen_i_type(12'b0, rd_rs1_full, FUNCT3_ADD, REG_RA, OPCODE_JALR);
  end else begin
    // C.ADD: add rd, rd, rs2
    c2_instr = gen_r_type(FUNCT7_ZERO, rs2_full, rd_rs1_full, FUNCT3_ADD, rd_rs1_full, OPCODE_OP);
  end
end
```

## Output Multiplexer

```systemverilog
always_comb begin
  case (quadrant)
    2'b00: begin
      instr_o = c0_instr;
      illegal_instr_o = c0_illegal;
    end
    2'b01: begin
      instr_o = c1_instr;
      illegal_instr_o = c1_illegal;
    end
    2'b10: begin
      instr_o = c2_instr;
      illegal_instr_o = c2_illegal;
    end
    default: begin  // 2'b11
      instr_o = instr_i;  // 32-bit normal instruction
      illegal_instr_o = 1'b0;
    end
  endcase
end

assign is_compressed_o = (quadrant != 2'b11);
```

## Illegal Instruction Detection

### Reserved Encodings

| Instruction | Condition | Açıklama |
|-------------|-----------|----------|
| C.ADDI4SPN | nzuimm = 0 | Reserved (no-op equivalent illegal) |
| C.ADDI16SP | nzimm = 0 | Reserved |
| C.LUI | nzimm = 0 (rd ≠ x2) | Reserved |
| C.SRLI | shamt = 0 | Reserved (HINT in some specs) |
| C.SRAI | shamt = 0 | Reserved |
| C.SLLI | shamt = 0 | Reserved |
| C.LWSP | rd = x0 | Reserved |
| C.JR | rs1 = x0 | Reserved |

### RV32 vs RV64 Restrictions

**RV32C Only:**
- Shift amount (shamt) bit[5] must be 0
- RV64C instructions (C.SUBW, C.ADDW, etc.) are illegal in RV32

```systemverilog
// Example: C.SRLI illegal check
if (instr_i[12])  // shamt[5] = 1
  c1_illegal = 1'b1;
```

### HINT Instructions

HINT instruction'lar encoding space'te yer kaplar ama işlemsel olarak NOP gibi davranır (illegal değil):

- C.NOP (rd = x0)
- C.LI (rd = x0)
- C.LUI (rd = x0)
- C.ADDI (imm = 0, rd ≠ x0)
- C.SLLI/SRLI/SRAI (rd = x0)
- C.MV (rd = x0)
- C.ADD (rd = x0)

**Decoder Behavior:** HINT'ler legal kabul edilir (`illegal_instr_o = 0`), execution'da NOP muamelesi görürler.

## Timing & Synthesis

### Critical Paths

1. **Immediate Extraction:** 
   - Bit shuffling ve sign extension
   - Combinational, ~2-3 logic levels

2. **Quadrant Decode:**
   - Case statement (priority encoder)
   - ~3-4 logic levels

3. **Output Multiplexer:**
   - 4-way mux (quadrant select)
   - ~2 logic levels

**Total Combinational Delay:** ~7-9 logic levels (tipik olarak tek cycle içinde tamamlanabilir)

### Area Optimization

- **Function Sharing:** Immediate extraction function'ları reuse edilir
- **Case Optimization:** Synthesis tool'lar case statement'ları parallel logic'e optimize eder
- **Illegal Detection:** AND/OR tree, minimal overhead

## Verification Strategy

### Test Vectors

```systemverilog
// C.ADDI4SPN test
input:  16'h0010  (C.ADDI4SPN x8, x2, 64)
output: 32'h04010413  (addi x8, x2, 64)
illegal: 0

// C.LW test
input:  16'h4588  (C.LW x10, 8(x9))
output: 32'h0084A503  (lw x10, 8(x9))
illegal: 0

// C.JAL test (RV32C)
input:  16'h2001  (C.JAL offset=4)
output: 32'h004000EF  (jal x1, 4)
illegal: 0

// C.EBREAK test
input:  16'h9002  (C.EBREAK)
output: 32'h00100073  (ebreak)
illegal: 0

// Illegal: C.ADDI4SPN with nzuimm=0
input:  16'h0000
output: 32'h00010413  (addi x8, x2, 0)
illegal: 1
```

### Coverage Points

- [ ] Tüm quadrant'lar (C0, C1, C2, non-compressed)
- [ ] Her compressed instruction tipi
- [ ] Register encoding (compressed vs full)
- [ ] Immediate range limits (min/max)
- [ ] Illegal encoding'ler
- [ ] HINT instruction'lar
- [ ] Edge cases (rd=x0, rs1=x0, imm=0)

## Performance Impact

### Code Density Improvement

**Örnek Program (Fibonacci):**
```
RV32I only:  240 bytes
RV32IC:      180 bytes (25% reduction)
```

**Typical Distribution:**
- C0: ~15% (load/store)
- C1: ~50% (control flow, ALU immediate)
- C2: ~35% (register ops, stack ops)

### Fetch Bandwidth

- **32-bit only:** 4 bytes/instruction → 1 inst/fetch
- **Mixed (RV32IC):** Average 3 bytes/instruction → ~1.33 inst/fetch (theoretical)

**Cache Efficiency:**
- Daha fazla instruction aynı cache line'da
- Instruction cache miss rate azalır (~10-15%)

## Debugging

### Common Issues

1. **Sign Extension Hatası:**
   - Immediate bit shuffling sırasında sign bit yanlış yerleştirilmesi
   - **Test:** Negative immediate'li instruction'lar

2. **Register Mapping Hatası:**
   - Compressed register encoding (x8-x15) yanlış decode
   - **Test:** All compressed register combinations

3. **Illegal Detection Eksikliği:**
   - Reserved encoding'ler yakalanmıyor
   - **Test:** All reserved instruction patterns

### Waveform Analysis

```
Signal Monitoring:
- instr_i[15:0]     : Input compressed instruction
- quadrant          : Detected quadrant (00/01/10/11)
- funct3            : Function field
- instr_o           : Decoded 32-bit instruction
- illegal_instr_o   : Illegal flag
```

## İlgili Modüller

1. **fetch.sv**: Compressed decoder'ı kullanarak instruction'ları decode eder
2. **decode.sv**: Decode edilen 32-bit instruction'ı işler
3. **align_buffer.sv**: 16-bit parcel'ları fetch eder (compressed support için)

## Referanslar

1. RISC-V Unprivileged ISA Specification v20191213 - Chapter 16: "C" Standard Extension
2. RISC-V Compressed Instruction Encoding Table
3. RISC-V Assembly Programmer's Manual - Compressed Instructions
4. "Code Density and Performance of Compressed Instruction Set Architectures" - Research paper

---

**Son Güncelleme:** 4 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
