# ALU Modülü - Teknik Döküman

## Genel Bakış

`alu.sv` modülü, RISC-V işlemcisinin **Arithmetic Logic Unit** (ALU) implementasyonudur. RV32I base instruction set ve RV32M extension (multiply/divide) operasyonlarını destekler. CSR instruction'ları için de operasyon logic'i içerir.

## Desteklenen İşlemler

### Base Integer (RV32I)

| Operation | Mnemonic | Description |
|-----------|----------|-------------|
| ADD | ADD/ADDI | Addition (signed/unsigned) |
| SUB | SUB | Subtraction |
| SLT | SLT/SLTI | Set less than (signed) |
| SLTU | SLTU/SLTIU | Set less than (unsigned) |
| AND | AND/ANDI | Bitwise AND |
| OR | OR/ORI | Bitwise OR |
| XOR | XOR/XORI | Bitwise XOR |
| SLL | SLL/SLLI | Shift left logical |
| SRL | SRL/SRLI | Shift right logical |
| SRA | SRA/SRAI | Shift right arithmetic |
| LUI | LUI | Load upper immediate |

### M Extension (RV32M)

| Operation | Mnemonic | Description | Cycles |
|-----------|----------|-------------|--------|
| MUL | MUL | Multiply (low 32-bit) | 1 or 32 |
| MULH | MULH | Multiply (high 32-bit, signed×signed) | 1 or 32 |
| MULHSU | MULHSU | Multiply (high 32-bit, signed×unsigned) | 1 or 32 |
| MULHU | MULHU | Multiply (high 32-bit, unsigned×unsigned) | 1 or 32 |
| DIV | DIV | Divide (signed) | 32 |
| DIVU | DIVU | Divide (unsigned) | 32 |
| REM | REM | Remainder (signed) | 32 |
| REMU | REMU | Remainder (unsigned) | 32 |

### CSR Operations (Zicsr)

| Operation | Mnemonic | Description |
|-----------|----------|-------------|
| CSRRW | CSRRW | Atomic read/write |
| CSRRS | CSRRS | Atomic read and set bits |
| CSRRC | CSRRC | Atomic read and clear bits |
| CSRRWI | CSRRWI | Atomic read/write immediate |
| CSRRSI | CSRRSI | Atomic read and set bits (immediate) |
| CSRRCI | CSRRCI | Atomic read and clear bits (immediate) |

## Port Tanımları

### Giriş Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u (mul/div için) |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `alu_a_i` | [XLEN-1:0] | Operand A (rs1 or PC or PC+4) |
| `alu_b_i` | [XLEN-1:0] | Operand B (rs2 or immediate) |
| `csr_rdata_i` | [XLEN-1:0] | CSR read data (for CSR ops) |
| `op_sel_i` | alu_op_e | Operation selection |

### Çıkış Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `alu_o` | [XLEN-1:0] | ALU result |
| `zero_o` | logic | Comparison: rs1 == rs2 (signed) |
| `slt_o` | logic | Comparison: rs1 < rs2 (signed) |
| `sltu_o` | logic | Comparison: rs1 < rs2 (unsigned) |
| `alu_stall_o` | logic | Multi-cycle operation in progress |

## ALU Operation Enumeration

```systemverilog
typedef enum logic [5:0] {
  OP_ADD,    // Addition
  OP_SUB,    // Subtraction
  OP_SLL,    // Shift left logical
  OP_SLT,    // Set less than (signed)
  OP_SLTU,   // Set less than (unsigned)
  OP_XOR,    // XOR
  OP_SRL,    // Shift right logical
  OP_SRA,    // Shift right arithmetic
  OP_OR,     // OR
  OP_AND,    // AND
  OP_LUI,    // Load upper immediate
  
  // M Extension
  OP_MUL,    // Multiply (low)
  OP_MULH,   // Multiply high (signed×signed)
  OP_MULHSU, // Multiply high (signed×unsigned)
  OP_MULHU,  // Multiply high (unsigned×unsigned)
  OP_DIV,    // Divide (signed)
  OP_DIVU,   // Divide (unsigned)
  OP_REM,    // Remainder (signed)
  OP_REMU,   // Remainder (unsigned)
  
  // CSR Operations
  OP_CSRRW,  // CSR read/write
  OP_CSRRS,  // CSR read/set
  OP_CSRRC,  // CSR read/clear
  OP_CSRRWI, // CSR read/write immediate
  OP_CSRRSI, // CSR read/set immediate
  OP_CSRRCI  // CSR read/clear immediate
} alu_op_e;
```

## Base Integer Operations

### Arithmetic Operations

#### Addition (ADD/ADDI)

```systemverilog
rslt.ADD = alu_a_i + alu_b_i;
```

**Examples:**
```assembly
add x1, x2, x3     # x1 = x2 + x3
addi x1, x2, 10    # x1 = x2 + 10
```

**Overflow:** No overflow exception in RISC-V (wrap-around semantics)

#### Subtraction (SUB)

```systemverilog
rslt.SUB = alu_a_i - alu_b_i;
```

**Examples:**
```assembly
sub x1, x2, x3     # x1 = x2 - x3
```

### Comparison Operations

#### Set Less Than (SLT/SLTI)

```systemverilog
rslt.SLT = ($signed(alu_a_i) < $signed(alu_b_i)) ? 32'b1 : 32'b0;
```

**Examples:**
```assembly
slt x1, x2, x3     # x1 = (x2 < x3) ? 1 : 0  (signed)
slti x1, x2, -5    # x1 = (x2 < -5) ? 1 : 0
```

**Signed Comparison:**
```
alu_a_i = 0xFFFFFFFF (-1)
alu_b_i = 0x00000001 (1)
→ rslt.SLT = 1 (true: -1 < 1)
```

#### Set Less Than Unsigned (SLTU/SLTIU)

```systemverilog
rslt.SLTU = (alu_a_i < alu_b_i) ? 32'b1 : 32'b0;
```

**Examples:**
```assembly
sltu x1, x2, x3    # x1 = (x2 < x3) ? 1 : 0  (unsigned)
sltiu x1, x2, 10   # x1 = (x2 < 10) ? 1 : 0
```

**Unsigned Comparison:**
```
alu_a_i = 0xFFFFFFFF (4294967295)
alu_b_i = 0x00000001 (1)
→ rslt.SLTU = 0 (false: 4294967295 > 1)
```

### Logical Operations

#### AND

```systemverilog
rslt.AND = alu_a_i & alu_b_i;
```

**Examples:**
```assembly
and x1, x2, x3     # x1 = x2 & x3
andi x1, x2, 0xFF  # x1 = x2 & 0xFF (mask lower byte)
```

#### OR

```systemverilog
rslt.OR = alu_a_i | alu_b_i;
```

**Examples:**
```assembly
or x1, x2, x3      # x1 = x2 | x3
ori x1, x2, 0x100  # x1 = x2 | 0x100 (set bit 8)
```

#### XOR

```systemverilog
rslt.XOR = alu_a_i ^ alu_b_i;
```

**Examples:**
```assembly
xor x1, x2, x3     # x1 = x2 ^ x3
xori x1, x2, -1    # x1 = ~x2 (complement)
```

### Shift Operations

#### Shift Left Logical (SLL/SLLI)

```systemverilog
rslt.SLL = alu_a_i << alu_b_i[4:0];
```

**Shift Amount:** Only lower 5 bits (0-31 for RV32)

**Examples:**
```assembly
sll x1, x2, x3     # x1 = x2 << (x3 & 0x1F)
slli x1, x2, 5     # x1 = x2 << 5
```

**Behavior:**
```
alu_a_i = 0x00000001
alu_b_i = 0x00000008
→ rslt.SLL = 0x00000100 (1 << 8)
```

#### Shift Right Logical (SRL/SRLI)

```systemverilog
rslt.SRL = alu_a_i >> alu_b_i[4:0];
```

**Zero Extension:** Zeros shifted in from MSB

**Examples:**
```assembly
srl x1, x2, x3     # x1 = x2 >> (x3 & 0x1F)  (logical)
srli x1, x2, 4     # x1 = x2 >> 4
```

**Behavior:**
```
alu_a_i = 0x80000000
alu_b_i = 0x00000001
→ rslt.SRL = 0x40000000 (logical: 0 shifted in)
```

#### Shift Right Arithmetic (SRA/SRAI)

```systemverilog
rslt.SRA = $signed(alu_a_i) >>> alu_b_i[4:0];
```

**Sign Extension:** Sign bit replicated from MSB

**Examples:**
```assembly
sra x1, x2, x3     # x1 = x2 >>> (x3 & 0x1F)  (arithmetic)
srai x1, x2, 4     # x1 = x2 >>> 4
```

**Behavior:**
```
alu_a_i = 0x80000000 (-2147483648)
alu_b_i = 0x00000001
→ rslt.SRA = 0xC0000000 (arithmetic: sign bit replicated)
```

### Load Upper Immediate (LUI)

```systemverilog
rslt.LUI = alu_b_i;
```

**Usage:** `alu_b_i` already contains `imm[31:12] << 12`

**Examples:**
```assembly
lui x1, 0x12345    # x1 = 0x12345000
```

## M Extension Operations

### Multiply Operations

#### Sign Management

```systemverilog
// Absolute values
abs_A = alu_a_i[XLEN-1] ? ~alu_a_i + 1'b1 : alu_a_i;
abs_B = alu_b_i[XLEN-1] ? ~alu_b_i + 1'b1 : alu_b_i;

// Sign determination
mul_sign = alu_a_i[XLEN-1] ^ alu_b_i[XLEN-1];  // XOR for signed multiply
```

**Signed Multiply Logic:**
1. Convert to absolute values
2. Perform unsigned multiply
3. Negate result if operands have different signs

#### MUL (Low 32-bit)

```systemverilog
rslt.MUL = product[31:0];
```

**Examples:**
```assembly
mul x1, x2, x3     # x1 = (x2 * x3)[31:0]
```

**Behavior:**
```
x2 = 0x00001000 (4096)
x3 = 0x00000100 (256)
→ x1 = 0x00100000 (1048576)
```

#### MULH (High 32-bit, Signed×Signed)

```systemverilog
mul_op_A = abs_A;
mul_op_B = abs_B;
mul_sign = alu_a_i[XLEN-1] ^ alu_b_i[XLEN-1];
product = mul_sign ? -unsigned_prod : unsigned_prod;

rslt.MULH = product[63:32];
```

**Examples:**
```assembly
mulh x1, x2, x3    # x1 = (x2 * x3)[63:32]  (signed×signed)
```

**Behavior:**
```
x2 = 0x80000000 (-2147483648)
x3 = 0x00000002 (2)
→ 64-bit product = 0xFFFFFFFF00000000 (-4294967296)
→ x1 = 0xFFFFFFFF (high 32 bits)
```

#### MULHSU (High 32-bit, Signed×Unsigned)

```systemverilog
mul_op_A = abs_A;        // |rs1| (signed)
mul_op_B = alu_b_i;      // rs2 (unsigned, no abs)
mul_sign = alu_a_i[XLEN-1];  // Sign from rs1 only
product = mul_sign ? -unsigned_prod : unsigned_prod;

rslt.MULHSU = product[63:32];
```

**Examples:**
```assembly
mulhsu x1, x2, x3  # x1 = (x2 * x3)[63:32]  (signed×unsigned)
```

**Behavior:**
```
x2 = 0xFFFFFFFE (-2, signed)
x3 = 0x00000003 (3, unsigned)
→ product = -6 (0xFFFFFFFFFFFFFFFA)
→ x1 = 0xFFFFFFFF (high 32 bits)
```

#### MULHU (High 32-bit, Unsigned×Unsigned)

```systemverilog
mul_op_A = alu_a_i;  // No abs (unsigned)
mul_op_B = alu_b_i;  // No abs (unsigned)
mul_sign = 1'b0;     // No sign

rslt.MULHU = unsigned_prod[63:32];
```

**Examples:**
```assembly
mulhu x1, x2, x3   # x1 = (x2 * x3)[63:32]  (unsigned×unsigned)
```

**Behavior:**
```
x2 = 0xFFFFFFFF (4294967295)
x3 = 0x00000002 (2)
→ product = 0x00000001FFFFFFFE
→ x1 = 0x00000001 (high 32 bits)
```

### Divide Operations

#### Sign Management

```systemverilog
// For DIV/REM (signed)
div_op_A = abs_A;
div_op_B = abs_B;
div_sign_quot = alu_a_i[XLEN-1] ^ alu_b_i[XLEN-1];  // Quotient sign
div_sign_rem = alu_a_i[XLEN-1];                     // Remainder sign = sign(dividend)

// Sign correction
quotient = div_sign_quot ? -unsigned_quo : unsigned_quo;
remainder = div_sign_rem ? -unsigned_rem : unsigned_rem;
```

#### DIV (Signed Division)

```systemverilog
rslt.DIV = div_quot_final;
```

**RISC-V Division Rules:**
1. **Division by zero**: `quotient = -1` (0xFFFFFFFF)
2. **Overflow**: `MIN_INT / -1 = MIN_INT` (saturation)
3. **Remainder sign**: Same as dividend

**Examples:**
```assembly
div x1, x2, x3     # x1 = x2 / x3  (signed)
```

**Behavior:**
```
x2 = 7, x3 = 2      → x1 = 3
x2 = 7, x3 = -2     → x1 = -3
x2 = -7, x3 = 2     → x1 = -3
x2 = -7, x3 = -2    → x1 = 3
x2 = 7, x3 = 0      → x1 = -1 (divide by zero)
```

#### DIVU (Unsigned Division)

```systemverilog
rslt.DIVU = div_dbz ? '1 : unsigned_quo;
```

**Examples:**
```assembly
divu x1, x2, x3    # x1 = x2 / x3  (unsigned)
```

**Behavior:**
```
x2 = 0xFFFFFFFF, x3 = 2  → x1 = 0x7FFFFFFF
x2 = 10, x3 = 0          → x1 = 0xFFFFFFFF (divide by zero)
```

#### REM (Signed Remainder)

```systemverilog
rslt.REM = div_rem_final;
```

**Remainder Sign:** Same as dividend (RISC-V convention)

**Examples:**
```assembly
rem x1, x2, x3     # x1 = x2 % x3  (signed)
```

**Behavior:**
```
x2 = 7, x3 = 2      → x1 = 1
x2 = 7, x3 = -2     → x1 = 1  (sign from dividend)
x2 = -7, x3 = 2     → x1 = -1 (sign from dividend)
x2 = -7, x3 = -2    → x1 = -1 (sign from dividend)
x2 = 7, x3 = 0      → x1 = 7  (divide by zero)
```

#### REMU (Unsigned Remainder)

```systemverilog
rslt.REMU = unsigned_rem;
```

**Examples:**
```assembly
remu x1, x2, x3    # x1 = x2 % x3  (unsigned)
```

**Behavior:**
```
x2 = 10, x3 = 3     → x1 = 1
x2 = 10, x3 = 0     → x1 = 10 (divide by zero)
```

### Multiply/Divide Unit Selection

#### Wallace Tree Multiplier (FEAT_WALLACE_SINGLE)

```systemverilog
`ifdef FEAT_WALLACE_SINGLE
  mul #(.XLEN(32), .YLEN(32), .TYP(Mul_Type)) i_mul (
    .a(mul_op_A),
    .b(mul_op_B),
    .c(unsigned_prod)
  );
  
  assign mul_valid = 1'b1;  // Single-cycle
  assign mul_busy = 1'b0;
`endif
```

**Characteristics:**
- **Latency:** 1 cycle
- **Area:** Large (CSA tree + final adder)
- **Use Case:** High-performance designs

#### DSP Multiplier (FEAT_DSP_MUL)

```systemverilog
`elsif FEAT_DSP_MUL
  assign unsigned_prod = mul_op_A * mul_op_B;
  assign mul_valid = 1'b1;  // Single-cycle
  assign mul_busy = 1'b0;
`endif
```

**Characteristics:**
- **Latency:** 1 cycle
- **Area:** Uses FPGA DSP blocks
- **Use Case:** FPGA implementations (Xilinx DSP48, Intel DSP)

#### Sequential Multiplier (Default)

```systemverilog
seq_multiplier #(.SIZE(32)) i_seq_multiplier (
  .clk_i(clk_i),
  .rst_ni(rst_ni),
  .start_i(mul_start),
  .busy_o(mul_busy),
  .done_o(mul_done),
  .valid_o(mul_valid),
  .multiplicand_i(mul_op_A),
  .multiplier_i(mul_op_B),
  .product_o(unsigned_prod)
);
```

**Characteristics:**
- **Latency:** 32 cycles
- **Area:** Minimal (shift-add algorithm)
- **Use Case:** Area-constrained designs

#### Restoring Division (divu_int)

```systemverilog
divu_int #(.WIDTH(32)) i_divu_int (
  .clk_i(clk_i),
  .rst_ni(rst_ni),
  .start_i(div_start),
  .busy_o(div_busy),
  .done_o(div_done),
  .valid_o(div_valid),
  .dbz_o(div_dbz),
  .dividend_i(div_op_A),
  .divisor_i(div_op_B),
  .quotient_o(unsigned_quo),
  .reminder_o(unsigned_rem)
);
```

**Characteristics:**
- **Latency:** 32 cycles
- **Algorithm:** Restoring division (shift-subtract)
- **Area:** Minimal

## CSR Operations

### CSRRW (Atomic Read/Write)

```systemverilog
OP_CSRRW: alu_o = alu_a_i;  // Write rs1 to CSR, return old value
```

**Semantics:**
```assembly
csrrw x1, mstatus, x2   # x1 = mstatus, mstatus = x2
```

### CSRRS (Atomic Read/Set)

```systemverilog
OP_CSRRS: alu_o = csr_rdata_i | alu_a_i;  // Set bits, return old value
```

**Semantics:**
```assembly
csrrs x1, mstatus, x2   # x1 = mstatus, mstatus = mstatus | x2
```

**Use Case:** Enable interrupt bits
```assembly
csrrs x0, mie, x1       # Set mie bits (no read needed)
```

### CSRRC (Atomic Read/Clear)

```systemverilog
OP_CSRRC: alu_o = csr_rdata_i & ~alu_a_i;  // Clear bits, return old value
```

**Semantics:**
```assembly
csrrc x1, mstatus, x2   # x1 = mstatus, mstatus = mstatus & ~x2
```

**Use Case:** Disable interrupt bits
```assembly
csrrc x0, mie, x1       # Clear mie bits
```

### Immediate Variants (CSRRWI/CSRRSI/CSRRCI)

```systemverilog
OP_CSRRWI: alu_o = alu_b_i;                 // Write zimm
OP_CSRRSI: alu_o = csr_rdata_i | alu_b_i;   // Set bits (zimm)
OP_CSRRCI: alu_o = csr_rdata_i & ~alu_b_i;  // Clear bits (zimm)
```

**Zimm:** 5-bit zero-extended immediate (0-31)

**Examples:**
```assembly
csrrwi x1, mstatus, 8   # mstatus = 8, x1 = old mstatus
csrrsi x0, mie, 0x888   # mie |= 0x888 (enable M-mode interrupts)
csrrci x0, mie, 0x888   # mie &= ~0x888 (disable M-mode interrupts)
```

## Comparison Flags

### Zero Flag (zero_o)

```systemverilog
zero_o = ($signed(alu_a_i) == $signed(alu_b_i));
```

**Usage:** BEQ/BNE branch conditions

**Examples:**
```assembly
beq x1, x2, target   # Branch if zero_o == 1
bne x1, x2, target   # Branch if zero_o == 0
```

### Signed Less Than (slt_o)

```systemverilog
slt_o = ($signed(alu_a_i) < $signed(alu_b_i));
```

**Usage:** BLT/BGE branch conditions

**Examples:**
```assembly
blt x1, x2, target   # Branch if slt_o == 1
bge x1, x2, target   # Branch if slt_o == 0 || zero_o == 1
```

### Unsigned Less Than (sltu_o)

```systemverilog
sltu_o = ($unsigned(alu_a_i) < $unsigned(alu_b_i));
```

**Usage:** BLTU/BGEU branch conditions

**Examples:**
```assembly
bltu x1, x2, target  # Branch if sltu_o == 1
bgeu x1, x2, target  # Branch if sltu_o == 0 || zero_o == 1
```

## Stall Logic

### Multi-Cycle Operation Stall

```systemverilog
mul_stall = (mul_type && !mul_valid) || (mul_valid && mul_start);
div_stall = (div_type && !div_valid) || (div_valid && div_start);
div_stall &= !div_dbz;  // No stall for divide-by-zero (immediate result)

alu_stall_o = mul_stall || div_stall;
```

**Stall Conditions:**
1. **mul_stall**: Multiply in progress OR multiply just completed (bypass cycle)
2. **div_stall**: Divide in progress (except divide-by-zero)

**Example:**
```assembly
Cycle N:   mul x1, x2, x3      # Start multiply (alu_stall_o = 1)
Cycle N+1: add x4, x1, x5      # Stalled (x1 not ready)
...
Cycle N+32: Multiply done (mul_valid = 1)
Cycle N+33: Resume (alu_stall_o = 0)
```

## Timing & Critical Paths

### Base Integer Operations

**Critical Path:**
```
alu_a_i → Adder/Shifter/Logic → alu_o
```

**Delay:**
- ADD/SUB: ~3-5 ns (32-bit ripple carry adder)
- SLL/SRL/SRA: ~2-4 ns (barrel shifter)
- AND/OR/XOR: ~1-2 ns (parallel logic gates)

### Multiply (Single-Cycle)

**Critical Path (Wallace Tree):**
```
mul_op_A, mul_op_B → CSA tree → Final adder → Sign correction → alu_o
```

**Delay:** ~10-15 ns (FPGA)

### Divide (Multi-Cycle)

**Per-Cycle Path:**
```
remainder_q → Comparator → Subtractor → remainder_next
```

**Delay:** ~5-7 ns per cycle

## Synthesis Considerations

### Area Optimization

**Minimal Configuration:**
```systemverilog
// No defines → Sequential multiply/divide
// Area: ~5000 LUTs (Xilinx 7-series)
```

**DSP Configuration:**
```systemverilog
`define FEAT_DSP_MUL
// Area: ~3000 LUTs + 4 DSP48 blocks
```

**High-Performance Configuration:**
```systemverilog
`define FEAT_WALLACE_SINGLE
// Area: ~8000 LUTs (large CSA tree)
```

### Frequency Optimization

**Pipeline Registers:** ALU result is registered in `execution.sv`

**Critical Frequency:**
- Base ops: 200-300 MHz (FPGA)
- Wallace multiply: 100-150 MHz (FPGA)
- Sequential mul/div: 200-300 MHz (multi-cycle, no critical path)

## Verification

### Test Cases

1. **Arithmetic:**
```assembly
add x1, x2, x3      # Basic addition
addi x1, x2, -1     # Immediate (sign-extended)
sub x1, x0, x3      # Negation (0 - x3)
```

2. **Shift:**
```assembly
slli x1, x2, 31     # Maximum shift
srai x1, x2, 31     # Sign replication (all 1s or 0s)
```

3. **Multiply:**
```assembly
mul x1, x0, x3      # Multiply by zero
mulh x1, x2, x2     # Square (high bits)
```

4. **Divide:**
```assembly
div x1, x2, x0      # Divide by zero (x1 = -1)
div x1, x2, x2      # Self-divide (x1 = 1)
rem x1, x2, x3      # Remainder sign check
```

### Assertions

```systemverilog
// Zero flag correctness
assert property (@(posedge clk_i)
  zero_o == ($signed(alu_a_i) == $signed(alu_b_i)));

// Signed comparison
assert property (@(posedge clk_i)
  slt_o == ($signed(alu_a_i) < $signed(alu_b_i)));

// Divide by zero handling
assert property (@(posedge clk_i)
  (div_dbz && (op_sel_i inside {OP_DIV, OP_DIVU})) |-> (alu_o == '1));
```

## İlgili Modüller

1. **execution.sv**: ALU wrapper
2. **mul_int.sv**: Sequential multiplier
3. **divu_int.sv**: Restoring divider
4. **wallace32x32**: Wallace tree multiplier

## Referanslar

1. RISC-V Unprivileged ISA Specification v20191213 - Chapter 2 (RV32I), Chapter 7 (RV32M)
2. "Computer Arithmetic: Algorithms and Hardware Designs" - Behrooz Parhami
3. "Digital Arithmetic" - Ercegovac & Lang

---

**Son Güncelleme:** 5 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
