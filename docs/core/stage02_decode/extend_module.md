# EXTEND (Immediate Generator) Modülü - Teknik Döküman

## Genel Bakış

`extend.sv` modülü, RISC-V instruction'larından immediate değerleri çıkarır ve 32-bit'e genişletir (sign/zero extension). Instruction format'ına göre (I, S, B, U, J, CSR) bit shuffling ve extension işlemlerini yapar. Tamamen combinational logic ile çalışır.

## RISC-V Immediate Formats

RISC-V instruction encoding'inde immediate değerler efficiency için bit shuffle edilmiş şekilde saklanır. Extend modülü bu bit'leri doğru sıraya koyar ve genişletir.

### Format Özeti

| Format | Bit Count | Alignment | Extension Type | Kullanım |
|--------|-----------|-----------|----------------|----------|
| I-Type | 12-bit | Byte | Sign | ADDI, Load, JALR |
| S-Type | 12-bit | Byte | Sign | Store |
| B-Type | 13-bit | 2-byte | Sign | Branch |
| U-Type | 20-bit | 4KB | Direct | LUI, AUIPC |
| J-Type | 21-bit | 2-byte | Sign | JAL |
| CSR-Imm | 5-bit | Byte | Zero | CSR immediate |

## Port Tanımları

### Giriş Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `imm_i` | [31:7] | Instruction'ın immediate bit'leri (bit 31-7) |
| `sel_i` | imm_e | Immediate format seçimi (control unit'ten) |

**imm_e enum:**
```systemverilog
typedef enum logic [2:0] {
  NO_IMM,   // No immediate (0x00000000)
  I_IMM,    // I-type: 12-bit signed immediate
  I_USIMM,  // I-type: 12-bit unsigned immediate (shift amount)
  S_IMM,    // S-type: 12-bit signed immediate
  B_IMM,    // B-type: 13-bit signed immediate
  U_IMM,    // U-type: 20-bit immediate (upper)
  J_IMM,    // J-type: 21-bit signed immediate
  CSR_IMM   // CSR: 5-bit zero-extended immediate (zimm)
} imm_e;
```

### Çıkış Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `imm_o` | [31:0] | Sign/zero extended 32-bit immediate değer |

## Immediate Format Details

### 1. I-Type Immediate (I_IMM)

```systemverilog
I_IMM: imm_o = {{20{imm_i[31]}}, imm_i[31:20]};
```

**Instruction Layout:**
```
31          20 19   15 14  12 11    7 6     0
+------------+-------+------+-------+-------+
| imm[11:0]  |  rs1  | f3   |  rd   | opcode|
+------------+-------+------+-------+-------+
```

**Extraction:**
- Immediate: `inst[31:20]` (12-bit)
- Sign-extend: Repeat bit 31 (sign bit) 20 times
- Result: 32-bit signed immediate

**Range:** -2048 to +2047 (12-bit signed)

**Örnekler:**
```assembly
addi x1, x2, 12       # imm = 12 (0x00000000C)
addi x1, x2, -5       # imm = -5 (0xFFFFFFFB)
lw x1, 8(x2)          # imm = 8 (offset)
jalr x1, 0(x2)        # imm = 0
```

### 2. I-Type Unsigned Immediate (I_USIMM)

```systemverilog
I_USIMM: imm_o = {{20{1'b0}}, imm_i[31:20]};
```

**Kullanım:** Shift instruction'ları (slli, srli, srai)

**Extraction:**
- Immediate: `inst[31:20]` (12-bit)
- Zero-extend: Pad with 20 zeros
- Result: 32-bit unsigned immediate

**Range:** 0 to 4095 (12-bit unsigned)

**Örnekler:**
```assembly
slli x1, x2, 5   # imm = 5 (shift amount)
srli x1, x2, 10  # imm = 10
srai x1, x2, 15  # imm = 15
```

**Not:** RV32I'de shift amount 5-bit (0-31), üst 7 bit illegal (control_unit check eder)

### 3. S-Type Immediate (S_IMM)

```systemverilog
S_IMM: imm_o = {{20{imm_i[31]}}, imm_i[31:25], imm_i[11:7]};
```

**Instruction Layout:**
```
31       25 24   20 19   15 14  12 11       7 6     0
+---------+-------+-------+------+---------+-------+
|imm[11:5]|  rs2  |  rs1  | f3   |imm[4:0] | opcode|
+---------+-------+-------+------+---------+-------+
```

**Extraction:**
- Immediate upper: `inst[31:25]` → `imm[11:5]`
- Immediate lower: `inst[11:7]` → `imm[4:0]`
- Concatenate: `{imm[11:5], imm[4:0]}`
- Sign-extend: Repeat bit 31

**Range:** -2048 to +2047 (12-bit signed)

**Örnekler:**
```assembly
sw x3, 8(x2)   # imm = 8 (offset)
sh x4, -4(x5)  # imm = -4 (0xFFFFFFC)
sb x6, 0(x7)   # imm = 0
```

**Why Split?** 
- rd field'i (inst[11:7]) S-type'da kullanılmaz
- Immediate bit'leri rs1/rs2'nin etrafına dağıtılır (decoder simplicity)

### 4. B-Type Immediate (B_IMM)

```systemverilog
B_IMM: imm_o = {{20{imm_i[31]}}, imm_i[7], imm_i[30:25], imm_i[11:8], 1'b0};
```

**Instruction Layout:**
```
31  30    25 24   20 19   15 14  12 11  8 7  6     0
+--+-------+-------+-------+------+----+--+-------+
|12|11:5   |  rs2  |  rs1  | f3   |4:1 |11| opcode|
+--+-------+-------+------+------+----+--+-------+
```

**Extraction:**
- `imm[12]`: `inst[31]`
- `imm[11]`: `inst[7]`
- `imm[10:5]`: `inst[30:25]`
- `imm[4:1]`: `inst[11:8]`
- `imm[0]`: Hardwired 0 (2-byte alignment)
- Sign-extend: Repeat bit 31

**Range:** -4096 to +4094 (13-bit signed, even values only)

**Örnekler:**
```assembly
beq x1, x2, 8      # imm = 8 (PC + 8)
bne x3, x4, -12    # imm = -12 (PC - 12)
blt x5, x6, 100    # imm = 100
```

**Why Shuffled?**
- Hardware decoder optimization
- Immediate encoding matches sign bit position (inst[31])

**2-Byte Alignment:**
- LSB (imm[0]) always 0 → Branch target aligned to 2-byte boundary
- Supports compressed instructions (16-bit) aligned access

### 5. U-Type Immediate (U_IMM)

```systemverilog
U_IMM: imm_o = {imm_i[31:12], 12'b0};
```

**Instruction Layout:**
```
31                 12 11    7 6     0
+--------------------+-------+-------+
|    imm[31:12]      |  rd   | opcode|
+--------------------+-------+-------+
```

**Extraction:**
- Immediate upper: `inst[31:12]` → `imm[31:12]`
- Immediate lower: 12 zeros → `imm[11:0]`
- No sign extension (direct placement)

**Range:** 0x00000000 to 0xFFFFF000 (4KB aligned)

**Örnekler:**
```assembly
lui x1, 0x12345    # x1 = 0x12345000
auipc x2, 0x10000  # x2 = PC + 0x10000000
```

**Kullanım:**
- **LUI (Load Upper Immediate):** Load 20-bit constant to upper 20 bits
- **AUIPC (Add Upper Immediate to PC):** PC + (imm << 12)

**Why 12 zeros?**
- Allows constructing full 32-bit constants:
```assembly
lui x1, 0x12345    # x1 = 0x12345000
addi x1, x1, 0x678 # x1 = 0x12345678
```

### 6. J-Type Immediate (J_IMM)

```systemverilog
J_IMM: imm_o = {{12{imm_i[31]}}, imm_i[19:12], imm_i[20], imm_i[30:21], 1'b0};
```

**Instruction Layout:**
```
31  30       21 20 19       12 11    7 6     0
+--+----------+--+----------+-------+-------+
|20|10:1      |11|19:12     |  rd   | opcode|
+--+----------+--+----------+-------+-------+
```

**Extraction:**
- `imm[20]`: `inst[31]`
- `imm[19:12]`: `inst[19:12]`
- `imm[11]`: `inst[20]`
- `imm[10:1]`: `inst[30:21]`
- `imm[0]`: Hardwired 0 (2-byte alignment)
- Sign-extend: Repeat bit 31 (12 times)

**Range:** -1048576 to +1048574 (21-bit signed, even values only)

**Örnekler:**
```assembly
jal x1, 100        # Jump to PC + 100, x1 = PC + 4
jal x0, -8         # Jump to PC - 8 (loop), no link
```

**Why Complex Shuffling?**
- Instruction encoding optimization
- Sign bit (imm[20]) at inst[31] for consistency

**2-Byte Alignment:**
- LSB (imm[0]) always 0 → Jump target aligned to 2-byte boundary

### 7. CSR Immediate (CSR_IMM)

```systemverilog
CSR_IMM: imm_o = {27'b0, imm_i[19:15]};
```

**Instruction Layout (CSR Immediate Instructions):**
```
31          20 19   15 14  12 11    7 6     0
+------------+-------+------+-------+-------+
| csr        | zimm  | f3   |  rd   | opcode|
+------------+-------+------+-------+-------+
```

**Extraction:**
- Immediate: `inst[19:15]` (5-bit, zimm field)
- Zero-extend: Pad with 27 zeros
- Result: 32-bit unsigned immediate

**Range:** 0 to 31 (5-bit unsigned)

**Örnekler:**
```assembly
csrrwi x1, mstatus, 5   # CSR[mstatus] = 5 (immediate)
csrrsi x2, mie, 8       # CSR[mie] |= 8
csrrci x3, mip, 3       # CSR[mip] &= ~3
```

**Why zimm?**
- CSR operations often set/clear specific bits
- Small immediate values (0-31) cover most use cases
- No sign extension (bitmask operations)

### 8. NO_IMM

```systemverilog
NO_IMM: imm_o = '0;  // 32'h00000000
```

**Kullanım:**
- R-type instruction'lar (register-register)
- Immediate kullanılmayan instruction'lar

## Immediate Extension Logic

### Sign Extension

**Mantık:** MSB (sign bit) tekrar edilerek 32-bit'e genişletir

```
12-bit signed immediate:  0b0000_0000_1000 (8)
Sign bit (bit 11):        0
Sign-extend (20 bits):    {20{1'b0}} = 20'b0
Result:                   32'h00000008

12-bit signed immediate:  0b1111_1111_1000 (-8)
Sign bit (bit 11):        1
Sign-extend (20 bits):    {20{1'b1}} = 20'hFFFFF
Result:                   32'hFFFFFFF8
```

### Zero Extension

**Mantık:** Üst bit'ler 0 ile doldurulur

```
5-bit unsigned immediate: 0b11111 (31)
Zero-extend (27 bits):    {27{1'b0}} = 27'h0
Result:                   32'h0000001F
```

## Bit Replication Syntax

```systemverilog
{20{imm_i[31]}}  // imm_i[31] bit'ini 20 kez tekrarla
```

**Örnek:**
```
imm_i[31] = 1
{20{imm_i[31]}} = 20'b11111111111111111111

imm_i[31] = 0
{20{imm_i[31]}} = 20'b00000000000000000000
```

## Timing & Synthesis

### Combinational Delay

```
imm_i → Mux (case statement) → Bit shuffling → imm_o
```

**Delay:** ~3-5 logic levels
- Case statement: 2-3 levels (8-way mux)
- Bit concatenation: 1-2 levels (wiring + mux)

**Critical Path:**
```
control_unit (imm_sel) → extend (imm_o) → ALU input mux
```

### Area

- **Logic Overhead:** Minimal (mostly wiring + mux)
- **Synthesis:** Case statement → parallel mux tree
- **No memory/register:** Pure combinational

## Verification Examples

### Test Case 1: I-Type Signed

```systemverilog
// addi x1, x2, -5
imm_i = 25'h1FFFFB;  // inst[31:7] for addi instruction
sel_i = I_IMM;
// Expected: imm_o = 32'hFFFFFFFB (-5)
```

**Calculation:**
```
imm_i[31:20] = 12'hFFB (12-bit)
Sign bit = imm_i[31] = 1
Sign-extend: {20{1'b1}, 12'hFFB} = 32'hFFFFFFFB
```

### Test Case 2: B-Type

```systemverilog
// beq x1, x2, 8
imm_i = 25'h000220;  // Bit shuffling: imm[12|10:5|4:1|11]
sel_i = B_IMM;
// Expected: imm_o = 32'h00000008
```

**Calculation:**
```
imm[12] = imm_i[31] = 0
imm[11] = imm_i[7] = 0
imm[10:5] = imm_i[30:25] = 6'b000000
imm[4:1] = imm_i[11:8] = 4'b0100 (4)
imm[0] = 0 (hardwired)
Result: {20'b0, 1'b0, 6'b0, 4'b0100, 1'b0} = 32'h00000008
```

### Test Case 3: U-Type

```systemverilog
// lui x1, 0x12345
imm_i = 25'h2468A0;  // inst[31:7] = {0x12345, 5'b0}
sel_i = U_IMM;
// Expected: imm_o = 32'h12345000
```

**Calculation:**
```
imm[31:12] = imm_i[31:12] = 20'h12345
imm[11:0] = 12'h000
Result: {20'h12345, 12'h000} = 32'h12345000
```

### Test Case 4: CSR Immediate

```systemverilog
// csrrwi x1, mstatus, 5
imm_i = 25'h00028;  // inst[19:15] = 5
sel_i = CSR_IMM;
// Expected: imm_o = 32'h00000005
```

**Calculation:**
```
zimm = imm_i[19:15] = 5'b00101 (5)
Zero-extend: {27'b0, 5'b00101} = 32'h00000005
```

## Common Pitfalls

### 1. Sign Extension Bug

**Wrong:**
```systemverilog
imm_o = {20'b0, imm_i[31:20]};  // Zero-extend instead of sign-extend
```

**Result:** Negative values become large positive
```
-5 (12'hFFB) → 32'h00000FFB (4091) instead of 32'hFFFFFFFB
```

### 2. Bit Order Confusion

**Wrong:**
```systemverilog
B_IMM: imm_o = {imm_i[31], imm_i[7], imm_i[11:8], imm_i[30:25], 1'b0};
```

**Result:** Incorrect immediate value (bit order swapped)

### 3. Missing LSB Zero

**Wrong:**
```systemverilog
B_IMM: imm_o = {{20{imm_i[31]}}, imm_i[7], imm_i[30:25], imm_i[11:8]};
```

**Result:** Unaligned branch target (missing imm[0]=0)

## Assertions (Önerilen)

```systemverilog
// I-type signed: negative values extend with 1's
assert property (@(posedge clk_i)
  (sel_i == I_IMM && imm_i[31]) |-> (imm_o[31:12] == 20'hFFFFF));

// I-type unsigned: always zero-extend
assert property (@(posedge clk_i)
  (sel_i == I_USIMM) |-> (imm_o[31:12] == 20'h0));

// B-type: LSB always 0
assert property (@(posedge clk_i)
  (sel_i == B_IMM) |-> (imm_o[0] == 1'b0));

// J-type: LSB always 0
assert property (@(posedge clk_i)
  (sel_i == J_IMM) |-> (imm_o[0] == 1'b0));

// U-type: lower 12 bits always 0
assert property (@(posedge clk_i)
  (sel_i == U_IMM) |-> (imm_o[11:0] == 12'h0));

// CSR: upper 27 bits always 0
assert property (@(posedge clk_i)
  (sel_i == CSR_IMM) |-> (imm_o[31:5] == 27'h0));
```

## İlgili Modüller

1. **decode.sv**: Extend modülünü kullanır
2. **control_unit.sv**: `imm_sel` sinyalini üretir
3. **execute.sv**: Extended immediate'i ALU'ya gönderir

## Referanslar

1. RISC-V Unprivileged ISA Specification v20191213 - Chapter 2 (Immediate Encoding)
2. "Computer Organization and Design: RISC-V Edition" - Patterson & Hennessy, Appendix B (Instruction Formats)

---

**Son Güncelleme:** 5 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
