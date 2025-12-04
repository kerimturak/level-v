# DIVU_INT (Restoring Division) Modülü - Teknik Döküman

## Genel Bakış

`divu_int.sv` modülü, **restoring division algoritması** kullanarak 32÷32-bit unsigned division yapan sequential bir bölücüdür. Minimal alan kullanımı için tasarlanmıştır ve 32 cycle'da quotient ve remainder üretir.

## Algoritma

### Restoring Division

**Temel Prensip:**
```
dividend = quotient × divisor + remainder
A ÷ B = Q ... R  (A = Q×B + R)
```

**Long Division (Binary):**
1. Remainder = 0, Quotient = Dividend
2. Her cycle:
   - Shift: {Remainder, Quotient} << 1
   - Trial subtraction: Remainder - Divisor
   - If result >= 0: Quotient[0] = 1, keep subtraction
   - If result < 0: Quotient[0] = 0, restore (add back divisor)
3. 32 iteration sonra: Quotient = A ÷ B, Remainder = A % B

### Optimization: Non-Restoring

Bu implementasyon **restoring** kullanır (negatif sonuç üzerine geri ekleme yapar).

**Alternative:** Non-restoring division (restore gerektirmez, daha hızlı)

### Example (8-bit)

```
A = 15 (0b00001111), B = 4 (0b00000100)

Initial: remainder = 0b00000000, quotient = 0b00001111

Cycle 1: {rem, quo} << 1 = {0b00000000, 0b00011110}
         rem = 0b0 0000001 (upper 9 bits)
         rem - divisor = 0b0 00000001 - 0b0 00000100 = -3 (negative)
         → Restore, quotient[0] = 0

Cycle 2: {rem, quo} << 1
         rem = 0b0 00000011
         rem - divisor = 0b0 00000011 - 0b0 00000100 = -1 (negative)
         → Restore, quotient[0] = 0

Cycle 3: {rem, quo} << 1
         rem = 0b0 00000111
         rem - divisor = 0b0 00000111 - 0b0 00000100 = 3 (positive)
         → Keep, quotient[0] = 1

Cycle 4: {rem, quo} << 1
         rem = 0b0 00000110
         rem - divisor = 0b0 00000110 - 0b0 00000100 = 2 (positive)
         → Keep, quotient[0] = 1

...

Cycle 8: done
         quotient = 0b00000011 (3)
         remainder = 0b00000011 (3)

Result: 15 ÷ 4 = 3 R 3  (15 = 3×4 + 3) ✓
```

## Port Tanımları

### Giriş Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `start_i` | logic | Başlat sinyali (1 cycle pulse) |
| `dividend_i` | [WIDTH-1:0] | Bölünen (A) - unsigned |
| `divisor_i` | [WIDTH-1:0] | Bölen (B) - unsigned |

### Çıkış Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `quotient_o` | [WIDTH-1:0] | Bölüm (A ÷ B) |
| `reminder_o` | [WIDTH-1:0] | Kalan (A % B) |
| `busy_o` | logic | İşlem devam ediyor (1 = busy) |
| `done_o` | logic | İşlem tamamlandı (1 cycle pulse) |
| `valid_o` | logic | Sonuç geçerli (1 = valid) |
| `dbz_o` | logic | Divide by zero (1 = zero divisor) |

## İç Sinyaller

```systemverilog
logic [WIDTH-1:0] divisor_q;       // Divisor (registered)
logic [WIDTH-1:0] quotient_q;      // Quotient (shifted)
logic [WIDTH:0] remainder_q;       // Remainder (WIDTH+1 bits, extra for sign)
logic [$clog2(WIDTH+1)-1:0] count_q;  // Cycle counter (0-WIDTH)

logic [WIDTH-1:0] quotient_next;
logic [WIDTH:0] remainder_next;
```

**Extra Bit:** `remainder_q` is WIDTH+1 bits to detect negative results

## Implementation Logic

### Division Step (Combinational)

```systemverilog
always_comb begin
  // Shift left: {remainder, quotient} << 1
  remainder_next = {remainder_q[WIDTH-1:0], quotient_q[WIDTH-1]};
  quotient_next = {quotient_q[WIDTH-2:0], 1'b0};
  
  // Trial subtraction: remainder - divisor
  if (remainder_next >= {1'b0, divisor_q}) begin
    remainder_next = remainder_next - {1'b0, divisor_q};  // Keep subtraction
    quotient_next[0] = 1'b1;                              // Set quotient bit
  end
  // Else: restore (do nothing), quotient[0] = 0 (already set above)
end
```

**Key Operations:**
1. **Shift**: `{remainder[31:0], quotient[31]}` → Bring next dividend bit into remainder
2. **Comparison**: `remainder >= divisor` (unsigned comparison)
3. **Conditional Subtract**: If true, subtract and set quotient bit

### State Machine

#### Start Condition

```systemverilog
if (start_i) begin
  if (divisor_i == '0) begin
    // Divide by zero: immediate done
    busy_o <= 1'b0;
    done_o <= 1'b1;
    valid_o <= 1'b1;
    dbz_o <= 1'b1;
    quotient_o <= '0;      // Unused (ALU wrapper handles)
    reminder_o <= dividend_i;  // RISC-V spec: remainder = dividend
  end else begin
    // Normal division
    busy_o <= 1'b1;
    done_o <= 1'b0;
    valid_o <= 1'b0;
    dbz_o <= 1'b0;
    
    divisor_q <= divisor_i;
    quotient_q <= dividend_i;  // Initialize quotient with dividend
    remainder_q <= '0;         // Initialize remainder to 0
    count_q <= WIDTH[$clog2(WIDTH+1)-1:0];  // Set counter to WIDTH (32)
  end
end
```

#### Iteration Step

```systemverilog
if (busy_o) begin
  remainder_q <= remainder_next;
  quotient_q <= quotient_next;
  
  if (count_q == 1) begin
    // Last step
    busy_o <= 1'b0;
    done_o <= 1'b1;
    valid_o <= 1'b1;
    
    quotient_o <= quotient_next;
    reminder_o <= remainder_next[WIDTH-1:0];  // Drop sign bit
    
    count_q <= '0;
  end else begin
    // Continue
    count_q <= count_q - 1'b1;
  end
end
```

## Timing Diagram

```
Cycle:     0    1    2   ...  32   33   34
           ___   ___   ___      ___  ___  ___
clk:      |   |_|   |_|   |_..._|   ||   ||   |

start_i:  ‾‾‾\___________________________

busy_o:   ____/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\____

count_q:  32   32   31   30  ...  1    0    0

done_o:   ___________________________/‾\___

valid_o:  ___________________________/‾‾‾\__

quotient_o: X    Q₀   Q₁   Q₂  ...  Q₃₁  Final
```

**Cycle Breakdown:**
- **Cycle 0**: `start_i = 1` → Initialize
- **Cycles 1-32**: Iteration (shift-subtract)
- **Cycle 33**: `done_o = 1`, `valid_o = 1`, `quotient_o = A ÷ B`, `reminder_o = A % B`
- **Cycle 34**: Return to IDLE

## Divide by Zero Handling

### Detection

```systemverilog
if (divisor_i == '0) begin
  dbz_o <= 1'b1;
end
```

### RISC-V Specification

**Divide by zero behavior (RISC-V spec):**
- **DIV/DIVU**: `quotient = -1` (0xFFFFFFFF)
- **REM/REMU**: `remainder = dividend`

**Implementation:** Handled in ALU wrapper (`alu.sv`):

```systemverilog
// alu.sv
if (div_dbz) begin
  div_quot_final = (op_sel_i inside {OP_DIV, OP_DIVU}) ? 32'hFFFF_FFFF : unsigned_quo;
  div_rem_final = alu_a_i;  // remainder = dividend
end
```

## Example: 15 ÷ 4

```
A = 0x0000000F, B = 0x00000004

Cycle 0: start_i=1
  divisor_q = 0x00000004
  quotient_q = 0x0000000F
  remainder_q = 0x000000000
  count_q = 32

Cycle 1:
  remainder_next = {0x00000000[30:0], 0x0000000F[31]} = 0x000000000
  quotient_next = {0x0000000F[30:0], 1'b0} = 0x0000001E
  0x000000000 >= 0x000000004? NO
  → quotient_next[0] = 0
  count_q = 31

Cycle 2:
  remainder_next = {0x00000000[30:0], 0x0000001E[31]} = 0x000000000
  quotient_next = {0x0000001E[30:0], 1'b0} = 0x0000003C
  0x000000000 >= 0x000000004? NO
  → quotient_next[0] = 0
  count_q = 30

Cycle 3:
  remainder_next = {0x00000000[30:0], 0x0000003C[31]} = 0x000000000
  quotient_next = {0x0000003C[30:0], 1'b0} = 0x00000078
  0x000000000 >= 0x000000004? NO
  count_q = 29

Cycle 4:
  remainder_next = {0x00000000[30:0], 0x00000078[31]} = 0x000000000
  quotient_next = {0x00000078[30:0], 1'b0} = 0x000000F0
  0x000000000 >= 0x000000004? NO
  count_q = 28

Cycle 5:
  remainder_next = {0x00000000[30:0], 0x000000F0[31]} = 0x000000001
  quotient_next = {0x000000F0[30:0], 1'b0} = 0x000001E0
  0x000000001 >= 0x000000004? NO
  count_q = 27

... (omitted for brevity)

Cycle 29:
  remainder_next = 0x00000007
  quotient_next = 0x00000007
  0x00000007 >= 0x00000004? YES
  → remainder_next = 0x00000007 - 0x00000004 = 0x00000003
  → quotient_next[0] = 1 → 0x00000007
  count_q = 3

Cycle 30:
  remainder_next = 0x00000006
  quotient_next = 0x0000000E
  0x00000006 >= 0x00000004? YES
  → remainder_next = 0x00000002
  → quotient_next[0] = 1 → 0x0000000F
  count_q = 2

Cycle 31:
  remainder_next = 0x00000005
  quotient_next = 0x0000001E
  0x00000005 >= 0x00000004? YES
  → remainder_next = 0x00000001
  → quotient_next[0] = 1 → 0x0000001F
  count_q = 1

Cycle 32:
  remainder_next = 0x00000003
  quotient_next = 0x0000003E
  0x00000003 >= 0x00000004? NO
  → quotient_next[0] = 0 → 0x0000003E
  count_q = 0
  done_o = 1

Cycle 33: valid_o = 1
  quotient_o = 0x00000003 (3)
  reminder_o = 0x00000003 (3)
```

**Result:** 15 ÷ 4 = 3 R 3 ✓

## Area & Performance

### Resource Usage

**Xilinx 7-Series FPGA:**
- **LUTs:** ~200-250 (33-bit subtractor + comparator + control)
- **Registers:** ~100 (divisor_q, quotient_q, remainder_q, count_q, state)
- **DSP Blocks:** 0 (pure logic)

**ASIC (typical 28nm):**
- **Gates:** ~2000-2500
- **Area:** ~0.015 mm²

### Latency

**Fixed Latency:** 32 cycles (independent of operand values)

**Exception:** Divide by zero → 1 cycle (immediate done)

### Critical Path

```
remainder_q → Comparator → Subtractor → Mux → remainder_next → Register
```

**Delay:** ~5-7 ns (FPGA), allows 150-200 MHz operation

## Comparison with Other Dividers

| Type | Latency | Area | Use Case |
|------|---------|------|----------|
| Restoring | 32 cycles | Minimal | Embedded, low-power |
| Non-restoring | 32 cycles | Minimal | Slightly faster |
| SRT Division | 16-32 cycles | Medium | Balanced |
| Newton-Raphson | Variable | Large | High-precision |
| Goldschmidt | Variable | Large | Floating-point |

## Integration with ALU

### alu.sv Interface

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

### Signed Division Wrapper

**ALU handles sign conversion:**

```systemverilog
// Sign determination
div_sign_quot = alu_a_i[XLEN-1] ^ alu_b_i[XLEN-1];  // Quotient sign
div_sign_rem = alu_a_i[XLEN-1];                     // Remainder sign = sign(dividend)

// Absolute values
div_op_A = abs_A;  // |dividend|
div_op_B = abs_B;  // |divisor|

// Sign correction
quotient = div_sign_quot ? -unsigned_quo : unsigned_quo;
remainder = div_sign_rem ? -unsigned_rem : unsigned_rem;
```

### Stall Logic

```systemverilog
div_start = div_type && !div_busy && !(alu_stall_q & !div_dbz);
div_stall = (div_type && !div_valid) || (div_valid && div_start);
div_stall &= !div_dbz;  // No stall for divide-by-zero
alu_stall_o = mul_stall || div_stall;
```

## RISC-V Division Semantics

### Signed Division (DIV/REM)

**Sign Rules:**
- **Quotient sign**: `sign(dividend) XOR sign(divisor)`
- **Remainder sign**: `sign(dividend)`

**Examples:**
```
 7 ÷  2 =  3 R  1
 7 ÷ -2 = -3 R  1
-7 ÷  2 = -3 R -1
-7 ÷ -2 =  3 R -1
```

### Overflow (DIV)

**Special Case:** `MIN_INT ÷ -1`

```
0x80000000 ÷ 0xFFFFFFFF = 0x80000000  (saturation, not overflow exception)
```

**Handled in ALU:**
```systemverilog
// Overflow detection
if ((alu_a_i == 32'h8000_0000) && (alu_b_i == 32'hFFFF_FFFF)) begin
  div_quot_final = 32'h8000_0000;  // Saturate
end
```

### Unsigned Division (DIVU/REMU)

**Straightforward:** No sign handling

**Examples:**
```
0xFFFFFFFF ÷ 2 = 0x7FFFFFFF R 1
10 ÷ 3 = 3 R 1
```

## Verification

### Test Cases

1. **Simple Division:**
```
15 ÷ 4 = 3 R 3
10 ÷ 5 = 2 R 0
7 ÷ 8 = 0 R 7
```

2. **Divide by Zero:**
```
100 ÷ 0 = -1 R 100  (RISC-V spec)
```

3. **Signed Division:**
```
-7 ÷ 2 = -3 R -1   (DIV)
-7 ÷ -2 = 3 R -1
```

4. **Overflow:**
```
0x80000000 ÷ -1 = 0x80000000  (saturation)
```

5. **Large Values:**
```
0xFFFFFFFF ÷ 2 = 0x7FFFFFFF R 1  (DIVU)
```

### Assertions

```systemverilog
// Counter decrements correctly
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (busy_o && count_q > 0) |=> (count_q == $past(count_q) - 1));

// Divide by zero immediate done
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (start_i && divisor_i == '0) |=> (done_o && dbz_o));

// Result valid when done
assert property (@(posedge clk_i) disable iff (!rst_ni)
  done_o |-> valid_o);

// Remainder < divisor (for non-zero divisor)
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (valid_o && !dbz_o) |-> (reminder_o < divisor_q));
```

## Optimization Opportunities

### 1. Non-Restoring Division

**Idea:** Skip restore step (add/subtract based on previous result sign)

**Benefit:** Slightly faster (no conditional restore)

**Trade-off:** More complex control logic

### 2. SRT Division (Radix-4)

**Idea:** Process 2 bits per cycle → 16 cycles

**Benefit:** 2× faster

**Trade-off:** Larger area (quotient digit selection logic)

### 3. Early Termination

**Idea:** If quotient bits settled early, terminate

**Challenge:** Hard to detect convergence

## Usage Guidelines

### When to Use Restoring Division

✅ **Good For:**
- Embedded systems (area-constrained)
- Infrequent division operations
- Low-power designs

❌ **Not Good For:**
- DSP applications (many divisions)
- High-performance computing

### Configuration

**Select in build system:**
```makefile
# Default: Restoring division (minimal area)
# No alternatives currently implemented
```

## İlgili Modüller

1. **alu.sv**: ALU wrapper, sign management, RISC-V semantics
2. **execution.sv**: Pipeline integration
3. **mul_int.sv**: Companion multiplier module

## Referanslar

1. "Computer Arithmetic: Algorithms and Hardware Designs" - Behrooz Parhami, Chapter 13 (Division)
2. "Digital Arithmetic" - Ercegovac & Lang, Chapter 6 (Division)
3. RISC-V Unprivileged ISA Specification v20191213 - Chapter 7 (RV32M, Division Semantics)
4. ProjectF - "Division in Verilog" (https://projectf.io/posts/division-in-verilog/)

---

**Son Güncelleme:** 5 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
