# MUL_INT (Sequential Multiplier) Modülü - Teknik Döküman

## Genel Bakış

`mul_int.sv` modülü, **shift-add algoritması** kullanarak 32×32-bit unsigned multiplication yapan sequential (çok-döngülü) bir çarpıcıdır. Minimal alan kullanımı için tasarlanmıştır ve 32 cycle'da sonuç üretir.

## Algoritma

### Shift-Add Multiplication

**Temel Prensip:**
```
A × B = A × (b₃₁·2³¹ + b₃₀·2³⁰ + ... + b₁·2¹ + b₀·2⁰)
      = A·b₃₁·2³¹ + A·b₃₀·2³⁰ + ... + A·b₁·2¹ + A·b₀·2⁰
```

**Adım Adım:**
1. Product = 0, Multiplier = B
2. Her cycle:
   - Eğer Multiplier MSB = 1 → Product += Multiplicand
   - Product << 1 (shift left)
   - Multiplier << 1 (next bit to MSB)
3. 32 iteration sonra: Product = A × B

### Example (8-bit)

```
A = 6 (0b00000110)
B = 5 (0b00000101)

Cycle 0: mult = 0b00000101, product = 0
Cycle 1: MSB=0 → product = 0 << 1 = 0
Cycle 2: MSB=0 → product = 0 << 1 = 0
Cycle 3: MSB=0 → product = 0 << 1 = 0
Cycle 4: MSB=0 → product = 0 << 1 = 0
Cycle 5: MSB=0 → product = 0 << 1 = 0
Cycle 6: MSB=1 → product = (0 + 6) << 1 = 12
Cycle 7: MSB=0 → product = 12 << 1 = 24
Cycle 8: MSB=1 → product = (24 + 6) << 0 = 30 (last cycle, no shift)

Result: 30 (6 × 5)
```

## Port Tanımları

### Giriş Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `start_i` | logic | Başlat sinyali (1 cycle pulse) |
| `multiplicand_i` | [SIZE-1:0] | Çarpılan (A) - unsigned |
| `multiplier_i` | [SIZE-1:0] | Çarpan (B) - unsigned |

### Çıkış Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `product_o` | [2*SIZE-1:0] | Çarpım sonucu (64-bit for RV32) |
| `busy_o` | logic | İşlem devam ediyor (1 = busy) |
| `done_o` | logic | İşlem tamamlandı (1 cycle pulse) |
| `valid_o` | logic | Sonuç geçerli (1 = valid) |

## İç Sinyaller

```systemverilog
logic [SIZE-1:0] mult;              // Multiplier (shifted)
logic [$clog2(SIZE)-1:0] counter;   // Cycle counter (0-31)
logic shift;                        // Shift enable
```

**shift Logic:**
```systemverilog
assign shift = |(counter ^ 31);  // 1 if counter < 31, 0 if counter == 31
```

## State Machine

### States

1. **IDLE**: `busy_o = 0`, waiting for `start_i`
2. **BUSY**: `busy_o = 1`, performing multiplication (32 cycles)
3. **DONE**: `done_o = 1`, `valid_o = 1` (1 cycle)

### State Transitions

```
IDLE --[start_i]--> BUSY --[counter==31]--> DONE --[auto]--> IDLE
```

## Implementation Logic

### Start Condition

```systemverilog
if (start_i) begin
  mult <= multiplier_i;      // Load multiplier
  product_o <= '0;           // Clear product
  counter <= '0;             // Reset counter
  busy_o <= 1'b1;            // Set busy
  valid_o <= 1'b0;           // Clear valid
end
```

### Iteration Step

```systemverilog
if (busy_o) begin
  mult <= mult << 1;                                          // Shift multiplier left
  product_o <= (product_o + (multiplicand_i & {SIZE{mult[SIZE-1]}})) << shift;
  counter <= counter + shift;
  
  done_o <= (counter + 1'b1 == 32'd32) ? 1'b1 : 1'b0;        // Done when counter = 31
  busy_o <= (counter + 1'b1 == 32'd32) ? 1'b0 : 1'b1;
  valid_o <= (counter + 1'b1 == 32'd32) ? 1'b1 : 1'b0;
end
```

**Key Operations:**
1. **`mult << 1`**: Shift multiplier left (next bit to MSB)
2. **`{SIZE{mult[SIZE-1]}}`**: Replicate MSB (0x00000000 or 0xFFFFFFFF)
3. **`multiplicand_i & {SIZE{mult[SIZE-1]}}`**: Conditional add (MSB=1 → add, MSB=0 → 0)
4. **`<< shift`**: Conditional shift (shift=1 for cycles 0-30, shift=0 for cycle 31)

### Last Cycle Optimization

**Problem:** Cycle 31'de shift gerekmez (sonuç hazır)

**Solution:**
```systemverilog
shift = |(counter ^ 31);  // 0 when counter == 31
```

**Benefit:** Product son cycle'da shift edilmez → doğru sonuç

## Timing Diagram

```
Cycle:     0    1    2   ...  31   32   33
           ___   ___   ___      ___  ___  ___
clk:      |   |_|   |_|   |_..._|   ||   ||   |

start_i:  ‾‾‾\___________________________

busy_o:   ____/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\____

counter:  0    0    1    2   ...  30   31   0

done_o:   ___________________________/‾\___

valid_o:  ___________________________/‾‾‾\__

product_o: 0    P₀   P₁   P₂  ...  P₃₀  Final
```

**Cycle Breakdown:**
- **Cycle 0**: `start_i = 1` → Initialize
- **Cycles 1-31**: Iteration (add + shift)
- **Cycle 32**: `done_o = 1`, `valid_o = 1`, `product_o = A × B`
- **Cycle 33**: Return to IDLE

## Example: 6 × 5 (32-bit)

```
A = 0x00000006, B = 0x00000005

Cycle 0: start_i=1
  mult = 0x00000005
  product_o = 0x00000000
  counter = 0

Cycle 1: mult MSB=0
  product_o = (0 + 0) << 1 = 0x00000000
  mult = 0x0000000A
  counter = 1

...

Cycle 29: mult MSB=0
  product_o = 0x00000018 (24 << 1)
  mult = 0x80000000
  counter = 29

Cycle 30: mult MSB=1
  product_o = (0x00000018 + 0x00000006) << 1 = 0x0000003C (30 << 1 = 60)
  mult = 0x00000000
  counter = 30

Cycle 31: mult MSB=0
  product_o = (0x0000003C + 0) << 0 = 0x0000003C (no shift, counter=31)
  counter = 31

Cycle 32: done_o=1, valid_o=1
  product_o = 0x0000001E (30)
```

**Result:** 30 (6 × 5) ✓

## Area & Performance

### Resource Usage

**Xilinx 7-Series FPGA:**
- **LUTs:** ~150-200 (32-bit adder + control logic)
- **Registers:** ~100 (mult, product_o, counter, state)
- **DSP Blocks:** 0 (pure logic, no DSP)

**ASIC (typical 28nm):**
- **Gates:** ~1500-2000
- **Area:** ~0.01 mm²

### Latency

**Fixed Latency:** 32 cycles (independent of operand values)

**Throughput:**
- **Without Pipelining:** 1 multiply per 32 cycles
- **With Pipelining (multiple instances):** 1 multiply per cycle (32× area)

### Critical Path

```
mult[MSB] → AND gate → 32-bit Adder → Register → product_o
```

**Delay:** ~4-6 ns (FPGA), allows 200-300 MHz operation

## Comparison with Other Multipliers

| Type | Latency | Area | Use Case |
|------|---------|------|----------|
| Sequential (shift-add) | 32 cycles | Minimal | Embedded, low-power |
| Wallace Tree | 1 cycle | Large | High-performance |
| Booth Radix-4 | 16 cycles | Medium | Balanced |
| DSP Block (FPGA) | 1-3 cycles | Dedicated | FPGA designs |

## Integration with ALU

### alu.sv Interface

```systemverilog
`ifndef FEAT_WALLACE_SINGLE
`ifndef FEAT_DSP_MUL

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

`endif
`endif
```

### Stall Logic

```systemverilog
mul_start = mul_type && !mul_busy && !alu_stall_q;
mul_stall = (mul_type && !mul_valid) || (mul_valid && mul_start);
alu_stall_o = mul_stall || div_stall;
```

**Stall Behavior:**
- `mul_start = 1`: Start new multiply
- `mul_busy = 1`: Multiply in progress (stall pipeline)
- `mul_valid = 1`: Result ready (1 cycle)
- Next multiply can start after `valid_o = 1`

## Verification

### Test Cases

1. **Simple Multiply:**
```
A = 5, B = 7 → Product = 35
A = 1, B = 1 → Product = 1
A = 0, B = 100 → Product = 0
```

2. **Large Values:**
```
A = 0xFFFFFFFF, B = 2 → Product = 0x00000001FFFFFFFE
A = 0x10000, B = 0x10000 → Product = 0x100000000
```

3. **Power of 2:**
```
A = 16, B = 16 → Product = 256 (shift-only case)
```

4. **Sequential Multiplies:**
```assembly
mul x1, x2, x3   # 32 cycles
mul x4, x5, x6   # 32 cycles (starts after first completes)
```

### Assertions

```systemverilog
// Counter wraps at 31
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (busy_o && counter == 31) |=> !busy_o);

// Product valid when done
assert property (@(posedge clk_i) disable iff (!rst_ni)
  done_o |-> valid_o);

// Busy cleared when done
assert property (@(posedge clk_i) disable iff (!rst_ni)
  done_o |=> !busy_o);

// Product stable after valid
assert property (@(posedge clk_i) disable iff (!rst_ni)
  valid_o |=> $stable(product_o));
```

## Optimization Opportunities

### 1. Early Termination

**Idea:** If remaining multiplier bits are 0, terminate early

```systemverilog
if (mult == '0) begin
  busy_o <= 1'b0;
  done_o <= 1'b1;
  valid_o <= 1'b1;
end
```

**Benefit:** Variable latency (average ~16 cycles for random data)

### 2. Radix-4 Booth Encoding

**Idea:** Process 2 bits per cycle → 16 cycles

**Trade-off:** 2× area (more complex adder)

### 3. Pipelined Design

**Idea:** Multiple multipliers in parallel

**Benefit:** 1 multiply per cycle throughput

**Cost:** 32× area

## Usage Guidelines

### When to Use Sequential Multiplier

✅ **Good For:**
- Embedded systems (area-constrained)
- Low-frequency designs (< 50 MHz)
- Infrequent multiply operations
- Battery-powered devices (low power)

❌ **Not Good For:**
- High-performance computing
- DSP applications (use DSP blocks)
- Tight multiply-dependent loops

### Configuration

**Select in build system:**
```makefile
# Default: Sequential multiplier (minimal area)
# No flags needed

# High-performance: Wallace tree
CFLAGS += -DFEAT_WALLACE_SINGLE

# FPGA: DSP blocks
CFLAGS += -DFEAT_DSP_MUL
```

## İlgili Modüller

1. **alu.sv**: ALU wrapper, sign management
2. **wallace32x32**: Wallace tree alternative
3. **execution.sv**: Pipeline integration

## Referanslar

1. "Computer Arithmetic: Algorithms and Hardware Designs" - Behrooz Parhami, Chapter 9 (Multiplication)
2. "Digital Design and Computer Architecture" - Harris & Harris, Section 5.2 (Multiplication)
3. RISC-V Unprivileged ISA Specification v20191213 - Chapter 7 (RV32M)

---

**Son Güncelleme:** 5 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
