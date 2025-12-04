# REGISTER FILE Modülü - Teknik Döküman

## Genel Bakış

`reg_file.sv` modülü, RISC-V işlemcisinin 32x32-bit genel amaçlı register dosyasıdır (General Purpose Registers - GPRs). Dual-port asenkron read ve single-port senkron write desteği sağlar. x0 register'ı hardwired zero olarak implement edilmiştir.

## RISC-V Register Conventions

### Register Set (x0-x31)

| Register | ABI Name | Description | Saver |
|----------|----------|-------------|-------|
| x0 | zero | Hardwired zero | - |
| x1 | ra | Return address | Caller |
| x2 | sp | Stack pointer | Callee |
| x3 | gp | Global pointer | - |
| x4 | tp | Thread pointer | - |
| x5-x7 | t0-t2 | Temporaries | Caller |
| x8 | s0/fp | Saved register / Frame pointer | Callee |
| x9 | s1 | Saved register | Callee |
| x10-x11 | a0-a1 | Function args / return values | Caller |
| x12-x17 | a2-a7 | Function arguments | Caller |
| x18-x27 | s2-s11 | Saved registers | Callee |
| x28-x31 | t3-t6 | Temporaries | Caller |

**Not:** ABI name'ler assembler'da kullanılır, hardware'de sadece x0-x31 index'leri önemlidir.

## Port Tanımları

### Giriş Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u (senkron write için) |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `rw_en_i` | logic | Write enable (writeback stage'den) |
| `r1_addr_i` | [4:0] | Source register 1 address (rs1) |
| `r2_addr_i` | [4:0] | Source register 2 address (rs2) |
| `waddr_i` | [4:0] | Destination register address (rd, writeback'ten) |
| `wdata_i` | [XLEN-1:0] | Write data (writeback'ten) |

### Çıkış Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `r1_data_o` | [XLEN-1:0] | Source register 1 data |
| `r2_data_o` | [XLEN-1:0] | Source register 2 data |

## Implementation

### Register Array

```systemverilog
logic [XLEN-1:0] registers[31:0];  // 32 registers, x0-x31
```

**Boyut:**
- 32 registers × 32 bits = 1024 bits = 128 bytes

**FPGA Implementation:**
- Distributed RAM: LUT'lar kullanılarak implement edilir
- Block RAM: BRAM primitive'leri kullanılır (daha büyük register file'lar için)

### Asenkron Read Logic

```systemverilog
always_comb begin : register_read
  r1_data_o = registers[r1_addr_i];
  r2_data_o = registers[r2_addr_i];
end
```

**Özellikler:**
- **Combinational Read**: Aynı cycle'da address → data
- **Dual-Port**: İki register aynı anda okunabilir (rs1, rs2)
- **No Latency**: Address geldiği cycle'da data hazır

**x0 Special Case:**
- x0 her zaman 0 okur (register array'de 0 tutulur)
- Reset'te tüm register'lar sıfırlanır, x0 da sıfır kalır

### Senkron Write Logic

```systemverilog
always_ff @(posedge clk_i) begin : register_write
  if (!rst_ni) begin
    registers <= '{default: 0};  // Reset: tüm register'lar sıfır
  end else if (rw_en_i == 1'b1 && waddr_i != 5'b0) begin
    registers[waddr_i] <= wdata_i;
  end
end
```

**Özellikler:**
- **Senkron Write**: Clock rising edge'de write
- **x0 Write Protection**: `waddr_i != 5'b0` kontrolü ile x0'a yazma engellenir
- **Single-Port**: Bir cycle'da sadece bir register yazılabilir

**Timing:**
```
Cycle N:   waddr_i=5, wdata_i=100, rw_en_i=1
Cycle N+1: registers[5] = 100 (write tamamlandı)
           r1_addr_i=5 → r1_data_o=100 (aynı cycle'da okunabilir)
```

## Register File Access Patterns

### Pattern 1: Dual Read, Single Write

```assembly
Cycle N:   add x5, x3, x4    # WB: Write x5
Cycle N+1: sub x6, x5, x7    # DE: Read x5, x7
```

**Cycle N+1 Register File Activity:**
- **Write Port**: x5 ← add result (from Cycle N writeback)
- **Read Port 1**: x5 (rs1 for sub)
- **Read Port 2**: x7 (rs2 for sub)

**Hazard:** Read-after-write (RAW) hazard
- x5 henüz yazılmadı (senkron write, cycle sonunda olur)
- Read ise combinational (cycle başında)
- **Çözüm:** Data forwarding (decode modülünde)

### Pattern 2: Independent Operations

```assembly
Cycle N:   add x5, x3, x4    # WB: Write x5
Cycle N+1: or x6, x10, x11   # DE: Read x10, x11 (x5 değil)
```

**No Hazard:**
- Write x5, read x10/x11 → No conflict
- Forwarding gerekmez

### Pattern 3: x0 Read

```assembly
Cycle N: add x5, x0, x4     # x0 + x4 → x5
```

**Register File:**
- `r1_addr_i = 0` → `r1_data_o = registers[0] = 0`
- x0 her zaman 0 döner

### Pattern 4: x0 Write (Ignored)

```assembly
Cycle N: add x0, x3, x4     # x3 + x4 → x0 (NOP equivalent)
```

**Register File:**
- `waddr_i = 0`, `rw_en_i = 1`
- `waddr_i != 5'b0` koşulu false → Write ignored
- x0 değişmeden 0 kalır

## Timing Characteristics

### Read Timing

```
Address Valid → [Combinational Delay] → Data Valid
  t = 0           t = 1-2 ns (FPGA)       t = 1-2 ns
```

**Read Delay:**
- Distributed RAM: ~1-2 ns (LUT delay)
- Block RAM: ~2-3 ns (BRAM access time)

**Critical Path:**
```
r1_addr_i → LUT[r1_addr_i] → Mux (forwarding) → r1_data_o
```

### Write Timing

```
Clock Edge → [Setup Time] → Register Update → [Hold Time]
  t = 0        t = -0.5 ns     t = 0.5 ns       t = 0.5 ns
```

**Write Constraints:**
- Setup time: waddr_i, wdata_i, rw_en_i must be stable before clk edge
- Hold time: Must remain stable after clk edge
- Propagation: New data available next cycle

## RAW Hazard Example

### Scenario: Back-to-Back Dependent Instructions

```assembly
Cycle N:   add x5, x3, x4    # x5 = x3 + x4 (Cycle N+3 WB)
Cycle N+1: sub x6, x5, x7    # x6 = x5 - x7 (Cycle N+1 DE)
```

**Problem:**
- Cycle N+1 Decode: `r1_addr_i = 5` → Read x5 (old value)
- Cycle N+3 Writeback: `waddr_i = 5`, `wdata_i = new_value` → Write x5

**Timeline:**
```
Cycle N:   FE: add     DE: -      EX: -      MEM: -     WB: -
Cycle N+1: FE: sub     DE: add    EX: -      MEM: -     WB: -
Cycle N+2: FE: next    DE: sub    EX: add    MEM: -     WB: -
Cycle N+3: FE: next    DE: next   EX: sub    MEM: add   WB: -
Cycle N+4: FE: next    DE: next   EX: next   MEM: sub   WB: add (x5 written)
```

**Cycle N+2 (sub in Decode):**
- `r1_addr_i = 5` → `r1_data_o = registers[5]` (old value!)
- add henüz writeback'e ulaşmadı

**Çözüm: Data Forwarding (decode.sv)**
```systemverilog
// decode.sv
r1_data_o = fwd_a_i ? wb_data_i : r1_data;
```

- Hazard unit: `(WB.rd == DE.rs1) && WB.rf_rw_en` → `fwd_a_i = 1`
- `r1_data_o = wb_data_i` (add'in sonucu)

## Reset Behavior

```systemverilog
if (!rst_ni) begin
  registers <= '{default: 0};  // All registers = 0
end
```

**Reset'te:**
- Tüm 32 register sıfırlanır
- x0 = 0 (zaten hardwired)
- x1-x31 = 0 (başlangıç değeri)

**RISC-V Convention:**
- Reset'te sadece PC belirlenir (RESET_VECTOR)
- Register'ların reset değeri RISC-V spec'inde tanımsızdır (implementation-defined)
- Tipik olarak tümü sıfır (deterministic behavior için)

## Synthesis Considerations

### Distributed RAM vs Block RAM

**Distributed RAM (LUT-based):**
- **Avantaj:** Asenkron read, low latency
- **Dezavantaj:** LUT resource tüketimi (32x32-bit = 1024 LUT bit)
- **Kullanım:** Xilinx: LUT RAM, Intel: MLAB

**Block RAM (BRAM):**
- **Avantaj:** Dedicated resource, LUT tasarrufu
- **Dezavantaj:** Senkron read (1 cycle latency ekler)
- **Kullanım:** Daha büyük register file'lar için (örn. RV64, 64 register)

**RV32I için Önerilen:** Distributed RAM (asenkron read gerekli)

### FPGA Optimization

```systemverilog
(* ram_style = "distributed" *) logic [XLEN-1:0] registers[31:0];
```

**Veya:**
```systemverilog
(* ram_style = "block" *) logic [XLEN-1:0] registers[31:0];
```

**Xilinx Vivado:**
- `distributed`: LUT RAM
- `block`: BRAM
- `auto`: Synthesis tool karar verir

## Debugging & Verification

### Waveform Analysis

```
Signal Monitoring:
- r1_addr_i, r2_addr_i   : Read addresses
- r1_data_o, r2_data_o   : Read data
- waddr_i, wdata_i       : Write address/data
- rw_en_i                : Write enable
- registers[0:31]        : All register contents
```

### Common Issues

1. **x0 Not Zero:**
   - **Symptom:** x0 reads non-zero value
   - **Cause:** Write protection logic missing (`waddr_i != 5'b0`)
   - **Fix:** Check condition in write logic

2. **RAW Hazard:**
   - **Symptom:** Incorrect operand read after write
   - **Cause:** No forwarding, old value read
   - **Fix:** Implement data forwarding in decode

3. **Write Not Happening:**
   - **Symptom:** Register value doesn't update
   - **Cause:** `rw_en_i = 0` or clock issue
   - **Fix:** Verify writeback stage control

### Assertions

```systemverilog
// x0 her zaman 0 olmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
  registers[0] == 32'h0);

// Write enable olmadan register değişmemeli
assert property (@(posedge clk_i) disable iff (!rst_ni)
  !rw_en_i |=> $stable(registers));

// x0'a yazma ignore edilmeli
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (rw_en_i && (waddr_i == 5'b0)) |=> (registers[0] == 32'h0));

// Read adresi değiştiğinde data güncellenmeli (combinational)
assert property (@(posedge clk_i) disable iff (!rst_ni)
  r1_data_o == registers[r1_addr_i]);
```

## Performance Impact

### Register File Access Latency

**Typical Pipeline:**
```
Cycle N:   Fetch
Cycle N+1: Decode + Register Read (combinational)
Cycle N+2: Execute
Cycle N+3: Memory
Cycle N+4: Writeback + Register Write
```

**Register File Contribution:**
- **Read:** 0 cycles (combinational, part of decode)
- **Write:** 0 cycles (parallel with other operations)

**No Performance Penalty:** Register file access doesn't stall pipeline

### Register File Size Impact

**32x32-bit = 1 KB:**
- Negligible area for modern FPGAs/ASICs
- Critical path: ~1-2 ns (well within 100-500 MHz)

**Larger Designs (RV64, 64 registers):**
- 64x64-bit = 4 KB
- May benefit from BRAM (but adds read latency)

## Test Bench Example

```systemverilog
initial begin
  // Reset
  rst_ni = 0; #10;
  rst_ni = 1; #10;
  
  // Test 1: Write to x5, read back
  waddr_i = 5;
  wdata_i = 32'h12345678;
  rw_en_i = 1;
  @(posedge clk_i);
  rw_en_i = 0;
  #1;  // Wait for combinational read
  r1_addr_i = 5;
  #1;
  assert(r1_data_o == 32'h12345678) else $error("Read mismatch!");
  
  // Test 2: Write to x0 (should be ignored)
  waddr_i = 0;
  wdata_i = 32'hDEADBEEF;
  rw_en_i = 1;
  @(posedge clk_i);
  rw_en_i = 0;
  #1;
  r1_addr_i = 0;
  #1;
  assert(r1_data_o == 32'h0) else $error("x0 not zero!");
  
  // Test 3: Dual read
  waddr_i = 10; wdata_i = 32'hAAAAAAAA; rw_en_i = 1; @(posedge clk_i);
  waddr_i = 11; wdata_i = 32'hBBBBBBBB; rw_en_i = 1; @(posedge clk_i);
  rw_en_i = 0;
  #1;
  r1_addr_i = 10;
  r2_addr_i = 11;
  #1;
  assert(r1_data_o == 32'hAAAAAAAA && r2_data_o == 32'hBBBBBBBB) 
    else $error("Dual read failed!");
end
```

## İlgili Modüller

1. **decode.sv**: Register file'ı kullanır (read port'ları)
2. **writeback.sv**: Register file'a write yapar
3. **hazard_unit.sv**: RAW hazard detection ve forwarding control

## Gelecek İyileştirmeler

1. **Register Renaming**: Out-of-order execution desteği
2. **Multi-Port**: Superscalar (2+ instruction/cycle)
3. **ECC Protection**: Soft-error detection/correction
4. **Power Gating**: Unused register'ları clock-gate et

## Referanslar

1. RISC-V Unprivileged ISA Specification v20191213 - Chapter 2 (RV32I Base Integer Instruction Set)
2. RISC-V Calling Convention - ABI Specification
3. "Computer Organization and Design: RISC-V Edition" - Patterson & Hennessy, Chapter 4 (Register File)

---

**Son Güncelleme:** 5 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
