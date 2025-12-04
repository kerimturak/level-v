# DECODE Modülü - Teknik Döküman

## Genel Bakış

`decode.sv` modülü, RISC-V işlemcisinin ikinci pipeline aşamasıdır (Stage 02). Fetch aşamasından gelen instruction'ı decode eder, register file'dan operand'ları okur, control signal'leri üretir ve immediate değerleri genişletir. Ayrıca data forwarding mekanizması ile hazard'ları önler.

## Temel Sorumluluklar

1. **Instruction Decode**: Control unit ile instruction'ın tipini ve kontrol sinyallerini belirler
2. **Register File Access**: Source register'lardan (rs1, rs2) değerleri okur
3. **Immediate Generation**: Instruction formatına göre immediate değeri genişletir (sign/zero extension)
4. **Data Forwarding**: Writeback aşamasından gelen verileri forward eder (hazard prevention)
5. **Exception Propagation**: Fetch aşamasından gelen exception'ları propagate eder

## Port Tanımları

### Giriş Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `inst_i` | inst_t | Fetch'ten gelen instruction (parsed format) |
| `fwd_a_i` | logic | Operand A için forward enable (hazard unit'ten) |
| `fwd_b_i` | logic | Operand B için forward enable (hazard unit'ten) |
| `wb_data_i` | [XLEN-1:0] | Writeback aşamasından forward edilecek data |
| `rd_addr_i` | [4:0] | Writeback destination register address |
| `rf_rw_en_i` | logic | Register file write enable (writeback'ten) |
| `instr_type_i` | instr_type_e | Instruction tipi (fetch'ten) |

**inst_t yapısı:**
```systemverilog
typedef struct packed {
  logic [6:0]  opcode;
  logic [4:0]  rd_addr;
  logic [2:0]  funct3;
  logic [4:0]  r1_addr;
  logic [4:0]  r2_addr;
  logic [6:0]  funct7;
} inst_t;
```

### Çıkış Portları

| Port | Tip | Açıklama |
|------|-----|----------|
| `r1_data_o` | [XLEN-1:0] | Source register 1 data (forwarded if needed) |
| `r2_data_o` | [XLEN-1:0] | Source register 2 data (forwarded if needed) |
| `ctrl_o` | ctrl_t | Control signal bundle (execute aşamasına) |
| `imm_o` | [XLEN-1:0] | Sign/zero extended immediate değer |
| `exc_type_o` | exc_type_e | Exception type (propagated/generated) |

**ctrl_t yapısı:**
```systemverilog
typedef struct packed {
  alu_ctrl_e   alu_ctrl;      // ALU operation type
  logic [1:0]  alu_in1_sel;   // ALU input 1 select
  logic        alu_in2_sel;   // ALU input 2 select (0=rs2, 1=imm)
  logic        rf_rw_en;      // Register file write enable
  logic        wr_en;         // Memory write enable
  logic        ld_op_sign;    // Load operation signed?
  logic [1:0]  rw_size;       // Memory access size (byte/half/word)
  logic [1:0]  result_src;    // Result source select
  pc_sel_e     pc_sel;        // Branch/jump type
  logic        dcache_valid;  // Data cache valid
  logic        csr_or_data;   // CSR or ALU result select
  logic        rd_csr;        // CSR read enable
  logic        wr_csr;        // CSR write enable
  logic [11:0] csr_idx;       // CSR index
  imm_e        imm_sel;       // Immediate type
  exc_type_e   exc_type;      // Exception type
} ctrl_t;
```

## Mimari Bloklar

### 1. Data Forwarding Logic

```systemverilog
always_comb begin
  r1_data_o = fwd_a_i ? wb_data_i : r1_data;
  r2_data_o = fwd_b_i ? wb_data_i : r2_data;
end
```

**Amaç:** RAW (Read-After-Write) hazard'larını önlemek

**Senaryo:**
```assembly
add x1, x2, x3   # Cycle N: x1'e write (writeback: Cycle N+3)
sub x4, x1, x5   # Cycle N+1: x1'i read (decode stage)
```

**Problem:** 
- `sub` instruction'ı decode'da x1'i okuyor (Cycle N+1)
- Ancak `add` instruction'ı x1'e henüz yazmadı (writeback Cycle N+3)
- x1'in eski (stale) değeri okunur

**Çözüm:**
- Hazard unit `fwd_a_i=1` yapar
- `wb_data_i` (add'in sonucu) doğrudan `r1_data_o`'ya forward edilir
- Pipeline stall gerekmez

### 2. Control Unit Integration

```systemverilog
control_unit i_control_unit (
  .inst_i       (inst_i),
  .instr_type_i (instr_type_i),
  .ctrl_o       (ctrl_o)
);
```

**İşlev:**
- Instruction type'a göre tüm control signal'leri üretir
- ALU operation, memory access, register write, CSR access, branch/jump kontrolleri
- Exception detection (illegal instruction, illegal shift, illegal CSR access)

### 3. Register File

```systemverilog
reg_file i_reg_file (
  .clk_i     (clk_i),
  .rst_ni    (rst_ni),
  .rw_en_i   (rf_rw_en_i),
  .r1_addr_i (inst_i.r1_addr),
  .r2_addr_i (inst_i.r2_addr),
  .waddr_i   (rd_addr_i),
  .wdata_i   (wb_data_i),
  .r1_data_o (r1_data),
  .r2_data_o (r2_data)
);
```

**İşlev:**
- 32x32-bit register array (x0-x31)
- Dual-port asenkron read (r1_data, r2_data)
- Single-port senkron write (writeback aşamasından)
- x0 hardwired to zero (write ignored)

### 4. Immediate Extension

```systemverilog
extend i_extend (
  .imm_i (inst_i[31:7]),
  .sel_i (ctrl_o.imm_sel),
  .imm_o (imm_o)
);
```

**İşlev:**
- Instruction formatına göre immediate bit'leri seçer ve genişletir
- Sign extension (I, S, B, J) veya zero extension (U, CSR)
- 7 farklı immediate format desteği

## Instruction Decode Flow

```
Fetch Stage → inst_i (32-bit instruction)
                ↓
         Parse to inst_t (opcode, rs1, rs2, rd, funct3, funct7)
                ↓
         Control Unit → Decode instruction type → Generate ctrl_o
                ↓
         Register File → Read rs1, rs2
                ↓
         Data Forwarding → Forward if hazard detected
                ↓
         Immediate Extend → Generate imm_o
                ↓
         Execute Stage (r1_data_o, r2_data_o, imm_o, ctrl_o)
```

## Data Forwarding Scenarios

### Scenario 1: Writeback to Decode Forwarding

```assembly
Cycle N:   add x1, x2, x3    # WB stage: x1 = 100
Cycle N+1: sub x4, x1, x5    # DE stage: needs x1
```

**Forwarding:**
```
hazard_unit detects: (DE.rs1 == WB.rd) && WB.rf_rw_en
  → fwd_a_i = 1
  → r1_data_o = wb_data_i (100)
```

### Scenario 2: No Forwarding (No Hazard)

```assembly
Cycle N:   add x1, x2, x3
Cycle N+1: sub x4, x6, x7    # x1 not used
```

**No Forwarding:**
```
fwd_a_i = 0, fwd_b_i = 0
r1_data_o = r1_data (from register file)
r2_data_o = r2_data (from register file)
```

### Scenario 3: Load-Use Hazard (Stall Required)

```assembly
Cycle N:   lw x1, 0(x2)      # MEM stage: x1 = mem[x2]
Cycle N+1: sub x4, x1, x5    # DE stage: needs x1 (not yet available)
```

**Stall + Forward:**
```
Cycle N+1: hazard_unit detects load-use hazard → STALL
Cycle N+2: lw reaches WB → forward wb_data_i
Cycle N+2: sub can proceed with forwarded data
```

## Exception Handling

```systemverilog
exc_type_o = ctrl_o.exc_type;
```

**Exception Types in Decode:**
1. **ILLEGAL_INSTRUCTION**: Unknown opcode, unsupported instruction
2. **Illegal Shift**: RV32 constraint violation (imm[5] must be 0 for shifts)
3. **Illegal CSR**: Unsupported CSR address
4. **CSR Read-Only Write**: Attempt to write to read-only CSR (bits [11:10] == 2'b11)

**Propagation:**
- Fetch stage exception'ları decode'dan propagate edilir
- Decode'daki yeni exception'lar `ctrl_o.exc_type` ile execute'a iletilir
- Exception commit writeback stage'de olur

## Timing Diagram

```
Cycle 0: Fetch
         inst_i = 0x00C58593 (addi x11, x11, 12)

Cycle 1: Decode
         inst_i parsed:
           opcode = 0x13 (I-type)
           rd = 11 (x11)
           rs1 = 11 (x11)
           imm = 12
         
         Control Unit:
           alu_ctrl = OP_ADD
           alu_in2_sel = 1 (immediate)
           rf_rw_en = 1
           result_src = 0 (ALU result)
         
         Register File:
           r1_data = registers[11] = 100
         
         Immediate:
           imm_o = 12 (sign-extended)
         
         Output:
           r1_data_o = 100 (no forwarding needed)
           imm_o = 12
           ctrl_o = { OP_ADD, rf_rw_en=1, ... }

Cycle 2: Execute
         ALU: r1_data_o + imm_o = 100 + 12 = 112
```

## Hazard Detection Examples

### Example 1: Simple Forwarding

```assembly
Program:
  add x1, x2, x3   # Cycle N
  sub x4, x1, x5   # Cycle N+1
```

**Timeline:**
```
Cycle N:
  Fetch: add
Cycle N+1:
  Decode: add
  Fetch: sub
Cycle N+2:
  Execute: add
  Decode: sub → hazard_unit: fwd_a_i=0 (no hazard yet)
  Fetch: next
Cycle N+3:
  Memory: add
  Execute: sub
  Decode: next
Cycle N+4:
  Writeback: add (x1 = result)
  Memory: sub
  Execute: next
  Decode: next
```

**Not:** Bu örnekte forwarding Cycle N+4'te gerekli değil (sub zaten execute'a geçmiş)

### Example 2: Writeback Forwarding

```assembly
Program:
  add x1, x2, x3   # I1
  nop              # I2
  nop              # I3
  sub x4, x1, x5   # I4
```

**Timeline:**
```
Cycle N+3:
  Writeback: I1 (x1 written)
  Memory: I2
  Execute: I3
  Decode: I4 → needs x1
  
Hazard Unit:
  WB.rd (x1) == DE.rs1 (x1) && WB.rf_rw_en (1)
  → fwd_a_i = 1
  → r1_data_o = wb_data_i (I1's result)
```

## Performance Considerations

### Register File Read Timing

- **Asenkron read**: Aynı cycle'da decode ve read tamamlanır
- **Combinational path**: inst_i.r1_addr → registers[r1_addr] → r1_data
- **Critical path**: Register array read → forwarding mux → output

**Optimization:**
- Register file BRAM/distributed RAM ile implement edilebilir
- Forwarding mux gecikme ekler (~2-3 logic levels)

### Forwarding Overhead

- **Logic Overhead**: 2x 2:1 mux (r1_data, r2_data)
- **Timing Impact**: ~1-2 ns (FPGA'da)
- **Benefit**: Stall avoidance → Performance gain >> overhead

**Örnek:**
- Load-use hazard without forwarding: 1 cycle stall
- 20% load instruction → 20% potential stall
- Forwarding ile stall oranı %5'e düşer → %15 performance gain

## Instruction Format Decoding

### R-Type
```
31       25 24   20 19   15 14 12 11    7 6     0
+---------+-------+-------+----+-------+-------+
| funct7  |  rs2  |  rs1  |f3  |  rd   |opcode |
+---------+-------+-------+----+-------+-------+
```
**Örnek:** `add x1, x2, x3` → `0x003100B3`

### I-Type
```
31            20 19   15 14 12 11    7 6     0
+--------------+-------+----+-------+-------+
|    imm[11:0] |  rs1  |f3  |  rd   |opcode |
+--------------+-------+----+-------+-------+
```
**Örnek:** `addi x1, x2, 12` → `0x00C10093`

### S-Type
```
31       25 24   20 19   15 14 12 11       7 6     0
+---------+-------+-------+----+---------+-------+
|imm[11:5]|  rs2  |  rs1  |f3  |imm[4:0] |opcode |
+---------+-------+-------+----+---------+-------+
```
**Örnek:** `sw x3, 8(x2)` → `0x00312423`

### B-Type (Branch)
```
31  30    25 24   20 19   15 14 12 11  8 7  6     0
+--+-------+-------+-------+----+----+--+-------+
|12|11:5   |  rs2  |  rs1  |f3  |4:1 |11|opcode |
+--+-------+-------+-------+----+----+--+-------+
```
**Örnek:** `beq x1, x2, offset` → offset bit shuffling

### U-Type
```
31                 12 11    7 6     0
+--------------------+-------+-------+
|      imm[31:12]    |  rd   |opcode |
+--------------------+-------+-------+
```
**Örnek:** `lui x1, 0x12345` → `0x123450B7`

### J-Type (JAL)
```
31  30       21 20 19       12 11    7 6     0
+--+----------+--+----------+-------+-------+
|20|10:1      |11|19:12     |  rd   |opcode |
+--+----------+--+----------+-------+-------+
```
**Örnek:** `jal x1, offset` → offset bit shuffling

## Control Signal Generation Examples

### Example 1: ADDI

```
Instruction: addi x11, x11, 12
Binary: 0x00C58593

Control Signals:
  alu_ctrl = OP_ADD
  alu_in1_sel = 0 (rs1)
  alu_in2_sel = 1 (imm)
  rf_rw_en = 1 (write to x11)
  wr_en = 0 (no memory write)
  result_src = 0 (ALU result)
  imm_sel = I_IMM (sign-extended 12-bit)
```

### Example 2: SW (Store Word)

```
Instruction: sw x5, 8(x10)
Binary: 0x00552423

Control Signals:
  alu_ctrl = OP_ADD (base + offset)
  alu_in1_sel = 0 (rs1 = x10)
  alu_in2_sel = 1 (imm = 8)
  rf_rw_en = 0 (no register write)
  wr_en = 1 (memory write)
  rw_size = 2'b11 (word, 4 bytes)
  dcache_valid = 1 (data cache access)
  imm_sel = S_IMM
```

### Example 3: BEQ (Branch Equal)

```
Instruction: beq x1, x2, offset
Binary: 0x00208463 (offset=8)

Control Signals:
  alu_ctrl = OP_ADD (PC + offset calculation)
  alu_in1_sel = 0 (rs1 for comparison)
  alu_in2_sel = 0 (rs2 for comparison)
  pc_sel = BEQ (branch type)
  rf_rw_en = 0 (no register write)
  imm_sel = B_IMM (13-bit offset)
```

## Debug & Verification

### Signal Monitoring

```systemverilog
// Decode stage'de monitor edilmesi gereken sinyaller:
- inst_i          // Input instruction
- ctrl_o          // Control signal bundle
- r1_data_o       // Operand A (forwarded)
- r2_data_o       // Operand B (forwarded)
- imm_o           // Extended immediate
- fwd_a_i, fwd_b_i // Forwarding enables
- exc_type_o      // Exception type
```

### Assertions (Önerilen)

```systemverilog
// x0 her zaman 0 olmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (inst_i.r1_addr == 5'b0) |-> (r1_data == 32'h0));

// Forwarding aktif olduğunda wb_data kullanılmalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
  fwd_a_i |-> (r1_data_o == wb_data_i));

// Register write enable olmadan forward edilmemeli
assert property (@(posedge clk_i) disable iff (!rst_ni)
  fwd_a_i |-> rf_rw_en_i);

// Illegal instruction'da register write yapılmamalı
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (ctrl_o.exc_type == ILLEGAL_INSTRUCTION) |-> !ctrl_o.rf_rw_en);
```

## İlgili Modüller

1. **control_unit.sv**: Control signal generation ve exception detection
2. **reg_file.sv**: 32x32-bit register file implementation
3. **extend.sv**: Immediate sign/zero extension
4. **hazard_unit.sv**: Forwarding control (fetch.sv'de)
5. **execute.sv**: Decode'dan gelen operand'ları işler

## Gelecek İyileştirmeler

1. **Multi-Cycle Instruction Support**: Division/Multiplication için iterative execution
2. **Register Renaming**: Out-of-order execution desteği
3. **Scoreboarding**: Daha gelişmiş hazard detection
4. **Dual-Issue Decode**: Superscalar architecture (2 instruction/cycle decode)

## Referanslar

1. RISC-V Unprivileged ISA Specification v20191213 - Instruction Formats
2. "Computer Organization and Design: RISC-V Edition" - Patterson & Hennessy, Chapter 4 (Pipelining)
3. "Computer Architecture: A Quantitative Approach" - Hennessy & Patterson, Appendix C (Pipelining)
4. RISC-V Calling Convention - ABI Specification

---

**Son Güncelleme:** 5 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
