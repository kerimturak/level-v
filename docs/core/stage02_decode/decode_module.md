# Decode Module — Technical Documentation

## Overview

The `decode.sv` module is the second pipeline stage of the RISC-V processor (stage 02). It decodes the instruction from fetch, reads operands from the register file, generates control signals, and extends immediates. Data forwarding from writeback avoids some hazards.

## Main responsibilities

1. **Instruction decode:** With the control unit, determines instruction type and control signals  
2. **Register file access:** Reads source registers (rs1, rs2)  
3. **Immediate generation:** Extends immediates per instruction format (sign/zero extension)  
4. **Data forwarding:** Forwards data from writeback when needed (hazard prevention)  
5. **Exception propagation:** Propagates exceptions raised in fetch  

## Port definitions

### Input ports

| Port | Type | Description |
|------|-----|----------|
| `clk_i` | logic | System clock |
| `rst_ni` | logic | Active-low asynchronous reset |
| `inst_i` | inst_t | Instruction from fetch (parsed) |
| `fwd_a_i` | logic | Forward enable for operand A (from hazard unit) |
| `fwd_b_i` | logic | Forward enable for operand B (from hazard unit) |
| `wb_data_i` | [XLEN-1:0] | Data to forward from writeback |
| `rd_addr_i` | [4:0] | Writeback destination register |
| `rf_rw_en_i` | logic | Register file write enable (from writeback) |
| `instr_type_i` | instr_type_e | Instruction type (from fetch) |

**`inst_t` layout:**
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

### Output ports

| Port | Type | Description |
|------|-----|----------|
| `r1_data_o` | [XLEN-1:0] | Source register 1 data (forwarded if needed) |
| `r2_data_o` | [XLEN-1:0] | Source register 2 data (forwarded if needed) |
| `ctrl_o` | ctrl_t | Control bundle (to execute) |
| `imm_o` | [XLEN-1:0] | Sign- or zero-extended immediate |
| `exc_type_o` | exc_type_e | Exception type (propagated/generated) |

**`ctrl_t` layout:**
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

## Architectural blocks

### 1. Data Forwarding Logic

```systemverilog
always_comb begin
  r1_data_o = fwd_a_i ? wb_data_i : r1_data;
  r2_data_o = fwd_b_i ? wb_data_i : r2_data;
end
```

**Purpose:** Avoid RAW (read-after-write) hazards.

**Scenario:**
```assembly
add x1, x2, x3   # Cycle N: write x1 (writeback: cycle N+3)
sub x4, x1, x5   # Cycle N+1: read x1 (in decode)
```

**Problem:** 
- `sub` reads x1 in decode (cycle N+1)
- `add` has not yet written x1 (writeback at cycle N+3)
- The register file would expose a stale x1

**Solution:**
- Hazard unit asserts `fwd_a_i`
- `wb_data_i` (`add`’s result) is muxed onto `r1_data_o`
- No pipeline stall needed in this pattern

### 2. Control Unit Integration

```systemverilog
control_unit i_control_unit (
  .inst_i       (inst_i),
  .instr_type_i (instr_type_i),
  .ctrl_o       (ctrl_o)
);
```

**Role:**
- Drives all control signals from instruction type
- ALU, memory, register write, CSR, branch/jump controls
- Detects illegal instruction, illegal shift, illegal CSR access

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

**Role:**
- 32×32-bit GPRs (x0–x31)
- Dual-port asynchronous read (r1_data, r2_data)
- Single-port synchronous write (from writeback)
- x0 hardwired to zero (writes ignored)

### 4. Immediate Extension

```systemverilog
extend i_extend (
  .imm_i (inst_i[31:7]),
  .sel_i (ctrl_o.imm_sel),
  .imm_o (imm_o)
);
```

**Role:**
- Selects and extends immediate bits per format
- Sign extension (I, S, B, J) or zero extension (U, CSR)
- Seven immediate modes

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
- Fetch-stage exceptions propagate through decode
- New decode exceptions are sent to execute via `ctrl_o.exc_type`
- Exception commit occurs in the writeback stage

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

**Note:** In this example forwarding at cycle N+4 is unnecessary (`sub` has already left decode)

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

- **Asynchronous read:** Decode and register read finish in the same cycle  
- **Combinational path:** `inst_i.r1_addr` → `registers[r1_addr]` → `r1_data`  
- **Critical path:** Register read → forwarding mux → output  

**Optimization:**
- Register file can use BRAM or distributed RAM  
- Forwarding mux adds ~2–3 levels of delay  

### Forwarding Overhead

- **Logic Overhead**: 2x 2:1 mux (r1_data, r2_data)
- **Timing Impact**: ~1–2 ns (on an FPGA)
- **Benefit**: Stall avoidance → Performance gain >> overhead

**Example:**
- Load-use hazard without forwarding: 1 cycle stall
- 20% load instruction → 20% potential stall
- With forwarding, stall rate can drop toward ~5% → ~15% performance gain

## Instruction Format Decoding

### R-Type
```
31       25 24   20 19   15 14 12 11    7 6     0
+---------+-------+-------+----+-------+-------+
| funct7  |  rs2  |  rs1  |f3  |  rd   |opcode |
+---------+-------+-------+----+-------+-------+
```
**Example:** `add x1, x2, x3` → `0x003100B3`

### I-Type
```
31            20 19   15 14 12 11    7 6     0
+--------------+-------+----+-------+-------+
|    imm[11:0] |  rs1  |f3  |  rd   |opcode |
+--------------+-------+----+-------+-------+
```
**Example:** `addi x1, x2, 12` → `0x00C10093`

### S-Type
```
31       25 24   20 19   15 14 12 11       7 6     0
+---------+-------+-------+----+---------+-------+
|imm[11:5]|  rs2  |  rs1  |f3  |imm[4:0] |opcode |
+---------+-------+-------+----+---------+-------+
```
**Example:** `sw x3, 8(x2)` → `0x00312423`

### B-Type (Branch)
```
31  30    25 24   20 19   15 14 12 11  8 7  6     0
+--+-------+-------+-------+----+----+--+-------+
|12|11:5   |  rs2  |  rs1  |f3  |4:1 |11|opcode |
+--+-------+-------+-------+----+----+--+-------+
```
**Example:** `beq x1, x2, offset` → offset bit shuffling

### U-Type
```
31                 12 11    7 6     0
+--------------------+-------+-------+
|      imm[31:12]    |  rd   |opcode |
+--------------------+-------+-------+
```
**Example:** `lui x1, 0x12345` → `0x123450B7`

### J-Type (JAL)
```
31  30       21 20 19       12 11    7 6     0
+--+----------+--+----------+-------+-------+
|20|10:1      |11|19:12     |  rd   |opcode |
+--+----------+--+----------+-------+-------+
```
**Example:** `jal x1, offset` → offset bit shuffling

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
// Useful signals to watch in decode:
- inst_i          // Input instruction
- ctrl_o          // Control signal bundle
- r1_data_o       // Operand A (forwarded)
- r2_data_o       // Operand B (forwarded)
- imm_o           // Extended immediate
- fwd_a_i, fwd_b_i // Forwarding enables
- exc_type_o      // Exception type
```

### Suggested assertions

```systemverilog
// x0 must always read as zero
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (inst_i.r1_addr == 5'b0) |-> (r1_data == 32'h0));

// When forwarding is on, wb_data must drive the operand
assert property (@(posedge clk_i) disable iff (!rst_ni)
  fwd_a_i |-> (r1_data_o == wb_data_i));

// Forwarding requires a register write in WB
assert property (@(posedge clk_i) disable iff (!rst_ni)
  fwd_a_i |-> rf_rw_en_i);

// Illegal instruction must not assert register write
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (ctrl_o.exc_type == ILLEGAL_INSTRUCTION) |-> !ctrl_o.rf_rw_en);
```

## Related modules

1. **control_unit.sv:** Control signal generation and exception detection
2. **reg_file.sv:** 32×32-bit register file  
3. **extend.sv:** Immediate sign/zero extension  
4. **hazard_unit.sv:** Forwarding control (driven from `fetch.sv`)  
5. **execute.sv:** Consumes operands from decode

## Future improvements

1. **Multi-cycle instructions:** Iterative divide/multiply execution  
2. **Register renaming:** Out-of-order execution  
3. **Scoreboarding:** Richer hazard tracking  
4. **Dual-Issue Decode**: Superscalar architecture (2 instruction/cycle decode)

## References

1. RISC-V Unprivileged ISA Specification v20191213 - Instruction Formats
2. "Computer Organization and Design: RISC-V Edition" - Patterson & Hennessy, Chapter 4 (Pipelining)
3. "Computer Architecture: A Quantitative Approach" - Hennessy & Patterson, Appendix C (Pipelining)
4. RISC-V Calling Convention - ABI Specification

---

**Last updated:** 5 December 2025  
**Author:** Kerim TURAK  
**License:** MIT License
