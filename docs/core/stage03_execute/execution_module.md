# EXECUTION Modülü - Teknik Döküman

## Genel Bakış

`execution.sv` modülü, RISC-V işlemcisinin **Execute Stage** üst seviye wrapper'ıdır. ALU, CSR register file, data forwarding, branch resolution ve exception detection işlemlerini koordine eder. Pipeline'ın üçüncü stage'idir.

## Sorumluluklar

1. **ALU Operations**: Aritmetik/mantıksal işlemler, karşılaştırmalar, shift
2. **M Extension**: Multiply/Divide operations (RV32M)
3. **CSR Operations**: Control and Status Register read/write
4. **Data Forwarding**: ALU ve writeback'ten forwarding
5. **Branch Resolution**: Branch condition evaluation
6. **PC Target Calculation**: Jump/branch target address
7. **Exception Detection**: Instruction misalignment, breakpoint
8. **Trap Handling**: Hardware interrupt integration

## Port Tanımları

### Clock & Control

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `stall_i` | stall_e | Pipeline stall sinyali |

### Data Forwarding

| Port | Tip | Açıklama |
|------|-----|----------|
| `fwd_a_i` | [1:0] | Operand A forward select (00=reg, 01=WB, 10=EX) |
| `fwd_b_i` | [1:0] | Operand B forward select |
| `alu_result_i` | [XLEN-1:0] | ALU result from previous cycle (EX forwarding) |
| `wb_data_i` | [XLEN-1:0] | Writeback data (WB forwarding) |
| `r1_data_i` | [XLEN-1:0] | Register file source 1 data |
| `r2_data_i` | [XLEN-1:0] | Register file source 2 data |

### ALU Control

| Port | Tip | Açıklama |
|------|-----|----------|
| `alu_in1_sel_i` | [1:0] | ALU operand A select (data_a/pc_incr/pc) |
| `alu_in2_sel_i` | logic | ALU operand B select (imm/data_b) |
| `alu_ctrl_i` | alu_op_e | ALU operation select |

### PC Calculation

| Port | Tip | Açıklama |
|------|-----|----------|
| `pc_i` | [XLEN-1:0] | Current PC |
| `pc_incr_i` | [XLEN-1:0] | PC + 4 (or PC + 2 for compressed) |
| `imm_i` | [XLEN-1:0] | Immediate value (from extend) |
| `pc_sel_i` | pc_sel_e | PC source selection (JAL/JALR/Branch) |
| `pc_target_o` | [XLEN-1:0] | Branch/jump target address |
| `pc_sel_o` | logic | Actual PC redirect (branch taken) |

### CSR Interface

| Port | Tip | Açıklama |
|------|-----|----------|
| `rd_csr_i` | logic | CSR read enable |
| `wr_csr_i` | logic | CSR write enable |
| `csr_idx_i` | [11:0] | CSR address |
| `csr_or_data_i` | logic | Use CSR data for rd (bypass ALU result) |

### Trap & Interrupt

| Port | Tip | Açıklama |
|------|-----|----------|
| `trap_active_i` | logic | Trap active (exception/interrupt) |
| `de_trap_active_i` | logic | Decode stage trap active |
| `trap_cause_i` | [XLEN-1:0] | Trap cause (exception code) |
| `trap_tval_i` | [XLEN-1:0] | Trap value (faulting instruction/address) |
| `trap_mepc_i` | [XLEN-1:0] | Trap mepc (return PC) |
| `timer_irq_i` | logic | CLINT timer interrupt |
| `sw_irq_i` | logic | CLINT software interrupt |
| `ext_irq_i` | logic | PLIC external interrupt |
| `mtvec_o` | [XLEN-1:0] | Trap vector base address |
| `exc_type_o` | exc_type_e | Exception type (misalignment/breakpoint) |

### Output

| Port | Tip | Açıklama |
|------|-----|----------|
| `write_data_o` | [XLEN-1:0] | Store data (rs2 with forwarding) |
| `alu_result_o` | [XLEN-1:0] | ALU/CSR result for writeback |
| `alu_stall_o` | logic | ALU stall (mul/div not ready) |
| `misa_c_o` | logic | MISA.C bit (compressed extension enabled) |
| `tdata1_o` | [XLEN-1:0] | Debug trigger data 1 |
| `tdata2_o` | [XLEN-1:0] | Debug trigger data 2 |
| `tcontrol_o` | [XLEN-1:0] | Debug trigger control |

## İç Yapı

### Data Forwarding Logic

```systemverilog
always_comb begin
  data_a = fwd_a_i[1] ? alu_result_i : (fwd_a_i[0] ? wb_data_i : r1_data_i);
end
```

**Forwarding Priority:**
1. `fwd_a_i[1]` → EX stage result (previous ALU output)
2. `fwd_a_i[0]` → WB stage data (memory/ALU writeback)
3. Default → Register file data

**Example:**
```assembly
Cycle N:   add x5, x3, x4   # EX: x5 = x3 + x4
Cycle N+1: sub x6, x5, x7   # EX: Needs x5 → fwd_a_i[1]=1 (EX forwarding)
```

### ALU Operand Selection

```systemverilog
case (alu_in1_sel_i)
  2'b00: operant_a = data_a;       // rs1 data
  2'b01: operant_a = pc_incr_i;    // PC + 4 (JALR result)
  2'b10: operant_a = pc_i;         // PC (AUIPC)
  2'b11: operant_a = data_a;       // Reserved
endcase

operant_b = alu_in2_sel_i ? imm_i : write_data_o;  // imm or rs2
```

**Operand A Sources:**
- **data_a**: Register-register operations (ADD, SUB, etc.)
- **pc_incr_i**: JALR return address (PC + 4)
- **pc_i**: AUIPC base address

**Operand B Sources:**
- **imm_i**: Immediate operations (ADDI, LW, SW, etc.)
- **write_data_o**: Register-register (ADD, SUB, etc.)

### PC Target Calculation

```systemverilog
pc_target_o = instr_type_i == mret ? mepc :
              pc_sel_i == JALR ? (data_a + imm_i) & ~1 :
              pc_i + signed_imm;
```

**Cases:**
1. **MRET**: Return from trap → `mepc` (exception PC)
2. **JALR**: Jump to register + offset → `(rs1 + imm) & ~1` (LSB cleared)
3. **JAL/Branch**: PC-relative → `PC + imm`

**LSB Clear for JALR:**
- RISC-V spec: Target address LSB must be 0 (aligned)
- `& ~1` ensures 2-byte alignment (supports compressed)

### Branch Resolution

```systemverilog
pc_sel_o = (pc_sel_i == BEQ) && ex_zero;        // BEQ taken if equal
pc_sel_o |= (pc_sel_i == BNE) && !ex_zero;      // BNE taken if not equal
pc_sel_o |= (pc_sel_i == BLT) && ex_slt;        // BLT taken if less than (signed)
pc_sel_o |= (pc_sel_i == BGE) && (!ex_slt || ex_zero);  // BGE taken if >= (signed)
pc_sel_o |= (pc_sel_i == BLTU) && ex_sltu;      // BLTU taken if < (unsigned)
pc_sel_o |= (pc_sel_i == BGEU) && (!ex_sltu || ex_zero);  // BGEU taken if >= (unsigned)
pc_sel_o |= (pc_sel_i == JALR);                 // JALR always taken
pc_sel_o |= (pc_sel_i == JAL);                  // JAL always taken
pc_sel_o |= (instr_type_i == mret);             // MRET always taken
```

**Comparison Flags (from ALU):**
- `ex_zero`: `rs1 == rs2` (signed comparison)
- `ex_slt`: `rs1 < rs2` (signed)
- `ex_sltu`: `rs1 < rs2` (unsigned)

**Branch Conditions:**
- **BEQ**: `rs1 == rs2` → `ex_zero`
- **BNE**: `rs1 != rs2` → `!ex_zero`
- **BLT**: `rs1 < rs2` (signed) → `ex_slt`
- **BGE**: `rs1 >= rs2` (signed) → `!ex_slt || ex_zero`
- **BLTU/BGEU**: Unsigned variants

### Exception Detection

```systemverilog
// LOAD/STORE breakpoint detection
if (tcontrol[3] && tdata1[6] && (tdata1[31:28] == 4'h2)) begin
  if (tdata1[0] && (instr_type_i inside {i_lb, i_lh, i_lw, i_lbu, i_lhu})) begin
    if (alu_result == tdata2) begin
      exc_type_o = BREAKPOINT;
    end
  end else if (tdata1[1] && (instr_type_i inside {s_sb, s_sh, s_sw})) begin
    if (alu_result == tdata2) begin
      exc_type_o = BREAKPOINT;
    end
  end
end
```

**Breakpoint Detection:**
- `tcontrol[3]`: MTE (M-mode Trigger Enable)
- `tdata1[6]`: M-mode match enable
- `tdata1[31:28] == 2`: mcontrol type (address match)
- `tdata1[0]`: LOAD match enable
- `tdata1[1]`: STORE match enable
- `tdata2`: Breakpoint address

**Example:**
```c
// Set breakpoint on address 0x80001000
write_csr(tdata2, 0x80001000);
write_csr(tdata1, 0x20000044);  // mcontrol, M-mode, LOAD+STORE match
write_csr(tcontrol, 0x08);      // Enable trigger in M-mode
```

**Instruction Misalignment:**
```systemverilog
exc_type_o = pc_sel_o && pc_target_o[0] ? INSTR_MISALIGNED : NO_EXCEPTION;
```

- Branch/jump target LSB = 1 → Misaligned (not 2-byte aligned)
- RV32C requires 2-byte alignment

### Writeback Data Selection

```systemverilog
always_comb begin
  unique case (instr_type_i)
    u_jal, i_jalr: rd_data = pc_incr_i;  // JAL/JALR: rd = PC + 4
    default:       rd_data = alu_result;
  endcase

  if (rd_csr_i && csr_or_data_i) rd_data = csr_rdata;
end

assign alu_result_o = rd_data;
```

**Priority:**
1. **CSR**: If `rd_csr_i && csr_or_data_i` → Use CSR read data
2. **JAL/JALR**: rd = PC + 4 (return address)
3. **Default**: ALU result (arithmetic, load address, etc.)

## Sub-Modules

### 1. ALU (alu.sv)

```systemverilog
alu i_alu (
  .clk_i       (clk_i),
  .rst_ni      (rst_ni),
  .alu_a_i     (operant_a),
  .alu_b_i     (operant_b),
  .csr_rdata_i (csr_rdata),
  .op_sel_i    (alu_ctrl_i),
  .alu_stall_o (alu_stall_o),
  .zero_o      (ex_zero),
  .slt_o       (ex_slt),
  .sltu_o      (ex_sltu),
  .alu_o       (alu_result)
);
```

**Capabilities:**
- Basic arithmetic: ADD, SUB, SLT, SLTU
- Logical: AND, OR, XOR
- Shift: SLL, SRL, SRA
- M Extension: MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU
- CSR: CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI

**Stall:**
- Multi-cycle multiply/divide → `alu_stall_o = 1`
- Pipeline waits until operation completes

### 2. CSR Register File (cs_reg_file.sv)

```systemverilog
cs_reg_file i_cs_reg_file (
  .clk_i            (clk_i),
  .rst_ni           (rst_ni),
  .stall_i          (stall_i),
  .rd_en_i          (rd_csr_i),
  .wr_en_i          (wr_csr_i),
  .csr_idx_i        (csr_idx_i),
  .csr_wdata_i      (alu_result),
  .csr_rdata_o      (csr_rdata),
  .trap_active_i    (trap_active_i),
  .de_trap_active_i (de_trap_active_i),
  .trap_cause_i     (trap_cause_i),
  .trap_mepc_i      (trap_mepc_i),
  .trap_tval_i      (trap_tval_i),
  .instr_type_i     (instr_type_i),
  .timer_irq_i      (timer_irq_i),
  .sw_irq_i         (sw_irq_i),
  .ext_irq_i        (ext_irq_i),
  .mtvec_o          (mtvec_o),
  .mepc_o           (mepc),
  .misa_c_o         (misa_c),
  .tdata1_o         (tdata1),
  .tdata2_o         (tdata2),
  .tcontrol_o       (tcontrol)
);
```

**CSRs Implemented:**
- **Machine Info**: mvendorid, marchid, mimpid, mhartid, misa
- **Trap Setup**: mstatus, mtvec, mie, mip
- **Trap Handling**: mepc, mcause, mtval, mscratch
- **Counters**: mcycle, minstret (+ upper 32 bits)
- **Debug**: tselect, tdata1, tdata2, tdata3, tcontrol

## Timing Diagram

### Branch Instruction (BEQ)

```
Cycle N:   Fetch BEQ
Cycle N+1: Decode BEQ, read rs1/rs2
Cycle N+2: Execute BEQ
             - Forward rs1/rs2 data
             - Compute rs1 - rs2 → ex_zero
             - Evaluate: pc_sel_o = (pc_sel_i == BEQ) && ex_zero
             - Calculate: pc_target_o = pc_i + signed_imm
Cycle N+3: Memory (NOP if taken)
           Branch resolved: redirect fetch to pc_target_o
```

### JAL Instruction

```
Cycle N:   Fetch JAL
Cycle N+1: Decode JAL
Cycle N+2: Execute JAL
             - pc_target_o = pc_i + signed_imm (21-bit offset)
             - pc_sel_o = 1 (always taken)
             - alu_result_o = pc_incr_i (return address for rd)
Cycle N+3: Memory
           Fetch redirected to pc_target_o
```

### JALR Instruction (with forwarding)

```
Cycle N:   Fetch ADD x5, x3, x4
Cycle N+1: Decode ADD, Fetch JALR x1, 0(x5)
Cycle N+2: Execute ADD, Decode JALR
Cycle N+3: Memory ADD, Execute JALR
             - fwd_a_i[1] = 1 (forward ADD result from EX)
             - data_a = alu_result_i (ADD result)
             - pc_target_o = (data_a + imm_i) & ~1
             - pc_sel_o = 1
             - alu_result_o = pc_incr_i (rd = PC + 4)
```

### CSR Read (CSRRS)

```
Cycle N:   Fetch CSRRS x1, mstatus, x2
Cycle N+1: Decode CSRRS
Cycle N+2: Execute CSRRS
             - cs_reg_file: Read mstatus → csr_rdata
             - ALU: alu_o = csr_rdata | rs2_data
             - cs_reg_file: Write alu_o to mstatus
             - alu_result_o = csr_rdata (old value to rd)
Cycle N+3: Memory (NOP)
Cycle N+4: Writeback: x1 = old mstatus value
```

## Pipeline Integration

### Data Forwarding Scenarios

#### Scenario 1: EX-to-EX Forwarding

```assembly
Cycle N:   add x5, x3, x4   # EX: Compute x5
Cycle N+1: sub x6, x5, x7   # EX: Use x5 → fwd_a_i[1]=1
```

**Forwarding Path:**
```
EX (Cycle N): alu_result → registered
EX (Cycle N+1): alu_result_i (input) → data_a (via fwd_a_i[1])
```

#### Scenario 2: WB-to-EX Forwarding

```assembly
Cycle N:   lw x5, 0(x2)    # MEM: Load x5
Cycle N+1: sub x6, x5, x7  # EX: Use x5 → fwd_a_i[0]=1
```

**Forwarding Path:**
```
WB (Cycle N): wb_data_i (memory data)
EX (Cycle N+1): data_a = wb_data_i (via fwd_a_i[0])
```

### Exception Priority

```
1. INSTR_MISALIGNED (execute stage detection)
2. BREAKPOINT (execute stage, hardware trigger match)
3. ILLEGAL_INSTRUCTION (decode stage)
4. ECALL/EBREAK (decode stage)
5. LOAD/STORE_MISALIGNED (memory stage)
6. LOAD/STORE_FAULT (memory stage)
```

**Execute Stage Exceptions:**
- **INSTR_MISALIGNED**: Branch/jump target LSB = 1
- **BREAKPOINT**: Trigger match on LOAD/STORE address

## Performance Considerations

### Critical Paths

1. **Branch Resolution:**
```
Register File → Forwarding Mux → ALU (Subtraction) → Comparator → pc_sel_o
```
**Delay:** ~5-7 ns (FPGA)

2. **PC Target Calculation:**
```
Register File → Forwarding Mux → Adder → AND (JALR) → pc_target_o
```
**Delay:** ~3-5 ns

3. **ALU Operation:**
```
Register File → Forwarding Mux → ALU → alu_result_o
```
**Delay:** ~4-6 ns (basic ops), 32+ cycles (mul/div)

### Branch Penalty

**Correctly Predicted (GSHARE):**
- 0 cycles (no stall)

**Mispredicted:**
- 2 cycles (flush fetch + decode)

**Example:**
```
Cycle N:   Fetch BEQ (predicted taken)
Cycle N+1: Fetch target (speculative)
Cycle N+2: Execute BEQ → Not taken (misprediction)
Cycle N+3: Flush N+1, Fetch correct target (2-cycle penalty)
```

### ALU Stall

**Multi-Cycle Operations:**
- Sequential multiply: 32 cycles
- Wallace tree multiply: 1 cycle
- Division: 32 cycles

**Stall Behavior:**
```assembly
Cycle N:   mul x5, x3, x4   # Start multiply
Cycle N+1: add x6, x5, x7   # Decode, but stalled (x5 not ready)
...
Cycle N+32: Multiply done → alu_stall_o = 0
Cycle N+33: Resume pipeline
```

## Verification

### Test Cases

1. **Data Forwarding:**
```assembly
add x5, x3, x4    # Produce x5
sub x6, x5, x7    # Consume x5 (EX forwarding)
or x8, x5, x9     # Consume x5 (WB forwarding)
```

2. **Branch Taken:**
```assembly
beq x1, x2, target  # Branch taken
nop                 # Should be flushed
target:
  add x3, x4, x5
```

3. **JALR Alignment:**
```assembly
addi x5, x0, 0x81   # Odd address
jalr x1, 0(x5)      # Target 0x81 → Exception (misaligned)
```

4. **CSR Operation:**
```assembly
csrrs x1, mstatus, x2   # Read-modify-write
csrrw x3, mtvec, x4     # Atomic swap
```

5. **Hardware Breakpoint:**
```assembly
lw x1, 0(x2)   # Load from address in tdata2 → Breakpoint exception
```

### Assertions

```systemverilog
// JALR target must be 2-byte aligned
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (pc_sel_i == JALR) |-> (pc_target_o[0] == 0));

// Branch target must be 2-byte aligned for RV32C
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (pc_sel_i inside {BEQ, BNE, BLT, BGE, BLTU, BGEU}) |-> (pc_target_o[0] == 0));

// JAL/JALR: rd must receive PC + 4
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (instr_type_i inside {u_jal, i_jalr}) |-> (alu_result_o == pc_incr_i));

// Forwarding: no data hazard
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (fwd_a_i != 2'b00) |-> (data_a != r1_data_i));
```

## İlgili Modüller

1. **alu.sv**: ALU operations, M extension
2. **cs_reg_file.sv**: CSR register file
3. **decode.sv**: Provides operands, control signals
4. **memory.sv**: Receives ALU result, store data
5. **hazard_unit.sv**: Generates forwarding control

## Gelecek İyileştirmeler

1. **Pipelined Multiply/Divide**: Reduce stall cycles
2. **Branch Target Buffer (BTB)**: Zero-cycle branch resolution
3. **Early Branch Resolution**: Decode stage branch resolution
4. **CSR Bypass Network**: Reduce CSR read latency

## Referanslar

1. RISC-V Unprivileged ISA Specification v20191213 - Chapter 2 (Base Instruction Set)
2. RISC-V Privileged ISA Specification v1.12 - Chapter 3 (Machine-Level ISA)
3. "Computer Architecture: A Quantitative Approach" - Hennessy & Patterson, Appendix C (Pipelining)

---

**Son Güncelleme:** 5 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
