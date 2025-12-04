# WRITEBACK Modülü - Teknik Döküman

## Genel Bakış

`writeback.sv` modülü, RISC-V işlemcisinin **Write-Back Stage** (WB) implementasyonudur. Pipeline'ın son stage'idir ve instruction sonuçlarını register file'a yazar. Bu modül, data source selection (ALU/Memory/PC) ve register file write enable kontrolünü yapar.

## Sorumluluklar

1. **Data Source Selection**: ALU result, memory data veya PC+4 arasında seçim
2. **Register File Write Control**: Stall ve flush durumlarında write enable kontrolü
3. **Commit Trace**: Instruction retirement tracking (debug/verification için)

## Port Tanımları

### Clock & Control

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `stall_i` | stall_e | Pipeline stall sinyali |
| `fe_flush_cache_i` | logic | Cache flush (FENCE.I, branch mispredict) |

### Data Inputs

| Port | Tip | Açıklama |
|------|-----|----------|
| `pc_i` | [XLEN-1:0] | Program counter |
| `pc_incr_i` | [XLEN-1:0] | PC + 4 (or PC + 2 for compressed) |
| `alu_result_i` | [XLEN-1:0] | ALU/CSR result from execute stage |
| `read_data_i` | [XLEN-1:0] | Load data from memory stage |
| `data_sel_i` | [1:0] | Data source selection |
| `rf_rw_en_i` | logic | Register file write enable (from decode) |

### Outputs

| Port | Tip | Açıklama |
|------|-----|----------|
| `wb_data_o` | [XLEN-1:0] | Write-back data (to register file) |
| `rf_rw_en_o` | logic | Actual register file write enable |

### Commit Tracer Ports (Debug/Verification)

```systemverilog
`ifdef COMMIT_TRACER
  input fe_tracer_info_t fe_tracer_i;
  input logic wr_en_i;
  input logic [1:0] rw_size_i;
  input logic [XLEN-1:0] write_data_i;
  input logic [XLEN-1:0] csr_wr_data_i;
  input logic [4:0] rd_addr_i;
  input logic rd_en_csr_i;
  input logic wr_en_csr_i;
  input logic trap_active_i;
  input logic [11:0] csr_idx_i;
  input instr_type_e instr_type_i;
  input logic [XLEN-1:0] tcontrol_i;
`endif
```

**Purpose:** Spike-compatible commit log generation for verification

## Data Source Selection

### Selection Logic

```systemverilog
wb_data_o = data_sel_i[1] ? pc_incr_i : 
            (data_sel_i[0] ? read_data_i : alu_result_i);
```

**Truth Table:**

| data_sel_i | Source | Description | Instruction Examples |
|------------|--------|-------------|----------------------|
| 2'b00 | alu_result_i | ALU/CSR result | ADD, SUB, ADDI, CSR ops |
| 2'b01 | read_data_i | Memory load data | LW, LH, LB, LHU, LBU |
| 2'b10 | pc_incr_i | PC + instruction size | JAL, JALR (link register) |
| 2'b11 | pc_incr_i | (same as 2'b10) | Not used |

### Data Source Examples

#### ALU Result (data_sel_i = 2'b00)

```assembly
add x1, x2, x3     # x1 = x2 + x3
addi x1, x2, 10    # x1 = x2 + 10
and x1, x2, x3     # x1 = x2 & x3
```

**Flow:**
```
EX: alu_result_i = x2 + x3
WB: wb_data_o = alu_result_i
    Register file: x1 ← wb_data_o
```

#### Memory Data (data_sel_i = 2'b01)

```assembly
lw x1, 0(x2)       # x1 = MEM[x2]
lh x1, 4(x2)       # x1 = sign_extend(MEM[x2+4][15:0])
lbu x1, 8(x2)      # x1 = zero_extend(MEM[x2+8][7:0])
```

**Flow:**
```
MEM: read_data_i = load_data (from D-Cache)
WB: wb_data_o = read_data_i
    Register file: x1 ← wb_data_o
```

#### PC Increment (data_sel_i = 2'b10)

```assembly
jal x1, target     # x1 = PC + 4, PC = PC + offset
jalr x1, 0(x2)     # x1 = PC + 4, PC = x2 + 0
```

**Flow:**
```
EX: pc_incr_i = PC + 4 (return address)
WB: wb_data_o = pc_incr_i
    Register file: x1 ← wb_data_o (link register)
```

## Register File Write Enable Control

### Write Enable Logic

```systemverilog
rf_rw_en_o = rf_rw_en_i && 
             !fe_flush_cache_i && 
             !(stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL});
```

**Conditions for Write:**
1. **rf_rw_en_i = 1**: Instruction writes to register (has rd)
2. **fe_flush_cache_i = 0**: No pipeline flush
3. **No Stall**: Pipeline not stalled

**Write Disabled When:**
- **IMISS_STALL**: I-Cache miss (instruction not valid)
- **DMISS_STALL**: D-Cache miss (data not ready)
- **ALU_STALL**: Multi-cycle ALU operation (mul/div)
- **FENCEI_STALL**: FENCE.I cache flush
- **fe_flush_cache_i = 1**: Branch mispredict or exception

### Example Scenarios

#### Normal Write (No Stall)

```
Cycle N:   FE: add    DE: -      EX: -      MEM: -     WB: -
Cycle N+1: FE: sub    DE: add    EX: -      MEM: -     WB: -
Cycle N+2: FE: or     DE: sub    EX: add    MEM: -     WB: -
Cycle N+3: FE: and    DE: or     EX: sub    MEM: add   WB: -
Cycle N+4: FE: xor    DE: and    EX: or     MEM: sub   WB: add
                                                        ↑
                                                   rf_rw_en_o=1
                                                   x1 ← alu_result
```

#### D-Cache Miss (Load Stall)

```
Cycle N:   FE: lw     DE: -      EX: -      MEM: -     WB: -
Cycle N+1: FE: add    DE: lw     EX: -      MEM: -     WB: -
Cycle N+2: FE: sub    DE: add    EX: lw     MEM: -     WB: -
Cycle N+3: FE: sub    DE: add    EX: lw     MEM: lw    WB: -  (D-miss start)
Cycle N+4: FE: sub    DE: add    EX: lw     MEM: lw    WB: -  (stalled)
...
Cycle N+12: FE: sub   DE: add    EX: lw     MEM: lw    WB: -  (stalled)
Cycle N+13: FE: or    DE: sub    EX: add    MEM: lw    WB: -  (refill done)
Cycle N+14: FE: and   DE: or     EX: sub    MEM: add   WB: lw
                                                        ↑
                                                   rf_rw_en_o=1
                                                   x1 ← read_data
```

**Key Point:** Write enable suppressed during stall (cycles N+4 to N+12)

#### Branch Mispredict (Flush)

```
Cycle N:   FE: beq    DE: -      EX: -      MEM: -     WB: -
Cycle N+1: FE: add    DE: beq    EX: -      MEM: -     WB: -  (predict taken)
Cycle N+2: FE: sub    DE: add    EX: beq    MEM: -     WB: -  (speculative)
Cycle N+3: FE: or     DE: sub    EX: add    MEM: beq   WB: -  (branch resolve: not taken)
                                             ↑                  fe_flush_cache_i=1
Cycle N+4: FE: corr   DE: -      EX: -      MEM: -     WB: sub
                                                        ↑
                                                   rf_rw_en_o=0 (flushed)
                                                   sub not committed
```

**Key Point:** Speculative instructions flushed, writes suppressed

## Instruction Commit

### What is Commit?

**Commit:** Point where instruction result becomes architecturally visible (written to register file)

**Before Commit:**
- Instruction in pipeline (speculative)
- Can be flushed (branch mispredict, exception)

**After Commit:**
- Result written to register file
- Cannot be undone (architecturally committed)

### Commit Point

**Writeback Stage = Commit Point**

```
Cycle N+4: WB stage
  - rf_rw_en_o = 1
  - Register file write
  - Instruction retired (committed)
```

## Pipeline Interaction

### Data Forwarding

**From Writeback to Decode:**
```systemverilog
// decode.sv
r1_data_o = fwd_a_i[0] ? wb_data_i : r1_data;  // WB forwarding
```

**Example:**
```assembly
Cycle N:   lw x5, 0(x2)    # WB: Write x5
Cycle N+1: add x6, x5, x7  # DE: Read x5 (forward from WB)
```

**Forwarding Path:**
```
WB: wb_data_o → Decode: wb_data_i → Mux (fwd_a_i[0]) → r1_data_o
```

### Stall Propagation

**Hazard Unit monitors stalls:**
```systemverilog
// hazard_unit.sv
if (dmiss_stall_o) begin
  // Stall all stages before MEM
  // WB receives stale/invalid data
  // rf_rw_en_o = 0 (suppress write)
end
```

## Commit Tracer (Verification)

### Purpose

**Generate Spike-compatible commit log for verification:**
- Compare CERES execution with Spike (RISC-V golden model)
- Detect RTL bugs by comparing register/CSR updates

### Trace Format

```
core   0: 0x80000000 (0x00000297) x5  0x80000000
core   0: 0x80000004 (0x01028293) x5  0x80000010
```

**Fields:**
- `core 0`: Core ID
- `0x80000000`: PC
- `(0x00000297)`: Instruction encoding
- `x5`: Destination register
- `0x80000000`: Written value

### Implementation (Simplified)

```systemverilog
`ifdef COMMIT_TRACER
  always_ff @(posedge clk_i) begin
    if (rf_rw_en_o && !trap_active_i) begin
      $display("core   0: 0x%08x (0x%08x) x%-2d 0x%08x",
               fe_tracer_i.pc,
               fe_tracer_i.instr,
               rd_addr_i,
               wb_data_o);
    end
    
    if (wr_en_csr_i) begin
      $display("core   0: CSR write: %s = 0x%08x",
               csr_name(csr_idx_i),
               csr_wr_data_i);
    end
  end
`endif
```

**Enabled by:** `make run T=test LOG_COMMIT=1`

## Timing Diagram

### Normal Instruction (ALU)

```
Cycle:      N       N+1     N+2     N+3     N+4
            ___     ___     ___     ___     ___
clk:       |   |___|   |___|   |___|   |___|   |___

Stage:     FE      DE      EX      MEM     WB

add:       ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

data_sel_i: XXXXXXXXXXXXXXXXXXXXXXXXXX|00|XXX

alu_result_i: XXXXXXXXXXXXXXXXXXXXXXXXX|RES|XX

wb_data_o:  XXXXXXXXXXXXXXXXXXXXXXXXXX|RES|XXX

rf_rw_en_o: ___________________________/‾‾‾\___

Register Write:                        ↑
                                    x1 = RES
```

### Load Instruction (Memory)

```
Cycle:      N       N+1     N+2     N+3     N+4
            ___     ___     ___     ___     ___
clk:       |   |___|   |___|   |___|   |___|   |___

Stage:     FE      DE      EX      MEM     WB

lw:        ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

data_sel_i: XXXXXXXXXXXXXXXXXXXXXXXXXX|01|XXX

read_data_i: XXXXXXXXXXXXXXXXXXXXXXXX|DATA|XX

wb_data_o:  XXXXXXXXXXXXXXXXXXXXXXXXXX|DATA|XX

rf_rw_en_o: ___________________________/‾‾‾\___

Register Write:                        ↑
                                    x1 = DATA
```

### JAL Instruction (Link Register)

```
Cycle:      N       N+1     N+2     N+3     N+4
            ___     ___     ___     ___     ___
clk:       |   |___|   |___|   |___|   |___|   |___

Stage:     FE      DE      EX      MEM     WB

jal:       ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

data_sel_i: XXXXXXXXXXXXXXXXXXXXXXXXXX|10|XXX

pc_incr_i:  XXXXXXXXXXXXXXXXXXXXXXXX|PC+4|XX

wb_data_o:  XXXXXXXXXXXXXXXXXXXXXXXXXX|PC+4|XX

rf_rw_en_o: ___________________________/‾‾‾\___

Register Write:                        ↑
                                    x1 = PC+4
```

## Performance Impact

### Throughput

**Ideal:** 1 instruction per cycle (IPC = 1.0)

**Actual:**
- ALU instructions: 1 IPC (no stall)
- Load (cache hit): 1 IPC (1 cycle latency)
- Load (cache miss): ~0.1 IPC (10 cycle stall)
- Branch (correct predict): 1 IPC
- Branch (mispredict): ~0.5 IPC (2 cycle penalty)

### Critical Path

**Write Enable Path:**
```
stall_i → OR gate → AND gate → rf_rw_en_o
```

**Data Path:**
```
alu_result_i/read_data_i/pc_incr_i → Mux (data_sel_i) → wb_data_o → Register file
```

**Delay:** ~2-3 ns (minimal logic)

## Verification

### Test Cases

1. **ALU Write:**
```assembly
add x1, x2, x3     # Check: x1 = x2 + x3
addi x5, x0, 10    # Check: x5 = 10
```

2. **Load Write:**
```assembly
lw x1, 0(x2)       # Check: x1 = MEM[x2]
```

3. **JAL Link:**
```assembly
jal x1, target     # Check: x1 = PC + 4
```

4. **x0 Write (should be ignored):**
```assembly
add x0, x1, x2     # Check: x0 = 0 (no write)
```

5. **Stall Suppression:**
```assembly
lw x1, 0(x2)       # D-miss → stall
add x3, x1, x4     # Should not write during stall
```

6. **Flush Suppression:**
```assembly
beq x1, x2, target # Mispredict
add x3, x4, x5     # Flushed, should not write
```

### Assertions

```systemverilog
// x0 never written
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (rf_rw_en_o && rd_addr_i == 5'b0) |-> 0);  // Should never happen

// Write enable only when no stall
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL}) |-> !rf_rw_en_o);

// Write enable cleared on flush
assert property (@(posedge clk_i) disable iff (!rst_ni)
  fe_flush_cache_i |-> !rf_rw_en_o);

// Data source matches selection
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (data_sel_i == 2'b00) |-> (wb_data_o == alu_result_i));
```

## Corner Cases

### 1. Back-to-Back Loads (RAW Hazard)

```assembly
lw x5, 0(x2)       # Cycle N+4: WB writes x5
add x6, x5, x7     # Cycle N+1: DE reads x5 (forward from WB)
```

**Forwarding Required:** WB data forwarded to decode (1 cycle delay)

### 2. Load After Store (WAR Hazard)

```assembly
sw x5, 0(x2)       # Store x5 to memory
lw x5, 4(x2)       # Load different location to x5
```

**No Hazard:** Different addresses, no structural hazard in WB stage

### 3. Branch Mispredict + Load

```assembly
beq x1, x2, taken  # Predict taken (wrong)
lw x5, 0(x3)       # Speculative load (flushed)
```

**Correct Behavior:**
- Load reaches WB stage
- Branch resolves (mispredict)
- `fe_flush_cache_i = 1`
- `rf_rw_en_o = 0` (write suppressed)
- x5 not modified

### 4. Exception During WB

```assembly
lw x5, 0(x2)       # Load (valid)
ecall              # Exception (trap)
```

**Handling:**
- Load commits normally (before ecall)
- Ecall traps, subsequent instructions flushed
- WB stage not affected by later exceptions

## İlgili Modüller

1. **register_file.sv**: Receives wb_data_o and rf_rw_en_o
2. **decode.sv**: Uses wb_data_o for data forwarding
3. **hazard_unit.sv**: Controls rf_rw_en_o via stall signals
4. **memory.sv**: Provides read_data_i (load data)
5. **execution.sv**: Provides alu_result_i and pc_incr_i

## Gelecek İyileştirmeler

1. **Register File Bypassing**: Reduce forwarding latency
2. **Write Buffer**: Decouple writeback from pipeline
3. **Out-of-Order Completion**: Allow later instructions to commit before earlier loads

## Referanslar

1. RISC-V Unprivileged ISA Specification v20191213 - Chapter 2 (Base Integer Instruction Set)
2. "Computer Organization and Design: RISC-V Edition" - Patterson & Hennessy, Chapter 4 (The Processor)
3. Spike RISC-V ISA Simulator - Commit Log Format

---

**Son Güncelleme:** 5 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
