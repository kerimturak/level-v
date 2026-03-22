# Gshare Branch Predictor Module — Technical Documentation

## Overview

The `gshare_bp.sv` module implements advanced branch prediction for the RISC-V core. It combines GSHARE (global history with shared indexing), a tournament meta-predictor, RAS (return address stack), BTB (branch target buffer), IBTC (indirect branch target cache), and a loop predictor for high accuracy.

## Why branch prediction matters

Modern pipelined processors:
- Branches resolve in execute (often 3–4 cycles after fetch)
- A wrong guess forces a **pipeline flush** (typically a 3–4 cycle penalty)
- A correct guess keeps the pipeline full

**Example:**
- 100M instructions, 20% branches
- 10% misprediction rate → 2M mispredictions
- 4-cycle penalty → **~8M wasted cycles** (~8% performance loss)

## Core predictor structures

### 1. GSHARE (primary)
- **Global history register (GHR):** last *N* branch outcomes
- **Pattern history table (PHT):** 2-bit saturating counters indexed by PC ⊕ GHR
- **Strength:** captures global branch correlation

### 2. Bimodal (secondary)
- **PHT:** 2-bit counters indexed by PC only
- **Strength:** simple; good on more local patterns

### 3. Tournament (meta)
- **Choice table:** selects GSHARE vs bimodal
- Favors whichever was more accurate
- **Typical accuracy:** ~90–95% (workload-dependent)

### 4. Return address stack (RAS)
- **Return prediction:** for `ret`-style control flow
- Stack-based LIFO
- **Typical accuracy:** ~95–99%

### 5. Branch target buffer (BTB)
- **Target cache:** stores branch target addresses
- Tag + target pair
- BTB miss → static BTFN-style fallback

### 6. Indirect branch target cache (IBTC)
- **JALR prediction:** for indirect jumps
- PC → target map
- Covers indirect jumps the RAS does not handle

### 7. Loop predictor
- **Iteration tracking:** estimates loop trip counts
- Learns trip counts
- Detects backward branches

## Port definitions

### Input ports

| Port | Type | Description |
|------|-----|----------|
| `clk_i` | logic | System clock |
| `rst_ni` | logic | Active-low asynchronous reset |
| `spec_hit_i` | logic | Was the prediction correct? (1=yes, 0=misprediction) |
| `stall_i` | logic | Pipeline stall signal |
| `inst_i` | inst_t | Fetched instruction |
| `pc_target_i` | [XLEN-1:0] | Resolved branch/jump target from execute |
| `pc_i` | [XLEN-1:0] | Current program counter |
| `pc_incr_i` | [XLEN-1:0] | PC + 4 (sequential) |
| `fetch_valid_i` | logic | Fetch cycle is valid |
| `de_info_i` | pipe_info_t | Decode pipeline info |
| `ex_info_i` | pipe_info_t | Execute pipeline info |

### Output ports

| Port | Type | Description |
|------|-----|----------|
| `spec_o` | predict_info_t | Prediction bundle (PC, taken, spectype) |

**`predict_info_t` layout:**
```systemverilog
typedef struct packed {
  logic [XLEN-1:0] pc;        // Predicted target PC
  logic            taken;     // Branch taken?
  spec_type_e      spectype;  // Prediction type (BRANCH/JUMP/RAS/NO_SPEC)
} predict_info_t;
```

## Data structures

### Global History Register (GHR)

```systemverilog
logic [GHR_SIZE-1:0] ghr;        // Committed GHR (EX feedback)
logic [GHR_SIZE-1:0] ghr_spec;   // Speculative GHR (prediction)
```

**Size:** `GHR_SIZE = 8–16` bits (from `level_param.sv`)

**Updates:**
- **Speculative:** on each prediction, shift left and append the predicted outcome
- **Committed:** when the branch resolves in execute, shift left and append the actual outcome

**Example (GHR_SIZE=8):**
```
Initial:    GHR = 8'b00000000
Branch 1 (taken):     GHR_spec = 8'b00000001
Branch 2 (not-taken): GHR_spec = 8'b00000010
Misprediction → GHR restore + correct outcome
```

### Pattern History Table (PHT)

```systemverilog
logic [1:0] pht [PHT_SIZE];      // GSHARE PHT
logic [1:0] bimodal [PHT_SIZE];  // Bimodal PHT
```

**Size:** `PHT_SIZE = 256–1024` entries (2^8 to 2^10)

**2-Bit Saturating Counter:**
```
State | Value | Prediction
------|-------|------------
SNT   | 2'b00 | Strongly Not-Taken
WNT   | 2'b01 | Weakly Not-Taken
WT    | 2'b10 | Weakly Taken
ST    | 2'b11 | Strongly Taken

Transition (on taken):
  2'b00 → 2'b01 → 2'b10 → 2'b11 (saturate)

Transition (on not-taken):
  2'b11 → 2'b10 → 2'b01 → 2'b00 (saturate)
```

**Index Calculation:**
```systemverilog
// GSHARE: XOR for correlation
pht_idx = pc[PC_BITS:1] ^ ghr_spec[GHR_SIZE-1:0];

// Bimodal: PC only
bimodal_idx = pc[PC_BITS:1];
```

### Choice Table (Tournament)

```systemverilog
logic [1:0] choice [PHT_SIZE];
```

**Selection:**
- `choice[1] == 1` → Use GSHARE prediction
- `choice[1] == 0` → Use Bimodal prediction

**Update Logic:**
```systemverilog
if (pht[idx][1] != bimodal[idx][1]) begin  // Disagreement
  if (pht[idx][1] == actual_outcome) begin
    // GSHARE correct → increase choice
    if (choice[idx] < 2'b11) choice[idx] <= choice[idx] + 1;
  end else begin
    // Bimodal correct → decrease choice
    if (choice[idx] > 2'b00) choice[idx] <= choice[idx] - 1;
  end
end
```

### Branch Target Buffer (BTB)

```systemverilog
logic btb_valid [BTB_SIZE];
logic [TAG_WIDTH-1:0] btb_tag [BTB_SIZE];
logic [XLEN-1:0] btb_target [BTB_SIZE];
```

**Size:** `BTB_SIZE = 128–512`

**Lookup:**
```systemverilog
btb_idx = pc[BTB_IDX_BITS:1];
btb_hit = btb_valid[btb_idx] && (btb_tag[btb_idx] == pc[XLEN-1:BTB_IDX_BITS+2]);
predicted_target = btb_target[btb_idx];
```

**Update (on branch resolution):**
```systemverilog
btb_valid[btb_wr_idx]  <= 1'b1;
btb_tag[btb_wr_idx]    <= ex_pc[XLEN-1:BTB_IDX_BITS+2];
btb_target[btb_wr_idx] <= actual_target;
```

### Indirect Branch Target Cache (IBTC)

```systemverilog
logic ibtc_valid [IBTC_SIZE];
logic [TAG_WIDTH-1:0] ibtc_tag [IBTC_SIZE];
logic [XLEN-1:0] ibtc_target [IBTC_SIZE];
```

**Size:** `IBTC_SIZE = 32–128`

**Usage:**
- JALR targets the RAS does not cover  
- Examples: computed jumps, vtable dispatches, switch jump tables  

**Lookup:**
```systemverilog
ibtc_idx = pc[IBTC_IDX_BITS:1];
ibtc_hit = ibtc_valid[ibtc_idx] && (ibtc_tag[ibtc_idx] == pc[XLEN-1:IBTC_IDX_BITS+2]);
predicted_target = ibtc_target[ibtc_idx];
```

### Loop Predictor

```systemverilog
logic [7:0] loop_count [LOOP_SIZE];  // Current iteration
logic [7:0] loop_trip [LOOP_SIZE];   // Max iterations seen
logic loop_valid [LOOP_SIZE];
logic [TAG_WIDTH-1:0] loop_tag [LOOP_SIZE];
```

**Size:** `LOOP_SIZE = 32–64`

**Operation:**
1. Detect backward branch (`$signed(target - pc) < 0`)
2. Loop entry: `loop_count = 1`
3. Each iteration: `loop_count++`
4. On loop exit: `loop_trip = loop_count`, `loop_count = 0`
5. Predict exit when `loop_count >= loop_trip - 1`

**Example:**
```c
for (int i = 0; i < 10; i++) {  // Loop trip count = 10
  // ...
}
```
- Iterations 1–9: predict TAKEN (continue loop)
- Iteration 10: predict NOT-TAKEN (exit)

## Prediction Logic (Priority order)

```systemverilog
if (popped.valid) 
  spec_o = RAS prediction;
else if (j_type)
  spec_o = JAL prediction (PC + imm);
else if (jr_type && ibtc_hit)
  spec_o = JALR prediction (IBTC target);
else if (b_type) begin
  if (loop_hit && is_backward_branch)
    spec_o = Loop predictor;
  else if (btb_hit)
    spec_o = Tournament predictor (GSHARE/Bimodal);
  else if (is_backward_branch)
    spec_o = Static BTFN (predict TAKEN);
  else
    spec_o = Static BTFN (predict NOT-TAKEN);
end
else
  spec_o = Sequential (PC + 4);
```

### 1. RAS prediction (highest priority)

```systemverilog
if (popped.valid) begin
  spec_o.pc       = popped.data;       // return address popped from RAS
  spec_o.taken    = 1'b1;
  spec_o.spectype = RAS;
end
```

**Condition:** `jr_type && (rd_addr == x1 || rd_addr == x5) && (rs1_addr == x1 || rs1_addr == x5)`

### 2. JAL Prediction (Unconditional Jump)

```systemverilog
if (j_type) begin
  spec_o.pc       = pc_i + imm;        // PC-relative jump
  spec_o.taken    = 1'b1;
  spec_o.spectype = JUMP;
end
```

**Accuracy:** 100% (unconditional; target is deterministic)

### 3. JALR with IBTC Prediction

```systemverilog
if (jr_type && ibtc_hit) begin
  spec_o.pc       = ibtc_predicted_target;
  spec_o.taken    = 1'b1;
  spec_o.spectype = JUMP;
end
```

**IBTC miss:** sequential fetch continues (target unknown)

### 4. Conditional Branch Prediction

#### 4a. Loop Predictor (Backward Branch)

```systemverilog
if (loop_hit && is_backward_branch) begin
  if (loop_pred_exit) begin
    spec_o.pc       = pc_incr_i;     // Predict loop exit
    spec_o.taken    = 1'b0;
  end else begin
    spec_o.pc       = btb_hit ? btb_predicted_target : branch_target_calc;
    spec_o.taken    = 1'b1;
  end
  spec_o.spectype = BRANCH;
end
```

#### 4b. Tournament Predictor (BTB Hit)

```systemverilog
if (btb_hit) begin
  use_gshare = choice[bimodal_idx][1];
  final_taken = use_gshare ? pht[pht_idx][1] : bimodal[bimodal_idx][1];
  
  if (final_taken) begin
    spec_o.pc       = btb_predicted_target;
    spec_o.taken    = 1'b1;
  end else begin
    spec_o.pc       = pc_incr_i;
    spec_o.taken    = 1'b0;
  end
  spec_o.spectype = BRANCH;
end
```

#### 4c. Static BTFN (BTB Miss)

**Backward-Taken, Forward-Not-Taken Heuristic:**

```systemverilog
if (is_backward_branch) begin
  spec_o.pc       = branch_target_calc;  // Predict TAKEN (likely loop)
  spec_o.taken    = 1'b1;
end else begin
  spec_o.pc       = pc_incr_i;           // Predict NOT-TAKEN
  spec_o.taken    = 1'b0;
end
```

**Rationale:**
- Backward branches are usually loops → predict TAKEN  
- Forward branches are usually `if` tests → predict NOT-TAKEN (early exits are less common)  

## GHR Update Mechanism

### Speculative Update (Prediction Phase)

```systemverilog
always_ff @(posedge clk_i) begin
  if (!rst_ni)
    ghr_spec <= '0;
  else if (!stall_i) begin
    if (spec_miss) begin
      // Misprediction → restore committed GHR + correct outcome
      ghr_spec <= {ghr[GHR_SIZE-2:0], ex_was_taken};
    end else if (fetch_valid_i && b_type) begin
      // Speculatively update GHR
      ghr_spec <= {ghr_spec[GHR_SIZE-2:0], spec_o.taken};
    end
  end
end
```

### Committed Update (Execute Feedback)

```systemverilog
always_ff @(posedge clk_i) begin
  if (ex_is_branch) begin
    ghr <= {ghr[GHR_SIZE-2:0], ex_was_taken};
  end
end
```

**Why two GHR copies?**
- **`ghr_spec`:** used during prediction (fetch)
- **`ghr`:** committed history from execute; used for recovery  
- On misprediction, `ghr_spec` is restored from `ghr` (plus correction)

## Predictor Update (Training)

### PHT Update (2-Bit Saturating Counter)

```systemverilog
if (ex_was_taken) begin
  if (pht[pht_wr_idx] < 2'b11) 
    pht[pht_wr_idx] <= pht[pht_wr_idx] + 1;
end else begin
  if (pht[pht_wr_idx] > 2'b00) 
    pht[pht_wr_idx] <= pht[pht_wr_idx] - 1;
end
```

### Choice Update (Tournament)

```systemverilog
if (pht[pht_wr_idx][1] != bimodal[bimodal_wr_idx][1]) begin
  if (pht[pht_wr_idx][1] == ex_was_taken) begin
    // GSHARE correct
    if (choice[bimodal_wr_idx] < 2'b11) 
      choice[bimodal_wr_idx] <= choice[bimodal_wr_idx] + 1;
  end else begin
    // Bimodal correct
    if (choice[bimodal_wr_idx] > 2'b00) 
      choice[bimodal_wr_idx] <= choice[bimodal_wr_idx] - 1;
  end
end
```

**Update only on disagreement:** if both predictors agree, the choice table is left unchanged (both right or both wrong).

### BTB Update

```systemverilog
btb_valid[btb_wr_idx]  <= 1'b1;
btb_tag[btb_wr_idx]    <= ex_info_i.pc[XLEN-1:$clog2(BTB_SIZE)+2];
btb_target[btb_wr_idx] <= pc_target_i;
```

**On every resolved branch:** the BTB is updated regardless of hit/miss.

### Loop Predictor Update

```systemverilog
if ($signed(pc_target_i - ex_info_i.pc) < 0) begin  // Backward branch
  if (ex_was_taken) begin
    if (loop_valid[lp_wr_idx] && loop_tag[lp_wr_idx] == ex_pc_tag) begin
      loop_count[lp_wr_idx] <= loop_count[lp_wr_idx] + 1;  // Iteration
    end else begin
      loop_valid[lp_wr_idx] <= 1'b1;  // New loop entry
      loop_tag[lp_wr_idx]   <= ex_pc_tag;
      loop_count[lp_wr_idx] <= 8'd1;
    end
  end else begin
    if (loop_valid[lp_wr_idx] && loop_tag[lp_wr_idx] == ex_pc_tag) begin
      loop_trip[lp_wr_idx]  <= loop_count[lp_wr_idx];  // Record trip count
      loop_count[lp_wr_idx] <= 8'd0;  // Reset for next loop
    end
  end
end
```

## Branch prediction logger (Optional)

`+define+LOG_BP` enables it.

### Statistics

```systemverilog
logic [63:0] total_branches;
logic [63:0] correct_predictions;
logic [63:0] mispredictions;
logic [63:0] ras_predictions, ras_correct;
logic [63:0] jal_count, jal_correct;
logic [63:0] jalr_count, jalr_correct;
logic [63:0] ibtc_predictions, ibtc_correct;
logic [63:0] btb_hits, btb_misses;
```

### Output format

```
╔══════════════════════════════════════════════════════════════╗
║          GSHARE Branch Predictor - Final Statistics          ║
╠══════════════════════════════════════════════════════════════╣
║  Total Control Transfers : 1000000                          ║
║  Correct Predictions     : 920000    (92.00%)              ║
║  Mispredictions          : 80000     (8.00%)               ║
╠══════════════════════════════════════════════════════════════╣
║  JAL (Direct Jump)                                           ║
║    Total                 : 150000                           ║
║    Correct               : 150000    (100.00%)             ║
╠══════════════════════════════════════════════════════════════╣
║  JALR (Indirect Jump)                                        ║
║    Total                 : 50000                            ║
║    Correct               : 47000     (94.00%)              ║
║    - RAS Predictions     : 40000     (98.00% accurate)     ║
║    - IBTC Predictions    : 7000      (85.71% accurate)     ║
╠══════════════════════════════════════════════════════════════╣
║  Conditional Branch (BEQ/BNE/BLT/BGE/BLTU/BGEU)               ║
║    Total                 : 800000                           ║
║    Correct               : 723000    (90.38%)              ║
║    Mispredicted          : 77000     (9.62%)               ║
╚══════════════════════════════════════════════════════════════╝
```

## Performance Analysis

### Typical Accuracy (Benchmark Dependent)

| Predictor | Accuracy | Misprediction Rate |
|-----------|----------|-------------------|
| Static (Always Not-Taken) | ~60% | ~40% |
| Bimodal (2-bit counter) | ~82-85% | ~15-18% |
| GSHARE (8-bit GHR) | ~87-92% | ~8-13% |
| Tournament (GSHARE+Bimodal) | ~90-95% | ~5-10% |
| Tournament + RAS + BTB + Loop | ~92-96% | ~4-8% |

### Pipeline Impact

**Example (Coremark benchmark):**
- Total instructions: 10M
- Branch instructions: 2M (20%)
- Misprediction rate: 5%
- Mispredictions: 100K
- Penalty: 4 cycles
- **Total penalty:** 400K cycles (~4% slowdown)

**Improvement:**
- Static predictor (15% misprediction) → 600K cycles lost (~6%)
- **Improvement:** 200K cycles saved (33% reduction in penalty)

## Timing Considerations

### Critical Paths

1. **Prediction Path (Fetch Stage):**
   ```
   PC → BTB lookup → PHT lookup → Tournament select → Mux → spec_o.pc
   ```
   - Timing critical (single cycle)
   - BTB/PHT often map to BRAM/SRAM → combinational read from registered address

2. **Update Path (Execute Stage):**
   ```
   ex_info_i → PHT update → Choice update → BTB update
   ```
   - Sequential logic, less critical

### Area Overhead

**Example Configuration:**
- PHT: 256 entries × 2-bit × 2 (GSHARE+Bimodal) = 1 Kbit
- Choice: 256 entries × 2-bit = 512 bit
- BTB: 128 entries × (22-bit tag + 32-bit target) = 6.75 Kbit
- IBTC: 32 entries × (22-bit tag + 32-bit target) = 1.69 Kbit
- Loop: 32 entries × (22-bit tag + 8-bit count + 8-bit trip + 1-bit valid) = 1.22 Kbit
- GHR: 8-bit × 2 (spec + committed) = 16 bit

**Total:** ~11 Kbit (~1.4 KB)

## Verification

### Test Scenarios

1. **Sequential Code:** Prediction accuracy ~100% (no branches)
2. **Simple Loops:** Loop predictor accuracy ~95%
3. **Nested Loops:** GSHARE correlation accuracy ~90%
4. **Function Calls:** RAS accuracy ~98%
5. **Switch-Case:** IBTC accuracy ~85% (after warmup)
6. **Random Branches:** Tournament accuracy ~75-80%

### Suggested assertions

```systemverilog
// On correct speculation, committed GHR must not double-update
assert property (@(posedge clk_i) disable iff (!rst_ni)
  spec_hit_i && ex_is_branch |-> $stable(ghr));

// On misprediction, speculative GHR must be repaired
assert property (@(posedge clk_i) disable iff (!rst_ni)
  !spec_hit_i && ex_is_branch |=> ghr_spec == {$past(ghr[GHR_SIZE-2:0]), $past(ex_was_taken)});

// BTB should update on every resolved branch
assert property (@(posedge clk_i) disable iff (!rst_ni)
  ex_is_branch |=> btb_valid[$past(btb_wr_idx)]);
```

## Future improvements

1. **TAGE predictor:** tagged geometric history length (higher accuracy potential)  
2. **Perceptron predictor:** neural-style predictors  
3. **BTB associativity:** multi-way BTB to reduce aliasing  
4. **Loop predictor:** deeper nested-loop support  
5. **Prefetch integration:** fetch ahead along the predicted path  
6. **Power:** clock gating, selective predictor updates  

## Related modules

1. **fetch.sv:** instantiates and queries the branch predictor  
2. **ras.sv**: Return Address Stack implementation
3. **hazard_unit.sv**: Misprediction handling
4. **execute.sv**: Branch resolution feedback

## References

1. "The GShare Predictor" - Scott McFarling, 1993
2. "A Case for (Partially) TAged GEometric History Length Branch Prediction" - André Seznec, 2006 (TAGE)
3. "Dynamic Branch Prediction with Perceptrons" - Daniel A. Jiménez, Calvin Lin, 2001
4. "Branch Prediction" - Computer Architecture: A Quantitative Approach - Hennessy & Patterson
5. RISC-V Unprivileged ISA Specification - Control Transfer Instructions

---

**Last updated:** 4 December 2025  
**Author:** Kerim TURAK  
**License:** MIT License
