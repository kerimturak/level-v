# Bug Report #002: Combinational Loop Causing Instruction Corruption in Verilator

## Summary
Verilator simulation produces incorrect instruction fetch results compared to Modelsim due to UNOPTFLAT (combinational loop) warnings in `align_buffer.sv` and `cache.sv`. This causes the RTL to fetch garbage instructions (e.g., `0x3333006f` instead of `0x0100006f`).

## Severity
**Critical** - Causes simulation failure and incorrect program execution

## Symptoms
1. Test `C-cbnez-01` passes in Modelsim but fails in Verilator
2. Verilator RTL fetches wrong instruction values
3. Match rate drops to ~22% compared to Spike golden model
4. RTL runs 100K cycles (timeout) instead of completing normally (~621 instructions)

### Example Mismatch
```
PC=0x800004de:
  Verilator RTL: INST=0x3333006f  ❌ (garbage - from x9 register value!)
  Modelsim RTL:  INST=0x0100006f  ✓
  Spike:         INST=0x0100006f  ✓
```

The `0x3333006f` value comes from `0x33333333` which was loaded into register `x9` in previous instructions - indicating memory/cache data corruption in the combinational logic.

## Root Cause Analysis

### UNOPTFLAT Warnings from Verilator Lint
```
%Warning-UNOPTFLAT: align_buffer.sv:56:10: Circular combinational logic: 'even'
%Warning-UNOPTFLAT: align_buffer.sv:56:41: Circular combinational logic: 'odd'
%Warning-UNOPTFLAT: align_buffer.sv:58:30: Circular combinational logic: 'miss_state'
%Warning-UNOPTFLAT: align_buffer.sv:59:30: Circular combinational logic: 'hit_state'
%Warning-UNOPTFLAT: align_buffer.sv:68:30: Circular combinational logic: 'half_sel'

%Warning-UNOPTFLAT: cache.sv:55:31: Circular combinational logic: 'cache_wr_way'
%Warning-UNOPTFLAT: cache.sv:56:31: Circular combinational logic: 'cache_wr_en'
%Warning-UNOPTFLAT: cache.sv:54:31: Circular combinational logic: 'cache_select_data'
```

### Why This Happens

#### Verilator vs Modelsim Simulation Model

| Feature | Modelsim | Verilator |
|---------|----------|-----------|
| Simulation Type | 4-state (0,1,X,Z) event-driven | 2-state (0,1) cycle-based |
| Combinational Loops | Iterates until stable | Limited iterations (converge-limit) |
| Evaluation Order | Non-deterministic but stable | Deterministic but may differ |
| X Propagation | Full X tracking | X → 0 (fast mode) |

When there's a combinational loop:
- **Modelsim**: Evaluates signals in event-driven order, naturally finding stable state
- **Verilator**: Uses fixed evaluation order, may not converge to same stable state

### Problematic Code Pattern in `align_buffer.sv`

```systemverilog
// bank_t struct contains many interdependent signals
typedef struct packed {
  logic valid, match, miss, hit;
  logic [IDX_WIDTH-1:0] rd_idx, data_wr_idx;
  logic tag_wr_en;
  logic [NUM_PARCELS/2-1:0][PARCEL_BITS-1:0] wr_parcel, rd_parcel;
  logic [TAG_SIZE:0] rd_tag, wr_tag;
  logic [PARCEL_BITS-1:0] parcel, deviceX_parcel;
} bank_t;
bank_t even, odd;  // ← UNOPTFLAT: These have circular dependencies

always_comb begin
  // even and odd depend on each other through complex logic
  even.miss = buff_req_i.valid && !(even.valid && even.match);
  odd.miss  = buff_req_i.valid && !(odd.valid && odd.match);
  
  miss_state = {odd.miss, even.miss};  // ← UNOPTFLAT
  hit_state  = {odd.hit, even.hit};    // ← UNOPTFLAT
  
  // These signals then feed back into parcel selection
  even.parcel = unalign ? even.rd_parcel[0] : even.rd_parcel[word_sel+half_sel];
  odd.parcel  = odd.rd_parcel[word_sel];
  
  // Output depends on hit_state which depends on even/odd
  if (&hit_state) begin
    buff_res_o.blk = {odd.parcel, even.parcel};  // ← Output affected!
  end
end
```

The circular dependency chain:
```
buff_req_i.addr → word_sel/half_sel → even.rd_idx/odd.rd_idx 
                                    ↓
                           even.rd_tag/odd.rd_tag (from RAM)
                                    ↓
                           even.match/odd.match
                                    ↓
                           even.miss/odd.miss/hit
                                    ↓
                           miss_state/hit_state
                                    ↓
                           buff_res_o.blk (instruction output!)
                                    ↓
                    [feedback through cache response]
                                    ↓
                           even.rd_parcel/odd.rd_parcel
                                    ↑
                        [circular back to output]
```

## Attempted Fixes (Did Not Fully Resolve)

### 1. Increased Converge Limit
```makefile
--converge-limit 100  # Default is 10
```
**Result**: Build succeeds but simulation still fails

### 2. Added split_var Directives
```systemverilog
bank_t even /*verilator split_var*/, odd /*verilator split_var*/;
logic [1:0] miss_state /*verilator split_var*/;
logic [1:0] hit_state /*verilator split_var*/;
```
**Result**: Verilator ignores split_var for packed structs

### 3. Changed X-Initial Handling
```makefile
X_ASSIGN  = fast
X_INITIAL = 0
--x-initial-edge
```
**Result**: No improvement

## Recommended Fixes

### Option A: Register Critical Signals (Adds 1 Cycle Latency)
Break the combinational loop by registering intermediate signals:
```systemverilog
// Register miss_state to break the loop
logic [1:0] miss_state_q;
always_ff @(posedge clk_i) begin
  miss_state_q <= {odd.miss, even.miss};
end
// Use registered version for output logic
```
**Tradeoff**: Adds 1 cycle latency to instruction fetch

### Option B: Restructure Logic into Pipeline Stages
Split the always_comb block into separate stages with clear dependencies:
```systemverilog
// Stage 1: Address decode (no feedback)
always_comb begin
  word_sel = buff_req_i.addr[OFFSET_WIDTH-1:2];
  half_sel = buff_req_i.addr[1];
  // ...
end

// Stage 2: Tag comparison (depends only on Stage 1)
always_comb begin
  even.match = (even.rd_tag == even.wr_tag);
  // ...
end

// Stage 3: Output mux (depends only on Stage 2)
always_comb begin
  // Final output selection
end
```

### Option C: Use Verilator Waiver (Suppress Warning Only)
```
// verilator.vlt
lint_off -rule UNOPTFLAT -file "*/align_buffer.sv" -match "*even*"
lint_off -rule UNOPTFLAT -file "*/align_buffer.sv" -match "*odd*"
```
**Warning**: This only suppresses the warning, doesn't fix the behavior!

## Files Affected
- `rtl/core/stage01_fetch/align_buffer.sv` - Main culprit
- `rtl/core/mmu/cache.sv` - Secondary issues
- `rtl/core/stage01_fetch/fetch.sv` - Downstream effects

## Test Case
```bash
make test T=C-cbnez-01 SIM=verilator  # FAILS
make test T=C-cbnez-01 SIM=modelsim   # PASSES
```

## Lint Output Location
```
results/lint/verilator/lint.log
results/lint/verilator/lint_waiver.vlt
```

## Related
- Bug #001: Unaligned instruction fetch across cache lines
- Verilator docs: https://verilator.org/guide/latest/warnings.html#cmdoption-arg-UNOPTFLAT

## Status
**Open** - Requires RTL restructuring to properly fix

## Date
2024-11-30
