# Fetch Module — Technical Documentation

## Overview

The `fetch.sv` module is the first stage of the RISC-V processor core (stage 01). It handles program counter (PC) management, instruction cache access, branch prediction, and exception detection. In a pipelined design it starts the instruction stream and supplies instructions to downstream stages (decode, execute, and so on).

## Main responsibilities

1. **Program counter (PC) management:** Correct PC updates for sequential flow, branches, jumps, and exceptions  
2. **Instruction fetch:** Fetching instructions through the instruction cache  
3. **Branch prediction:** Branch prediction using the GSHARE algorithm  
4. **Misaligned instruction handling:** Handling misaligned instructions via the align buffer  
5. **Exception detection:** Exception detection with configurable priority  
6. **Compressed instruction support:** Decoding RV32C (16-bit) instructions  

## Port definitions

### Input ports

| Port | Type | Description |
|------|------|-------------|
| `clk_i` | logic | System clock |
| `rst_ni` | logic | Active-low asynchronous reset |
| `stall_i` | stall_e | Pipeline stall signal (NO_STALL / stall enum) |
| `flush_i` | logic | Pipeline flush (misprediction / exception) |
| `flush_pc_i` | [XLEN-1:0] | New PC value on flush |
| `lx_ires_i` | ilowX_res_t | Instruction response from lower-level memory |
| `pc_target_i` | [XLEN-1:0] | Resolved branch/jump target from execute |
| `ex_mtvec_i` | [XLEN-1:0] | Machine trap vector (exception handler address) |
| `trap_active_i` | logic | Trap handler active? |
| `misa_c_i` | logic | C extension (compressed instructions) enabled? |
| `tdata1_i` | [XLEN-1:0] | Trigger data 1 (debug breakpoint config) |
| `tdata2_i` | [XLEN-1:0] | Trigger data 2 (breakpoint address) |
| `tcontrol_i` | [XLEN-1:0] | Trigger control (mte bit[3] enables triggers) |
| `spec_hit_i` | logic | Branch prediction correct? (1 = correct, 0 = misprediction) |
| `de_info_i` | pipe_info_t | Pipeline info from decode |
| `ex_info_i` | pipe_info_t | Pipeline info from execute |

### Output ports

| Port | Type | Description |
|------|------|-------------|
| `spec_o` | predict_info_t | Prediction info (predicted PC, taken / not-taken) |
| `lx_ireq_o` | ilowX_req_t | Instruction request to lower-level memory |
| `pc_o` | [XLEN-1:0] | Current program counter |
| `pc_incr_o` | [XLEN-1:0] | Sequential PC (pc+2 or pc+4) |
| `inst_o` | [XLEN-1:0] | Fetched instruction (to decode) |
| `imiss_stall_o` | logic | Instruction cache miss stall |
| `exc_type_o` | exc_type_e | Detected exception type |
| `instr_type_o` | instr_type_e | Instruction type (decode helper) |

## Architectural blocks

### 1. Program counter (PC) register

```systemverilog
always_ff @(posedge clk_i) begin
  if (!rst_ni) begin
    pc <= RESET_VECTOR;
  end else if (pc_en) begin
    pc <= pc_next;
  end
end
```

**Behavior:**
- On reset, PC loads `RESET_VECTOR` (parameterized, typically `0x80000000`)
- When `pc_en` is asserted, `pc_next` is captured
- While stalled, the PC does not change

### 2. PC next logic (priority order)

The next PC is chosen in this priority order:

```
1. flush_i         → flush_pc_i        (highest — pipeline flush)
2. trap_active_i   → ex_mtvec_i        (exception handler)
3. !spec_hit_i     → pc_target_i       (misprediction recovery)
4. spec_o.taken    → spec_o.pc         (predicted taken branch)
5. Default         → pc_incr_o         (sequential — PC+2/+4)
```

**Details:**
- **Flush:** Flush from decode/execute (e.g. FENCE.I)
- **Trap:** On exception/interrupt, jump to trap handler (`mtvec`)
- **Misprediction:** Correct wrong branch prediction in execute
- **Branch taken:** If prediction says taken, use predicted target
- **Sequential:** Default — fetch the next instruction

### 3. PC increment calculation

```systemverilog
pc_incr_o = (buff_res.valid && is_comp) ? (pc_o + 32'd2) : (pc_o + 32'd4);
```

- **Compressed** (16-bit, C extension): PC + 2  
- **32-bit instruction:** PC + 4  
- Compressed vs uncompressed comes from `compressed_decoder`

### 4. Fetch valid logic

Fetch validity is derived as follows:

```systemverilog
if (flush_i) 
  fetch_valid = 1'b0;  // Invalid during flush
else if (spec_hit_i)
  fetch_valid = !trap_active_i;  // If speculation correct, apply trap check
else
  fetch_valid = !trap_active_i;  // If speculation wrong, same trap gating
```

**Logic:**
- **During flush:** No instruction is valid
- **Speculation hit:** Normal exception rules
- **Speculation miss:** Fetch may still be valid except where execute exceptions dominate (pipeline will flush)

### 5. Exception detection and parametric priority

Parametric priority per RISC-V Privileged Specification section 3.1.15:

```systemverilog
// Exception detection flags
has_debug_breakpoint   = fetch_valid && tcontrol_i[3] && tdata1_i[2] && (pc_o == tdata2_i);
has_instr_misaligned   = fetch_valid && (misa_c_i ? pc_o[0] : (pc_o[1:0] != 2'b00));
has_instr_access_fault = fetch_valid && !grand;
has_illegal_instr      = fetch_valid && illegal_instr && buff_res.valid;
has_ebreak             = fetch_valid && (instr_type_o == ebreak);
has_ecall              = fetch_valid && (instr_type_o == ecall);
```

**Priority order** (configurable in `level_param.sv`):
1. **BREAKPOINT** (hardware debug): `EXC_PRIORITY_DEBUG_BREAKPOINT`
2. **INSTR_MISALIGNED** (misaligned PC): `EXC_PRIORITY_INSTR_MISALIGNED`
3. **INSTR_ACCESS_FAULT** (PMA violation): `EXC_PRIORITY_INSTR_ACCESS_FAULT`
4. **ILLEGAL_INSTRUCTION**: `EXC_PRIORITY_ILLEGAL`
5. **EBREAK**: `EXC_PRIORITY_EBREAK`
6. **ECALL**: `EXC_PRIORITY_ECALL`

**Parametric control:**
- Each exception type has a priority level in `level_param.sv`
- `check_exc_priority()` gates which exceptions are active
- Allows tuning to different RISC-V privileged spec interpretations

### 6. Instruction cache miss handling

```systemverilog
imiss_stall_o = (buff_req.valid && !buff_res.valid);
```

**Stall:**
- Valid request to the align buffer but no response yet
- Pipeline stalls (via `hazard_unit`)
- Ready/valid is not fully registered on the align-buffer request path

**TODO:** A full handshake protocol may be added later (as noted in code)

### 7. Buffer-to-cache request gating

The align buffer may hold `valid` high across cycles; this is gated to a single-cycle I-cache handshake:

```systemverilog
icache_req.valid = abuff_icache_req.valid && !buf_lookup_ack;

always_ff @(posedge clk_i) begin
  if (buff_lowX_res.valid) 
    buf_lookup_ack <= 1'b0;  // Response arrived; allow new request
  else if (buff_res.waiting_second && buf_lookup_ack)
    buf_lookup_ack <= 1'b0;  // Double miss: clear for second request
  else if (icache_req.valid && buff_lowX_res.ready && !buf_lookup_ack)
    buf_lookup_ack <= 1'b1;  // Request accepted; set ack
end
```

**Purpose:**
- On miss, the align buffer keeps `valid` asserted
- That must not issue a new I-cache request every cycle
- `buf_lookup_ack` suppresses repeats until the response clears it (including double-miss cases)

## Submodules

### 1. PMA (physical memory attributes)

```systemverilog
pma i_pma (
  .addr_i      (pc_o),
  .uncached_o  (uncached),
  .memregion_o (memregion),
  .grand_o     (grand)
);
```

**Role:**
- Classifies the PC for memory attributes
- **uncached:** bypass I-cache (e.g. MMIO)
- **grand:** access allowed (if not, `INSTR_ACCESS_FAULT`)
- **memregion:** region type (reserved for future use)

### 2. GSHARE branch predictor

```systemverilog
gshare_bp i_gshare_bp (
  .clk_i         (clk_i),
  .rst_ni        (rst_ni),
  .spec_hit_i    (spec_hit_i),
  .pc_target_i   (pc_target_i),
  .inst_i        (inst_o),
  .stall_i       (!pc_en),
  .pc_i          (pc_o),
  .pc_incr_i     (pc_incr_o),
  .fetch_valid_i (buff_res.valid),
  .spec_o        (spec_o),
  .de_info_i     (de_info_i),
  .ex_info_i     (ex_info_i)
);
```

**Role:**
- Performs branch prediction
- GSHARE: GHR ⊕ PC indexes the PHT
- RAS predicts returns
- BTB caches branch targets
- See `gshare_bp_module.md` for detail

### 3. Align buffer

```systemverilog
align_buffer i_align_buffer (
  .clk_i      (clk_i),
  .rst_ni     (rst_ni),
  .flush_i    (flush_i),
  .buff_req_i (buff_req),
  .buff_res_o (buff_res),
  .lowX_res_i (buff_lowX_res),
  .lowX_req_o (abuff_icache_req)
);
```

**Role:**
- Aligns 128-bit I-cache lines into 32-bit instructions
- Supports misaligned fetches spanning a line boundary
- Handles double miss (two lines)
- Even/odd banks organize 16-bit parcels
- See `align_buffer_module.md` for detail

### 4. Instruction cache

```systemverilog
cache #(
  .IS_ICACHE   (1),
  .cache_req_t (icache_req_t),
  .cache_res_t (icache_res_t),
  .lowX_req_t  (ilowX_req_t),
  .lowX_res_t  (ilowX_res_t),
  .CACHE_SIZE  (IC_CAPACITY),
  .BLK_SIZE    (BLK_SIZE),
  .XLEN        (XLEN),
  .NUM_WAY     (IC_WAY)
) i_icache (
  .clk_i          (clk_i),
  .rst_ni         (rst_ni),
  .flush_i        (flush_i),
  .cache_req_i    (icache_req),
  .cache_res_o    (icache_res),
  .lowX_res_i     (lx_ires_i),
  .lowX_req_o     (lx_ireq_o),
  .fencei_stall_o (icache_fencei_stall)
);
```

**Role:**
- Caches instructions (set-associative or direct-mapped)
- On miss, fetches from lower level (L2 / memory)
- Parameterized size, associativity, block size
- `fencei_stall_o` is tied low for I-cache (used on D-cache)

### 5. Compressed decoder

```systemverilog
compressed_decoder i_compressed_decoder (
  .instr_i         (buff_res.blk),
  .instr_o         (inst_o),
  .is_compressed_o (is_comp),
  .illegal_instr_o (illegal_instr)
);
```

**Role:**
- Expands 16-bit RV32C encodings to 32-bit instructions
- Handles C0, C1, C2 quadrants
- Flags illegal compressed encodings
- Matches the RISC-V C extension spec
- See `compressed_decoder_module.md` for detail

## Timing Diagram

```
Cycle 0: Reset
         PC = RESET_VECTOR (0x80000000)

Cycle 1: Sequential Fetch
         PC = 0x80000000
         Request to Align Buffer & ICache
         
Cycle 2: Align Buffer Response
         inst_o = 0x00000013 (NOP)
         is_comp = 0 (32-bit instruction)
         pc_incr_o = PC + 4 = 0x80000004
         
Cycle 3: Sequential Fetch
         PC = 0x80000004
         
Cycle 4: Branch Instruction Fetch
         inst_o = 0x00C0006F (JAL)
         spec_o.taken = 1
         spec_o.pc = PC + 0xC = 0x80000010
         
Cycle 5: Branch Target Fetch
         PC = 0x80000010 (predicted)
         
Cycle N: Branch Resolution (in Execute stage)
         spec_hit_i = 1 (correct prediction)
         
Cycle M: Misprediction Case
         spec_hit_i = 0
         pc_next = pc_target_i (actual target from EX)
         flush_i = 1 (flush decode/fetch stages)
```

## Performance Considerations

### 1. Cache miss handling
- **Single-cycle hit:** align buffer + I-cache hit → `inst_o` valid same cycle  
- **Multi-cycle miss:** request to lower memory; stall until response  
- **Double miss** (misaligned / straddle): two lines; align buffer sequences them  

### 2. Branch prediction impact
- **Correct:** steady pipeline  
- **Mispredict:** ~3–4 cycle penalty (flush + refetch)  
- GSHARE accuracy: ~85–95% (workload-dependent)  

### 3. Compressed instructions
- **Code density:** ~25–30% smaller binaries  
- **Performance:** PC step +2 or +4  
- **Decode:** combinational, same cycle  

## Exception Handling Flow

```
1. Exception Detection (Fetch Stage)
   ↓
2. exc_type_o signal → Pipeline
   ↓
3. Propagate through the pipeline (toward writeback)
   ↓
4. Writeback: trap_active_i = 1
   ↓
5. Fetch: pc_next = ex_mtvec_i (trap handler)
   ↓
6. Trap Handler Execution
```

**Notes:**
- Exceptions are detected in fetch but committed in writeback
- On speculation miss, fetch-side exceptions may be flushed
- Trap entry PC comes from `mtvec` (vectored or direct mode)

## Debug & Verification

### Commit Tracer Support

```systemverilog
`ifdef COMMIT_TRACER
  always_comb begin
    fe_tracer_o.inst = '0;
    if ((stall_i == NO_STALL) && buff_res.valid) begin
      if (is_comp)
        fe_tracer_o.inst = {16'b0, buff_res.blk[15:0]};
      else
        fe_tracer_o.inst = buff_res.blk;
    end
  end
`endif
```

**Purpose:**
- Trace each committed instruction in simulation/verification
- Distinguish compressed vs uncompressed
- Active when the fetch is valid

### Suggested assertions

```systemverilog
// PC alignment (2-byte if C, else 4-byte)
assert property (@(posedge clk_i) disable iff (!rst_ni)
  misa_c_i |-> pc_o[0] == 1'b0 else pc_o[1:0] == 2'b00);

// No valid fetch during flush
assert property (@(posedge clk_i) disable iff (!rst_ni)
  flush_i |-> !fetch_valid);

// PC must correct after misprediction
assert property (@(posedge clk_i) disable iff (!rst_ni)
  !spec_hit_i && (ex_info_i.bjtype != NO_BJ) |=> pc_o == $past(pc_target_i));
```

## Parameter configuration

### RESET_VECTOR
```systemverilog
parameter RESET_VECTOR = level_param::RESET_VECTOR
```
- Default: `0x80000000`
- RISC-V convention: machine-mode reset vector
- SoC-specific overrides possible

### Cache parameters (via `level_param.sv`)
- `IC_CAPACITY`: I-cache size (e.g. 16 KB)
- `IC_WAY`: associativity (1 = direct-mapped; 2/4/8 = set-associative)
- `BLK_SIZE`: line size (often 128 bits = 16 bytes)

### Predictor parameters (via `level_param.sv`)
- `GHR_SIZE`: global history width (e.g. 8)
- `PHT_SIZE`: PHT entries (e.g. 256)
- `BTB_SIZE`: BTB entries (e.g. 128)
- `RAS_SIZE`: RAS depth (e.g. 8)

## Related modules

1. **align_buffer.sv** — alignment and misaligned fetch  
2. **gshare_bp.sv** — branch prediction and BTB  
3. **compressed_decoder.sv** — RV32C decode  
4. **ras.sv** — return-address stack  
5. **cache.sv** — shared cache wrapper (I/D)  
6. **pma.sv** — physical memory attributes  

## Future improvements (TODO)

1. **Full handshake:** register align-buffer requests for strict ready/valid  
2. **Prefetcher:** detect sequential PC and prefetch ahead  
3. **Multiple outstanding misses:** overlap refills  
4. **Fusion:** fuse hot instruction pairs into one micro-op  
5. **Advanced predictors:** perceptron or TAGE  

## References

1. RISC-V Unprivileged ISA Specification v20191213
2. RISC-V Privileged Specification v1.12
3. RISC-V "C" Standard Extension (Compressed Instructions)
4. "A Case for (Partially) TAgged GEometric History Length Branch Prediction" - André Seznec, 2006
5. "The GShare Predictor" - Scott McFarling, 1993

---

**Last updated:** 4 December 2025  
**Author:** Kerim TURAK  
**License:** MIT License
