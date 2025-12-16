# Combinational Loop Fix Documentation

## Problem Description

Verilator was reporting circular combinational logic warnings (UNOPTFLAT) in the fetch stage:

```
%Warning-UNOPTFLAT: Signal unoptimizable: Circular combinational logic:
  - ceres_wrapper.i_soc.i_fetch.i_pma.uncached_o
  - ceres_wrapper.i_soc.i_fetch.i_pma.grand_o
  - ceres_wrapper.i_soc.i_fetch.__Vcellinp__i_gshare_bp__fetch_valid_i
```

### Root Cause

The combinational loop was:
1. `fe_pc` → `pma` → `uncached_o/grand_o`
2. → `fetch_valid` computation (used `grand` for exception detection)
3. → `gshare_bp` (takes `fetch_valid_i`)
4. → `spec_o` (branch prediction output)
5. → `fe_spec` → back to `fe_pc` (via `pc_next`)

This created a circular dependency that Verilator couldn't optimize.

## Solution

### 1. Register PMA Outputs with PC (Zero-Cycle Latency)

**Key Insight:** Instead of looking up PMA for current PC, we look up for `pc_next` and register the result together with PC.

**Changes in `fetch.sv`:**

```systemverilog
// Internal signals
logic uncached, uncached_next;
logic grand, grand_next;
logic memregion, memregion_next;

// PC Register with PMA attributes
always_ff @(posedge clk_i) begin
  if (!rst_ni) begin
    pc        <= RESET_VECTOR;
    uncached  <= 1'b0;        // Reset vector is cached
    grand     <= 1'b1;        // Reset vector is executable
    memregion <= 1'b1;        // Reset vector is valid memory
  end else if (pc_en) begin
    pc        <= pc_next;
    uncached  <= uncached_next;
    grand     <= grand_next;
    memregion <= memregion_next;
  end
end

// PMA lookup for pc_next (combinational)
pma i_pma (
    .addr_i     (pc_next),      // Look up NEXT pc
    .uncached_o (uncached_next), // Result goes to register
    .memregion_o(memregion_next),
    .grand_o    (grand_next)
);
```

**Benefits:**
- ✅ No additional latency (PMA result ready same cycle as PC)
- ✅ Breaks combinational loop (`pc_next` is combinational, but result is registered)
- ✅ Exception handling works correctly (uses registered `grand`)

### 2. Register `fetch_valid` Signal

**Changes in `fetch.sv`:**

```systemverilog
logic fetch_valid;
logic fetch_valid_reg;  // Registered version for gshare_bp

always_ff @(posedge clk_i) begin
  if (!rst_ni) begin
    fetch_valid_reg <= 1'b0;
  end else if (pc_en) begin
    fetch_valid_reg <= fetch_valid;  // Register for branch predictor
  end
end

// Branch predictor uses registered version
gshare_bp i_gshare_bp (
    .fetch_valid_i(fetch_valid_reg),  // 1 cycle delayed
    // ... other signals
);
```

**Impact:**
- Branch predictor sees `fetch_valid` one cycle late
- Minimal performance impact (branch prediction is already speculative)
- Breaks the `fetch_valid` → `spec_o` → `pc_next` loop

## Verification

After fixes, Verilator reports:
```
✓ No UNOPTFLAT warnings
✓ Build successful
✓ All tests pass
```

## Related Build Issues

### ccache Corruption

During debugging, we encountered strange C++ compilation errors:

```
error: invalid preprocessing directive #include
```

**Root Cause:** ccache (compiler cache) had corrupted entries from a previous build.

**Solution:**
```bash
make clean_ccache
```

**Prevention:** Use `make clean_verilator_nuclear` for complete cleanup when:
- Upgrading Verilator
- After interrupted builds
- Seeing unexplained C++ errors

## Architecture Impact

### Before Fix
- Combinational path from PC through PMA, exception logic, branch predictor, back to PC
- Verilator optimization limited
- Potential timing issues in synthesis

### After Fix
- PMA lookup still combinational (for `pc_next`)
- Results registered with PC (no extra latency)
- Clean separation of combinational and sequential logic
- Better synthesis QoR (Quality of Results)

## Performance Analysis

### Timing Impact
- **PMA Lookup:** 0 cycle penalty (pipelined with PC update)
- **fetch_valid:** 1 cycle delay to branch predictor
  - Negligible impact: branch prediction already tolerates multi-cycle latency
  - Mispredict penalty >> 1 cycle fetch_valid delay

### Verification Test Results
```bash
make run_verilator TEST_NAME=rv32ui-p-add    # ✓ PASS
make run_verilator TEST_NAME=dhrystone       # ✓ PASS
make run_verilator TEST_NAME=coremark        # ✓ PASS
```

## Makefile Enhancements

Added new clean targets:

```makefile
# Clear compiler cache (fix strange C++ errors)
make clean_ccache

# Nuclear clean (everything + ccache)
make clean_verilator_nuclear
```

## References

- Verilator UNOPTFLAT Warning: https://verilator.org/warn/UNOPTFLAT
- ccache Documentation: https://ccache.dev/
- Original Issue: Circular combinational logic in fetch stage
- Fixed Files:
  - `rtl/core/stage01_fetch/fetch.sv`
  - `script/makefiles/sim/verilator.mk`

## Lessons Learned

1. **PMA Pipeline Stage:** Instead of adding a pipeline stage (1 cycle penalty), we moved PMA lookup to `pc_next` and registered results with PC (0 cycle penalty).

2. **Registered Interfaces:** When a signal creates a combinational loop through multiple modules, registering it at module boundaries breaks the loop with minimal impact.

3. **ccache Issues:** Compiler cache corruption can manifest as bizarre C++ preprocessing errors. Always try `clean_ccache` when seeing unexplained build failures.

4. **Verilator Optimization:** Eliminating combinational loops improves Verilator's ability to optimize and can improve synthesis timing.

---

**Date:** 2025-12-16
**Author:** Kerim TURAK
**Verilator Version:** 5.042
**Status:** ✅ Resolved
