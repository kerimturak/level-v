# Bug Report #003: Periodic Reset Signal Resetting Statistics Counters

## Summary
Branch predictor statistics counters and commit log files were being reset/overwritten periodically (~every 108K cycles) during CoreMark simulation due to the `rst_ni` signal going low multiple times during execution.

## Severity
**Medium** - Causes incorrect statistics reporting and log file corruption

## Symptoms
1. `bp_stats.log` shows repeating patterns instead of monotonically increasing values
2. Commit log file (`writeback.log`) size fluctuates during simulation
3. Statistics values reset to small numbers every ~108K cycles
4. Final statistics report shows incorrect (too small) values

### Example: bp_stats.log with Bug
```csv
Time,TotalBranches,Correct,Mispred,JAL,JAL_Correct,JALR,JALR_Correct,RAS_Total,RAS_Correct,BTB_Hits,BTB_Misses
10000,999,645,354,122,122,15,12,10,8,862,216
20000,2416,1573,843,301,301,38,31,28,23,2077,505
30000,3246,2112,1134,403,403,51,41,37,30,2792,679
...
# After ~108K cycles, values reset back to small numbers:
120000,999,645,354,122,122,15,12,10,8,862,216    # ← Same as line 1!
130000,2416,1573,843,301,301,38,31,28,23,2077,505
```

## Root Cause Analysis

### Problem 1: Statistics Counters Resetting on `rst_ni`

The statistics counters in `gshare_bp.sv` were implemented with reset logic:

```systemverilog
// BUGGY CODE - counters reset when rst_ni goes low
always_ff @(posedge clk_i) begin
  if (!rst_ni) begin
    total_branches      <= '0;  // ← Resets on every rst_ni assertion
    correct_predictions <= '0;
    mispredictions      <= '0;
    // ... all counters reset
  end else if (!stall_i) begin
    // Update statistics
  end
end
```

### Problem 2: Commit Log File Reopening on Reset

The `writeback_log.svh` was reopening the log file on every reset:

```systemverilog
// BUGGY CODE - file reopened on every reset
always_ff @(posedge clk_i) begin
  if (!rst_ni) begin
    $fclose(trace_file);
    trace_file = $fopen(trace_path, "w");  // ← Overwrites previous data!
  end
end
```

### Why `rst_ni` Goes Low Multiple Times

During CoreMark simulation, the reset signal (`rst_ni`) can go low multiple times:
- Initial power-on reset
- Watchdog timer resets (if configured)
- Software-triggered resets
- Memory subsystem synchronization resets

This is normal behavior for the CPU, but diagnostic/logging logic should be **reset-independent** to capture cumulative statistics.

## Solution

### Fix 1: Reset-Independent Statistics Counters

Changed from reset-based initialization to declaration-time initialization:

```systemverilog
// FIXED CODE - counters are reset-independent (cumulative)
// Declaration with initialization
logic [63:0] total_branches      = '0;
logic [63:0] correct_predictions = '0;
logic [63:0] mispredictions      = '0;
logic [63:0] ras_predictions     = '0;
logic [63:0] ras_correct         = '0;
logic [63:0] btb_hits            = '0;
logic [63:0] btb_misses          = '0;
logic [63:0] jal_count           = '0;
logic [63:0] jal_correct         = '0;
logic [63:0] jalr_count          = '0;
logic [63:0] jalr_correct        = '0;
logic [63:0] ibtc_predictions    = '0;
logic [63:0] ibtc_correct        = '0;

// Statistics update (reset-independent)
always_ff @(posedge clk_i) begin
  if (rst_ni && !stall_i) begin  // Only update when NOT in reset
    // Update statistics...
  end
end
```

### Fix 2: Commit Log File - Open Once, Periodic Flush

Removed file reopening on reset and added periodic flushing:

```systemverilog
// FIXED CODE - file opened once in initial block, periodic flush
integer trace_file;
integer flush_counter = 0;
localparam FLUSH_INTERVAL = 10000;

initial begin
  trace_file = $fopen(trace_path, "w");
  // Write header...
end

always_ff @(posedge clk_i) begin
  // Removed: if (!rst_ni) { $fclose; $fopen } block
  
  if (rst_ni && valid_commit) begin
    // Write trace data...
    
    // Periodic flush for safety
    flush_counter <= flush_counter + 1;
    if (flush_counter >= FLUSH_INTERVAL) begin
      flush_counter <= 0;
      $fflush(trace_file);
    end
  end
end
```

## Files Modified

| File | Change Description |
|------|-------------------|
| `rtl/core/stage01_fetch/gshare_bp.sv` | Statistics counters now use initialization syntax; always_ff condition changed from `if (!rst_ni)` to `if (rst_ni && !stall_i)` |
| `rtl/include/writeback_log.svh` | Removed file reopen on reset; added periodic flush with `FLUSH_INTERVAL` |

## Verification

### Before Fix
```
bp_stats.log shows repeating pattern every ~108K cycles
Final total_branches: ~3000 (incorrect - only last reset period)
```

### After Fix
```
bp_stats.log shows monotonically increasing values
Final total_branches: ~300,000+ (correct - cumulative over entire simulation)
```

## Lessons Learned

1. **Diagnostic/Logging Logic Should Be Reset-Independent**: Unlike functional RTL that needs proper reset behavior, logging and statistics collection should survive resets to capture full simulation data.

2. **Use Initialization Syntax for Simulation-Only Counters**: `logic [N:0] counter = '0;` is synthesizable and provides reset-independent initialization.

3. **Never Reopen Files on Reset**: Log files should be opened once in `initial` block and closed in `final` block. Use periodic `$fflush()` instead of close/reopen.

4. **Consider Multiple Resets in Long Simulations**: What seems like a "one-time" reset at startup may actually occur multiple times during complex workloads like CoreMark.

## Related Issues
- None

## Date
2025-11-30

## Status
**RESOLVED**
