# DCache ModelSim Debug Guide

## Quick Start

1. Navigate to the testbench directory:
```bash
cd /home/kerim/level-v/sim/tb/mmu/dcache
```

2. Run ModelSim with the TCL script:
```bash
vsim -do run_modelsim.tcl
```

## What to Look For

The waveform will show you:

### Critical Signals for Writeback Debug:

1. **Writeback State Machine** (`wb_state_q`):
   - WB_IDLE (0)
   - WB_REQUEST (1)
   - WB_WAIT (2)
   - WB_DONE (3)

2. **Eviction Signals**:
   - `evict_tag`: Combinational tag being evicted
   - `wb_evict_tag_q`: Latched tag (check if this matches evict_tag)
   - `evict_data`: Data being written back
   - `wb_evict_data_q`: Latched data

3. **Lower Memory Writes** (`lowX_req`):
   - Check `lowX_req.addr` when `lowX_req.rw=1` (write)
   - Compare with `{evict_tag, rd_idx, 4'b0000}`
   - Should write to correct address!

4. **Tag Array**:
   - `tsram.rtag[0]`, `tsram.rtag[1]`, etc.: Tags read from BRAM
   - `tsram.wtag`: Tag being written
   - `tsram.way`: Which way is being written
   - `tag_array_wr_en`: Tag write enable

## Known Issues Fixed

- **Issue**: First writeback went to 0x00000000 instead of correct address
- **Root Cause**: On WB_IDLE→WB_REQUEST transition, `wb_evict_tag_q` wasn't latched yet
- **Fix**: Use combinational `evict_tag` when `wb_state_q == WB_IDLE`

## Debugging Steps

1. **Find First Writeback**:
   - Search for `lowX_req.valid=1 AND lowX_req.rw=1`
   - Check `lowX_req.addr`

2. **Trace Back to Eviction**:
   - Look at `wb_state_q` transition to WB_REQUEST
   - Check `evict_tag` and `wb_evict_tag_q` values
   - Verify they match!

3. **Check Tag Reads**:
   - When cache miss occurs, tags are read from `tsram.rtag`
   - Verify tag values are correct (not 0x00000 after writes)

4. **Check Data Corruption**:
   - If wrong data is written back, check `evict_data` vs `wb_evict_data_q`
   - Verify data array reads (`dsram.rdata`)

## Alternative: Dump VCD for GTKWave

If you prefer GTKWave, add to testbench:
```systemverilog
initial begin
  $dumpfile("dcache_writeback.vcd");
  $dumpvars(0, tb_dcache_writeback);
end
```

Then view with:
```bash
gtkwave dcache_writeback.vcd
```

## Current Test Status

The standalone testbench (`tb_dcache_writeback.sv`) shows:
- ✅ Writeback addresses are now CORRECT (0x80000000, 0x80000100)
- ❌ Still 3 test errors (test logic issues, not dcache bugs)

For full system CoreMark:
- ✅ First 200 commits match correct.log exactly
- ❌ Diverges at line 10213 with wrong memory read value
- This suggests a different bug (possibly data corruption during writeback)
