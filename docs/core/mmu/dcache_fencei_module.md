# `dcache_fencei` — FENCE.I write-back helper

## Overview

`dcache_fencei` is a **standalone FSM** extracted from `dcache.sv` to handle **FENCE.I**: scan sets/ways, detect **dirty** lines, issue write-backs on the lower memory interface, then mark lines clean.

## File location

```
rtl/core/mmu/dcache_fencei.sv
```

## Parameters

Sized to match the parent D-cache arrays: `TAG_SIZE`, `BLK_SIZE`, `XLEN`, `NUM_WAY`, `IDX_WIDTH`, `BOFFSET`, `NUM_SET`.

## Interface (conceptual)

**Inputs:** clock/reset, `flush_i` (FENCE.I trigger edge-detected), lower-memory ready/valid, dirty bits and tag/data readouts from the D-cache SRAM models.

**Outputs:** `fi_active`, writeback request/address/data/tag, way one-hot and set index for array writes, `fi_mark_clean` to clear dirty after successful WB.

## FSM states

`FI_IDLE` → `FI_SCAN` → `FI_CHECK_WAY` → `FI_WRITEBACK_REQ` / `WAIT` → `FI_MARK_CLEAN` → `FI_NEXT_WAY` → … → `FI_DONE`.

## Notes

- Dirty is derived from tag/metadata (see RTL: valid bit in MSB of tag word plus dirty array).
- Starting a new fence is qualified on a rising edge of `flush_i` while idle.

## Related

- [dcache](dcache_module.md)
