# Wallace multiplier tree (`wallace32x32`) — technical documentation

## Overview

The directory `rtl/core/stage03_execute/mul_div/wallace32x32/` contains a **generator-style Wallace-tree multiplier** built from small **parametric building blocks**. It is an alternative to `mul_int` / `mul_pipelined` when `FEAT_WALLACE_*` defines select that path in the execution unit.

## File location

```
rtl/core/stage03_execute/mul_div/wallace32x32/
├── configure.sv   # Top-level 32×32 composition
├── wallace.sv       # Wallace reduction stage
├── mul.sv           # Base multiplier tile
├── add.sv, cla.sv   # Adders / carry lookahead
├── dadda.sv, fa.sv, ha.sv
└── mutex.sv         # Mutex for shared resources in the tree
```

## Hierarchy (conceptual)

1. **`configure`** — wires partial products and reduction stages into a 32-bit × 32-bit product.
2. **`wallace`** — compresses partial products using Wallace/Dadda-style counters.
3. **Leaf `mul`** — small multipliers inferred as logic.
4. **Adders** — `cla`, `add`, `fa`, `ha` build the final sum.

## When used

Controlled by feature macros in `level_defines.svh` / makefile (e.g. `FEAT_WALLACE_SINGLE`, `FEAT_WALLACE_MULTI`). Only **one** multiplier implementation should be active at a time.

## Trade-offs

- **Area / timing**: deeper tree, different PPA than inferred DSP or pipelined split.
- **Verification**: treat as a black box with random tests against `mul_pipelined` / ISA MUL.

## Related

- [mul_int](mul_int_module.md), [mul_pipelined](mul_pipelined_module.md)
- [ALU](alu_module.md)
