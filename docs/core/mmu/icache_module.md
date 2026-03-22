# Instruction cache (`icache`) — technical documentation

## Overview

`icache` is a **parametric set-associative instruction cache** with a generic `cache_req_t` / `cache_res_t` front side and a **lower** `lowX_req_t` / `lowX_res_t` interface to the next memory level (unified cache, L2, or bus bridge).

## File location

```
rtl/core/mmu/icache.sv
```

## Key parameters

| Parameter | Role |
|-----------|------|
| `CACHE_SIZE` | Total capacity in bits (with default 1024 used as in RTL) |
| `BLK_SIZE` | Line size in bits (`level_param::BLK_SIZE`) |
| `NUM_WAY` | Set associativity |
| `XLEN` | Address width |
| `cache_req_t`, `cache_res_t`, `lowX_*` | Typed structs from `level_param` |

## Ports

| Port | Description |
|------|-------------|
| `clk_i`, `rst_ni`, `flush_i` | Clock, reset, invalidate / flush control |
| `cache_req_i` | Fetch-side request (read-only path in practice) |
| `cache_res_o` | Hit/miss, data, ready |
| `lowX_res_i`, `lowX_req_o` | Fill / refill to backing memory |

## Internals (summary)

- Tag/data arrays and **PLRU** (or equivalent) replacement indexed by set.
- Line fill on miss: drives lower interface until the line is valid.
- `flush_i` coordinates with pipeline exceptions and `fence.i` flows at the SoC level.

## Related

- [Fetch stage](../stage01_fetch/fetch_module.md)
- [D-cache](dcache_module.md) — symmetric data-side cache
- [Unified cache](cache_module.md) — alternative top-level cache path in some configs
- [L2 cache](l2_cache_module.md)
