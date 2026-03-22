# L2 cache (`nbmbmp_l2_cache`) — technical documentation

## Overview

`nbmbmp_l2_cache` (**n**on-**b**locking **m**ulti-**b**ank **m**ulti-**p**ort) is a **write-back L2** shared by the **I-side** and **D-side** lower ports (`ilowX_*`, `dlowX_*`). It arbitrates to a single **memory** port (`iomem_*`) compatible with the SoC memory bridge.

## File location

```
rtl/core/mmu/nbmbmp_l2_cache.sv
```

## High-level topology

```
I-cache ilowX ──► I-pipe ──┐
                          ├──► shared memory controller ──► wb_master_bridge / memory
D-cache dlowX ──► D-pipe ──┘
```

## Features (from design header)

- Two independent **pipeline FSMs** (I-pipe, D-pipe)
- **Dual-port BRAM** (`dp_bram`) per way per bank — port A for I-pipe, port B for D-pipe
- Register-based **PLRU** and **dirty** arrays with merged updates
- **MSHR**-style miss handling with `from_dport` routing for fills
- **Uncached bypass** (D-port; I-side bypass rules via I-pipe)
- **Set-conflict** hazard protection when both ports target the same set
- Parametric **multi-bank** (`L2_NUM_BANKS`, `L2_BANK_SETS`, etc. from `level_param`)

## Pipeline timing (per pipe)

Roughly: **IDLE** (accept) → **TAG_LOOKUP** (SRAM register) → **RESOLVE** (hit vs miss) → hit response or miss + evict/fill/wb path. See enum `pipe_state_t` in RTL.

## Ports

| Port | Description |
|------|-------------|
| `clk_i`, `rst_ni`, `flush_i` | Clock, reset, global flush |
| `icache_req_i`, `icache_res_o` | I-side L1 refill path |
| `dcache_req_i`, `dcache_res_o` | D-side L1 path |
| `mem_req_o`, `mem_res_i` | Single downstream memory port |

## Configuration

Enable with `USE_L2_CACHE` / related `level_param` fields (see `level_param.sv` and makefile defines).

## Related

- [icache](icache_module.md), [dcache](dcache_module.md)
- `rtl/ram/dp_bram.sv` — dual-port array primitive
