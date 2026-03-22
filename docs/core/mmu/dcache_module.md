# Data cache (`dcache`) — technical documentation

## Overview

`dcache` is a **parametric set-associative data cache** with read/write support, dirty tracking, and a **lower** memory port for fills and write-backs. It exposes `fencei_stall_o` so the pipeline can stall while **FENCE.I**–related writebacks complete.

## File location

```
rtl/core/mmu/dcache.sv
```

## Key parameters

Same pattern as [icache](icache_module.md): `CACHE_SIZE`, `BLK_SIZE`, `NUM_WAY`, `XLEN`, plus typed `cache_*` and `lowX_*` ports.

## Ports

| Port | Description |
|------|-------------|
| `clk_i`, `rst_ni`, `flush_i` | Clock, reset, flush |
| `cache_req_i` | Loads and stores (size, write data, byte enables, uncached) |
| `cache_res_o` | Responses to the memory stage |
| `lowX_res_i`, `lowX_req_o` | Refill / evict to backing store |
| `fencei_stall_o` | **High while I-cache fence logic is draining dirty lines** via the helper FSM |

## FENCE.I cooperation

Dirty lines may need write-back before instruction memory can be treated as coherent. The submodule [dcache_fencei](dcache_fencei_module.md) implements the scan/writeback FSM; `fencei_stall_o` keeps the CPU from retiring past a safe point.

## Related

- [Store buffer](../stage04_memory/store_buffer_module.md)
- [dcache_fencei](dcache_fencei_module.md)
- [Memory stage](../stage04_memory/memory_module.md)
