# Prefetcher wrapper — technical documentation

## Overview

`prefetcher_wrapper` selects one of several **prefetch strategies** at elaboration time via `level_param::PREFETCH_TYPE`. It normalizes the cache-facing interface for `fetch` / cache integration.

## File location

```
rtl/core/stage01_fetch/prefetcher_wrapper.sv
```

## Parameters

| Parameter | Description |
|-----------|-------------|
| `XLEN`, `BLK_SIZE` | From `level_param` |
| `PREFETCH_TYPE` | `level_param::PREFETCH_TYPE` — see table below |

## Prefetch types

| Value | Name | Behavior |
|-------|------|----------|
| `0` | None | `prefetch_valid_o` tied low |
| `1` | Next-line | Instantiates [next_line_prefetcher](next_line_prefetcher_module.md) |
| `2`–`4` | Stride / stream / hybrid | Reserved (TODO in RTL) |

## Ports

| Port | Description |
|------|-------------|
| `clk_i`, `rst_ni`, `flush_i` | Clock, reset, flush |
| `cache_miss_i`, `cache_hit_i` | Miss/hit from cache (hit used by future strategies) |
| `access_addr_i`, `access_pc_i`, `access_valid_i` | Observed access (PC for stride, etc.) |
| `cache_busy_i` | Back-pressure from cache |
| `prefetch_ack_i` | Ack from memory / queue |
| `prefetch_valid_o`, `prefetch_addr_o` | Outbound prefetch |

## Notes

- For type `1`, `miss_addr_i` of the internal prefetcher is driven from `access_addr_i`.
- When adding new types, keep the external port list stable so `fetch` does not need churn.
