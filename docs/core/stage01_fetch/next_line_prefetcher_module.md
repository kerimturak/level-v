# Next-line prefetcher — technical documentation

## Overview

`next_line_prefetcher` issues a **prefetch to the next cache line** after a miss. It is small (on the order of tens of flip-flops), single-cycle in terms of control, and targets **sequential** access patterns.

## File location

```
rtl/core/stage01_fetch/next_line_prefetcher.sv
```

## Parameters

| Parameter | Description |
|-----------|-------------|
| `XLEN` | Address width (default from `level_param::XLEN`) |
| `BLK_SIZE` | Cache line size in **bits** (default `level_param::BLK_SIZE`) |

## Ports

| Port | Direction | Description |
|------|-----------|-------------|
| `clk_i` | in | Clock |
| `rst_ni` | in | Active-low reset |
| `flush_i` | in | Pipeline flush — cancels pending prefetch |
| `cache_miss_i` | in | A miss occurred on the monitored cache |
| `miss_addr_i` | in | Address that missed |
| `prefetch_ack_i` | in | Downstream accepted the prefetch request |
| `cache_busy_i` | in | Cache busy — suppress new prefetch |
| `prefetch_valid_o` | out | Prefetch request valid |
| `prefetch_addr_o` | out | Line-aligned address of the line to prefetch |

## Behavior

1. On a **new** miss (line index changed vs. last miss), the module computes the **next line address**: current line base + `BLK_SIZE/8` bytes.
2. A small FSM (`IDLE` → `PENDING` → `WAIT_ACK`) holds the request until `prefetch_ack_i` or `flush_i`.
3. Duplicate prefetches for the **same line** as the previous miss are suppressed.

## Integration

Typically driven from I- or D-cache miss logic and connected to the memory side or a prefetch queue. See also [Prefetcher wrapper](prefetcher_wrapper_module.md).
