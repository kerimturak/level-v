# Dual-port BRAM (`dp_bram`) — technical documentation

## Overview

`dp_bram` is a **true dual-port** synchronous RAM template in **write-first** mode: on each port, a read in the same cycle as a write returns the **new** write data. **Simultaneous writes to the same address from both ports are undefined** — do not rely on ordering.

## File location

```
rtl/ram/dp_bram.sv
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `DATA_WIDTH` | 32 | Word width |
| `NUM_SETS` | 1024 | Depth (rows) |

## Ports

| Port group | Signals |
|------------|---------|
| **Port A** | `a_chip_en`, `a_addr`, `a_wr_en`, `a_wr_data`, `a_rd_data` |
| **Port B** | `b_chip_en`, `b_addr`, `b_wr_en`, `b_wr_data`, `b_rd_data` |
| **Common** | `clk` — single clock for both ports |

## Behavior

Each port has the same semantics as [sp_bram](overview.md) (write-first): if `*_chip_en` and `*_wr_en`, `*_rd_data` gets `*_wr_data`; else `*_rd_data` reads the array.

## Usage

- **L2 cache** tag/data banks (`nbmbmp_l2_cache`) — one pipeline per port.
- Other **true dual-port** structures needing independent readers/writers on the same array.

## Related

- [Single-port BRAM overview](overview.md) — `sp_bram`
- [L2 cache](../core/mmu/l2_cache_module.md)
