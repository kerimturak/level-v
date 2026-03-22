# Store buffer — technical documentation

## Overview

`store_buffer` is a **FIFO of pending stores** between the execute stage and the data cache. It enables **store-to-load forwarding** and decouples commit-time stores from D-cache timing.

## File location

```
rtl/core/stage04_memory/store_buffer.sv
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `DEPTH` | `SB_DEPTH` (`level_param`) | Number of entries |

## Ports

### Write port (from execute)

| Port | Description |
|------|-------------|
| `wr_valid_i` | Push a new store |
| `wr_addr_i`, `wr_data_i` | Address and data |
| `wr_size_i` | `rw_size_e` (byte/half/word) |
| `wr_uncached_i` | Uncached attribute |

### Forwarding (combinational)

| Port | Description |
|------|-------------|
| `fwd_addr_i`, `fwd_size_i` | Load under consideration |
| `fwd_hit_o`, `fwd_data_o` | Forwarded data if youngest matching store exists |
| `fwd_conflict_o` | Overlap with a store that cannot be safely forwarded (pipeline hazard) |

### Drain port (to D-cache / `memory`)

| Port | Description |
|------|-------------|
| `drain_valid_o` … `drain_uncached_o` | Oldest entry presented while non-empty |
| `drain_ack_i` | Pop head when the downstream accepts the store |

### Status

| Port | Description |
|------|-------------|
| `full_o`, `empty_o` | FIFO full / empty |

## Behavior

- **FIFO order**: head = oldest store, tail = newest.
- **Forwarding rules** (see comments in RTL): word stores match on word alignment; sub-word stores need exact address and covering size.
- **Conflict**: overlapping store that does not meet forwarding rules asserts `fwd_conflict_o` so the pipeline can stall.

## Related

- [Memory stage](memory_module.md) — instantiates and connects the store buffer to `dcache`.
