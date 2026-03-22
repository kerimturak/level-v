# Pipelined divider (`divu_pipelined`) — technical documentation

## Overview

`divu_pipelined` performs **unsigned division** with **restoring division**, processing **`BITS_PER_CYCLE` bits per clock** (default 2) to trade latency for **shorter combinational paths** than `divu_int`.

## File location

```
rtl/core/stage03_execute/mul_div/divu_pipelined.sv
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `WIDTH` | 32 | Operand width |
| `BITS_PER_CYCLE` | 2 | Iteration width per cycle |

Iteration count: `WIDTH / BITS_PER_CYCLE` (e.g. 16 cycles for 32/2).

## Ports

| Port | Description |
|------|-------------|
| `clk_i`, `rst_ni` | Clock, reset |
| `start_i` | Start new division |
| `dividend_i`, `divisor_i` | Operands |
| `busy_o`, `done_o`, `valid_o` | Handshake |
| `dbz_o` | Divide-by-zero |
| `quotient_o`, `reminder_o` | Results (note: port name `reminder_o` in RTL) |

## Algorithm (summary)

Each cycle applies one or more **shift–compare–subtract** steps to a wide remainder/quotient register, split across **two combinational stages** (`rem_stage1`/`rem_stage2`) before registering.

## Related

- [Iterative divider (`divu_int`)](divu_int_module.md)
- [Execution](execution_module.md)
