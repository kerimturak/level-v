# Pipelined multiplier (`mul_pipelined`) — technical documentation

## Overview

`mul_pipelined` implements a **2-cycle** 32×32 multiply to **shorten combinational depth** vs. a single-cycle array. Operands are split into **four 8×32 partial products** in stage 1; stage 2 **adds/shifts** them into a 64-bit product.

## File location

```
rtl/core/stage03_execute/mul_div/mul_pipelined.sv
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `XLEN` | 32 | Multiplicand width |
| `YLEN` | 32 | Multiplier width |

## Ports

| Port | Description |
|------|-------------|
| `clk_i`, `rst_ni` | Clock, reset |
| `start_i` | Latch new `a_i`, `b_i` and begin |
| `a_i`, `b_i` | Operands |
| `product_o` | `XLEN+YLEN`-bit result |
| `busy_o` | Operation in flight |
| `done_o` | One-cycle pulse when result is ready |
| `valid_o` | Result valid (with `done_o` semantics per connection in `execution`) |

## Micro-architecture

1. **Stage 1** (registered): compute `a * b[7:0]`, `a * b[15:8]`, `a * b[23:16]`, `a * b[31:24]`.
2. **Stage 2** (registered): align and sum partial products into `product_o`.

## Related

- [Integer multiplier (`mul_int`)](mul_int_module.md) — single-cycle variant
- [Wallace multiplier tree](wallace_multiplier_module.md) — optional generator-based path
- [Execution](execution_module.md) — selects and sequences MUL ops
