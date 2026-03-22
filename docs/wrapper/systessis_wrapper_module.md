# `systessis_wrapper` — FPGA synthesis shell

## Overview

`systessis_wrapper` is a **thin top** for **FPGA synthesis** (e.g. Xilinx). It optionally instantiates a **clock wizard** when `` `ifdef SYNTHESIS `` and otherwise wraps **`level_wrapper`** with a reduced pin list compared to full SoC simulation.

## File location

```
rtl/wrapper/systessis_wrapper.sv
```

## Parameters

| Parameter | Role |
|-----------|------|
| `CLK_FREQ_HZ` | Passed to `level_wrapper` (default `CPU_CLK`) |
| `BAUD_RATE` | UART baud |

## Pins (active build)

Typical exposed signals:

- `clk_i`, `rst_ni`
- `uart0_tx_o`, `uart0_rx_i`
- `prog_rx_i`, `prog_mode_o` — UART programming path

Additional peripheral ports (SPI, I2C, GPIO, PWM, VGA, etc.) appear in the source as **commented placeholders** for future board-specific packages.

## Clock generation

```systemverilog
`ifdef SYNTHESIS
  clk_wiz_0 clk_generator ( ... );
`endif
```

The generated `clk_out1` / `locked` must be connected to `level_wrapper` per your board flow (see full RTL for exact wiring).

## Usage

1. Add this module as the **top** in Vivado (or other) when targeting FPGA.
2. Provide constraints for `clk_i`, UART, and programming pins.
3. Expand commented ports when the PCB design includes more interfaces.

## Related

- [Level wrapper](level_wrapper.md)
- [RAM programmer](ram_programmer.md)
