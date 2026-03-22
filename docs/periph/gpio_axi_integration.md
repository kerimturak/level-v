# GPIO — AXI integration (Xilinx-compatible)

## Overview

Besides the native [GPIO controller](gpio.md) (`gpio.sv`), the tree includes **AXI-Lite–based** options for **Xilinx IP** and block-design flows.

## Modules

### `axi_gpio` — drop-in AXI GPIO

**File:** `rtl/periph/gpio/axi_gpio.sv`

- **AXI-Lite slave** with register map compatible with **Xilinx AXI GPIO**.
- Parameters: channel widths, dual channel, all-inputs/all-outputs, interrupt presence.
- Use when you want a **pure RTL** AXI GPIO without Xilinx core licensing in simulation.

### `axi_gpio_bridge` — simple bus → AXI-Lite

**File:** `rtl/periph/gpio/axi_gpio_bridge.sv`

- Bridges the SoC **simple memory-mapped** interface (`stb_i`, `adr_i`, `we_i`, `dat_i/o`, `ack_o`) to **AXI-Lite** signals.
- Address width default **9** bits (Xilinx GPIO decode space).

### `xilinx_gpio_wrapper` — Xilinx IP + bridge

**File:** `rtl/periph/gpio/xilinx_gpio_wrapper.sv`

- Instantiates **`axi_gpio_bridge`** and connects to **Xilinx AXI GPIO IP** ports in Vivado.
- Typical use: **`GPIO_EN = 0`**, **`XILINX_GPIO_EN = 1`** in the SoC wrapper so the internal `gpio` is disabled.

## Register map (summary)

Matches Xilinx documentation, e.g.:

| Offset | Register |
|--------|----------|
| `0x00` | GPIO_DATA |
| `0x04` | GPIO_TRI |
| `0x08` / `0x0C` | Second channel (if dual) |
| `0x11C` | GIER |
| `0x120` | IP_ISR |
| `0x128` | IP_IER |

See file headers in RTL for the authoritative map.

## Related

- [GPIO (native)](gpio.md)
- [Level wrapper](../wrapper/level_wrapper.md)
