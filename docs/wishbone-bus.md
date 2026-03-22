# Wishbone B4 Bus Architecture

## Overview

Level RISC-V SoC now supports Wishbone B4 pipelined bus interface for peripheral and memory interconnect.

## Bus Topology

```
                              ┌─────────────────┐
                              │   CPU Core      │
                              │  (memory.sv)    │
                              └────────┬────────┘
                                       │ iomem_req/res
                              ┌────────▼────────┐
                              │ memory_arbiter  │
                              │   (icache/      │
                              │    dcache arb)  │
                              └────────┬────────┘
                                       │ iomem_req/res
                              ┌────────▼────────┐
                              │ wb_master_bridge│
                              │ (iomem → WB B4) │
                              └────────┬────────┘
                                       │ wb_master_t / wb_slave_t
                              ┌────────▼────────┐
                              │ wb_interconnect │
                              │ (1-to-N switch) │
                              └───┬────┬────┬───┘
                                  │    │    │
            ┌─────────────────────┘    │    └─────────────────────┐
            │                          │                          │
   ┌────────▼────────┐        ┌────────▼────────┐        ┌────────▼────────┐
   │  wb_ram_slave   │        │ wb_clint_slave  │        │ wb_pbus_slave   │
   │  (0x8xxx_xxxx)  │        │ (0x3xxx_xxxx)   │        │ (0x2xxx_xxxx)   │
   └────────┬────────┘        └────────┬────────┘        └────────┬────────┘
            │                          │                          │
   ┌────────▼────────┐        ┌────────▼────────┐        ┌────────▼────────┐
   │   Main RAM      │        │ Timer Registers │        │   Peripherals   │
   │   (BRAM)        │        │ mtime/mtimecmp  │        │ UART/SPI/I2C/.. │
   └─────────────────┘        └─────────────────┘        └─────────────────┘
```

## Files

| File | Description |
|------|-------------|
| `rtl/pkg/level_param.sv` | Wishbone B4 type definitions (wb_master_t, wb_slave_t, etc.) |
| `rtl/core/mmu/wb_master_bridge.sv` | Converts iomem interface to Wishbone B4 master |
| `rtl/core/mmu/wb_interconnect.sv` | 1-to-N address-based switch/crossbar |
| `rtl/wrapper/wb_ram_slave.sv` | Wishbone slave wrapper for main RAM |
| `rtl/wrapper/wb_clint_slave.sv` | Wishbone CLINT (timer/software interrupt) |
| `rtl/wrapper/wb_pbus_slave.sv` | Wishbone peripheral bus gateway |

## Wishbone B4 Signals

### Master → Slave (wb_master_t)

| Signal | Width | Description |
|--------|-------|-------------|
| `adr` | 32 | Address |
| `dat` | 32 | Write data |
| `sel` | 4 | Byte select |
| `we` | 1 | Write enable |
| `stb` | 1 | Strobe (valid transfer) |
| `cyc` | 1 | Cycle (bus grant) |
| `cti` | 3 | Cycle type identifier |
| `bte` | 2 | Burst type extension |

### Slave → Master (wb_slave_t)

| Signal | Width | Description |
|--------|-------|-------------|
| `dat` | 32 | Read data |
| `ack` | 1 | Acknowledge |
| `err` | 1 | Error response |
| `rty` | 1 | Retry request |
| `stall` | 1 | Pipeline stall (B4) |

## Cycle Types (CTI)

| Value | Name | Description |
|-------|------|-------------|
| 000 | Classic | Single transfer |
| 001 | Const | Constant address burst |
| 010 | Incr | Incrementing address burst |
| 111 | EOB | End of burst |

## Burst Types (BTE)

| Value | Name | Description |
|-------|------|-------------|
| 00 | Linear | Linear burst |
| 01 | Wrap4 | 4-beat wrap burst |
| 10 | Wrap8 | 8-beat wrap burst |
| 11 | Wrap16 | 16-beat wrap burst |

## Memory Map

| Address Range | Slave | Description |
|---------------|-------|-------------|
| 0x8000_0000 - 0x8FFF_FFFF | RAM | Main memory (128KB-1MB) |
| 0x3000_0000 - 0x3FFF_FFFF | CLINT | Timer/Software interrupts |
| 0x2000_0000 - 0x2FFF_FFFF | PBUS | Peripherals |

### Peripheral Bus (0x2xxx_xxxx)

| Address Range | Peripheral |
|---------------|------------|
| 0x2000_0xxx | UART0 |
| 0x2000_1xxx | UART1 (reserved) |
| 0x2000_2xxx | SPI0 (reserved) |
| 0x2000_3xxx | I2C0 (reserved) |
| 0x2000_4xxx | GPIO (reserved) |
| 0x2000_5xxx | PWM (reserved) |
| 0x2000_6xxx | Timer (reserved) |
| 0x2000_7xxx | PLIC (reserved) |

## Usage Notes

### Single Transfer (Uncached)
For uncached peripheral access, the master bridge uses classic Wishbone cycles:
- CTI = 000 (Classic)
- Single `stb` pulse
- Wait for `ack`

### Burst Transfer (Cache Line)
For cache line fills/writebacks, 4-beat incrementing bursts are used:
- CTI = 010 (Incr) for first 3 beats
- CTI = 111 (EOB) for last beat
- BTE = 01 (Wrap4) for cache alignment
- 4 × 32-bit = 128-bit cache line

### Stall Handling
The Wishbone B4 pipelined interface uses `stall` for flow control:
- If `stall` is high, master must hold request
- Once `stall` goes low, request is accepted
- This allows zero-wait-state pipelining

## Integration Status

**Current**: iomem interface (internal)
**Planned**: Full Wishbone B4 integration

The Wishbone modules are designed but not yet integrated into the main wrapper.
To enable Wishbone, the `level_wrapper.sv` needs to be updated to instantiate:
1. `wb_master_bridge` between CPU and interconnect
2. `wb_interconnect` for address decode and routing
3. Individual slave wrappers for each peripheral
