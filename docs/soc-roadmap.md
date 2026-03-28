# Level SoC Development Roadmap

This document defines the components needed for the Level RISC-V processor to become a full SoC, the current state, and future goals.

---

## 📊 Current Status Summary

### ✅ Completed Components

| Component | Path | Description |
|-----------|------|-------------|
| CPU Core | `rtl/core/` | 5-stage pipeline, RV32IMC |
| I-Cache | `rtl/core/mmu/cache.sv` | 32KB, 8-way set-associative |
| D-Cache | `rtl/core/mmu/cache.sv` | 32KB, 8-way set-associative |
| Branch Predictor | `rtl/core/stage01_fetch/` | GShare + BTB + RAS + Loop |
| CLINT | `rtl/core/cpu.sv` | Timer interrupt (mtime/mtimecmp) |
| UART | `rtl/periph/uart/` | TX/RX with FIFO |
| SPI Master | `rtl/periph/spi/` | 8-bit, configurable clock |
| I2C Master | `rtl/periph/i2c/` | Standard/Fast/Fast+ mode |
| PMA | `rtl/core/pmp_pma/pma.sv` | Physical Memory Attributes |
| CSR | `rtl/core/stage03_execute/cs_reg_file.sv` | M-mode CSR set |

---

## 🎯 Target Components

### Priority 1: Critical (Basic SoC Functionality)

#### 1.1 GPIO Controller
```
Path      : rtl/periph/gpio/gpio.sv
Priority  : 🔴 HIGH
Status    : ❌ Missing
```

**Description:**
GPIO (General Purpose Input/Output) is the basic block that lets a microcontroller talk to the outside world. It is required for fundamental I/O such as driving LEDs, reading buttons, and attaching sensors.

**Features:**
| Feature | Description |
|---------|-------------|
| Port width | 32-bit (parametric) |
| Direction control | Per-pin input/output selection |
| Output register | Holds output values |
| Input register | Samples input values |
| Pull-up/pull-down | Internal pull resistor per pin |
| Interrupt on change | Interrupt on pin change |
| Edge detection | Rising/falling/both edge selection |
| Atomic set/clear | Bit-wise set/clear/toggle |

**Register map:**
| Offset | Name | R/W | Description |
|--------|------|-----|----------|
| 0x00 | GPIO_DIR | RW | Direction (0=input, 1=output) |
| 0x04 | GPIO_OUT | RW | Output data register |
| 0x08 | GPIO_IN | R | Input data register |
| 0x0C | GPIO_SET | W | Atomic bit set (write 1 to set) |
| 0x10 | GPIO_CLR | W | Atomic bit clear (write 1 to clear) |
| 0x14 | GPIO_TGL | W | Atomic bit toggle |
| 0x18 | GPIO_PUE | RW | Pull-up enable |
| 0x1C | GPIO_PDE | RW | Pull-down enable |
| 0x20 | GPIO_IE | RW | Interrupt enable |
| 0x24 | GPIO_IS | R/W1C | Interrupt status (write 1 to clear) |
| 0x28 | GPIO_IBE | RW | Interrupt both edges |
| 0x2C | GPIO_IEV | RW | Interrupt event (0=falling, 1=rising) |

---

#### 1.2 PLIC (Platform-Level Interrupt Controller)
```
Path      : rtl/periph/plic/plic.sv
Priority  : 🔴 HIGH
Status    : ❌ Missing
```

**Description:**
The PLIC is the external interrupt controller defined in the RISC-V specification. It arbitrates multiple interrupt sources and presents them to the CPU by priority. The existing CLINT only provides timer and software interrupts; a PLIC is needed for external devices (UART RX, GPIO, SPI complete, etc.).

**Features:**
| Feature | Description |
|---------|-------------|
| Interrupt sources | 32 (parametric, max 1024) |
| Priority levels | 8 levels (0=disabled, 7=highest) |
| Pending register | Pending bit per source |
| Enable register | Enable bit per source |
| Threshold | Minimum priority the CPU accepts |
| Claim/complete | Interrupt acknowledge mechanism |

**Register map (base: 0x2000_7000):**
| Offset | Name | R/W | Description |
|--------|------|-----|----------|
| 0x000-0x07C | PRIORITY[0:31] | RW | Interrupt priority (per source) |
| 0x080 | PENDING | R | Pending interrupts bitmap |
| 0x100 | ENABLE | RW | Interrupt enable bitmap |
| 0x200 | THRESHOLD | RW | Priority threshold |
| 0x204 | CLAIM | R | Claim highest pending interrupt |
| 0x204 | COMPLETE | W | Complete interrupt handling |

**Interrupt connections:**
```
Source 0  : Reserved (always 0)
Source 1  : UART0 RX (receive complete)
Source 2  : UART0 TX (transmit empty)
Source 3  : UART1 RX
Source 4  : UART1 TX
Source 5  : SPI0 Complete
Source 6  : I2C0 Complete
Source 7  : I2C0 Arbitration Lost
Source 8-15 : GPIO[0-7] interrupts
Source 16-23 : GPIO[8-15] interrupts
Source 24-31 : External interrupts
```

---

#### 1.3 General Purpose Timer
```
Path      : rtl/periph/timer/gptimer.sv
Priority  : 🔴 HIGH
Status    : ❌ Missing
```

**Description:**
CLINT `mtime` is used as the system timer only. User applications need separate, configurable timers—for PWM output, periodic interrupts, time measurement, and similar functions.

**Features:**
| Feature | Description |
|---------|-------------|
| Timer count | 4 (parametric) |
| Counter width | 32-bit |
| Prescaler | 16-bit (clock divider) |
| Modes | One-shot, continuous, PWM |
| Compare channels | 2 per timer |
| Capture channels | 1 per timer |
| Interrupt | Overflow, compare match, capture |

**Register map (per timer, 0x40 spacing):**
| Offset | Name | R/W | Description |
|--------|------|-----|----------|
| 0x00 | TIMx_CTRL | RW | Control register |
| 0x04 | TIMx_CNT | RW | Counter value |
| 0x08 | TIMx_PSC | RW | Prescaler |
| 0x0C | TIMx_ARR | RW | Auto-reload value |
| 0x10 | TIMx_CCR0 | RW | Compare/Capture 0 |
| 0x14 | TIMx_CCR1 | RW | Compare/Capture 1 |
| 0x18 | TIMx_SR | R/W1C | Status register |
| 0x1C | TIMx_IER | RW | Interrupt enable |

**CTRL Register Bits:**
```
[0]     : EN      - Timer enable
[1]     : DIR     - Count direction (0=up, 1=down)
[2]     : OPM     - One-pulse mode
[4:3]   : CMS     - Center-aligned mode select
[7:5]   : Reserved
[9:8]   : CC0M    - Capture/Compare 0 mode
[11:10] : CC1M    - Capture/Compare 1 mode
[31:12] : Reserved
```

---

### Priority 2: Important (Advanced Features)

#### 2.1 PWM Controller
```
Path      : rtl/periph/pwm/pwm.sv
Priority  : 🟡 MEDIUM
Status    : ❌ Missing
```

**Description:**
PWM (pulse width modulation) is used when applications need an analog-like output: LED brightness, motor speed, servo control, and similar. A GP timer can provide simple PWM, but a dedicated PWM block offers more features.

**Features:**
| Feature | Description |
|---------|-------------|
| Channel count | 8 (parametric) |
| Resolution | 16-bit |
| Dead-time | For complementary outputs |
| Phase shift | Phase difference between channels |
| Sync mode | Start all channels in sync |

**Register map:**
| Offset | Name | R/W | Description |
|--------|------|-----|----------|
| 0x00 | PWM_CTRL | RW | Global control |
| 0x04 | PWM_PERIOD | RW | PWM period (all channels) |
| 0x08 | PWM_EN | RW | Channel enable bitmap |
| 0x0C | PWM_POL | RW | Output polarity |
| 0x10-0x2C | PWM_DUTY[0-7] | RW | Duty cycle per channel |
| 0x30 | PWM_DEADTIME | RW | Dead-time configuration |

---

#### 2.2 Watchdog Timer
```
Path      : rtl/periph/wdt/watchdog.sv
Priority  : 🟡 MEDIUM
Status    : ❌ Missing
```

**Description:**
A watchdog timer resets the system automatically if it locks up. Software must periodically “kick” the watchdog; otherwise the system resets.

**Features:**
| Feature | Description |
|---------|-------------|
| Counter | 32-bit |
| Prescaler | 8-bit |
| Window mode | Protection against early kick |
| Lock | Configuration lock |
| Reset/interrupt | Reset or interrupt on timeout |

**Register map:**
| Offset | Name | R/W | Description |
|--------|------|-----|----------|
| 0x00 | WDT_CTRL | RW | Control (enable, mode) |
| 0x04 | WDT_LOAD | RW | Reload value |
| 0x08 | WDT_COUNT | R | Current count |
| 0x0C | WDT_WINDOW | RW | Window start (for window mode) |
| 0x10 | WDT_KICK | W | Kick register (write any value) |
| 0x14 | WDT_LOCK | RW | Lock configuration |

**Security:**
- Writing `WDT_LOCK` locks configuration
- Unlock magic sequence: `0x1ACCE551`

---

#### 2.3 DMA Controller
```
Path      : rtl/periph/dma/dma_controller.sv
Priority  : 🟡 MEDIUM
Status    : ❌ Missing
```

**Description:**
DMA (direct memory access) moves data between memory and peripherals without involving the CPU, reducing CPU load for large transfers.

**Features:**
| Feature | Description |
|---------|-------------|
| Channel count | 4 (parametric) |
| Transfer types | M2M, M2P, P2M |
| Burst size | 1, 4, 8, 16 words |
| Address mode | Fixed, increment, decrement |
| Circular mode | Auto reload |
| Priority | Per-channel priority |
| Linked list | Scatter-gather support |

**Register map (per channel, 0x20 spacing):**
| Offset | Name | R/W | Description |
|--------|------|-----|----------|
| 0x00 | DMA_CTRL | RW | Channel control |
| 0x04 | DMA_SRC | RW | Source address |
| 0x08 | DMA_DST | RW | Destination address |
| 0x0C | DMA_CNT | RW | Transfer count |
| 0x10 | DMA_CFG | RW | Configuration |
| 0x14 | DMA_LLI | RW | Linked list item pointer |
| 0x18 | DMA_SR | R | Status |

**Peripheral connections:**
```
Request 0 : UART0 TX
Request 1 : UART0 RX
Request 2 : SPI0 TX
Request 3 : SPI0 RX
Request 4 : I2C0 TX
Request 5 : I2C0 RX
Request 6-7 : Reserved
```

---

#### 2.4 System Controller
```
Path      : rtl/periph/sysctrl/sysctrl.sv
Priority  : 🟡 MEDIUM
Status    : ❌ Missing
```

**Description:**
Provides system-wide clock, reset, and power management.

**Features:**
| Feature | Description |
|---------|-------------|
| Clock gating | Per-peripheral clock on/off |
| Reset control | Per-peripheral soft reset |
| Power domains | Low-power mode management |
| Chip ID | Unique chip identifier |
| Boot config | Boot source selection |

**Register map:**
| Offset | Name | R/W | Description |
|--------|------|-----|----------|
| 0x00 | SYS_CHIPID | R | Chip ID (read-only) |
| 0x04 | SYS_CLKEN | RW | Clock enable bitmap |
| 0x08 | SYS_SRST | RW | Soft reset (write 1 to reset) |
| 0x0C | SYS_BOOTCFG | R | Boot configuration pins |
| 0x10 | SYS_PWRCTRL | RW | Power control |
| 0x14 | SYS_RSTSTAT | R/W1C | Reset status (reason) |

---

### Priority 3: Bonus (Advanced Features)

#### 3.1 Debug Module (JTAG)
```
Path      : rtl/debug/dm_top.sv
Priority  : 🟢 LOW
Status    : ❌ Missing
```

**Description:**
Debug module compliant with the RISC-V Debug Specification: JTAG or cJTAG connection, breakpoints, single-step, register read/write.

---

#### 3.2 RTC (Real-Time Clock)
```
Path      : rtl/periph/rtc/rtc.sv
Priority  : 🟢 LOW
Status    : ❌ Missing
```

**Description:**
Battery-backed real-time clock: date/time keeping and alarms.

---

#### 3.3 CRC Accelerator
```
Path      : rtl/periph/crc/crc_engine.sv
Priority  : 🟢 LOW
Status    : ❌ Missing
```

**Description:**
Hardware CRC: CRC-8, CRC-16, CRC-32.

---

#### 3.4 External Memory Controller
```
Path      : rtl/periph/emc/emc.sv
Priority  : 🟢 LOW
Status    : ❌ Missing
```

**Description:**
Controller for external SRAM, SDRAM, or DDR memory.

---

## 🗺️ Memory Map (Target)

```
0x0000_0000 - 0x0FFF_FFFF : Debug Region (256MB)
    0x0000_0000 : Debug Module

0x1000_0000 - 0x1FFF_FFFF : Boot ROM (256MB reserved, 4KB used)
    0x1000_0000 : Boot ROM Start

0x2000_0000 - 0x2FFF_FFFF : Peripheral Region (256MB)
    0x2000_0000 : UART0          (4KB)
    0x2000_1000 : UART1          (4KB)
    0x2000_2000 : SPI0           (4KB)
    0x2000_3000 : I2C0           (4KB)
    0x2000_4000 : GPIO           (4KB)  ← NEW
    0x2000_5000 : PWM            (4KB)  ← NEW
    0x2000_6000 : Timer0-3       (4KB)  ← NEW
    0x2000_7000 : PLIC           (4KB)  ← NEW
    0x2000_8000 : Watchdog       (4KB)  ← NEW
    0x2000_9000 : DMA            (4KB)  ← NEW
    0x2000_A000 : System Ctrl    (4KB)  ← NEW
    0x2000_B000 : RTC            (4KB)  ← NEW
    0x2000_C000 : CRC            (4KB)  ← NEW
    0x2000_D000 - 0x2000_FFFF : Reserved

0x3000_0000 - 0x3FFF_FFFF : CLINT (256MB reserved)
    0x3000_0000 : MSIP
    0x3000_4000 : MTIMECMP
    0x3000_BFF8 : MTIME

0x4000_0000 - 0x7FFF_FFFF : External Memory (1GB)
    0x4000_0000 : QSPI Flash / External RAM

0x8000_0000 - 0xFFFF_FFFF : Main RAM (2GB)
    0x8000_0000 : RAM Start (Reset Vector)
```

---

## 📈 Implementation Order

### Phase 1: Basic I/O (1–2 weeks)
1. ✅ GPIO Controller
2. ✅ PLIC integration
3. ✅ Add interrupts to existing peripherals

### Phase 2: Timing (1 week)
4. ✅ General Purpose Timer
5. ✅ PWM (may be combined with timer)
6. ✅ Watchdog Timer

### Phase 3: System (1–2 weeks)
7. ✅ System Controller
8. ✅ DMA Controller

### Phase 4: Advanced (optional)
9. Debug Module
10. RTC
11. CRC Accelerator
12. External Memory Controller

---

## 🧰 Software, peripherals, and RTOS (community reference)

Level-v already has a richer ISA (**RV32IMC**), caches, and a Wishbone SoC than many teaching cores. A useful **product-style goal** is still: **run a real RTOS** and **reuseable C drivers** against your memory map—similar in spirit to [AngeloJacobo/RISC-V](https://github.com/AngeloJacobo/RISC-V) (MIT-licensed Verilog **RV32I + Zicsr**, Harvard-style bus split, **FreeRTOS**, `test/` regression script, and a small **peripheral library**: UART, I²C, GPIO, CLINT, LCD/sensor demos).

### What is worth borrowing (ideas, not RTL duplication)

| From that project | Application to Level-v |
|-------------------|-------------------------|
| **`test.sh`-style automation** | One entrypoint: toolchain check → compile bare-metal/FreeRTOS → run ISA or sim → optional FPGA bitstream (you already have `make`/`script/`; align *documentation* for “RTOS developer path”). |
| **FreeRTOS port package** | `FreeRTOSConfig.h`, `freertos_risc_v_chip_specific_extensions.h`, stack/interrupt ABI—**retarget** to Level-v’s **CLINT + PLIC** base addresses and trap vector (their core is simpler: no **C** extension, different memory map). |
| **Thin C HAL (`rv32i.h`-style)** | A **Level BSP** header: register offsets for *your* UART/GPIO/SPI/I²C/CLINT/PLIC; keeps app code portable across revs. |
| **End-to-end demo** | Their “Smart Garden” style app proves **RTOS + drivers + UART**; equivalent here could be a **small sensor / CLI demo** on Verilator or FPGA. |
| **Formal flow (`*.sby`)** | Same *discipline* (SymbiYosys) you may already use; compare property scope as a checklist, not a code merge. |

### Explicit goals (add to project backlog)

- [ ] **Document a stable “application memory map”** (flash/RAM/mmio) for software porters.  
- [ ] **FreeRTOS (or Zephyr later)** on Level-v: timer tick from **mtime/mtimecmp**, context switch with correct **FPU-less** ABI, peripheral ISRs via **PLIC**.  
- [ ] **Minimal driver suite** in `env/` or `sw/`: UART console, GPIO LED/button, one **blocking** I²C/SPI sample—enough to mirror Angelo’s library *coverage*, not necessarily the same API names.  
- [ ] **CI or script** that builds a **RTOS smoke binary** and runs it in simulation (even if UART output is scoreboard-only).  

### Differences to remember

- Their core is **Verilog + RV32I** (no **M/C**), **no branch predictor**; Level-v is **SystemVerilog**, **Wishbone**, caches, **BP**—**higher performance**, more to verify when enabling multi-IRQ RTOS.  
- **Harvard** `rv32i_soc` split buses vs your **unified SoC** path: linker scripts and DMA visibility differ; BSP docs must match **your** loader.  

---

## 📋 Checklist

- [ ] **GPIO**
  - [ ] Basic I/O (direction, read, write)
  - [ ] Atomic operations (set, clear, toggle)
  - [ ] Pull-up/pull-down
  - [ ] Interrupt on change
  - [ ] PLIC integration

- [ ] **PLIC**
  - [ ] Priority registers
  - [ ] Pending/Enable registers
  - [ ] Claim/Complete
  - [ ] Threshold
  - [ ] CPU interrupt output

- [ ] **Timer**
  - [ ] Counter, prescaler
  - [ ] Compare match
  - [ ] PWM output
  - [ ] Input capture
  - [ ] Interrupt generation

- [ ] **Watchdog**
  - [ ] Timeout reset
  - [ ] Window mode
  - [ ] Lock mechanism

- [ ] **DMA**
  - [ ] Basic M2M transfer
  - [ ] Peripheral integration
  - [ ] Circular mode
  - [ ] Linked list

- [ ] **System Controller**
  - [ ] Clock gating
  - [ ] Soft reset
  - [ ] Chip ID

---

## 🔗 References

1. [AngeloJacobo/RISC-V](https://github.com/AngeloJacobo/RISC-V) — Verilog RV32I+Zicsr, FreeRTOS, peripheral C library, regression/FPGA flow (ideas for BSP + RTOS goals above)
2. [RISC-V Privileged Specification](https://riscv.org/specifications/privileged-isa/)
3. [SiFive FE310 Manual](https://sifive.cdn.prismic.io/sifive/4faf3e34-4a42-4c2f-be9e-c77baa4928c7_fe310-g002-manual-v1p5.pdf)
4. [RISC-V PLIC Specification](https://github.com/riscv/riscv-plic-spec)
5. [RISC-V Debug Specification](https://riscv.org/specifications/debug-specification/)

---

*Last updated: 2026-03-28*  
*Version: 1.0*
