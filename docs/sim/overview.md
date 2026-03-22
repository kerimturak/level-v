# Simulation (sim/) - Technical Documentation

## Contents

1. [Overview](#overview)
2. [Testbenches (tb/)](#testbenches-tb)
3. [DO Scripts (do/)](#do-scripts-do)
4. [Test Programs (test/)](#test-programs-test)

---

## Overview

### Directory Layout

```
sim/
├── README.md              # Simulation guide
├── tb/                    # Testbench'ler
│   ├── tb_wrapper.sv      # SystemVerilog top-level testbench
│   ├── tb_wrapper.cpp     # Verilator C++ testbench
│   ├── mmu/               # MMU unit testleri
│   └── stage01_fetch/     # Fetch stage testleri
├── do/                    # ModelSim/Questa DO scripts
│   ├── pipeline.do        # Full pipeline debug waveform
│   ├── questa.do          # Questa simulation script
│   ├── minimal.do         # Minimal debug view
│   ├── cache_debug.do     # Cache debugging
│   ├── hazard_debug.do    # Hazard unit debugging
│   ├── branch_debug.do    # Branch predictor debugging
│   ├── exception_debug.do # Exception handling debug
│   └── memory_debug.do    # Memory system debugging
└── test/                  # Test programs and manifests
    ├── riscv_test_list.flist     # ISA test listesi
    ├── arch_test.flist           # Architecture test listesi
    ├── imperas_test_list.flist   # Imperas test listesi
    ├── custom/                   # Custom C testleri
    │   ├── uart_hello_test.c
    │   ├── gpio_test.c
    │   └── ...
    └── coremark/                 # CoreMark benchmark
```

### Simulation Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                      SIMULATION FLOW                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐  │
│  │  Test    │    │  ELF →   │    │Testbench │    │  Results │  │
│  │ Program  │───▶│  MEM     │───▶│ Execute  │───▶│ Analysis │  │
│  └──────────┘    └──────────┘    └──────────┘    └──────────┘  │
│       │                               │                          │
│       │         ┌─────────────────────┼─────────────────────┐   │
│       │         │                     │                     │   │
│       ▼         ▼                     ▼                     ▼   │
│  ┌──────────┐ ┌──────────┐      ┌──────────┐          ┌──────────┐
│  │ C/ASM    │ │Verilator │      │ Waveform │          │ Pass/Fail│
│  │ Source   │ │tb_wrapper│      │   .vcd   │          │  Report  │
│  └──────────┘ │   .cpp   │      │   .fst   │          └──────────┘
│               └──────────┘      │   .wlf   │                     │
│                     │           └──────────┘                     │
│                     ▼                                            │
│               ┌──────────┐                                       │
│               │ModelSim  │                                       │
│               │tb_wrapper│                                       │
│               │   .sv    │                                       │
│               └──────────┘                                       │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Testbenches (tb/)

### tb_wrapper.sv - SystemVerilog Testbench

**Dosya:** `sim/tb/tb_wrapper.sv`

Main testbench for ModelSim/Questa.

#### Code Structure

```systemverilog
`timescale 1ns / 1ps
module tb_wrapper;
  // ═══════════════════════════════════════════════════════════════
  // Signal Declarations
  // ═══════════════════════════════════════════════════════════════
  logic        clk_i = 0;
  logic        rst_ni = 0;
  logic        program_rx_i = 1;
  logic        uart_rx_i = 1;
  logic        prog_mode_led_o;
  logic        uart_tx_o;
  
  // SPI Interface
  logic        spi0_sclk_o;
  logic        spi0_mosi_o;
  logic        spi0_miso_i;
  logic [ 3:0] spi0_ss_o;
  
  // I2C Interface
  wire         i2c0_sda_io;
  wire         i2c0_scl_io;
  
  // GPIO Interface
  logic [31:0] gpio_i;
  logic [31:0] gpio_o;
  logic [31:0] gpio_oe_o;
  
  // External Interrupts
  logic [ 7:0] ext_irq_i;
  logic [ 3:0] status_led_o;

  // ═══════════════════════════════════════════════════════════════
  // DUT Instantiation
  // ═══════════════════════════════════════════════════════════════
  level_wrapper level_wrapper (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .program_rx_i   (program_rx_i),
      .prog_mode_led_o(prog_mode_led_o),
      .uart_tx_o      (uart_tx_o),
      .uart_rx_i      (uart_rx_i),
      .spi0_sclk_o    (spi0_sclk_o),
      .spi0_mosi_o    (spi0_mosi_o),
      .spi0_miso_i    (spi0_miso_i),
      .spi0_ss_o      (spi0_ss_o),
      .i2c0_sda_io    (i2c0_sda_io),
      .i2c0_scl_io    (i2c0_scl_io),
      .gpio_i         (gpio_i),
      .gpio_o         (gpio_o),
      .gpio_oe_o      (gpio_oe_o),
      .ext_irq_i      (ext_irq_i),
      .status_led_o   (status_led_o)
  );

  // ═══════════════════════════════════════════════════════════════
  // Peripheral Loopbacks
  // ═══════════════════════════════════════════════════════════════
  // SPI Loopback: MOSI → MISO
  assign spi0_miso_i = spi0_mosi_o;

  // ═══════════════════════════════════════════════════════════════
  // Reset & Clock Generation
  // ═══════════════════════════════════════════════════════════════
  initial begin
    rst_ni       <= 0;
    program_rx_i <= 1;
    uart_rx_i    <= 1;
    #10;
    rst_ni <= 1;
  end

  // 100 MHz clock (10ns period)
  always #5 clk_i = !clk_i;

endmodule
```

#### Port Descriptions

| Port | Direction | Width | Description |
|------|-----|----------|----------|
| `clk_i` | input | 1 | System clock |
| `rst_ni` | input | 1 | Active-low reset |
| `program_rx_i` | input | 1 | Programming UART RX |
| `uart_rx_i` | input | 1 | Console UART RX |
| `uart_tx_o` | output | 1 | Console UART TX |
| `spi0_*` | mixed | - | SPI interface |
| `i2c0_*` | inout | - | I2C interface |
| `gpio_*` | mixed | 32 | GPIO interface |
| `ext_irq_i` | input | 8 | External interrupts |
| `status_led_o` | output | 4 | Status LEDs |

---

### tb_wrapper.cpp - Verilator C++ Testbench

**Dosya:** `sim/tb/tb_wrapper.cpp`

C++ testbench driver for Verilator.

#### Features

- **Trace support**: FST or VCD format
- **Coverage**: Line/toggle coverage
- **Progress Reporting**: progress in 10% steps
- **Configurable**: Command-line arguments

#### Code Structure

```cpp
#include "Vlevel_wrapper.h"
#include "verilated.h"

#if defined(VM_TRACE_FST)
#include "verilated_fst_c.h"
#elif defined(VM_TRACE)
#include "verilated_vcd_c.h"
#endif

#if VM_COVERAGE
#include "verilated_cov.h"
#endif

static vluint64_t main_time = 0;
double sc_time_stamp() { return main_time; }

int main(int argc, char **argv) {
    // Create Verilator context
    VerilatedContext* contextp = new VerilatedContext;
    contextp->commandArgs(argc, argv);

    // Enable tracing
#if defined(VM_TRACE_FST) || defined(VM_TRACE)
    Verilated::traceEverOn(true);
#endif

    // Instantiate DUT
    Vlevel_wrapper* top = new Vlevel_wrapper{contextp};

    // Setup trace file
#if defined(VM_TRACE_FST)
    VerilatedFstC* tfp = new VerilatedFstC;
    top->trace(tfp, 99);
    const char* dump_file = "waveform.fst";
#elif defined(VM_TRACE)
    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    const char* dump_file = "waveform.vcd";
#endif

    // Parse dump file argument
#if defined(VM_TRACE_FST) || defined(VM_TRACE)
    for (int i = 1; i < argc; ++i) {
        if (strncmp(argv[i], "+DUMP_FILE=", 11) == 0)
            dump_file = argv[i] + 11;
    }
    tfp->open(dump_file);
#endif

    // Initialize signals
    top->clk_i     = 0;
    top->rst_ni    = 0;
    top->uart_rx_i = 1;

    // Reset phase (10 cycles)
    for (int i = 0; i < 10; ++i) {
        top->clk_i = 0; top->eval();
#if defined(VM_TRACE_FST) || defined(VM_TRACE)
        tfp->dump(main_time++);
#endif
        top->clk_i = 1; top->eval();
#if defined(VM_TRACE_FST) || defined(VM_TRACE)
        tfp->dump(main_time++);
#endif
    }

    top->rst_ni = 1;

    // Get max cycles from command line
    uint64_t MAX_CYCLES = (argc > 1) ? 
        std::strtoull(argv[1], nullptr, 10) : 100000ULL;
    
    uint64_t progress_interval = (MAX_CYCLES > 10000) ? 
        (MAX_CYCLES / 10) : 1000;

    // Main simulation loop
    while (!contextp->gotFinish() && (main_time / 2) < MAX_CYCLES) {
        // Progress reporting
        if (((main_time / 2) % progress_interval) == 0 && (main_time / 2) > 0) {
            std::cout << "[CYCLE] " << (main_time / 2) << "/" 
                      << MAX_CYCLES << std::endl;
        }
        
        // Clock toggle
        top->clk_i = 0; top->eval();
#if defined(VM_TRACE_FST) || defined(VM_TRACE)
        tfp->dump(main_time++);
#endif
        top->clk_i = 1; top->eval();
#if defined(VM_TRACE_FST) || defined(VM_TRACE)
        tfp->dump(main_time++);
#endif
    }

    // Cleanup
#if defined(VM_TRACE_FST) || defined(VM_TRACE)
    tfp->close();
    delete tfp;
#endif

    top->final();

#if VM_COVERAGE
    const char* coverage_file = "coverage.dat";
    VerilatedCov::write(coverage_file);
#endif

    std::cout << "[INFO] Simulation finished after " 
              << (main_time / 2) << " cycles." << std::endl;

    delete top;
    delete contextp;
    return 0;
}
```

#### Command Line Arguments

| Argument | Format | Description |
|----------|--------|----------|
| `<cycles>` | integer | Maximum simulation cycles |
| `+DUMP_FILE=` | path | Waveform output file |
| `+COVERAGE_FILE=` | path | Coverage output file |

---

## DO Scripts (do/)

### pipeline.do - Full Pipeline Debug

**File:** `sim/do/pipeline.do`

Full pipeline debug waveform script.

#### Features

```tcl
##################################################################################
#                     Level RISC-V — Advanced Debug Waveform                     #
##################################################################################
# Features:
#   - Hierarchical grouping by pipeline stage
#   - Color-coded signal categories
#   - Automatic radix selection (hex/decimal/binary)
#   - Collapsible groups for easy navigation
#   - Critical path signals highlighted
#   - Exception/Interrupt debugging section
#   - Performance counter monitoring
#   - Memory transaction tracking
##################################################################################
```

#### Hierarchy Paths

```tcl
set TB        "sim:/tb_wrapper"
set WRAPPER   "$TB/level_wrapper"
set SOC       "$WRAPPER/i_soc"
set FETCH     "$SOC/i_fetch"
set DECODE    "$SOC/i_decode"
set EXECUTE   "$SOC/i_execution"
set MEMORY    "$SOC/i_memory"
set WRITEBACK "$SOC/i_writeback"
set HAZARD    "$SOC/i_hazard_unit"
set ARBITER   "$SOC/i_memory_arbiter"
```

#### Signal Groups

| Group | Color | Contents |
|-------|------|--------|
| ⏱️ CLK/RST | Gold/Orange | Clock and reset |
| 🔄 PIPELINE | Gradient | PC and instruction per stage |
| ⚠️ STALL/FLUSH | Red/Orange | Stall and flush signals |
| 🎯 FETCH | Cyan | Fetch stage signals |
| 📖 DECODE | Green | Decode stage signals |
| ⚡ EXECUTE | Yellow | ALU and execution |
| 💾 MEMORY | Magenta | Load/store operations |
| ✅ WRITEBACK | Blue | Register writeback |
| 🔀 HAZARD | Red | Forwarding and hazard |
| 🌿 BRANCH | Cyan | Branch predictor |
| 💥 EXCEPTION | Red | Exception handling |

### Other DO Scripts

| Script | Description |
|--------|----------|
| `questa.do` | Questa simulation runner |
| `minimal.do` | Minimal debug view |
| `cache_debug.do` | Cache hit/miss debugging |
| `hazard_debug.do` | Hazard unit detailed view |
| `branch_debug.do` | Branch predictor analysis |
| `exception_debug.do` | Exception/interrupt flow |
| `memory_debug.do` | Memory transaction debug |

---

## Test Programs (test/)

### Test Lists

| File | Contents |
|-------|--------|
| `riscv_test_list.flist` | riscv-tests ISA tests |
| `arch_test.flist` | riscv-arch-test compliance |
| `imperas_test_list.flist` | Imperas extended tests |
| `custom_tests.flist` | Custom C tests |
| `all_tests.flist` | All tests (combined) |
| `branch_test.flist` | Branch predictor tests |
| `exception_test.flist` | Exception tests |
| `machine_csr_test.flist` | CSR tests |

### Custom Test Programs (custom/)

#### File List

| File | Description |
|-------|----------|
| `startup.s` | Assembly startup code |
| `level_test.h` | Common test header |
| `uart_hello_test.c` | UART basic test |
| `gpio_test.c` | GPIO functionality |
| `timer_test.c` | Timer peripheral |
| `spi_test.c` | SPI controller |
| `i2c_test.c` | I2C controller |
| `plic_test.c` | Interrupt controller |
| `pwm_test.c` | PWM output |
| `dma_test.c` | DMA controller |
| `wdt_test.c` | Watchdog timer |
| `vga_test.c` | VGA controller |
| `clint_test.c` | Core-local interruptor |
| `exception_test.c` | Exception handling |
| `csr_test.c` | CSR read/write |
| `memory_test.c` | Memory operations |
| `cache_test.c` | Cache behavior |
| `branch_test.c` | Branch operations |
| `arithmetic_test.c` | ALU operations |
| `fibonacci_test.c` | Fibonacci benchmark |
| `loop_test.c` | Loop performance |
| `interrupt_test.c` | Interrupt handling |

#### startup.s

```riscv
.section .text._start
.globl _start

_start:
    /* Set stack pointer */
    la sp, __stack_end
    
    /* Jump to main */
    jal ra, main
    
    /* Infinite loop on return */
    j _start

.section .bss
.align 4
__stack_start:
    .space 0x4000    # 16KB stack
__stack_end:
```

#### uart_hello_test.c Example

```c
/**
 * UART Hello Test - Level-V RV32IMC_Zicsr
 */

#include <stdint.h>

/* Hardware Definitions */
#define CPU_CLK          50000000   /* 50 MHz */
#define BAUD_RATE        115200

/* UART MMIO Map */
#define UART_CTRL        (*(volatile uint32_t*)0x20000000)
#define UART_STATUS      (*(volatile uint32_t*)0x20000004)
#define UART_RDATA       (*(volatile uint32_t*)0x20000008)
#define UART_WDATA       (*(volatile uint32_t*)0x2000000c)

/* Status Register Bits */
#define UART_STATUS_TX_FULL   0x1
#define UART_STATUS_RX_FULL   0x2

/* Control Register Bits */
#define UART_CTRL_TX_EN   0x1
#define UART_CTRL_RX_EN   0x2

void uart_init(void) {
    uint32_t baud_div = CPU_CLK / BAUD_RATE;
    UART_CTRL = (baud_div << 16) | UART_CTRL_TX_EN | UART_CTRL_RX_EN;
}

void uart_putc(char c) {
    while (UART_STATUS & UART_STATUS_TX_FULL);
    UART_WDATA = (uint32_t)c;
}

void uart_puts(const char *s) {
    while (*s) {
        if (*s == '\n') uart_putc('\r');
        uart_putc(*s++);
    }
}

int main(void) {
    uart_init();
    uart_puts("Hello from Level!\n");
    while (1);
    return 0;
}
```

---

## Usage Examples

### Simulation with Verilator

```bash
# Build
make verilate

# Run ISA test
make run T=rv32ui-p-add

# Run with trace
make run T=rv32ui-p-add TRACE=1

# Run CoreMark
make run_coremark SIM_FAST=1 SIM_UART_MONITOR=1
```

### Simulation with ModelSim

```bash
# Compile
make compile

# Batch simulation
make simulate TEST_NAME=rv32ui-p-add

# Questa/ModelSim GUI
make simulate TEST_NAME=rv32ui-p-add GUI=1
```

### Custom Test Build

```bash
# Build custom test
./script/shell/build_level_custom_c_test.sh uart_hello_test

# Run custom test
make run T=uart_hello_test TEST_TYPE=custom
```

---

## Summary

The simulation tree:

1. **tb/**: SystemVerilog and C++ testbenches
2. **do/**: ModelSim/Questa debug waveform scripts
3. **test/**: Test programs and lists
4. **Dual simulator**: Verilator and ModelSim support
5. **Comprehensive Debug**: Color-coded, grouped waveforms
6. **Custom Tests**: Peripheral test suite
