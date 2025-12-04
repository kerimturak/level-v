# Copilot Instructions for CERES RISC-V Project

## Project Overview

This is **CERES RISC-V** - a lightweight, modular 32-bit RISC-V processor core implementing the **RV32IMC** instruction set with CSR and FENCE support. The project is designed for learning, experimentation, and FPGA deployment.

## Technology Stack

- **Hardware Description Language**: SystemVerilog (IEEE 1800-2017)
- **Simulation Tools**: Verilator (primary), ModelSim, Icarus Verilog
- **Synthesis**: Yosys
- **Toolchain**: riscv32-unknown-elf-gcc
- **Scripting**: Python 3, Bash/Zsh, Make
- **Formal Verification**: riscv-formal

---

## Project Structure

```
rtl/                    # RTL source files
├── core/               # Processor core modules
│   ├── stage01_fetch/  # Instruction Fetch stage
│   ├── stage02_decode/ # Decode stage
│   ├── stage03_execute/# Execute stage (ALU, MUL/DIV)
│   │   ├── alu.sv
│   │   ├── execution.sv
│   │   ├── cs_reg_file.sv
│   │   └── mul_div/
│   ├── stage04_memory/ # Memory access stage
│   ├── stage05_writeback/ # Write-back stage
│   ├── mmu/            # Memory Management Unit
│   ├── pmp_pma/        # Physical Memory Protection
│   ├── cpu.sv          # Top-level CPU module
│   └── hazard_unit.sv  # Pipeline hazard handling
├── include/            # Header files (.svh)
│   ├── ceres_defines.svh      # Global defines & feature flags
│   ├── exception_priority.svh # Exception handling
│   ├── fetch_log.svh          # Fetch stage logging
│   └── writeback_log.svh      # Writeback logging
├── periph/             # Peripherals
│   ├── uart/           # UART controller
│   ├── gpio/           # GPIO controller
│   ├── timer/          # Timer peripheral
│   ├── spi/            # SPI controller
│   ├── i2c/            # I2C controller
│   ├── plic/           # Platform-Level Interrupt Controller
│   ├── pwm/            # PWM controller
│   ├── dma/            # DMA controller
│   ├── wdt/            # Watchdog timer
│   └── vga/            # VGA controller
├── pkg/                # SystemVerilog packages
│   └── ceres_param.sv  # Central configuration (1000+ lines)
├── ram/                # Memory modules
├── tracer/             # Instruction tracer (Konata support)
├── util/               # Utility modules
└── wrapper/            # Top-level wrappers

sim/                    # Simulation files
├── tb/                 # Testbenches
├── test/               # Test programs
└── do/                 # ModelSim DO files

script/                 # Build and test scripts
├── makefiles/          # Modular makefiles
│   ├── config/         # Configuration (config.mk, profiles.mk, paths.mk)
│   ├── sim/            # Simulator configs (verilator.mk, modelsim.mk)
│   ├── test/           # Test runners (isa, arch, imperas, coremark)
│   ├── synth/          # Synthesis (yosys.mk)
│   ├── lint/           # Linting rules
│   └── tools/          # Utilities (clean, waveform viewers)
├── python/             # Python utilities
├── shell/              # Shell scripts
└── config/             # JSON test configurations

docs/                   # Documentation (Turkish & English)
env/                    # Test environments
subrepo/                # External test suites (riscv-tests, riscv-arch-test, etc.)
build/                  # Build outputs
├── logs/               # Simulation logs
├── obj_dir/            # Verilator object files
└── tests/              # Compiled test binaries
```

---

## Coding Conventions

### SystemVerilog Style

1. **Module Naming**: Use lowercase with underscores (e.g., `fetch_stage`, `alu_unit`)
2. **Signal Naming**:
   - Inputs: `i_` prefix (e.g., `i_clk`, `i_rst_n`)
   - Outputs: `o_` prefix (e.g., `o_valid`, `o_data`)
   - Internal signals: descriptive names without prefix
   - Active-low signals: `_n` suffix (e.g., `i_rst_n`)
3. **Clock/Reset**: `i_clk` for clock, `i_rst_n` for active-low reset
4. **Parameters**: UPPER_CASE (e.g., `DATA_WIDTH`, `ADDR_WIDTH`)
5. **Types**: Use `typedef` for custom types, define in packages
6. **Always blocks**: Use `always_ff` for sequential, `always_comb` for combinational

### File Organization

- One module per file
- Filename matches module name
- Headers in `rtl/include/` with `.svh` extension
- Packages in `rtl/pkg/` with `_pkg.sv` or `_param.sv` suffix
- Import `ceres_param` package for all parameters

### Code Example Template

```systemverilog
// Module description
module module_name
  import ceres_param::*;
#(
    parameter int PARAM_NAME = 32
) (
    input  logic        i_clk,
    input  logic        i_rst_n,
    input  logic [31:0] i_data,
    output logic [31:0] o_result,
    output logic        o_valid
);

    // Internal signals
    logic [31:0] internal_reg;

    // Sequential logic
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            internal_reg <= '0;
        end else begin
            internal_reg <= i_data;
        end
    end

    // Combinational logic
    always_comb begin
        o_result = internal_reg;
        o_valid  = |internal_reg;
    end

endmodule
```

---

## Architecture Details

### Pipeline Stages (5-stage)

1. **IF (Instruction Fetch)**: PC management, instruction buffer, compressed instruction handling
2. **ID (Instruction Decode)**: Instruction decoding, register file read, immediate generation
3. **EX (Execute)**: ALU operations, multiply/divide, branch calculation
4. **MEM (Memory)**: Data memory access, load/store operations
5. **WB (Write-Back)**: Register file write-back

### Key Features

- **ISA**: RV32IMC (Base Integer + Multiply + Compressed)
- **Memory**: Von Neumann architecture (unified memory)
- **Cache**: 8-way set associative, 8KB I-Cache, 8KB D-Cache
- **Branch Predictor**: GShare with 512-entry PHT, 256-entry BTB, 16-deep RAS
- **Hazards**: Full forwarding, stall on load-use
- **Exceptions**: Parametric priority system
- **CSR**: Machine-mode CSR support
- **PMP/PMA**: Physical Memory Protection
- **Bus**: Wishbone B4 compatible

### Core Parameters (from `ceres_param.sv`)

```systemverilog
// Core
CPU_CLK = 50_000_000        // 50 MHz
XLEN = 32                   // 32-bit architecture
RESET_VECTOR = 0x8000_0000  // Boot address

// Cache
IC_WAY = 8, IC_CAPACITY = 8KB
DC_WAY = 8, DC_CAPACITY = 8KB
BLK_SIZE = 128 bits

// Branch Predictor
PHT_SIZE = 512, BTB_SIZE = 256
GHR_SIZE = 24, RAS_SIZE = 16

// Peripherals
UART_BAUD = 115200
GPIO_WIDTH = 32
```

### Memory Map

| Region | Base Address | Description |
|--------|--------------|-------------|
| DEBUG | 0x0000_0000 | Debug module |
| BOOTROM | 0x1000_0000 | Boot ROM |
| PERIPH | 0x2000_0000 | Peripherals base |
| CLINT | 0x3000_0000 | Core-local interruptor |
| EXTMEM | 0x4000_0000 | External memory |
| RAM | 0x8000_0000 | Main RAM (boot) |

### Peripheral Offsets (from PERIPH base 0x2000_0000)

| Peripheral | Offset | Full Address |
|------------|--------|--------------|
| UART0 | 0x0000 | 0x2000_0000 |
| UART1 | 0x1000 | 0x2000_1000 |
| SPI0 | 0x2000 | 0x2000_2000 |
| I2C0 | 0x3000 | 0x2000_3000 |
| GPIO | 0x4000 | 0x2000_4000 |
| PWM | 0x5000 | 0x2000_5000 |
| TIMER | 0x6000 | 0x2000_6000 |
| PLIC | 0x7000 | 0x2000_7000 |
| WDT | 0x8000 | 0x2000_8000 |
| DMA | 0x9000 | 0x2000_9000 |
| VGA | 0xD000 | 0x2000_D000 |

### Important Modules

| Module | Path | Description |
|--------|------|-------------|
| `cpu` | `rtl/core/cpu.sv` | Top-level CPU |
| `hazard_unit` | `rtl/core/hazard_unit.sv` | Pipeline hazards |
| `fetch_stage` | `rtl/core/stage01_fetch/` | Instruction fetch |
| `decode_stage` | `rtl/core/stage02_decode/` | Decode logic |
| `execution` | `rtl/core/stage03_execute/execution.sv` | Execute stage top |
| `alu` | `rtl/core/stage03_execute/alu.sv` | ALU operations |
| `cs_reg_file` | `rtl/core/stage03_execute/cs_reg_file.sv` | CSR register file |
| `memory_stage` | `rtl/core/stage04_memory/` | Memory access |
| `writeback_stage` | `rtl/core/stage05_writeback/` | Register writeback |
| `ceres_param` | `rtl/pkg/ceres_param.sv` | All parameters & types |

---

## Build & Test Commands

### Quick Reference

```bash
# === BUILD ===
make verilate           # Build Verilator model
make compile            # Compile with ModelSim
make iverilog           # Compile with Icarus Verilog

# === SIMULATION ===
make simulate           # Run batch simulation (ModelSim)
make simulate_gui       # Run GUI simulation with waveforms
make run_verilator      # Run Verilator simulation
make run_icarus         # Run Icarus simulation

# === TEST SUITES ===
make isa                # All ISA tests (riscv-tests)
make arch               # Architecture tests (riscv-arch-test)
make csr                # CSR tests
make bench              # Benchmarks
make imperas            # Imperas tests
make all_tests          # Run ALL tests

# === QUICK SHORTCUTS ===
make t T=rv32ui-p-add   # Quick single ISA test
make tb T=dhrystone     # Quick single benchmark
make ti T=I-ADD-01      # Quick Imperas test

# === SINGLE TEST ===
make run T=<test_name>  # Run single test with RTL+Spike comparison
make quick_test T=<name> # Run RTL only (skip Spike)
make run_batch          # Run multiple tests from list
make list_tests         # List available tests

# === COREMARK ===
make cm                 # Build and run CoreMark
make cm_run             # Quick CoreMark run (skip rebuild)
make coremark           # Build CoreMark only
make coremark_help      # Show CoreMark help

# === EXTENDED SUITES ===
make embench            # Build Embench-IoT benchmarks
make embench_run        # Run Embench benchmarks
make dhrystone          # Build Dhrystone
make dhrystone_run      # Run Dhrystone
make torture            # Generate & build torture tests
make torture_run        # Run torture tests
make riscv_dv           # Build RISCV-DV generated tests
make riscv_dv_run       # Run RISCV-DV tests
make formal             # Run formal verification

# === UTILITIES ===
make lint               # Run Verilator lint check
make yosys_check        # Run Yosys structural checks
make clean              # Clean all build directories
make gtkwave            # Open waveform with GTKWave
make surfer             # Open waveform with Surfer
make help               # Show full help
make help_lists         # Show all test commands
```

### Logging & Trace Options

```bash
# === LOG CONTROLS (enable with VAR=1) ===
LOG_COMMIT=1      # Spike-compatible commit trace
LOG_PIPELINE=1    # Konata pipeline trace file
LOG_RAM=1         # RAM initialization messages
LOG_UART=1        # UART TX file logging
LOG_BP=1          # Branch predictor statistics
LOG_BP_VERBOSE=1  # Per-branch verbose logging

# === TRACE CONTROLS ===
KONATA_TRACER=1   # Enable Konata pipeline visualizer
TRACE=1           # Enable waveform tracing (.vcd/.wlf)

# === SIMULATION CONTROLS ===
SIM_FAST=1        # Fast mode (all logs disabled)
SIM_UART_MONITOR=1 # UART monitoring + auto-stop (for benchmarks)
SIM_COVERAGE=1    # Enable coverage collection
MAX_CYCLES=N      # Set max simulation cycles

# === BUILD MODES ===
MODE=debug        # Full tracing, assertions ON (default)
MODE=release      # Optimized build, minimal logging
MODE=test         # RISC-V test mode with assertions
```

### Example Commands

```bash
# Run ISA test with commit trace
make run T=rv32ui-p-add LOG_COMMIT=1

# Run CoreMark in fast mode with branch stats
make cm SIM_FAST=1 LOG_BP=1 SIM_UART_MONITOR=1

# Run all ISA tests with commit log
make isa LOG_COMMIT=1

# Run with pipeline visualization
make run T=rv32ui-p-add KONATA_TRACER=1 LOG_PIPELINE=1

# Run architecture test
make run T=C-ADDI-01 TEST_TYPE=arch

# Increase cycle limit for long tests
make run T=coremark MAX_CYCLES=10000000
```

### Test Type Auto-Detection

The makefile auto-detects test type from name:
- `rv32*-p-*` → `isa` (riscv-tests)
- `*-01`, `*-02` → `arch` (riscv-arch-test)
- `I-*`, `M-*`, `C-*` → `imperas`
- `median`, `dhrystone`, `coremark` → `bench`

---

## Feature Flags (ceres_defines.svh)

```systemverilog
// Multiplier implementation (only one active)
`define FEAT_WALLACE_SINGLE  // Single-cycle Wallace tree (default)
//`define FEAT_WALLACE_MULTI // Multi-cycle Wallace tree
//`define FEAT_DSP_MUL       // DSP block multiplier

// Trace enables (activated via +define+ from makefile)
// COMMIT_TRACER  : Carry trace info in pipeline registers
// KONATA_TRACER  : Konata pipeline visualizer
// LOG_COMMIT     : Spike-compatible commit trace
// LOG_RAM        : RAM initialization messages
// LOG_UART       : UART TX file logging
// LOG_BP         : Branch predictor statistics
```

---

## RISC-V Specific Knowledge

### Instruction Formats

- **R-type**: Register-register operations (ADD, SUB, AND, OR, etc.)
- **I-type**: Immediate operations, loads (ADDI, LW, JALR)
- **S-type**: Stores (SW, SH, SB)
- **B-type**: Branches (BEQ, BNE, BLT, BGE)
- **U-type**: Upper immediate (LUI, AUIPC)
- **J-type**: Jumps (JAL)

### Key Opcodes (RV32I)

| Instruction | Opcode (binary) | Opcode (hex) |
|-------------|-----------------|--------------|
| LUI | 0110111 | 0x37 |
| AUIPC | 0010111 | 0x17 |
| JAL | 1101111 | 0x6F |
| JALR | 1100111 | 0x67 |
| BRANCH | 1100011 | 0x63 |
| LOAD | 0000011 | 0x03 |
| STORE | 0100011 | 0x23 |
| OP-IMM | 0010011 | 0x13 |
| OP | 0110011 | 0x33 |
| MISC-MEM | 0001111 | 0x0F |
| SYSTEM | 1110011 | 0x73 |

### RV32M Extension (Multiply/Divide)

| Instruction | funct7 | funct3 |
|-------------|--------|--------|
| MUL | 0000001 | 000 |
| MULH | 0000001 | 001 |
| MULHSU | 0000001 | 010 |
| MULHU | 0000001 | 011 |
| DIV | 0000001 | 100 |
| DIVU | 0000001 | 101 |
| REM | 0000001 | 110 |
| REMU | 0000001 | 111 |

### RV32C Extension (Compressed)

16-bit instructions with quadrant encoding:
- Quadrant 0: `C.LW`, `C.SW`, etc.
- Quadrant 1: `C.ADDI`, `C.JAL`, `C.BEQZ`, etc.
- Quadrant 2: `C.LWSP`, `C.SWSP`, `C.JR`, `C.JALR`, etc.

---

## Common Tasks

### Adding a New Module

1. Create file in appropriate `rtl/` subdirectory
2. Follow naming conventions (lowercase, underscores)
3. Import `ceres_param` package: `import ceres_param::*;`
4. Add to filelist in `script/makefiles/config/sources.mk`
5. Update testbench if needed
6. Run `make lint` to verify

### Adding a New Peripheral

1. Create directory under `rtl/periph/`
2. Define register offsets in `ceres_param.sv`
3. Add to peripheral bus decoder
4. Create software header file
5. Add test program in `sim/test/`

### Debugging Tips

- Use `$display` for simulation debugging
- Check `build/logs/` for simulation logs
- Use tracer module for instruction tracing
- Waveform files: `.wlf` (ModelSim), `.vcd` (Verilator)
- Use `LOG_COMMIT=1` for Spike comparison
- Use `KONATA_TRACER=1` for pipeline visualization

### Running Formal Verification

```bash
make formal              # Full formal check
make formal_bmc          # Bounded model checking only
make formal_prove        # Proof mode
```

---

## Documentation

- **Main docs**: `docs/` directory (Turkish & English)
- **Architecture**: `docs/architecture.md` (comprehensive)
- **Index**: `docs/INDEX.md`
- **Test guide**: `docs/test/`
- **Per-stage docs**: `docs/fetch/`, `docs/decode/`, `docs/execute/`
- **Getting started**: `docs/GETTING_STARTED.md`
- **Tools guide**: `docs/TOOLS.md`

---

## Important Notes

1. **Language**: Documentation is primarily in Turkish (especially in `docs/`)
2. **Active Development**: Check `docs/AI_ENHANCEMENT_PLANS.md` for planned features
3. **Testing**: Always run `make quick` or `make lint` before committing
4. **Formal**: Use `make formal` for formal verification checks
5. **Package**: Always import `ceres_param` for parameters and types
6. **Reset**: Active-low reset (`i_rst_n`), synchronous design

---

## Key Files Reference

| File | Purpose |
|------|---------|
| `rtl/pkg/ceres_param.sv` | **Central config** - ALL parameters, types, enums, structs |
| `rtl/include/ceres_defines.svh` | Feature flags, trace controls |
| `rtl/core/cpu.sv` | Top-level CPU module |
| `rtl/core/hazard_unit.sv` | Pipeline hazard detection |
| `script/makefiles/config/config.mk` | Build configuration |
| `script/makefiles/config/profiles.mk` | Build profiles (debug/release/test) |
| `makefile` | Top-level build entry point |
| `docs/architecture.md` | Full architecture documentation |
| `docs/INDEX.md` | Documentation index |

---

## Enumeration Types (from ceres_param.sv)

Common enums used throughout RTL - always use these instead of magic numbers:

```systemverilog
// ALU operations, branch types, memory operations, CSR operations
// Exception codes, privilege levels, etc.
// See rtl/pkg/ceres_param.sv for complete list
```

---

## Wishbone Bus Interface

The design uses Wishbone B4 pipelined bus:

```systemverilog
// Bus parameters
WB_DATA_WIDTH = 32
WB_ADDR_WIDTH = 32
WB_SEL_WIDTH = 4
WB_NUM_SLAVES = 4
WB_BURST_LEN = 4  // 128-bit cache line / 32-bit
```
