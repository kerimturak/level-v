# Level RISC-V documentation

!!! info "GitHub repository"
    **Source code**: [github.com/kerimturak/level-v](https://github.com/kerimturak/level-v)  
    **Documentation**: [kerimturak.github.io/level-v](https://kerimturak.github.io/level-v/)

<div class="grid cards" markdown>

-   :material-rocket-launch:{ .lg .middle } __Quick start__

    ---

    Set up the project and run your first simulation

    [:octicons-arrow-right-24: Getting started guide](getting-started.md)

-   :material-cpu-64-bit:{ .lg .middle } __Architecture__

    ---

    Five-stage pipeline, branch predictor, cache subsystem

    [:octicons-arrow-right-24: Architecture details](architecture.md)

-   :material-chip:{ .lg .middle } __Core modules__

    ---

    CPU, fetch, decode, execute, memory, writeback

    [:octicons-arrow-right-24: Core documentation](core/index.md)

-   :material-memory:{ .lg .middle } __Peripheral modules__

    ---

    UART, SPI, I2C, GPIO, timer, PWM, DMA, VGA

    [:octicons-arrow-right-24: Peripheral documentation](periph/index.md)

</div>

---

## Project highlights

| Feature | Value |
|---------|-------|
| **ISA** | RV32IMC (base integer + multiply + compressed) |
| **Pipeline** | Five-stage (IF → ID → EX → MEM → WB) |
| **Cache** | 8-way set-associative, 8 KB I-cache, 8 KB D-cache |
| **Branch predictor** | GShare (512-entry PHT, 256-entry BTB, 16-deep RAS) |
| **Bus** | Wishbone B4 pipelined |
| **Clock** | 50 MHz target |
| **Language** | SystemVerilog (IEEE 1800-2017) |

---

## Documentation layout

```
docs/
├── index.md                   # This page
├── getting-started.md         # Setup guide
├── architecture.md            # Architecture
├── tools.md                   # Tool setup
│
├── core/                      # Core module docs
│   ├── index.md               # Core overview
│   ├── cpu_module.md          # CPU top level
│   ├── hazard_unit_module.md  # Hazard handling
│   ├── stage01_fetch/         # Fetch stage
│   ├── stage02_decode/        # Decode stage
│   ├── stage03_execute/       # Execute stage
│   ├── stage04_memory/        # Memory stage
│   ├── stage05_writeback/     # Writeback stage
│   ├── mmu/                   # Memory subsystem
│   └── pmp_pma/               # Physical memory attributes
│
├── periph/                    # Peripheral docs
│   ├── index.md               # Peripheral overview
│   ├── uart.md
│   ├── spi.md
│   ├── i2c.md
│   ├── gpio.md
│   ├── timer.md
│   ├── plic.md
│   ├── pwm.md
│   ├── dma.md
│   ├── wdt.md
│   └── vga.md
│
├── include/                   # Include files
├── pkg/                       # Packages
├── ram/                       # Memory modules
├── tracer/                    # Instruction tracer
├── util/                      # Utilities
├── wrapper/                   # Top-level wrappers
│
├── script/                    # Build system
├── sim/                       # Simulation
└── env/                       # Test environments
```

---

## Quick commands

```bash
# Build with Verilator
make verilate

# Run a single test
make t T=rv32ui-p-add

# CoreMark benchmark
make run_coremark SIM_UART_MONITOR=1

# Full ISA suite
make isa

# Lint
make lint
```

---

## References

- [RISC-V ISA specifications](https://riscv.org/technical/specifications/)
- [Wishbone B4 specification](https://cdn.opencores.org/downloads/wbspec_b4.pdf)
- [Verilator manual](https://verilator.org/guide/latest/)

---

## Contact

- **GitHub**: [kerimturak/level-v](https://github.com/kerimturak/level-v)
- **Issues**: [GitHub issues](https://github.com/kerimturak/level-v/issues)
