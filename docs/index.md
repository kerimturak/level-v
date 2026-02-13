# CERES RISC-V Dokümantasyon

!!! info "GitHub Repository"
    **Kaynak Kod**: [github.com/kerimturak/level-v](https://github.com/kerimturak/level-v)  
    **Dokümantasyon**: [kerimturak.github.io/level-v](https://kerimturak.github.io/level-v/)

<div class="grid cards" markdown>

-   :material-rocket-launch:{ .lg .middle } __Hızlı Başlangıç__

    ---

    Projeyi kurun ve ilk simülasyonunuzu çalıştırın

    [:octicons-arrow-right-24: Başlangıç Rehberi](getting-started.md)

-   :material-cpu-64-bit:{ .lg .middle } __Mimari__

    ---

    5 aşamalı pipeline, branch predictor, cache sistemi

    [:octicons-arrow-right-24: Mimari Detayları](architecture.md)

-   :material-chip:{ .lg .middle } __Core Modülleri__

    ---

    CPU, Fetch, Decode, Execute, Memory, Writeback

    [:octicons-arrow-right-24: Core Dokümantasyonu](core/index.md)

-   :material-memory:{ .lg .middle } __Peripheral Modülleri__

    ---

    UART, SPI, I2C, GPIO, Timer, PWM, DMA, VGA

    [:octicons-arrow-right-24: Peripheral Dokümantasyonu](periph/index.md)

</div>

---

## 🎯 Proje Özellikleri

| Özellik | Değer |
|---------|-------|
| **ISA** | RV32IMC (Base Integer + Multiply + Compressed) |
| **Pipeline** | 5-aşamalı (IF → ID → EX → MEM → WB) |
| **Cache** | 8-way set associative, 8KB I-Cache, 8KB D-Cache |
| **Branch Predictor** | GShare (512-entry PHT, 256-entry BTB, 16-deep RAS) |
| **Bus** | Wishbone B4 pipelined |
| **Clock** | 50 MHz hedef |
| **Dil** | SystemVerilog (IEEE 1800-2017) |

---

## 📂 Dokümantasyon Yapısı

```
docs/
├── index.md                   # Bu sayfa
├── getting-started.md         # Kurulum rehberi
├── architecture.md            # Mimari dokümantasyonu
├── tools.md                   # Araç kurulumu
│
├── core/                      # Core modül dokümantasyonu
│   ├── index.md               # Core genel bakış
│   ├── cpu.md                 # CPU top-level
│   ├── hazard-unit.md         # Hazard detection
│   ├── stage01_fetch/         # Fetch stage
│   ├── stage02_decode/        # Decode stage
│   ├── stage03_execute/       # Execute stage
│   ├── stage04_memory/        # Memory stage
│   ├── stage05_writeback/     # Writeback stage
│   ├── mmu/                   # Memory management
│   └── pmp_pma/               # Physical memory protection
│
├── periph/                    # Peripheral dokümantasyonu
│   ├── index.md               # Peripheral genel bakış
│   ├── uart.md                # UART controller
│   ├── spi.md                 # SPI master
│   ├── i2c.md                 # I2C master
│   ├── gpio.md                # GPIO controller
│   ├── timer.md               # General purpose timer
│   ├── plic.md                # Platform-level interrupt controller
│   ├── pwm.md                 # PWM controller
│   ├── dma.md                 # DMA controller
│   ├── wdt.md                 # Watchdog timer
│   └── vga.md                 # VGA controller
│
├── include/                   # Include files
├── pkg/                       # Packages
├── ram/                       # Memory modules
├── tracer/                    # Instruction tracer
├── util/                      # Utility modules
├── wrapper/                   # Top-level wrappers
│
├── script/                    # Build system
├── sim/                       # Simulation
└── env/                       # Test environments
```

---

## 🚀 Hızlı Komutlar

```bash
# Verilator ile derleme
make verilate

# Tek test çalıştırma
make t T=rv32ui-p-add

# CoreMark benchmark
make cm SIM_UART_MONITOR=1

# Tüm ISA testleri
make isa

# Lint kontrolü
make lint
```

---

## 📖 Referanslar

- [RISC-V ISA Specification](https://riscv.org/technical/specifications/)
- [Wishbone B4 Specification](https://cdn.opencores.org/downloads/wbspec_b4.pdf)
- [Verilator Manual](https://verilator.org/guide/latest/)

---

## 📞 İletişim

- **GitHub**: [kerimturak/level-v](https://github.com/kerimturak/level-v)
- **Issues**: [GitHub Issues](https://github.com/kerimturak/level-v/issues)
