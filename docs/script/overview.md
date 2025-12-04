# Script Directory - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Dizin Yapısı](#dizin-yapısı)
3. [Makefiles](#makefiles)
4. [Python Scripts](#python-scripts)
5. [Shell Scripts](#shell-scripts)
6. [Configuration Files](#configuration-files)

---

## Genel Bakış

### Amaç

`script/` dizini, CERES RISC-V projesinin **build**, **test**, **simulation** ve **verification** süreçlerini yöneten tüm otomasyon scriptlerini içerir.

### Dizin Konumu

```
/home/kerim/level-v/script/
```

### Temel Özellikler

- Modüler makefile yapısı
- JSON-tabanlı konfigürasyon sistemi
- Python utility araçları
- Shell otomasyon scriptleri
- Çoklu simülatör desteği (Verilator, ModelSim, Icarus)

---

## Dizin Yapısı

```
script/
├── README.md                    # Script dokümantasyonu
├── config/                      # JSON konfigürasyon dosyaları
│   ├── modelsim.json           # ModelSim ayarları
│   ├── modelsim.schema.json    # ModelSim JSON şeması
│   ├── verilator.json          # Verilator ayarları
│   ├── verilator.local.json.example  # Local override örneği
│   ├── verilator.schema.json   # Verilator JSON şeması
│   └── tests/                  # Test suite konfigürasyonları
│       ├── isa.json            # ISA test ayarları
│       ├── arch.json           # Architecture test ayarları
│       ├── imperas.json        # Imperas test ayarları
│       ├── coremark.json       # CoreMark ayarları
│       └── ...                 # Diğer test suites
│
├── makefiles/                   # Modüler makefile sistemi
│   ├── config/                 # Temel konfigürasyon
│   │   ├── config.mk          # Ana konfigürasyon
│   │   ├── paths.mk           # Dizin path'leri
│   │   ├── profiles.mk        # Build profilleri
│   │   ├── sources.mk         # RTL kaynak dosyaları
│   │   ├── toolchain.mk       # Toolchain ayarları
│   │   ├── colors.mk          # Terminal renkleri
│   │   ├── test_config.mk     # Test konfigürasyonu
│   │   └── test_types.mk      # Test tipi tanımları
│   │
│   ├── sim/                    # Simülasyon kuralları
│   │   ├── common.mk          # Ortak simülasyon defines
│   │   ├── verilator.mk       # Verilator kuralları
│   │   ├── modelsim.mk        # ModelSim kuralları
│   │   ├── icarus.mk          # Icarus Verilog kuralları
│   │   └── spike.mk           # Spike referans simülatör
│   │
│   ├── test/                   # Test suite kuralları
│   │   ├── run_test.mk        # Test runner ana dosya
│   │   ├── isa_import.mk      # riscv-tests import
│   │   ├── arch_test.mk       # riscv-arch-test
│   │   ├── imperas_test.mk    # Imperas testleri
│   │   ├── coremark.mk        # CoreMark benchmark
│   │   ├── dhrystone.mk       # Dhrystone benchmark
│   │   ├── embench.mk         # Embench-IoT
│   │   ├── torture.mk         # Torture testleri
│   │   ├── riscv_dv.mk        # RISCV-DV random tests
│   │   ├── riscv_formal.mk    # Formal verification
│   │   └── test_lists.mk      # Test listeleri
│   │
│   ├── lint/                   # Linting kuralları
│   │   └── lint.mk            # svlint, Slang, Verilator lint
│   │
│   ├── synth/                  # Synthesis kuralları
│   │   └── yosys.mk           # Yosys synthesis ve analiz
│   │
│   ├── tools/                  # Yardımcı araçlar
│   │   ├── help.mk            # Merkezi help sistemi
│   │   ├── clean.mk           # Clean targets
│   │   ├── konata.mk          # Konata pipeline viewer
│   │   └── surfer.mk          # Surfer waveform viewer
│   │
│   └── custom_test.mk         # Custom test build kuralları
│
├── python/                      # Python utility scriptleri
│   ├── requirements.txt        # Python bağımlılıkları
│   ├── requirements-dev.txt    # Geliştirme bağımlılıkları
│   ├── elf_to_mem.py          # ELF → .mem converter
│   ├── gen_linker.py          # Linker script generator
│   ├── torture_gen.py         # Torture test generator
│   ├── simple_torture_gen.py  # Basit torture generator
│   ├── hex2mem_32to128.py     # HEX format converter
│   ├── get_static_hex.py      # Static hex extractor
│   ├── compare_bp_stats.py    # Branch predictor analizi
│   ├── slang_lint.py          # Slang linter wrapper
│   ├── riscv_dv_gen.py        # RISCV-DV generator
│   ├── riscv_dv_config.py     # RISCV-DV konfigürasyon
│   ├── download_pdfs.py       # PDF downloader utility
│   ├── multiply.py            # Multiplier test generator
│   ├── convert_dump_to_elf_hex.py  # Dump converter
│   ├── fpga/                  # FPGA araçları
│   ├── makefile/              # Makefile için Python helpers
│   │   ├── isa_pipeline.py    # ISA test pipeline
│   │   ├── elf_to_mem.py      # ELF converter
│   │   ├── hex_to_mem.py      # HEX converter
│   │   ├── compare_logs.py    # Log karşılaştırma
│   │   ├── generate_test_dashboard.py  # Test dashboard
│   │   └── html_diff_generator.py      # HTML diff
│   └── tests/                 # Python test scriptleri
│
└── shell/                       # Shell scriptleri
    ├── run_verilator.sh        # Verilator runner
    ├── build_custom_test.sh    # Custom test builder
    ├── parse_verilator_config.sh  # Verilator config parser
    ├── parse_modelsim_config.sh   # ModelSim config parser
    ├── parse_test_config.sh       # Test config parser
    ├── init_ceres_structure.sh    # Proje init scripti
    ├── uart_test_quickstart.sh    # UART test quick start
    ├── exception_priority_test.sh # Exception priority test
    └── PARAMETRIC_PRIORITY_QUICKSTART.sh  # Priority test
```

---

## Makefiles

### config/ - Temel Konfigürasyon

#### config.mk - Ana Konfigürasyon

```makefile
# Temel parametreler
MODE          ?= debug           # Build mode: debug/release/test
SIM_TIME      := 20000ns         # Default simülasyon süresi
TEST_NAME     ?= rv32ui-p-add    # Default test

# Test tipi otomatik tespiti
# rv32*-p-* → isa
# *-01      → arch
# I-*, M-*  → imperas
# median    → bench
```

**İçerik:**
- Default parametre tanımları
- TEST_TYPE auto-detection
- MAX_CYCLES test tipine göre ayarlama
- Diğer config dosyalarını include etme

#### paths.mk - Dizin Tanımları

```makefile
ROOT_DIR      := $(abspath .)
RTL_DIR       := $(ROOT_DIR)/rtl
SIM_DIR       := $(ROOT_DIR)/sim
SCRIPT_DIR    := $(ROOT_DIR)/script
BUILD_DIR     := $(ROOT_DIR)/build
RESULTS_DIR   := $(ROOT_DIR)/results
SUBREPO_DIR   := $(ROOT_DIR)/subrepo
ENV_DIR       := $(ROOT_DIR)/env
```

**İçerik:**
- Proje kök dizinleri
- Build çıktı dizinleri
- Test dizinleri
- Log/Report dizinleri

#### profiles.mk - Build Profilleri

```makefile
# Debug mode
ifeq ($(MODE),debug)
  BUILD_MODE_NAME := Debug
  DEFINE_MACROS   += +define+DEBUG
  BUILD_DESC      := "Debug mode enabled"
endif

# Release mode
ifeq ($(MODE),release)
  BUILD_MODE_NAME := Release
  DEFINE_MACROS   += +define+RELEASE
  BUILD_DESC      := "Release mode enabled"
endif

# Test mode
ifeq ($(MODE),test)
  BUILD_MODE_NAME := Test
  DEFINE_MACROS   += +define+TEST_ENV
  BUILD_DESC      := "Test mode enabled"
endif
```

#### sources.mk - RTL Kaynakları

```makefile
# Top-level modüller
RTL_LEVEL     := ceres_wrapper
TB_LEVEL      := tb_wrapper

# SystemVerilog kaynakları
SV_SOURCES := \
  $(RTL_DIR)/pkg/ceres_param.sv \
  $(wildcard $(RTL_DIR)/core/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage*/*.sv) \
  $(wildcard $(RTL_DIR)/periph/*/*.sv) \
  ...
```

#### toolchain.mk - Toolchain Ayarları

```makefile
# RISC-V GCC
RISCV_PREFIX   ?= riscv32-unknown-elf
RISCV_MARCH    := rv32imc_zicsr_zifencei_zfinx
RISCV_ABI      := ilp32

# Spike simulator
SPIKE          ?= $(HOME)/tools/spike/bin/spike
SPIKE_ISA      ?= rv32imc_zicsr_zicntr_zifencei

# EDA Tools
VERILATOR      ?= $(shell command -v verilator)
YOSYS          := yosys
```

#### test_types.mk - Test Tipi Tanımları

```makefile
# TEST_TYPE → TEST_ROOT mapping
TEST_TYPE_isa_ROOT       := $(BUILD_DIR)/tests/riscv-tests
TEST_TYPE_arch_ROOT      := $(BUILD_DIR)/tests/riscv-arch-test
TEST_TYPE_imperas_ROOT   := $(BUILD_DIR)/tests/imperas
TEST_TYPE_bench_ROOT     := $(BUILD_DIR)/tests/riscv-benchmarks
TEST_TYPE_coremark_ROOT  := $(BUILD_DIR)/tests/coremark

# Geçerli test tipleri
VALID_TEST_TYPES := isa arch imperas bench dhrystone embench torture riscv-dv custom coremark

# ELF uzantısı mapping
TEST_TYPE_isa_ELF_EXT       :=
TEST_TYPE_arch_ELF_EXT      := .elf
TEST_TYPE_imperas_ELF_EXT   := .elf
```

---

### sim/ - Simülasyon Kuralları

#### common.mk - Ortak Defines

```makefile
# LOG kontrolleri → SV_DEFINES
ifeq ($(LOG_COMMIT),1)
  _SV_DEFINES_TMP += +define+LOG_COMMIT
endif
ifeq ($(LOG_BP),1)
  _SV_DEFINES_TMP += +define+LOG_BP
endif

# TRACE kontrolleri
ifeq ($(KONATA_TRACER),1)
  _SV_DEFINES_TMP += +define+KONATA_TRACER
endif

# SIM kontrolleri
ifeq ($(SIM_FAST),1)
  _SV_DEFINES_TMP += +define+SIM_FAST
  DISABLE_TRACE := 1
endif
```

#### verilator.mk - Verilator Kuralları

```makefile
# Temel targetlar
.PHONY: verilate verilate-fast run_verilator rebuild-cpp

verilate:
	# Verilator C++ model build
	$(VERILATOR) $(VERILATOR_FLAGS) $(SV_SOURCES)

run_verilator:
	# Simülasyon çalıştırma
	./build/obj_dir/Vceres_wrapper +mem=$(MEM_FILE) +max_cycles=$(MAX_CYCLES)
```

**Özellikler:**
- JSON config desteği
- Multi-threading (THREADS=N)
- Trace FST/VCD
- Coverage collection
- Warning suppressions

#### modelsim.mk - ModelSim Kuralları

```makefile
# Temel targetlar
.PHONY: compile simulate simulate_gui lint_modelsim

compile:
	vlib $(WORK_DIR)
	vlog $(VLOG_OPTS) $(SV_SOURCES)

simulate:
	vsim -c $(TB_LEVEL) -do "run -all; quit"

simulate_gui:
	vsim $(TB_LEVEL) -do $(DO_FILE)
```

---

### test/ - Test Suite Kuralları

#### run_test.mk - Ana Test Runner

```makefile
# Ana pipeline
run: test_prepare run_rtl run_spike compare_logs test_report

# RTL simülasyonu
run_rtl:
	$(MAKE) run_verilator TEST_NAME=$(TEST_NAME)

# Spike golden model
run_spike:
	$(SPIKE) $(SPIKE_FLAGS) $(ELF_FILE)

# Log karşılaştırma
compare_logs:
	$(PYTHON) compare_logs.py $(RTL_LOG) $(SPIKE_LOG)
```

#### isa_import.mk - riscv-tests Pipeline

```makefile
# Tam pipeline
isa_auto: isa_clone isa_configure isa_my_configure isa_build isa_import

# Adımlar
isa_clone:      # Git clone/submodule init
isa_configure:  # autoconf + ./configure
isa_my_configure: # Ceres env setup
isa_build:      # make isa
isa_import:     # ELF → MEM conversion
```

#### arch_test.mk - riscv-arch-test

```makefile
# Desteklenen extensions
ARCH_EXTENSIONS := I M C Zicsr Zifencei

# Pipeline
arch_auto: arch_clone arch_setup arch_build arch_import

# Per-extension build
arch_build_I:    # I extension tests
arch_build_M:    # M extension tests
arch_build_C:    # C extension tests
arch_build_Zicsr: # Zicsr tests
```

#### coremark.mk - CoreMark Benchmark

```makefile
# Konfigürasyon
COREMARK_ITERATIONS ?= 1
COREMARK_SRC_DIR    := $(SUBREPO_DIR)/coremark
COREMARK_PORT_SRC   := $(ROOT_DIR)/env/coremark/ceresv

# Pipeline
coremark: coremark_check coremark_setup coremark_gen_linker coremark_build

# Çalıştırma
cm: coremark run_coremark
cm_run: run_coremark
```

---

### lint/ - Linting Kuralları

```makefile
# Targetlar
.PHONY: svlint slang_lint lint_all

svlint:
	svlint $(SVLINT_CONFIG) $(LINT_SOURCES)

slang_lint:
	python3 slang_lint.py $(LINT_SOURCES)

lint_all: svlint slang_lint
```

---

### synth/ - Synthesis Kuralları

```makefile
# Yosys structural check
yosys_check:
	$(YOSYS) -p "read_verilog -sv $(SV_SOURCES); \
	             hierarchy -check -top $(RTL_LEVEL); \
	             proc; opt; check"

# Yosys synthesis
yosys_synth:
	$(YOSYS) -p "... synth -top $(TOP_LEVEL); \
	             write_json $(REPORT_DIR)/netlist.json"

# Netlist visualization
yosys_show:
	$(YOSYS) -p "... show -format svg"
```

---

### tools/ - Yardımcı Araçlar

#### help.mk - Merkezi Help Sistemi

```makefile
help:           # Ana help
help_sim:       # Simülasyon help
help_tests:     # Test help
help_build:     # Build help
help_utils:     # Utility help
help_all:       # Tüm help
```

#### clean.mk - Clean Targets

```makefile
clean:          # Build temizleme
clean_logs:     # Log temizleme
clean_all:      # Tam temizlik
```

---

## Python Scripts

### elf_to_mem.py - ELF/Binary Converter

```python
"""
ELF/binary -> .mem converter for RAM initialization.
Generates one hex line per block (default 16 bytes / 128 bits).

Usage:
  ./elf_to_mem.py --in test.bin --out test.mem --addr 0x80000000 \
      --block-bytes 16 --word-size 4 --word-endian little
"""
```

**Parametreler:**
- `--in`: Input binary dosyası
- `--out`: Output .mem dosyası
- `--addr`: Base address (default: 0x80000000)
- `--block-bytes`: Block size (default: 16)
- `--word-size`: Word size (default: 4)
- `--word-endian`: little/big
- `--word-order`: high-to-low/low-to-high

### gen_linker.py - Linker Script Generator

```python
"""
Linker Script Generator for Ceres-V
Memory map YAML dosyasından linker script oluşturur.

Usage:
    python3 gen_linker.py memory_map.yaml output.ld
    python3 gen_linker.py memory_map.yaml output.ld --header output.h
"""
```

**Özellikler:**
- YAML memory map parse
- Linker script generation
- C header generation
- Stack/heap size calculation

### torture_gen.py - Torture Test Generator

```python
"""
RISC-V Torture Test Generator for Ceres-V
Generates random but valid RISC-V instruction sequences.

Features:
- Configurable instruction mix
- RV32I, M, C extension support
- Memory-safe load/store generation
- Branch coverage optimization
- Deterministic via seed control
"""

# Kullanım
python3 torture_gen.py --seed 12345 --max-instructions 1000 \
    --march rv32imc --output torture_test.S
```

### compare_bp_stats.py - Branch Predictor Analysis

```python
"""
Branch predictor istatistik karşılaştırma aracı.
Farklı konfigürasyonların performansını analiz eder.
"""
```

### slang_lint.py - Slang Linter Wrapper

```python
"""
Slang (pyslang) linter wrapper.
SystemVerilog dosyalarını Slang ile analiz eder.
"""
```

### makefile/ Alt Dizini

| Script | Açıklama |
|--------|----------|
| `isa_pipeline.py` | ISA test import pipeline |
| `elf_to_mem.py` | ELF → MEM converter (makefile versiyonu) |
| `hex_to_mem.py` | HEX → MEM converter |
| `compare_logs.py` | RTL/Spike log karşılaştırma |
| `generate_test_dashboard.py` | HTML test dashboard |
| `html_diff_generator.py` | HTML diff report |

---

## Shell Scripts

### run_verilator.sh - Verilator Runner

```bash
#!/usr/bin/env bash
# Verilator Simulation Runner

# Features:
# - Safe shell flags with error handling
# - MEM file resolution
# - Comprehensive logging with JSON summary
# - Performance timing and statistics
# - Signal handling for clean termination
# - Timeout support

Usage:
  TEST_NAME=rv32ui-p-add ./run_verilator.sh
  MEM_FILE=/path/to/test.mem MAX_CYCLES=100000 ./run_verilator.sh
```

### build_custom_test.sh - Custom Test Builder

```bash
#!/bin/bash
# Custom UART Test Build and Run Script

# Kullanım:
#   ./build_custom_test.sh uart_hello_test

# Adımlar:
# 1. Source check
# 2. Compile with riscv32-unknown-elf-gcc
# 3. Generate .bin, .hex, .mem files
# 4. Create objdump
# 5. Optionally run simulation
```

### parse_verilator_config.sh - Config Parser

```bash
#!/usr/bin/env bash
# Verilator JSON config → Makefile variable converter

# verilator.json dosyasını parse eder
# Makefile include edilebilir format üretir
```

### parse_modelsim_config.sh - ModelSim Config Parser

```bash
#!/usr/bin/env bash
# ModelSim JSON config → Makefile variable converter
```

### init_ceres_structure.sh - Proje Init

```bash
#!/bin/bash
# Ceres proje yapısını initialize eder
# Gerekli dizinleri ve template dosyaları oluşturur
```

---

## Configuration Files

### verilator.json - Verilator Konfigürasyonu

```json
{
  "simulation": {
    "max_cycles": 100000,
    "timeout": 0,
    "threads": "auto",
    "seed": "auto"
  },

  "build": {
    "mode": "release",
    "jobs": "auto",
    "opt_level": "-O3",
    "cpp_standard": "c++17"
  },

  "trace": {
    "enabled": true,
    "format": "fst",
    "depth": 99,
    "structs": true
  },

  "coverage": {
    "enabled": true,
    "line": true,
    "toggle": true
  },

  "logging": {
    "fast_sim": false,
    "bp_log": false,
    "commit_trace": true,
    "pipeline_log": true
  },

  "profiles": {
    "fast": { ... },
    "debug": { ... },
    "coverage": { ... }
  }
}
```

### modelsim.json - ModelSim Konfigürasyonu

```json
{
  "compilation": {
    "sv_mode": "-sv",
    "mfcu": "-mfcu",
    "svinputport": "relaxed",
    "timescale": "1ns/1ps"
  },

  "simulation": {
    "time_resolution": "ns",
    "voptargs": "+acc=npr"
  },

  "lint": {
    "enabled": true,
    "mode": "default"
  }
}
```

### tests/ Alt Dizini - Test Suite Configs

| Dosya | Açıklama |
|-------|----------|
| `isa.json` | riscv-tests ISA ayarları |
| `arch.json` | riscv-arch-test ayarları |
| `imperas.json` | Imperas test ayarları |
| `coremark.json` | CoreMark benchmark ayarları |
| `dhrystone.json` | Dhrystone ayarları |
| `embench.json` | Embench-IoT ayarları |
| `torture.json` | Torture test ayarları |
| `riscv-dv.json` | RISCV-DV random test ayarları |
| `formal.json` | Formal verification ayarları |
| `custom.json` | Custom test ayarları |

---

## Kullanım Örnekleri

### Test Çalıştırma

```bash
# Tek test
make run T=rv32ui-p-add

# ISA test suite
make isa

# Architecture tests
make arch

# CoreMark benchmark
make cm

# Custom test build and run
./script/shell/build_custom_test.sh my_test
```

### Simülasyon Seçenekleri

```bash
# Verilator ile trace
make run T=rv32ui-p-add TRACE=1 LOG_COMMIT=1

# Fast mode (no trace)
make run T=coremark SIM_FAST=1

# Branch predictor stats
make run T=dhrystone LOG_BP=1

# Pipeline visualization
make run T=rv32ui-p-add KONATA_TRACER=1 LOG_PIPELINE=1
```

### Build Modları

```bash
# Debug build
make verilate MODE=debug

# Release build (optimized)
make verilate MODE=release

# Test mode
make verilate MODE=test
```

### Linting ve Analysis

```bash
# Verilator lint
make lint

# svlint
make svlint

# Slang lint
make slang_lint

# Yosys structural check
make yosys_check
```

---

## Özet

`script/` dizini:

1. **Modüler Makefiles**: Organize edilmiş, bakımı kolay makefile sistemi
2. **JSON Config**: Simülatör ve test konfigürasyonları
3. **Python Tools**: ELF/HEX conversion, test generation, analysis
4. **Shell Scripts**: Otomasyon ve runner scriptleri
5. **Multi-Simulator**: Verilator, ModelSim, Icarus desteği
6. **Test Suites**: ISA, arch, imperas, CoreMark, Dhrystone, Embench
7. **Verification**: Lint, Yosys check, formal verification
