# Makefiles - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Config Modülleri](#config-modülleri)
3. [Simülasyon Modülleri](#simülasyon-modülleri)
4. [Test Modülleri](#test-modülleri)
5. [Lint ve Synth](#lint-ve-synth)
6. [Araç Modülleri](#araç-modülleri)

---

## Genel Bakış

### Yapı

```
script/makefiles/
├── config/              # Temel konfigürasyon
│   ├── config.mk       # Ana konfigürasyon hub
│   ├── paths.mk        # Dizin path tanımları
│   ├── profiles.mk     # Build profilleri (debug/release/test)
│   ├── sources.mk      # RTL kaynak dosya listesi
│   ├── toolchain.mk    # Toolchain ayarları
│   ├── colors.mk       # Terminal renk kodları
│   ├── test_config.mk  # JSON-based test config
│   └── test_types.mk   # Test tipi → path mapping
│
├── sim/                 # Simülatör kuralları
│   ├── common.mk       # Ortak LOG/TRACE defines
│   ├── verilator.mk    # Verilator rules
│   ├── modelsim.mk     # ModelSim/Questa rules
│   ├── icarus.mk       # Icarus Verilog rules
│   └── spike.mk        # Spike ISS rules
│
├── test/                # Test suite kuralları
│   ├── run_test.mk     # Ana test runner
│   ├── isa_import.mk   # riscv-tests import
│   ├── arch_test.mk    # riscv-arch-test
│   ├── imperas_test.mk # Imperas tests
│   ├── coremark.mk     # CoreMark benchmark
│   ├── dhrystone.mk    # Dhrystone benchmark
│   ├── embench.mk      # Embench-IoT
│   ├── torture.mk      # Torture tests
│   ├── riscv_dv.mk     # RISCV-DV random tests
│   ├── riscv_formal.mk # Formal verification
│   └── test_lists.mk   # Test listeleri
│
├── lint/                # Linting kuralları
│   └── lint.mk         # svlint, Slang, Verilator lint
│
├── synth/               # Synthesis kuralları
│   └── yosys.mk        # Yosys analysis & synthesis
│
├── tools/               # Yardımcı araçlar
│   ├── help.mk         # Merkezi help sistemi
│   ├── clean.mk        # Clean targets
│   ├── konata.mk       # Konata pipeline viewer
│   └── surfer.mk       # Surfer waveform viewer
│
└── custom_test.mk       # Custom test build kuralları
```

### Include Hiyerarşisi

```
makefile (root)
    │
    └─► config/config.mk
            │
            ├─► paths.mk
            ├─► toolchain.mk
            ├─► sources.mk
            ├─► colors.mk
            ├─► profiles.mk
            ├─► test_types.mk
            └─► test_config.mk
    │
    └─► sim/common.mk
            │
            ├─► verilator.mk
            ├─► modelsim.mk
            ├─► icarus.mk
            └─► spike.mk
    │
    └─► test/run_test.mk
            │
            ├─► isa_import.mk
            ├─► arch_test.mk
            ├─► imperas_test.mk
            ├─► coremark.mk
            └─► ...
    │
    └─► lint/lint.mk
    └─► synth/yosys.mk
    └─► tools/help.mk
    └─► tools/clean.mk
```

---

## Config Modülleri

### config.mk - Ana Konfigürasyon Hub

**Dosya:** `script/makefiles/config/config.mk`

```makefile
# =========================================
# CERES RISC-V Project Configuration
# =========================================

# -----------------------------------------
# Default Parameters
# -----------------------------------------
MODE          ?= debug           # debug/release/test
SIM_TIME      := 20000ns

# T kısayolu: make run T=rv32ui-p-add
ifdef T
  TEST_NAME   := $(T)
else
  TEST_NAME   ?= rv32ui-p-add
endif

# -----------------------------------------
# Auto-detect TEST_TYPE from TEST_NAME
# -----------------------------------------
# Patterns:
#   rv32*-p-*, rv64*-p-*  → isa
#   *-01, *-02            → arch
#   I-*, M-*, A-*, C-*    → imperas
#   median, dhrystone     → bench

ifndef TEST_TYPE
  ifneq ($(filter rv32%-p-% rv64%-p-%,$(TEST_NAME)),)
    TEST_TYPE := isa
  else ifneq ($(filter %-01 %-02,$(TEST_NAME)),)
    TEST_TYPE := arch
  else ifneq ($(filter I-% M-% A-% C-%,$(TEST_NAME)),)
    TEST_TYPE := imperas
  else ifneq ($(filter median dhrystone coremark,$(TEST_NAME)),)
    TEST_TYPE := bench
  else
    TEST_TYPE := isa
  endif
endif

# -----------------------------------------
# MAX_CYCLES defaults based on TEST_TYPE
# -----------------------------------------
ifeq ($(TEST_TYPE),arch)
    MAX_CYCLES ?= 100000
else ifeq ($(TEST_TYPE),imperas)
    MAX_CYCLES ?= 2000000
else ifeq ($(TEST_TYPE),bench)
    MAX_CYCLES ?= 1000000
else
    MAX_CYCLES ?= 10000
endif

# -----------------------------------------
# Include Core Modules
# -----------------------------------------
include $(dir $(lastword $(MAKEFILE_LIST)))paths.mk
include $(dir $(lastword $(MAKEFILE_LIST)))toolchain.mk
include $(dir $(lastword $(MAKEFILE_LIST)))sources.mk
include $(dir $(lastword $(MAKEFILE_LIST)))colors.mk
include $(dir $(lastword $(MAKEFILE_LIST)))profiles.mk
include $(dir $(lastword $(MAKEFILE_LIST)))test_types.mk
include $(dir $(lastword $(MAKEFILE_LIST)))test_config.mk
```

### paths.mk - Dizin Tanımları

**Dosya:** `script/makefiles/config/paths.mk`

```makefile
# -----------------------------------------
# Root Paths
# -----------------------------------------
ROOT_DIR      := $(abspath .)
RTL_DIR       := $(ROOT_DIR)/rtl
SIM_DIR       := $(ROOT_DIR)/sim
SCRIPT_DIR    := $(ROOT_DIR)/script
BUILD_DIR     := $(ROOT_DIR)/build
RESULTS_DIR   := $(ROOT_DIR)/results
SUBREPO_DIR   := $(ROOT_DIR)/subrepo
ENV_DIR       := $(ROOT_DIR)/env
CONFIG_DIR    := $(SCRIPT_DIR)/config

# -----------------------------------------
# Derived Directories
# -----------------------------------------
WORK_DIR      := $(BUILD_DIR)/work
OBJ_DIR       := $(BUILD_DIR)/obj_dir
LOG_DIR       := $(RESULTS_DIR)/logs
REPORT_DIR    := $(RESULTS_DIR)/reports
LINT_DIR      := $(RESULTS_DIR)/lint

# -----------------------------------------
# RTL Paths
# -----------------------------------------
INC_DIRS      := $(RTL_DIR)/include

# -----------------------------------------
# Testbench Paths
# -----------------------------------------
TB_FILE       := $(SIM_DIR)/tb/tb_wrapper.sv
CPP_TB_FILE   := $(SIM_DIR)/tb/tb_wrapper.cpp

# -----------------------------------------
# Test Directories
# -----------------------------------------
TEST_WORK_DIR := $(BUILD_DIR)/test_work
ISA_ROOT      := $(SUBREPO_DIR)/riscv-tests
ARCH_ROOT     := $(SUBREPO_DIR)/riscv-arch-test
```

### profiles.mk - Build Profilleri

**Dosya:** `script/makefiles/config/profiles.mk`

```makefile
# =========================================
# CERES Build Profiles
# =========================================

ifeq ($(MODE),debug)
  BUILD_MODE_NAME := Debug
  DEFINE_MACROS   += +define+DEBUG
  VLOG_FLAGS_EXTRA := +define+SIM_DEBUG
  BUILD_DESC      := "Debug mode (assertions, waveforms, full tracing)"
endif

ifeq ($(MODE),release)
  BUILD_MODE_NAME := Release
  DEFINE_MACROS   += +define+RELEASE
  VLOG_FLAGS_EXTRA := +define+FAST_SIM
  BUILD_DESC      := "Release mode (optimized, minimal logs)"
endif

ifeq ($(MODE),test)
  BUILD_MODE_NAME := Test
  DEFINE_MACROS   += +define+TEST_ENV
  VLOG_FLAGS_EXTRA := +define+RISCV_TEST
  BUILD_DESC      := "Test mode (arch tests, extended assertions)"
endif

ifndef BUILD_MODE_NAME
  $(error Unknown build mode: $(MODE). Use MODE=debug|release|test)
endif
```

### sources.mk - RTL Kaynakları

**Dosya:** `script/makefiles/config/sources.mk`

```makefile
# -----------------------------------------
# Top Level Modules
# -----------------------------------------
RTL_LEVEL     := ceres_wrapper
TB_LEVEL      := tb_wrapper
TOP_LEVEL     ?= $(RTL_LEVEL)

# -----------------------------------------
# RTL Source Files
# -----------------------------------------
SV_SOURCES := \
  $(RTL_DIR)/pkg/ceres_param.sv \
  $(wildcard $(RTL_DIR)/core/*.sv) \
  $(wildcard $(RTL_DIR)/core/pmp_pma/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage01_fetch/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage02_decode/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage03_execute/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage03_execute/mul_div/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage04_memory/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage05_writeback/*.sv) \
  $(wildcard $(RTL_DIR)/core/mmu/*.sv) \
  $(wildcard $(RTL_DIR)/core/bus/*.sv) \
  $(wildcard $(RTL_DIR)/tracer/*.sv) \
  $(wildcard $(RTL_DIR)/util/*.sv) \
  $(wildcard $(RTL_DIR)/periph/*/*.sv) \
  $(wildcard $(RTL_DIR)/ram/*.sv) \
  $(wildcard $(RTL_DIR)/wrapper/*.sv)
```

### toolchain.mk - Toolchain Ayarları

**Dosya:** `script/makefiles/config/toolchain.mk`

```makefile
# -----------------------------------------
# Architecture
# -----------------------------------------
XLEN          := 32

# -----------------------------------------
# RISC-V GCC Toolchain
# -----------------------------------------
RISCV_PREFIX   ?= riscv32-unknown-elf
RISCV_MARCH    := rv32imc_zicsr_zifencei_zfinx
RISCV_ABI      := ilp32
RISCV_TARGET   ?= $(HOME)/riscv/target

RISCV_GCC      ?= $(RISCV_PREFIX)-gcc
RISCV_OBJDUMP  ?= $(RISCV_PREFIX)-objdump
RISCV_AR       ?= $(RISCV_PREFIX)-ar
RISCV_OBJCOPY  ?= $(RISCV_PREFIX)-objcopy

# -----------------------------------------
# Spike Simulator
# -----------------------------------------
SPIKE          ?= $(HOME)/tools/spike/bin/spike
SPIKE_ISA      ?= rv32imc_zicsr_zicntr_zifencei
SPIKE_PC       ?= 0x80000000
SPIKE_PRIV     ?= m
SPIKE_FLAGS    := --isa=$(SPIKE_ISA) --pc=$(SPIKE_PC) \
                  --priv=$(SPIKE_PRIV) --log-commits

# -----------------------------------------
# EDA Tools
# -----------------------------------------
VLIB           := vlib
VLOG           := vlog
VSIM           := vsim
VERILATOR      ?= $(shell command -v verilator 2>/dev/null || echo verilator)
YOSYS          := yosys
PYTHON         ?= python3
```

### test_types.mk - Test Tipi Mapping

**Dosya:** `script/makefiles/config/test_types.mk`

```makefile
# -----------------------------------------
# TEST_TYPE → TEST_ROOT Mapping
# -----------------------------------------
TEST_TYPE_isa_ROOT       := $(BUILD_DIR)/tests/riscv-tests
TEST_TYPE_arch_ROOT      := $(BUILD_DIR)/tests/riscv-arch-test
TEST_TYPE_imperas_ROOT   := $(BUILD_DIR)/tests/imperas
TEST_TYPE_bench_ROOT     := $(BUILD_DIR)/tests/riscv-benchmarks
TEST_TYPE_dhrystone_ROOT := $(BUILD_DIR)/tests/dhrystone
TEST_TYPE_embench_ROOT   := $(BUILD_DIR)/tests/embench
TEST_TYPE_torture_ROOT   := $(BUILD_DIR)/tests/torture
TEST_TYPE_riscv-dv_ROOT  := $(BUILD_DIR)/tests/riscv-dv
TEST_TYPE_custom_ROOT    := $(BUILD_DIR)/tests/custom
TEST_TYPE_coremark_ROOT  := $(BUILD_DIR)/tests/coremark

# Geçerli test tipleri
VALID_TEST_TYPES := isa arch imperas bench dhrystone embench \
                    torture riscv-dv custom coremark

# -----------------------------------------
# TEST_TYPE → ELF Extension Mapping
# -----------------------------------------
TEST_TYPE_isa_ELF_EXT       :=
TEST_TYPE_arch_ELF_EXT      := .elf
TEST_TYPE_imperas_ELF_EXT   := .elf
TEST_TYPE_bench_ELF_EXT     :=

# -----------------------------------------
# Helper Functions
# -----------------------------------------
define GET_TEST_ROOT
$(or $(TEST_TYPE_$(1)_ROOT),$(error Unknown TEST_TYPE: $(1)))
endef

define GET_ELF_EXT
$(TEST_TYPE_$(1)_ELF_EXT)
endef

# -----------------------------------------
# Derived Paths
# -----------------------------------------
ELF_DIR  ?= $(TEST_ROOT)/elf
MEM_DIR  ?= $(TEST_ROOT)/mem
HEX_DIR  ?= $(TEST_ROOT)/hex
DUMP_DIR ?= $(TEST_ROOT)/dump
ADDR_DIR ?= $(TEST_ROOT)/pass_fail_addr
```

---

## Simülasyon Modülleri

### common.mk - Ortak Defines

**Dosya:** `script/makefiles/sim/common.mk`

```makefile
# =========================================
# Common Simulation Defines
# =========================================
# Merkezi LOG/TRACE/SIM kontrolleri

# -----------------------------------------
# Backward Compatibility Aliases
# -----------------------------------------
ifdef BP_LOG
  LOG_BP ?= $(BP_LOG)
endif
ifdef FAST_SIM
  SIM_FAST ?= $(FAST_SIM)
endif

# -----------------------------------------
# LOG Variables → SV_DEFINES
# -----------------------------------------
_SV_DEFINES_TMP :=

ifeq ($(LOG_COMMIT),1)
  _SV_DEFINES_TMP += +define+LOG_COMMIT
endif

ifeq ($(LOG_PIPELINE),1)
  _SV_DEFINES_TMP += +define+LOG_PIPELINE
endif

ifeq ($(LOG_RAM),1)
  _SV_DEFINES_TMP += +define+LOG_RAM
endif

ifeq ($(LOG_UART),1)
  _SV_DEFINES_TMP += +define+LOG_UART
endif

ifeq ($(LOG_BP),1)
  _SV_DEFINES_TMP += +define+LOG_BP
endif

ifeq ($(LOG_BP_VERBOSE),1)
  _SV_DEFINES_TMP += +define+LOG_BP +define+LOG_BP_VERBOSE
endif

# -----------------------------------------
# TRACE Controls
# -----------------------------------------
ifeq ($(KONATA_TRACER),1)
  _SV_DEFINES_TMP += +define+KONATA_TRACER
endif

# -----------------------------------------
# SIM Controls
# -----------------------------------------
ifeq ($(SIM_FAST),1)
  _SV_DEFINES_TMP += +define+SIM_FAST
  DISABLE_TRACE := 1
endif

ifeq ($(SIM_UART_MONITOR),1)
  _SV_DEFINES_TMP += +define+SIM_UART_MONITOR
endif

ifeq ($(SIM_COVERAGE),1)
  _SV_DEFINES_TMP += +define+SIM_COVERAGE
  ENABLE_COVERAGE := 1
endif

# -----------------------------------------
# Export
# -----------------------------------------
SV_DEFINES := $(_SV_DEFINES_TMP)
```

### verilator.mk - Verilator Kuralları

**Dosya:** `script/makefiles/sim/verilator.mk`

```makefile
# =========================================
# Verilator Simulation
# =========================================

# -----------------------------------------
# Threading Configuration
# -----------------------------------------
VERILATOR_THREADS  ?= $(shell nproc 2>/dev/null || echo 4)
BUILD_JOBS         ?= $(VERILATOR_THREADS)
SIM_THREADS        ?= 1

# -----------------------------------------
# Trace Flags
# -----------------------------------------
ifeq ($(DISABLE_TRACE),1)
  TRACE_FLAGS :=
else
  TRACE_FLAGS := --trace-fst --trace-structs --trace-params
  TRACE_FLAGS += --trace-depth $(TRACE_DEPTH)
endif

# -----------------------------------------
# Warning Suppressions
# -----------------------------------------
NO_WARN_WIDTH = --Wno-WIDTH --Wno-WIDTHEXPAND --Wno-WIDTHTRUNC
NO_WARN_UNUSED = --Wno-UNDRIVEN --Wno-UNUSED --Wno-UNUSEDPARAM
NO_WARN_STYLE = --Wno-style --Wno-DECLFILENAME --Wno-VARHIDDEN

# -----------------------------------------
# Verilator Flags
# -----------------------------------------
VERILATOR_FLAGS := \
    --cc --exe --build \
    -Mdir $(OBJ_DIR) \
    --top-module $(RTL_LEVEL) \
    $(VERILATOR_INCLUDES) \
    $(TRACE_FLAGS) \
    $(COVERAGE_FLAGS) \
    $(NO_WARN_WIDTH) $(NO_WARN_UNUSED) $(NO_WARN_STYLE) \
    $(VERILATOR_DEFINE) \
    -j $(BUILD_JOBS) \
    -CFLAGS "$(OPT_LEVEL) $(CFLAGS_DEBUG)" \
    -LDFLAGS "$(THREAD_LDFLAGS)"

# =========================================
# Targets
# =========================================

.PHONY: verilate verilate-fast run_verilator rebuild-cpp

verilate:
	@echo -e "$(YELLOW)[VERILATOR] Building...$(RESET)"
	$(VERILATOR) $(VERILATOR_FLAGS) $(SV_SOURCES) $(CPP_TB_FILE)
	@echo -e "$(GREEN)[VERILATOR] Build complete$(RESET)"

verilate-fast:
	@if [ ! -f "$(OBJ_DIR)/V$(RTL_LEVEL)" ]; then \
		$(MAKE) verilate; \
	else \
		echo -e "$(GREEN)[VERILATOR] Binary exists, skipping$(RESET)"; \
	fi

run_verilator: verilate-fast
	@$(SCRIPT_DIR)/shell/run_verilator.sh

rebuild-cpp:
	@echo -e "$(YELLOW)[VERILATOR] Rebuilding C++ only$(RESET)"
	@cd $(OBJ_DIR) && make -f V$(RTL_LEVEL).mk
```

### modelsim.mk - ModelSim Kuralları

**Dosya:** `script/makefiles/sim/modelsim.mk`

```makefile
# =========================================
# ModelSim / Questa Simulation
# =========================================

# -----------------------------------------
# Compilation Options
# -----------------------------------------
VLOG_OPTS := -sv -mfcu +acc=npr +incdir+$(INC_DIRS) \
             -work $(WORK_DIR) -svinputport=relaxed \
             -timescale "1ns/1ps"

# -----------------------------------------
# Simulation Flags
# -----------------------------------------
VSIM_FLAGS := -t ns -voptargs=+acc=npr \
              +test_name=$(TEST_NAME) $(SV_DEFINES)

DO_FILE    ?= $(SIM_DIR)/do/questa.do

# =========================================
# Targets
# =========================================

.PHONY: compile simulate simulate_gui lint_modelsim

compile:
	@echo -e "$(YELLOW)[MODELSIM] Compiling...$(RESET)"
	@$(MKDIR) -p $(WORK_DIR)
	$(VLIB) $(WORK_DIR)
	$(VLOG) $(VLOG_OPTS) $(SV_SOURCES) $(TB_FILE)
	@echo -e "$(GREEN)[MODELSIM] Compilation complete$(RESET)"

simulate: compile
	@echo -e "$(YELLOW)[MODELSIM] Running batch simulation...$(RESET)"
	$(VSIM) -c $(VSIM_FLAGS) $(TB_LEVEL) -do "run -all; quit"

simulate_gui: compile
	@echo -e "$(YELLOW)[MODELSIM] Running GUI simulation...$(RESET)"
	$(VSIM) $(VSIM_FLAGS) $(TB_LEVEL) -do $(DO_FILE)
```

---

## Test Modülleri

### run_test.mk - Ana Test Runner

**Dosya:** `script/makefiles/test/run_test.mk`

```makefile
# ============================================================
# CERES RISC-V Test Runner
# ============================================================
# Usage:
#   make run T=rv32ui-p-add         # Auto-detects TEST_TYPE=isa
#   make run T=C-ADDI-01            # Auto-detects TEST_TYPE=arch
#   make run T=median               # Auto-detects TEST_TYPE=bench
# ============================================================

# ============================================================
# Main Pipeline
# ============================================================
run: test_prepare run_rtl run_spike compare_logs test_report

# ============================================================
# 1️⃣ Prepare Test Environment
# ============================================================
test_prepare:
	@echo -e "$(GREEN)  CERES RISC-V Test Runner$(RESET)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Test Name   : $(TEST_NAME)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Test Type   : $(TEST_TYPE)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Simulator   : $(SIM)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Max Cycles  : $(MAX_CYCLES)"
	@$(MKDIR) "$(TEST_LOG_DIR)" "$(TEST_WORK_DIR)"

# ============================================================
# 2️⃣ Run RTL Simulation
# ============================================================
run_rtl:
ifeq ($(SIM),verilator)
	@$(MAKE) run_verilator TEST_NAME=$(TEST_NAME) \
		MAX_CYCLES=$(MAX_CYCLES) \
		MEM_FILE=$(MEM_DIR)/$(TEST_NAME).mem
else ifeq ($(SIM),modelsim)
	@$(MAKE) simulate TEST_NAME=$(TEST_NAME) GUI=0
endif

# ============================================================
# 3️⃣ Run Spike Golden Reference
# ============================================================
run_spike:
	@$(SPIKE) $(SPIKE_FLAGS) -l $(ELF_FILE) 2>$(SPIKE_LOG)

# ============================================================
# 4️⃣ Compare Logs
# ============================================================
compare_logs:
	@$(PYTHON) $(SCRIPT_DIR)/python/makefile/compare_logs.py \
		$(RTL_LOG) $(SPIKE_LOG)

# ============================================================
# 5️⃣ Generate Report
# ============================================================
test_report:
	@echo -e "$(GREEN)Test completed: $(TEST_NAME)$(RESET)"
```

### coremark.mk - CoreMark Benchmark

**Dosya:** `script/makefiles/test/coremark.mk`

```makefile
# ============================================================
# CERES CoreMark Build Rules
# ============================================================

# Configuration
COREMARK_ITERATIONS ?= 1
COREMARK_SRC_DIR    := $(SUBREPO_DIR)/coremark
COREMARK_PORT_SRC   := $(ROOT_DIR)/env/coremark/ceresv
COREMARK_BUILD_DIR  := $(BUILD_DIR)/tests/coremark

# Output files
COREMARK_ELF  := $(COREMARK_BUILD_DIR)/coremark.elf
COREMARK_MEM  := $(COREMARK_BUILD_DIR)/coremark.mem

# ============================================================
# Targets
# ============================================================

.PHONY: coremark cm cm_run run_coremark

# Full pipeline
coremark: coremark_check coremark_setup coremark_gen_linker coremark_build

# Quick shortcuts
cm: coremark run_coremark
cm_run: run_coremark

# Run CoreMark simulation
run_coremark:
	@$(MAKE) run T=coremark TEST_TYPE=coremark \
		MEM_DIR=$(COREMARK_BUILD_DIR) \
		SIM_UART_MONITOR=1 LOG_BP=1

# Build CoreMark
coremark_build:
	@$(MAKE) -C $(COREMARK_SRC_DIR) \
		PORT_DIR=ceresv \
		ITERATIONS=$(COREMARK_ITERATIONS)
	# Generate .mem file
	@$(PYTHON) $(SCRIPT_DIR)/python/elf_to_mem.py \
		--in $(COREMARK_ELF:.elf=.bin) \
		--out $(COREMARK_MEM)
```

---

## Lint ve Synth

### lint.mk - Linting Kuralları

**Dosya:** `script/makefiles/lint/lint.mk`

```makefile
# =========================================
# CERES RISC-V — Linting Tools
# =========================================

# -----------------------------------------
# Targets
# -----------------------------------------
.PHONY: svlint slang_lint lint_all verilator_lint

# svlint - SystemVerilog style checker
svlint: check_svlint
	@echo -e "$(YELLOW)[svlint] Running...$(RESET)"
	$(SVLINT) -c $(SVLINT_CONFIG) $(LINT_SOURCES)
	@echo -e "$(GREEN)[svlint] Complete$(RESET)"

# Slang - SystemVerilog compiler lint
slang_lint: check_slang
	@echo -e "$(YELLOW)[slang] Running...$(RESET)"
	$(PYTHON) $(SCRIPT_DIR)/python/slang_lint.py $(LINT_SOURCES)
	@echo -e "$(GREEN)[slang] Complete$(RESET)"

# Verilator lint-only mode
verilator_lint:
	@echo -e "$(YELLOW)[verilator] Lint mode...$(RESET)"
	$(VERILATOR) --lint-only $(VERILATOR_INCLUDES) $(LINT_SOURCES)

# Run all linters
lint_all: svlint slang_lint verilator_lint
	@echo -e "$(GREEN)[lint] All linters complete$(RESET)"
```

### yosys.mk - Yosys Kuralları

**Dosya:** `script/makefiles/synth/yosys.mk`

```makefile
# =========================================
# CERES RISC-V — Yosys Synthesis & Analysis
# =========================================

# =========================================
# Targets
# =========================================

.PHONY: yosys_check yosys_synth yosys_show

# Structural Check (combinational loops, multiple drivers, etc.)
yosys_check:
	@echo -e "$(YELLOW)[YOSYS] Structural checks...$(RESET)"
	$(YOSYS) -q -p "\
		read_verilog -sv $(SV_SOURCES) $(TB_FILE); \
		hierarchy -check -top $(RTL_LEVEL); \
		proc; opt; check" 2>&1 | tee $(REPORT_DIR)/yosys_check.log
	# Check for issues
	@if grep -qi "Combinational loop" $(REPORT_DIR)/yosys_check.log; then \
		echo -e "$(RED)Combinational loop detected!$(RESET)"; exit 1; \
	fi
	@if grep -qi "multiple drivers" $(REPORT_DIR)/yosys_check.log; then \
		echo -e "$(RED)Multiple drivers detected!$(RESET)"; exit 1; \
	fi
	@echo -e "$(GREEN)[YOSYS] Check passed$(RESET)"

# Full Synthesis
yosys_synth:
	@echo -e "$(YELLOW)[YOSYS] Synthesizing...$(RESET)"
	$(YOSYS) -q -p "\
		read_verilog -sv $(SV_SOURCES); \
		hierarchy -check -top $(TOP_LEVEL); \
		synth -top $(TOP_LEVEL); \
		write_json $(REPORT_DIR)/$(TOP_LEVEL)_netlist.json; \
		write_verilog $(REPORT_DIR)/$(TOP_LEVEL)_netlist.v"
	@echo -e "$(GREEN)[YOSYS] Synthesis complete$(RESET)"

# Graphical Netlist
yosys_show:
	$(YOSYS) -p "\
		read_verilog -sv $(SV_SOURCES); \
		hierarchy -top $(TOP_LEVEL); \
		proc; opt; synth -top $(TOP_LEVEL); \
		show -format svg -prefix $(REPORT_DIR)/$(TOP_LEVEL)"
```

---

## Araç Modülleri

### help.mk - Merkezi Help Sistemi

**Dosya:** `script/makefiles/tools/help.mk`

```makefile
# =========================================
# CERES RISC-V — Centralized Help System
# =========================================

.PHONY: help help_all help_tests help_sim help_build help_utils

help:
	@echo -e "$(GREEN)  CERES RISC-V Makefile Help$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Quick Reference:$(RESET)"
	@echo -e "  help            Show this help"
	@echo -e "  help_sim        Simulation targets"
	@echo -e "  help_tests      Test commands"
	@echo -e "  help_build      Build targets"
	@echo -e ""
	@echo -e "$(CYAN)▶ Most Common Commands:$(RESET)"
	@echo -e "  make verilate         Build Verilator model"
	@echo -e "  make run T=<test>     Run single test"
	@echo -e "  make isa              Run all ISA tests"
	@echo -e "  make cm               Run CoreMark"
	@echo -e "  make clean            Clean build"

help_sim:
	@echo -e "$(CYAN)▶ Verilator:$(RESET)"
	@echo -e "  verilate        Build Verilator model"
	@echo -e "  run_verilator   Run simulation"
	@echo -e ""
	@echo -e "$(CYAN)▶ ModelSim:$(RESET)"
	@echo -e "  compile         Compile RTL"
	@echo -e "  simulate        Batch simulation"
	@echo -e "  simulate_gui    GUI simulation"
	@echo -e ""
	@echo -e "$(CYAN)▶ Options:$(RESET)"
	@echo -e "  LOG_COMMIT=1        Commit trace"
	@echo -e "  LOG_BP=1            Branch predictor stats"
	@echo -e "  TRACE=1             Waveform tracing"
	@echo -e "  SIM_FAST=1          Fast mode"

help_tests:
	@echo -e "$(CYAN)▶ Test Suites:$(RESET)"
	@echo -e "  isa             riscv-tests ISA suite"
	@echo -e "  arch            riscv-arch-test"
	@echo -e "  imperas         Imperas tests"
	@echo -e "  cm              CoreMark benchmark"
	@echo -e "  dhrystone       Dhrystone benchmark"
```

---

## Özet

Makefile sistemi:

1. **Modüler Yapı**: Her işlev için ayrı .mk dosyası
2. **Merkezi Config**: config.mk hub olarak çalışır
3. **Test Auto-Detection**: TEST_NAME'den TEST_TYPE tespit edilir
4. **Multi-Simulator**: Verilator, ModelSim, Icarus desteği
5. **Comprehensive Testing**: ISA, arch, imperas, CoreMark, etc.
6. **Lint & Synth**: svlint, Slang, Verilator lint, Yosys
7. **Help System**: Detaylı yardım mesajları
