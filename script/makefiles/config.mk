# =========================================
# CERES RISC-V Project Configuration
# =========================================
# Bu dosya tüm alt makefile’lar tarafından include edilir.
# Ortak dizinler, araç yolları, test/log ayarları ve environment değişkenlerini içerir.
# =========================================

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

XLEN          := 32
PYTHON        ?= python3
MODE          ?= debug

# -----------------------------------------
# Derived Directories
# -----------------------------------------
WORK_DIR      := $(BUILD_DIR)/work
OBJ_DIR       := $(BUILD_DIR)/obj_dir
LOG_DIR       := $(RESULTS_DIR)/logs
REPORT_DIR    := $(RESULTS_DIR)/reports
CLEAN_DIRS    := $(OBJ_DIR) $(WORK_DIR) $(LOG_DIR) $(REPORT_DIR)

# -----------------------------------------
# RTL / Testbench
# -----------------------------------------
INC_DIRS      := $(RTL_DIR)/include
RTL_LEVEL     := ceres_wrapper
TB_LEVEL      := tb_wrapper
TB_FILE       := $(SIM_DIR)/tb/tb_wrapper.sv
CPP_TB_FILE   := $(SIM_DIR)/tb/tb_wrapper.cpp

# -----------------------------------------
# Toolchain
# -----------------------------------------
RISCV_PREFIX   ?= riscv32-unknown-elf
RISCV_MARCH    := rv32imc_zicsr_zifencei_zfinx
RISCV_ABI      := ilp32
RISCV_TARGET   ?= $(HOME)/riscv/target

RISCV_GCC      ?= $(RISCV_PREFIX)-gcc
RISCV_OBJDUMP  ?= $(RISCV_PREFIX)-objdump
RISCV_AR       ?= $(RISCV_PREFIX)-ar
RISCV_OBJCOPY  ?= $(RISCV_PREFIX)-objcopy

SPIKE          ?= $(HOME)/tools/spike/bin/spike

# -----------------------------------------
# Default Simulation/Test Parameters
# -----------------------------------------
TEST_NAME     ?= rv32ui-p-add
MAX_CYCLES    ?= 10000
SIM_TIME      := 200000ns
SIM           ?= verilator

# -----------------------------------------
# Automatic MEM Directory Discovery
# -----------------------------------------
MEM_DIRS := $(wildcard $(BUILD_DIR)/tests/*/mem)
ifeq ($(strip $(MEM_DIRS)),)
$(warning ⚠️  No mem directories found under $(BUILD_DIR)/tests)
endif

# -----------------------------------------
# OS Detection
# -----------------------------------------
SHELL := /bin/bash
ifeq ($(OS),Windows_NT)
	PLATFORM := Windows
	MKDIR := mkdir
	RM := rmdir /s /q
else
	PLATFORM := Linux
	MKDIR := mkdir -p
	RM := rm -rf
endif

# -----------------------------------------
# Tools
# -----------------------------------------
VLIB        := vlib
VLOG        := vlog
VSIM        := vsim
# Prefer detected tools in PATH; keep sane defaults for backwards compatibility
VERILATOR   ?= $(shell command -v verilator 2>/dev/null || echo verilator)
YOSYS       := yosys

# -----------------------------------------
# SPIKE Configuration
# -----------------------------------------
SPIKE_ISA    ?= RV32IMC
SPIKE_PC     ?= 0x80000000
SPIKE_FLAGS  := --isa=$(SPIKE_ISA) --pc=$(SPIKE_PC) --log-commits

# -----------------------------------------
# Colors
# -----------------------------------------
GREEN        := \033[1;32m
YELLOW       := \033[1;33m
RED          := \033[1;31m
RESET        := \033[0m

# -----------------------------------------
# Source Files (RTL)
# -----------------------------------------
SV_SOURCES := \
  $(RTL_DIR)/pkg/ceres_param.sv \
  $(wildcard $(RTL_DIR)/core/*.sv) \
  $(wildcard $(RTL_DIR)/core/pmp_pma/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage01_fetch/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage02_decode/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage03_execute/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage03_execute/mul_div/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage03_execute/mul_div/wallace8x8/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage03_execute/mul_div/wallace32x32/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage04_memory/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage05_writeback/*.sv) \
  $(wildcard $(RTL_DIR)/core/mmu/*.sv) \
  $(wildcard $(RTL_DIR)/tracer/*.sv) \
  $(wildcard $(RTL_DIR)/util/*.sv) \
  $(wildcard $(RTL_DIR)/periph/*.sv) \
  $(wildcard $(RTL_DIR)/ram/*.sv) \
  $(wildcard $(RTL_DIR)/wrapper/*.sv) \
  $(wildcard $(RTL_DIR)/wrapper/*.v)

# -----------------------------------------
# Environment Export
# -----------------------------------------
export XLEN
export RISCV_PREFIX
export PATH

# -----------------------------------------
# Test Runner (Unified Paths - UPDATED)
# -----------------------------------------
TEST_LIST         ?= riscv_test_list.flist
FLIST             ?= $(SIM_DIR)/test/$(TEST_LIST)
PASS_LIST_FILE    := $(LOG_DIR)/tests_passed.list
FAIL_LIST_FILE    := $(LOG_DIR)/tests_failed.list

# Unified log directory per simulator and test
# Pattern: results/logs/<simulator>/<test_name>/
TEST_LOG_DIR      := $(LOG_DIR)/$(SIM)/$(TEST_NAME)
RTL_LOG_DIR       := $(TEST_LOG_DIR)

# Test files within unified directory
TEST_WORK_DIR     := $(BUILD_DIR)/test_work
ELF_DIR           := $(BUILD_DIR)/tests/riscv-tests/elf
MEM_DIR           := $(BUILD_DIR)/tests/riscv-tests/mem

RTL_LOG           := $(TEST_LOG_DIR)/rtl_sim.log
SPIKE_LOG         := $(TEST_LOG_DIR)/spike.log
DIFF_LOG          := $(TEST_LOG_DIR)/diff.log
REPORT_FILE       := $(TEST_LOG_DIR)/test_report.txt

# Legacy variables (kept for backward compatibility)
PASS_FAIL_FILE    := $(TEST_LOG_DIR)/pass_fail.txt
DUMP_FILE         := $(TEST_LOG_DIR)/dump.txt

# -----------------------------------------
# ISA / Pipeline Setup
# -----------------------------------------
ISA_REPO_URL   := https://github.com/riscv-software-src/riscv-tests.git
ISA_ROOT       := $(SUBREPO_DIR)/riscv-tests
ISA_SRC_DIR    := $(ISA_ROOT)/isa
ISA_OUT_DIR    := $(BUILD_DIR)/tests
PIPELINE_PY    := $(SCRIPT_DIR)/python/makefile/isa_pipeline.py
MAKE_JOBS      ?= $(shell nproc)

# -----------------------------------------
# RISC-V Arch Test Config
# -----------------------------------------
ARCH_REPO_URL := https://github.com/riscv-non-isa/riscv-arch-test.git
ARCH_ROOT      := $(SUBREPO_DIR)/riscv-arch-test
ARCH_DEVICE    ?= I
ARCH_TARGET    ?= ceres
RISCOF         ?= $(HOME)/.venv/riscof/bin/riscof

RISCOF_CONFIG  := $(ARCH_ROOT)/config/config.ini
CERES_PLUGIN   := $(ARCH_ROOT)/riscv-target/$(ARCH_TARGET)/$(ARCH_TARGET)_plugin.py
CERES_YAML     := $(ARCH_ROOT)/riscv-target/$(ARCH_TARGET)/$(ARCH_TARGET).yaml

# -----------------------------------------
# ModelSim / Questa Simulation
# -----------------------------------------
MODELSIM_LOG_DIR := $(LOG_DIR)/modelsim/$(TEST_NAME)

VLOG_OPTS := -sv -mfcu +acc=npr +incdir+$(INC_DIRS) \
             -work $(WORK_DIR) -svinputport=relaxed \
             -suppress vlog-2583 -suppress vlog-2275 

VSIM_FLAGS_BASE := -t ns -voptargs=+acc=npr +notimingchecks +define+TRACER_EN=1 +test_name=$(TEST_NAME) +sim=modelsim +define+KONATA_TRACE $(SV_DEFINES) \
             +simulator=modelsim
DO_FILE         ?= $(SIM_DIR)/do/questa.do
VSIM_LOG        := $(LOG_DIR)/vsim_$(shell date +%Y%m%d_%H%M%S).log

# -----------------------------------------
# Verilator Settings
# -----------------------------------------
VERILATOR_LOG_DIR := $(LOG_DIR)/verilator/$(TEST_NAME)
VERILATOR_INCLUDES := $(addprefix -I, $(INC_DIRS))
ifeq ($(TEST_TYPE),bench)
  # dosya yok → define aktif
  SV_DEFINES += +define+CERES_UART_TX_MONITOR
else
  # dosya var → define kapalı
  SV_DEFINES +=
endif

VERILATOR_DEFINE = +define+KONATA_TRACE +define+VM_TRACE_FST $(SV_DEFINES)
TRACE        ?= 0
VERBOSE      ?= 0
GUI          ?= 0
LOGGER_SRC   ?= $(RTL_DIR)/tracer/pipeline_logger.sv

ifeq ($(MODE),debug)
    OPT_LEVEL     := -O0
    CFLAGS_DEBUG  := -g
else
    OPT_LEVEL     := -O2
    CFLAGS_DEBUG  :=
endif

NO_WARNING = --Wno-UNOPTFLAT \
              --Wno-CASEINCOMPLETE \
              --Wno-fatal \
              --Wno-lint \
              --Wno-style \
              --Wno-WIDTH \
              --Wno-WIDTHEXPAND \
              --Wno-WIDTHTRUNC \
              --Wno-WIDTHCONCAT \
              --Wno-UNDRIVEN \
              --Wno-UNUSED \
              --Wno-UNUSEDPARAM \
              --Wno-UNUSEDSIGNAL \
              --Wno-LATCH \
              --Wno-IMPLICIT \
              --Wno-MODDUP \
              --Wno-PINCONNECTEMPTY \
              --Wno-DECLFILENAME \
              --Wno-GENUNNAMED \
              --Wno-ASSIGNDLY \
              --Wno-ALWCOMBORDER \
              --Wno-ENUMVALUE \
              --Wno-INITIALDLY \
              --Wno-BLKANDNBLK \
              --Wno-UNOPTTHREADS \
              --Wno-SYMRSVDWORD \
              --Wno-TIMESCALEMOD \
              --Wno-IMPORTSTAR \
              --Wno-VARHIDDEN

NO_WARNING_LINT = --Wno-DECLFILENAME \
                  --Wno-PINCONNECTEMPTY \
                  --Wno-GENUNNAMED \
                  --Wno-IMPORTSTAR \
                  --Wno-VARHIDDEN \
                  --Wno-WIDTHEXPAND \
                  --Wno-UNUSEDSIGNAL \
                  --Wno-UNUSEDPARAM \
                  --Wno-UNDRIVEN \
                  --Wno-UNOPTFLAT \
                  --Wno-ALWCOMBORDER \

LINT_FLAGS  = --lint-only -Wall $(NO_WARNING_LINT) -I$(INC_DIRS) --top-module $(RTL_LEVEL)
BUILD_FLAGS = -Wall --timing $(NO_WARNING) -I$(INC_DIRS) --top-module $(RTL_LEVEL)

RUN_BIN     := $(OBJ_DIR)/V$(RTL_LEVEL)
WAVEFORM    ?= waveform.vcd

# -----------------------------------------
# Utility targets
# -----------------------------------------
.PHONY: validate print-config

validate:
	@echo "[validate] Checking required tools..."
	@command -v $(VERILATOR) >/dev/null 2>&1 || { echo "[ERROR] verilator not found in PATH" >&2; exit 1; }
	@command -v $(RISCV_GCC) >/dev/null 2>&1 || echo "[WARN] $(RISCV_GCC) not found in PATH"
	@echo "[validate] OK"

print-config:
	@echo "ROOT_DIR: $(ROOT_DIR)"
	@echo "RTL_DIR: $(RTL_DIR)"
	@echo "BUILD_DIR: $(BUILD_DIR)"
	@echo "RESULTS_DIR: $(RESULTS_DIR)"
	@echo "VERILATOR: $(VERILATOR)"
	@echo "VERILATOR_INCLUDES: $(VERILATOR_INCLUDES)"
	@echo "RISCV_GCC: $(RISCV_GCC)"
	@echo "SIM: $(SIM)"
	@echo "TEST_NAME: $(TEST_NAME)"

# Allow local overrides without changing tracked files
-include $(ROOT_DIR)/script/makefiles/local_config.mk

# -----------------------------------------
# Yosys (Synthesis)
# -----------------------------------------
YOSYS_FLAGS := -q
YOSYS_CMD   := read_verilog -sv $(SV_SOURCES) $(TB_FILE); \
               hierarchy -check -top $(RTL_LEVEL); \
               proc; opt; check

# -----------------------------------------
# Konata Integration
# -----------------------------------------
KONATA_REPO_URL := https://github.com/shioyadan/Konata.git
#KONATA_DIR      := $(SUBREPO_DIR)/Konata
#KONATA_BIN      := $(KONATA_DIR)/konata
#KONATA_URL      := https://github.com/shioyadan/Konata/releases/latest/download/konata-linux-x64.tar.gz
#KANATA_LOG      := $(BUILD_DIR)/logs/rtl/ceres.kanata


TEST_TYPE ?= isa



# ============================================================
# CERES CoreMark Pipeline — Submodule Clone & Build
# ============================================================

COREMARK_REPO_URL ?= https://github.com/eembc/coremark.git
COREMARK_SUBDIR   ?= $(SUBREPO_DIR)/coremark
COREMARK_BUILD_DIR ?= $(BUILD_DIR)/coremark
