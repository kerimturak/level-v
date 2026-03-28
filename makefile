# ==================================================
# Level RISC-V — Unified Makefile
# ==================================================
# Previously, pieces under script/makefiles/**/*.mk were merged here.
# Local override: script/makefiles/config/local.mk (optional)
# ==================================================
.DEFAULT_GOAL := help

SHELL := /bin/bash

# ---------- defaults (root makefile) ----------
# -----------------------------------------
# Default Parameters (MODE: Verilator OPT / debug flags — see "Compiler Flags (based on MODE)"; .conf → CFG_MODE)
# -----------------------------------------
MODE          ?= debug
TEST_NAME     ?= rv32ui-p-add
SIM_TIME      := 200000ns

# -----------------------------------------
# Auto-detect TEST_TYPE from TEST_NAME pattern
# -----------------------------------------
# Priority: User-specified TEST_TYPE > Auto-detection
#
# Detection patterns:
#   - rv32*-p-*, rv64*-p-*           → isa      (riscv-tests)
#   - *-01 (e.g., C-ADDI-01)         → arch     (riscv-arch-test)  
#   - I-*, M-*, A-*, C-*, F-*, D-*   → imperas  (Imperas tests)
#   - median, dhrystone, coremark    → bench    (benchmarks)
#
ifndef TEST_TYPE
  # Check for riscv-tests ISA pattern: rv32ui-p-add, rv32um-p-mul, etc.
  ifneq ($(filter rv32%-p-% rv64%-p-% rv32%-v-% rv64%-v-%,$(TEST_NAME)),)
    TEST_TYPE := isa
  # Check for arch-test pattern: ends with -01, -02, etc. (e.g., C-ADDI-01)
  else ifneq ($(filter %-01 %-02 %-03 %-04 %-05,$(TEST_NAME)),)
    TEST_TYPE := arch
  # Check for Imperas pattern: starts with I-, M-, A-, C-, F-, D- (uppercase)
  else ifneq ($(filter I-% M-% A-% C-% F-% D-% Zifencei-%,$(TEST_NAME)),)
    # Could be arch or imperas - check if it ends with -01 pattern
    ifneq ($(filter %-01 %-02 %-03,$(TEST_NAME)),)
      TEST_TYPE := arch
    else
      TEST_TYPE := imperas
    endif
  # Check for common benchmark names
  else ifneq ($(filter median dhrystone coremark multiply qsort rsort towers vvadd,$(TEST_NAME)),)
    TEST_TYPE := bench
  # Default to ISA if no pattern matches
  else
    TEST_TYPE := isa
  endif
endif
SIM           ?= verilator
GUI           ?= 0
TRACE         ?= 0
NO_ADDR       ?= 0
SIM_FAST      ?= 0

# MAX_CYCLES: in normal flow script/config/tests/default.conf + <TEST_CONFIG>.conf
# → CFG_MAX_CYCLES in build/.test_config_<profile>.mk; applied below.
# This line is only a fallback when .mk does not exist yet or could not be parsed (same base as default.conf).
MAX_CYCLES ?= 100000

# ---------- config: paths, toolchain, sources, colors, profiles, test_config ----------

# ====== config/paths.mk ======
# =========================================
# Level RISC-V — Directory Paths
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
ENV_DIR       := $(ROOT_DIR)/env
CONFIG_DIR    := $(SCRIPT_DIR)/config

# -------------------------------------------------------------------------
# CPU clock for C env (UART, CoreMark timebase). MUST match RTL:
#   rtl/pkg/level_param.sv localparam CPU_CLK
# Override:  make any_build CPU_CLK_HZ=48000000
# -------------------------------------------------------------------------
CPU_CLK_HZ            ?= 25000000
export CPU_CLK_HZ
LEVELV_CPU_CLK_CPPFLAGS := -I$(ENV_DIR)/common -DCPU_CLK_HZ=$(CPU_CLK_HZ)UL

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

# -----------------------------------------
# Automatic MEM Directory Discovery
# -----------------------------------------
# riscv-tests uses */mem subdirectory, coremark and custom tests use direct folder
MEM_DIRS := $(wildcard $(BUILD_DIR)/tests/*/mem) $(BUILD_DIR)/tests/coremark $(BUILD_DIR)/tests/custom

# ====== config/toolchain.mk ======
# =========================================
# Level RISC-V — Toolchain Configuration
# =========================================

# -----------------------------------------
# Architecture
# -----------------------------------------
XLEN          := 32

# -----------------------------------------
# RISC-V GCC Toolchain
# -----------------------------------------
RISCV_PREFIX   ?= riscv32-unknown-elf
RISCV_TARGET   ?= $(HOME)/riscv/target

RISCV_GCC      ?= $(RISCV_PREFIX)-gcc

# -----------------------------------------
# Spike Simulator
# -----------------------------------------
SPIKE          ?= $(HOME)/tools/spike/bin/spike
SPIKE_ISA      ?= rv32imc_zicsr_zicntr_zifencei
SPIKE_PC       ?= 0x80000000
SPIKE_PRIV     ?= m
# -----------------------------------------
# EDA Tools
# -----------------------------------------
VLIB           := vlib
VLOG           := vlog
VERILATOR      ?= $(shell command -v verilator 2>/dev/null || echo verilator)
YOSYS          := yosys

# -----------------------------------------
# Python
# -----------------------------------------
PYTHON         ?= python3

# -----------------------------------------
# Build Jobs
# -----------------------------------------
MAKE_JOBS      ?= $(shell nproc)

# -----------------------------------------
# Environment Export
# -----------------------------------------
export XLEN
export RISCV_PREFIX
export PATH

# ====== config/sources.mk ======
# =========================================
# Level RISC-V — RTL Source Files
# =========================================

# -----------------------------------------
# Top Level Modules
# -----------------------------------------
RTL_LEVEL     := level_wrapper
TB_LEVEL      := tb_wrapper
TOP_LEVEL     ?= $(RTL_LEVEL)

# -----------------------------------------
# RTL Source Files (rtl/flist.f — paths relative to repo root)
# -----------------------------------------
FLIST_SV := $(RTL_DIR)/flist.f
ifeq ($(wildcard $(FLIST_SV)),)
  $(error Missing $(FLIST_SV) — add RTL paths there, one per line)
endif
SV_SOURCES := $(addprefix $(ROOT_DIR)/,$(shell awk '!/^[[:space:]]*#/ && NF {print $$1}' $(FLIST_SV)))

# ====== config/colors.mk ======
# =========================================
# Level RISC-V — Terminal Colors
# =========================================

GREEN   := \033[1;32m
YELLOW  := \033[1;33m
RED     := \033[1;31m
CYAN    := \033[1;36m
MAGENTA := \033[1;35m
RESET   := \033[0m
BOLD    := \033[1m

WARN	:= ⚠️
SUCCESS	:= ✓
ERROR	:= ❌
# For Yosys / synth messages (old debug|release|test names removed; RTL +defines come from .conf / SV_DEFINES chain)
BUILD_MODE_NAME ?= $(MODE)

# ====== config/test_config.mk ======
# Test profile: script/config/tests/default.conf + <TEST_CONFIG>.conf
# → build/.test_config_<name>.mk (CFG_* + CFG_SV_DEFINES for Verilator +define+)
# Parser: script/shell/parse_test_conf.sh — jq not required.
# RTL macros: UPPER_SNAKE=1 lines or CFG_SV_DEFINES=+define+FOO ...

# -----------------------------------------
# Configuration Paths
# -----------------------------------------
TEST_CONFIG_DIR   := $(ROOT_DIR)/script/config/tests
TEST_CONF_PARSER  := $(ROOT_DIR)/script/shell/parse_test_conf.sh
TEST_CONF_DEFAULT := $(TEST_CONFIG_DIR)/default.conf

# -----------------------------------------
# Auto-detect TEST_CONFIG from TEST_TYPE (override: TEST_CONFIG=<profile>)
# -----------------------------------------
ifndef TEST_CONFIG
  ifeq ($(TEST_TYPE),isa)
    TEST_CONFIG := isa
  else ifeq ($(TEST_TYPE),arch)
    TEST_CONFIG := arch
  else ifeq ($(TEST_TYPE),imperas)
    TEST_CONFIG := imperas
  else ifeq ($(TEST_TYPE),bench)
    TEST_CONFIG := bench
  else ifeq ($(TEST_TYPE),embench)
    TEST_CONFIG := embench
  else ifeq ($(TEST_TYPE),dhrystone)
    TEST_CONFIG := dhrystone
  else ifeq ($(TEST_TYPE),torture)
    TEST_CONFIG := torture
  else ifeq ($(TEST_TYPE),riscv-dv)
    TEST_CONFIG := riscv-dv
  else ifeq ($(TEST_TYPE),custom)
    TEST_CONFIG := custom
  else
    TEST_CONFIG := default
  endif
endif

# -----------------------------------------
# Load Configuration from .conf
# -----------------------------------------
TEST_CONF_PROFILE := $(TEST_CONFIG_DIR)/$(TEST_CONFIG).conf
TEST_CONFIG_MK    := $(BUILD_DIR)/.test_config_$(TEST_CONFIG).mk
TEST_CONFIG_MK_DEPS := $(wildcard $(TEST_CONF_DEFAULT)) $(wildcard $(TEST_CONF_PROFILE))

ifneq ($(TEST_CONFIG_MK_DEPS),)
  -include $(TEST_CONFIG_MK)
  $(TEST_CONFIG_MK): $(TEST_CONFIG_MK_DEPS) | $(BUILD_DIR)
		@echo -e "$(YELLOW)[TEST_CONFIG]$(RESET) Parsing $(TEST_CONFIG) (.conf)..."
		@chmod +x $(TEST_CONF_PARSER) 2>/dev/null || true
		@$(TEST_CONF_PARSER) $(TEST_CONFIG) --make > $@ || echo "# parse_test_conf failed" > $@
endif

# -----------------------------------------
# .conf → makefile: copy CFG_* values from parse_test_conf.sh output.
# If a variable with the same name was given on the command line, GNU Make ignores these assignments (no override).
# CFG_* vs MAX_CYCLES are different names: .conf-readable keys (MAX_CYCLES=) vs in-makefile name.
# -----------------------------------------
ifdef CFG_MAX_CYCLES
  MAX_CYCLES := $(CFG_MAX_CYCLES)
endif
# Respect `make SIM_FAST=0` over .conf (e.g. enable commit/cache logs on coremark profile)
ifdef CFG_SIM_FAST
ifeq ($(filter command line,$(origin SIM_FAST)),)
  SIM_FAST := $(CFG_SIM_FAST)
endif
endif
ifdef CFG_BP_LOG
  BP_LOG := $(CFG_BP_LOG)
endif
ifdef CFG_NO_ADDR
  NO_ADDR := $(CFG_NO_ADDR)
endif
ifdef CFG_MODE
  MODE := $(CFG_MODE)
endif
ifdef CFG_TRACE
ifeq ($(filter command line,$(origin TRACE)),)
  TRACE := $(CFG_TRACE)
endif
endif

# Snapshot .conf defines now: `SV_DEFINES += $(CFG_SV_DEFINES)` would be recursive/deferred,
# and `-include build/.modelsim_config.mk` later overwrites CFG_SV_DEFINES (ModelSim JSON) —
# Verilator would then see the wrong +define+ list for profiles like coremark.
ifdef CFG_SV_DEFINES
  SV_DEFINES := $(strip $(CFG_SV_DEFINES))
else
  SV_DEFINES :=
endif

# -----------------------------------------
# Spike (from .conf / CFG_*)
# -----------------------------------------
ifdef CFG_SPIKE_ISA
  SPIKE_ISA := $(CFG_SPIKE_ISA)
endif

ifdef CFG_SPIKE_PRIV
  SPIKE_PRIV := $(CFG_SPIKE_PRIV)
endif

ifdef CFG_SPIKE_PC
  SPIKE_PC := $(CFG_SPIKE_PC)
endif

ifdef CFG_SPIKE_TRIGGERS
  SPIKE_TRIGGERS := $(CFG_SPIKE_TRIGGERS)
else
  SPIKE_TRIGGERS := 1
endif

ifdef CFG_SPIKE_PMP_REGIONS
  SPIKE_PMP_REGIONS := $(CFG_SPIKE_PMP_REGIONS)
else
  SPIKE_PMP_REGIONS := 0
endif

ifdef CFG_SPIKE_PMP_GRANULARITY
  SPIKE_PMP_GRANULARITY := $(CFG_SPIKE_PMP_GRANULARITY)
else
  SPIKE_PMP_GRANULARITY := 4
endif

SPIKE_ARGS := --isa=$(SPIKE_ISA) --pc=$(SPIKE_PC) --priv=$(SPIKE_PRIV)
SPIKE_ARGS += --triggers=$(SPIKE_TRIGGERS)

ifneq ($(SPIKE_PMP_REGIONS),0)
  SPIKE_ARGS += --pmpregions=$(SPIKE_PMP_REGIONS)
  SPIKE_ARGS += --pmpgranularity=$(SPIKE_PMP_GRANULARITY)
endif

ifeq ($(CFG_SPIKE_MISALIGNED),1)
  SPIKE_ARGS += --misaligned
endif

ifeq ($(CFG_SPIKE_LOG_COMMITS),1)
  SPIKE_ARGS += --log-commits
else ifdef CFG_SPIKE_LOG_COMMITS
else
  SPIKE_ARGS += --log-commits
endif

# -----------------------------------------
# Debug: Show loaded config
# -----------------------------------------
.PHONY: show-config config-info

show-config config-info:
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  Current Test Configuration$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  TEST_CONFIG     = $(GREEN)$(TEST_CONFIG)$(RESET)"
	@echo -e "  TEST_TYPE       = $(TEST_TYPE)"
	@echo -e "  MAX_CYCLES      = $(MAX_CYCLES)"
	@echo -e "  SIM_FAST        = $(SIM_FAST)"
	@echo -e "  BP_LOG          = $(BP_LOG)"
	@echo -e "  NO_ADDR         = $(NO_ADDR)"
	@echo -e "  MODE            = $(MODE)"
	@echo -e "  TRACE           = $(TRACE)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  Spike Configuration$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  SPIKE_ISA       = $(SPIKE_ISA)"
	@echo -e "  SPIKE_PC        = $(SPIKE_PC)"
	@echo -e "  SPIKE_PRIV      = $(SPIKE_PRIV)"
	@echo -e "  SPIKE_TRIGGERS  = $(SPIKE_TRIGGERS)"
	@echo -e "  SPIKE_PMP_REGIONS= $(SPIKE_PMP_REGIONS)"
	@echo -e "  SPIKE_ARGS      = $(SPIKE_ARGS)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo ""
	@echo -e "$(YELLOW).conf sources:$(RESET) $(TEST_CONF_DEFAULT) $(wildcard $(TEST_CONF_PROFILE))"

# -----------------------------------------
# List available configs
# -----------------------------------------
.PHONY: list-configs configs

list-configs configs:
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  Available Test Configurations (.conf)$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@chmod +x $(TEST_CONF_PARSER) 2>/dev/null || true
	@$(TEST_CONF_PARSER) --list 2>/dev/null || true
	@echo ""
	@echo -e "$(YELLOW)Usage:$(RESET)"
	@echo -e "  make run TEST_CONFIG=isa"
	@echo -e "  make bench                 # Auto-selects bench config"
	@echo -e "  make show-config           # Show current config values"

# ---------- config.mk (OS, paths, validate; local.mk) ----------

# -----------------------------------------
# OS Detection
# -----------------------------------------
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
# Test Runner Paths
# -----------------------------------------
TEST_LIST         ?= riscv_test_list.flist
FLIST             ?= $(SIM_DIR)/test/$(TEST_LIST)
PASS_LIST_FILE    := $(LOG_DIR)/tests_passed.list
FAIL_LIST_FILE    := $(LOG_DIR)/tests_failed.list

# Unified log directory per simulator and test (overridden after T=/TEST_NAME finalization below)
TEST_LOG_DIR      := $(LOG_DIR)/$(SIM)/$(TEST_NAME)
RTL_LOG_DIR       := $(TEST_LOG_DIR)
SPIKE_LOG         := $(TEST_LOG_DIR)/spike.log
DIFF_LOG          := $(TEST_LOG_DIR)/diff.log

# -----------------------------------------
# External Repository URLs
# -----------------------------------------
ISA_REPO_URL      := https://github.com/riscv-software-src/riscv-tests.git
ARCH_REPO_URL     := https://github.com/riscv-non-isa/riscv-arch-test.git
COREMARK_REPO_URL := https://github.com/eembc/coremark.git

# -----------------------------------------
# ISA Test Pipeline
# -----------------------------------------
ISA_SRC_DIR       := $(ISA_ROOT)/isa
ISA_OUT_DIR       := $(BUILD_DIR)/tests
PIPELINE_PY       := $(SCRIPT_DIR)/python/makefile/isa_pipeline.py

# -----------------------------------------
# Utility Targets
# -----------------------------------------
.PHONY: validate print-config

validate:
	@echo "[validate] Checking required tools..."
	@command -v $(VERILATOR) >/dev/null 2>&1 || { echo "[ERROR] verilator not found in PATH" >&2; exit 1; }
	@command -v $(RISCV_GCC) >/dev/null 2>&1 || echo "[WARN] $(RISCV_GCC) not found in PATH"
	@echo "[validate] OK"

print-config:
	@echo "ROOT_DIR     : $(ROOT_DIR)"
	@echo "RTL_DIR      : $(RTL_DIR)"
	@echo "BUILD_DIR    : $(BUILD_DIR)"
	@echo "RESULTS_DIR  : $(RESULTS_DIR)"
	@echo "VERILATOR    : $(VERILATOR)"
	@echo "RISCV_GCC    : $(RISCV_GCC)"
	@echo "SIM          : $(SIM)"
	@echo "TEST_NAME    : $(TEST_NAME)"
	@echo "MODE         : $(MODE)"

# -----------------------------------------
# Local Overrides (optional)
# -----------------------------------------
-include $(ROOT_DIR)/script/makefiles/config/local.mk

# CoreMark/Dhrystone: default UART-only RTL logs (override with e.g. make LOG_COMMIT=1 …)
ifneq ($(filter coremark dhrystone,$(TEST_CONFIG)),)
ifeq ($(filter command line,$(origin LOG_COMMIT)),)
  override LOG_COMMIT := 0
endif
ifeq ($(filter command line,$(origin LOG_BP)),)
  override LOG_BP := 0
endif
ifeq ($(filter command line,$(origin LOG_PIPELINE)),)
  override LOG_PIPELINE := 0
endif
ifeq ($(filter command line,$(origin KONATA_TRACER)),)
  override KONATA_TRACER := 0
endif
ifeq ($(filter command line,$(origin LOG_RAM)),)
  override LOG_RAM := 0
endif
endif

# ====== sim/modelsim.mk ======
# =========================================
# Level RISC-V — ModelSim / Questa Simulation
# =========================================

# -----------------------------------------
# Configuration Loading (from JSON)
# -----------------------------------------
MODELSIM_CONFIG_SCRIPT := $(ROOT_DIR)/script/python/makefile/modelsim_config.py
MODELSIM_CONFIG_FILE   := $(ROOT_DIR)/script/config/modelsim.json

# Load config if available and no explicit overrides
ifneq ($(wildcard $(MODELSIM_CONFIG_SCRIPT)),)
  ifneq ($(wildcard $(MODELSIM_CONFIG_FILE)),)
    # Check if jq is available
    JQ_EXISTS := $(shell command -v jq 2>/dev/null)
    ifdef JQ_EXISTS
      # Load profile if specified
      ifdef MODELSIM_PROFILE
        MODELSIM_CONFIG_ARGS := --profile $(MODELSIM_PROFILE)
      endif
      
      # Include generated config (only if not already set)
      -include $(BUILD_DIR)/.modelsim_config.mk
      
      # Generate config makefile
    $(BUILD_DIR)/.modelsim_config.mk: $(MODELSIM_CONFIG_FILE) $(wildcard $(ROOT_DIR)/script/config/modelsim.local.json)
		@mkdir -p $(BUILD_DIR)
		@python3 $(MODELSIM_CONFIG_SCRIPT) --make $(MODELSIM_CONFIG_ARGS) > $@ 2>/dev/null || true
    endif
  endif
endif

# -----------------------------------------
# ModelSim Paths
# -----------------------------------------
MODELSIM_LOG_DIR := $(LOG_DIR)/modelsim/$(TEST_NAME)

# -----------------------------------------
# Default Values (can be overridden by JSON config)
# -----------------------------------------
MODELSIM_TIME_RES       ?= ns
MODELSIM_SV_MODE        ?= -sv
MODELSIM_MFCU           ?= -mfcu
MODELSIM_SVINPUTPORT    ?= relaxed
MODELSIM_ACC            ?= npr
MODELSIM_FSMDEBUG       ?=
MODELSIM_ASSERTDEBUG    ?=
MODELSIM_COVERAGE       ?=
MODELSIM_SV_COMPAT      ?= -sv12compat
MODELSIM_TIMESCALE      ?= 1ns/1ps
MODELSIM_NOTIMINGCHECKS ?= +notimingchecks
MODELSIM_SUPPRESS       ?= -suppress vlog-2583 -suppress vlog-2275
MODELSIM_NOWARN         ?=
MODELSIM_SOURCE         ?= -source
MODELSIM_MULTICORE      ?=

# -----------------------------------------
# Trace/Log Defines (compile-time)
# These must be passed to vlog, not vsim
# -----------------------------------------
MODELSIM_DEFINES :=

# Commit trace (Spike-compatible) - LOG_COMMIT=1
ifeq ($(LOG_COMMIT),1)
  MODELSIM_DEFINES += +define+LOG_COMMIT
endif

# Pipeline trace (KONATA format) - LOG_PIPELINE=1
ifeq ($(LOG_PIPELINE),1)
  MODELSIM_DEFINES += +define+LOG_PIPELINE
endif

# RAM init messages - LOG_RAM=1
ifeq ($(LOG_RAM),1)
  MODELSIM_DEFINES += +define+LOG_RAM
endif

# UART file logging - LOG_UART=1
ifeq ($(LOG_UART),1)
  MODELSIM_DEFINES += +define+LOG_UART
endif

# GPTimer ARR register trace ($display) - LOG_GPTIMER_ARR=1
ifeq ($(LOG_GPTIMER_ARR),1)
  MODELSIM_DEFINES += +define+LOG_GPTIMER_ARR
endif

# Branch Predictor stats - LOG_BP=1
ifeq ($(LOG_BP),1)
  MODELSIM_DEFINES += +define+LOG_BP
endif

# Verbose BP logging - LOG_BP_VERBOSE=1
ifeq ($(LOG_BP_VERBOSE),1)
  MODELSIM_DEFINES += +define+LOG_BP +define+LOG_BP_VERBOSE
endif

# KONATA pipeline visualizer - KONATA_TRACER=1
ifeq ($(KONATA_TRACER),1)
  MODELSIM_DEFINES += +define+KONATA_TRACER
endif

# COMMIT_TRACER for pipeline register trace info
ifeq ($(COMMIT_TRACER),1)
  MODELSIM_DEFINES += +define+COMMIT_TRACER
endif

# Default: Always enable COMMIT_TRACER for trace info in pipeline
MODELSIM_DEFINES += +define+COMMIT_TRACER

# Shared feature defines (same as verilator.mk)
ifeq ($(SIM_FAST),1)
  MODELSIM_DEFINES += +define+SIM_FAST
endif
ifeq ($(MINIMAL_SOC),1)
  MODELSIM_DEFINES += +define+MINIMAL_SOC
endif
ifeq ($(USE_L2_CACHE),1)
  MODELSIM_DEFINES += +define+USE_L2_CACHE
endif
ifeq ($(SIM_UART_MONITOR),1)
  MODELSIM_DEFINES += +define+SIM_UART_MONITOR
endif

# -----------------------------------------
# Compilation Options
# -----------------------------------------
VLOG_BASE_OPTS := $(MODELSIM_SV_MODE) $(MODELSIM_MFCU) \
                  +acc=$(MODELSIM_ACC) +incdir+$(INC_DIRS) \
                  -work $(WORK_DIR) -svinputport=$(MODELSIM_SVINPUTPORT) \
                  $(MODELSIM_SUPPRESS) $(MODELSIM_NOWARN) \
                  $(MODELSIM_DEFINES)

ifdef MODELSIM_SV_COMPAT
  VLOG_BASE_OPTS += $(MODELSIM_SV_COMPAT)
endif

# Timescale
VLOG_BASE_OPTS += -timescale "$(MODELSIM_TIMESCALE)"

# Coverage options
ifneq ($(MODELSIM_COVERAGE),)
  VLOG_BASE_OPTS += $(MODELSIM_COVERAGE)
endif

# Multicore options
ifneq ($(MODELSIM_MULTICORE),)
  VLOG_BASE_OPTS += $(MODELSIM_MULTICORE)
endif

VLOG_OPTS := $(VLOG_BASE_OPTS)

# -----------------------------------------
# ModelSim/Questa: +define+ at vlog time; runtime uses +plusargs (Python runner).
# -----------------------------------------
DO_FILE    ?= $(SIM_DIR)/do/questa.do

# =========================================
# Targets
# =========================================

.PHONY: $(WORK_DIR) compile \
        resolve_mem simulate validate_config show_config \
        clean_modelsim modelsim_help modelsim_config_summary

# ============================================================
# Library Creation
# ============================================================
$(WORK_DIR):
	@echo -e "$(YELLOW)[CREATING WORK LIBRARY]$(RESET)"
	@$(MKDIR) "$(MODELSIM_LOG_DIR)"
	$(VLIB) $(WORK_DIR)

# ============================================================
# Standard Compilation
# ============================================================
compile: $(WORK_DIR)
	@echo -e "$(YELLOW)[COMPILING RTL SOURCES]$(RESET)"
	@$(MKDIR) "$(MODELSIM_LOG_DIR)"
	@($(VLOG) $(VLOG_OPTS) \
		$(SV_SOURCES) $(TB_FILE) 2>&1 | tee "$(MODELSIM_LOG_DIR)/compile.log"); \
	EXIT_CODE=$$?; \
	if [ $$EXIT_CODE -ne 0 ]; then \
		echo -e "$(RED)$(ERROR) Compilation failed.$(RESET)"; exit $$EXIT_CODE; \
	elif grep -i "Error" $(MODELSIM_LOG_DIR)/compile.log | grep -v "Errors: 0" >/dev/null; then \
		echo -e "$(RED)$(ERROR) Errors found in log.$(RESET)"; exit 1; \
	else \
		echo -e "$(GREEN)Compilation successful.$(RESET)"; \
	fi

# ============================================================
# Resolve Memory File (TEST_NAME -> absolute path)
# ============================================================
resolve_mem:
	@if [ -z "$(TEST_NAME)" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) TEST_NAME not provided (use TEST_NAME=<name>)."; \
		exit 1; \
	fi; \
	MATCH=""; \
	for dir in $(MEM_DIRS); do \
		if [ -f "$$dir/$(TEST_NAME).mem" ]; then MATCH="$$dir/$(TEST_NAME).mem"; break; fi; \
		if [ -f "$$dir/$(TEST_NAME).hex" ]; then MATCH="$$dir/$(TEST_NAME).hex"; break; fi; \
	done; \
	if [ -z "$$MATCH" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Could not find $(TEST_NAME).mem in: $(MEM_DIRS)"; \
		exit 1; \
	fi; \
	ABS="$$(cd $$(dirname $$MATCH) && pwd)/$$(basename $$MATCH)"; \
	MEM_TMP="$(BUILD_DIR)/.mem_path_$(TEST_NAME).tmp"; \
	echo -e "MEM_FILE=$$ABS" > "$$MEM_TMP"; \
	echo -e "$(GREEN)[OK]$(RESET) Found memory file:"; echo -e "       → $$ABS"


# ============================================================
# Python Runner Script
# ============================================================
MODELSIM_RUNNER := $(ROOT_DIR)/script/python/makefile/modelsim_runner.py

# ============================================================
# Simulation
# ============================================================
simulate: compile
	@python3 $(MODELSIM_RUNNER) \
		--test=$(TEST_NAME) \
		--work-dir=$(WORK_DIR) \
		--log-dir=$(MODELSIM_LOG_DIR) \
		--mem-dirs="$(MEM_DIRS)" \
		--build-dir=$(BUILD_DIR) \
		--sim-time=$(SIM_TIME) \
		--tb-level=$(TB_LEVEL) \
		$(if $(filter 1,$(LOG_COMMIT)),--debug,) \
		$(if $(filter 1,$(KONATA_TRACER)),--debug,) \
		$(if $(filter 1,$(TRACE)),--debug,) \
		$(if $(MODELSIM_PROFILE),--profile=$(MODELSIM_PROFILE)) \
		$(if $(filter 1,$(GUI)),--gui) \
		$(if $(DO_FILE),--do-file=$(DO_FILE)) \
		$(if $(MEM_FILE),--mem-file=$(MEM_FILE)) \
		$(foreach def,$(subst +define+,,$(SV_DEFINES)),-D $(def))

# Config validation
validate_config:
	@python3 $(MODELSIM_RUNNER) \
		--test=dummy \
		--work-dir=$(WORK_DIR) \
		--log-dir=/tmp \
		--mem-dirs="." \
		--validate-config \
		$(if $(MODELSIM_PROFILE),--profile=$(MODELSIM_PROFILE))

# Show current config
show_config:
	@python3 $(MODELSIM_RUNNER) \
		--test=dummy \
		--work-dir=$(WORK_DIR) \
		--log-dir=/tmp \
		--mem-dirs="." \
		--show-config \
		$(if $(MODELSIM_PROFILE),--profile=$(MODELSIM_PROFILE))


# ============================================================
# Configuration Summary
# ============================================================
modelsim_config_summary:
	@echo -e "$(CYAN)════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)        ModelSim Configuration Summary$(RESET)"
	@echo -e "$(CYAN)════════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Compile Options:$(RESET)"
	@echo -e "  SV Mode:       $(MODELSIM_SV_MODE)"
	@echo -e "  MFCU:          $(MODELSIM_MFCU)"
	@echo -e "  SV Input Port: $(MODELSIM_SVINPUTPORT)"
	@echo -e "  Opt Level:     $(MODELSIM_OPT_LEVEL)"
	@echo -e "  Incremental:   $(MODELSIM_INCREMENTAL)"
	@echo ""
	@echo -e "$(YELLOW)Debug Options:$(RESET)"
	@echo -e "  Access:        $(MODELSIM_ACC)"
	@echo -e "  FSM Debug:     $(if $(MODELSIM_FSMDEBUG),Yes,No)"
	@echo -e "  Assert Debug:  $(if $(MODELSIM_ASSERTDEBUG),Yes,No)"
	@echo -e "  Line Info:     $(if $(MODELSIM_LINEINFO),Yes,No)"
	@echo ""
	@echo -e "$(YELLOW)Coverage:$(RESET)"
	@echo -e "  Options:       $(if $(MODELSIM_COVERAGE),$(MODELSIM_COVERAGE),Disabled)"
	@echo ""
	@echo -e "$(YELLOW)Simulation:$(RESET)"
	@echo -e "  Time Res:      $(MODELSIM_TIME_RES)"
	@echo -e "  Sim Time:      $(SIM_TIME)"
	@echo -e "  Timing Checks: $(if $(MODELSIM_NOTIMINGCHECKS),Disabled,Enabled)"
	@echo ""
	@echo -e "$(YELLOW)Message Handling:$(RESET)"
	@echo -e "  Suppress:      $(MODELSIM_SUPPRESS)"
	@echo ""
	@echo -e "$(CYAN)════════════════════════════════════════════════════════════$(RESET)"

# ============================================================
# Clean
# ============================================================
clean_modelsim:
	@echo -e "$(RED)[CLEANING MODELSIM FILES]$(RESET)"
	@$(RM) "$(WORK_DIR)" "transcript" "vsim.wlf" "modelsim.ini" || true
	@$(RM) "$(LOG_DIR)/rtl/modelsim" || true
	@$(RM) "$(BUILD_DIR)/.modelsim_config.mk" || true
	@echo -e "$(GREEN)ModelSim clean complete.$(RESET)"

# ============================================================
# Help
# ============================================================
modelsim_help:
	@echo ""
	@echo -e "$(CYAN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)        Level RISC-V — ModelSim / Questa Simulation            $(RESET)"
	@echo -e "$(CYAN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)COMPILATION TARGETS:$(RESET)"
	@echo -e "  $(GREEN)compile$(RESET)              Compile all RTL + Testbench sources"
	@echo ""
	@echo -e "$(YELLOW)SIMULATION TARGETS:$(RESET)"
	@echo -e "  $(GREEN)simulate$(RESET)             Run simulation (add $(CYAN)GUI=1$(RESET) for Questa GUI)"
	@echo ""
	@echo -e "$(YELLOW)CONFIG TARGETS:$(RESET)"
	@echo -e "  $(GREEN)show_config$(RESET)          Show current JSON configuration"
	@echo -e "  $(GREEN)validate_config$(RESET)      Validate JSON config and show warnings"
	@echo ""
	@echo -e "$(YELLOW)UTILITY TARGETS:$(RESET)"
	@echo -e "  $(GREEN)resolve_mem$(RESET)          Resolve memory file path for a test"
	@echo -e "  $(GREEN)modelsim_config_summary$(RESET)  Show Makefile variable summary"
	@echo -e "  $(GREEN)clean_modelsim$(RESET)       Clean ModelSim/Questa build artifacts"
	@echo ""
	@echo -e "$(YELLOW)CONFIGURATION FILES:$(RESET)"
	@echo -e "  $(CYAN)script/config/modelsim.json$(RESET)       Main configuration"
	@echo -e "  $(CYAN)script/config/modelsim.local.json$(RESET) Local overrides (git ignored)"
	@echo ""
	@echo -e "$(YELLOW)PROFILES (MODELSIM_PROFILE=...):$(RESET)"
	@echo -e "  $(MAGENTA)fast$(RESET)       Maximum speed, minimal checking"
	@echo -e "  $(MAGENTA)debug$(RESET)      Full debugging features (+acc=full)"
	@echo -e "  $(MAGENTA)coverage$(RESET)   Coverage collection mode"
	@echo -e "  $(MAGENTA)gls$(RESET)        Gate-level simulation settings"
	@echo ""
	@echo -e "$(YELLOW)PARAMETERS:$(RESET)"
	@echo -e "  $(CYAN)TEST_NAME=<name>$(RESET)     Test to run (e.g., rv32ui-p-add)"
	@echo -e "  $(CYAN)MEM_FILE=<path>$(RESET)      Override memory file path"
	@echo -e "  $(CYAN)SIM_TIME=<time>$(RESET)      Simulation duration (default: $(SIM_TIME))"
	@echo -e "  $(CYAN)GUI=1$(RESET)                Launch ModelSim GUI"
	@echo ""
	@echo -e "$(YELLOW)EXAMPLES:$(RESET)"
	@echo -e "  $(GREEN)make compile$(RESET)"
	@echo -e "  $(GREEN)make simulate TEST_NAME=rv32ui-p-add$(RESET)"
	@echo -e "  $(GREEN)make simulate TEST_NAME=rv32ui-p-add GUI=1$(RESET)"
	@echo -e "  $(GREEN)make simulate TEST_NAME=rv32uc-p-rvc SIM_TIME=50000ns$(RESET)"
	@echo -e "  $(GREEN)make compile MODELSIM_PROFILE=debug$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)OUTPUT DIRECTORIES:$(RESET)"
	@echo -e "  Compile logs:  $(CYAN)$(LOG_DIR)/modelsim/<test>/compile.log$(RESET)"
	@echo -e "  Sim logs:      $(CYAN)$(LOG_DIR)/modelsim/<test>/modelsim_run.log$(RESET)"
	@echo -e "  Summary:       $(CYAN)$(LOG_DIR)/modelsim/<test>/summary.json$(RESET)"
	@echo -e "  Waveforms:     $(CYAN)$(LOG_DIR)/modelsim/<test>/waveform.wlf$(RESET)"
	@echo ""
	@echo -e "$(CYAN)══════════════════════════════════════════════════════════════$(RESET)"
# ====== sim/verilator.mk ======
# =========================================
# Level RISC-V — Verilator Simulation
# Optimized for Verilator 5.x + Python Runner
# =========================================

# -----------------------------------------
# Configuration (Python-based)
# -----------------------------------------
# JSON config is now handled by Python runner
# See: script/python/makefile/verilator_config.py
VERILATOR_CONFIG_FILE := $(ROOT_DIR)/script/config/verilator.json

# -----------------------------------------
# Verilator Paths
# -----------------------------------------
# Use provided VERILATOR_LOG_DIR or default to LOG_DIR/verilator/TEST_NAME
VERILATOR_LOG_DIR  ?= $(LOG_DIR)/verilator/$(TEST_NAME)
VERILATOR_INCLUDES := $(addprefix -I, $(INC_DIRS))

# Waiver file for suppressing known UNOPTFLAT warnings
VERILATOR_WAIVER   := $(RTL_DIR)/verilator.vlt

# -----------------------------------------
# Threading Configuration
# -----------------------------------------
# .conf BUILD_THREADS=auto → CPU count; Verilator --build -j only accepts a number ("auto" causes a module error).
ifneq ($(filter auto AUTO,$(CFG_BUILD_THREADS)),)
  _CFG_BUILD_THREADS_RESOLVED := $(shell nproc 2>/dev/null || echo 4)
else
  _CFG_BUILD_THREADS_RESOLVED := $(CFG_BUILD_THREADS)
endif
VERILATOR_THREADS  ?= $(or $(_CFG_BUILD_THREADS_RESOLVED),$(shell nproc 2>/dev/null || echo 4))
BUILD_JOBS         ?= $(VERILATOR_THREADS)

# -----------------------------------------
# Verilator Defines (New naming convention)
# -----------------------------------------

# ===========================================
# LOG CONTROLS (LOG_XXX=1 to enable)
# ===========================================

# Commit trace (Spike-compatible) - LOG_COMMIT=1
ifeq ($(LOG_COMMIT),1)
  SV_DEFINES += +define+LOG_COMMIT
endif

# Pipeline trace (KONATA format) - LOG_PIPELINE=1
ifeq ($(LOG_PIPELINE),1)
  SV_DEFINES += +define+LOG_PIPELINE
endif

# RAM init messages - LOG_RAM=1
ifeq ($(LOG_RAM),1)
  SV_DEFINES += +define+LOG_RAM
endif

# D-cache interface table log (memory.sv → cache_logger) — LOG_CACHE=1
ifeq ($(LOG_CACHE),1)
  SV_DEFINES += +define+LOG_CACHE
endif

# D-cache evict/dirty writeback file (writeback_log.svh) — LOG_WRITEBACK=1
ifeq ($(LOG_WRITEBACK),1)
  SV_DEFINES += +define+LOG_WRITEBACK
endif

# UART file logging - LOG_UART=1
ifeq ($(LOG_UART),1)
  SV_DEFINES += +define+LOG_UART
endif

# GPTimer ARR register trace ($display) - LOG_GPTIMER_ARR=1
ifeq ($(LOG_GPTIMER_ARR),1)
  SV_DEFINES += +define+LOG_GPTIMER_ARR
endif

# Branch Predictor stats - LOG_BP=1
ifeq ($(LOG_BP),1)
  SV_DEFINES += +define+LOG_BP
endif

# Verbose BP logging - LOG_BP_VERBOSE=1
ifeq ($(LOG_BP_VERBOSE),1)
  SV_DEFINES += +define+LOG_BP +define+LOG_BP_VERBOSE
endif

# ===========================================
# TRACE CONTROLS
# ===========================================

# KONATA pipeline visualizer - KONATA_TRACER=1
ifeq ($(KONATA_TRACER),1)
  SV_DEFINES += +define+KONATA_TRACER
endif

# ===========================================
# SIMULATION CONTROLS
# ===========================================

# Fast simulation mode - SIM_FAST=1
ifeq ($(SIM_FAST),1)
  SV_DEFINES += +define+SIM_FAST
  TRACE_FLAGS :=
  TRACE_DEFINE :=
endif

# UART monitoring + auto-stop - SIM_UART_MONITOR=1
ifeq ($(SIM_UART_MONITOR),1)
  SV_DEFINES += +define+SIM_UART_MONITOR
endif

# Coverage collection - SIM_COVERAGE=1
ifeq ($(SIM_COVERAGE),1)
  COVERAGE_FLAGS := --coverage --coverage-line --coverage-toggle
  SV_DEFINES += +define+SIM_COVERAGE
else
  COVERAGE_FLAGS :=
endif

# ===========================================
# BACKWARD COMPATIBILITY (old names)
# ===========================================

# BP_LOG -> LOG_BP
ifeq ($(BP_LOG),1)
  SV_DEFINES += +define+LOG_BP
endif

# BP_VERBOSE -> LOG_BP_VERBOSE  
ifeq ($(BP_VERBOSE),1)
  SV_DEFINES += +define+LOG_BP +define+LOG_BP_VERBOSE
endif

# MINIMAL_SOC -> Minimal peripherals for faster simulation
# Only CPU + RAM + UART + Timer + CLINT active
# MINIMAL_NO_L2=1 skips L2 (memory arbiter only) for faster sim / isolating L2.
ifeq ($(MINIMAL_SOC),1)
  SV_DEFINES += +define+MINIMAL_SOC
  ifeq ($(MINIMAL_NO_L2),1)
    SV_DEFINES += +define+NO_L2_CACHE
  endif
endif

# USE_L2_CACHE -> Enable Yarok14-based L2 non-blocking cache
ifeq ($(USE_L2_CACHE),1)
  SV_DEFINES += +define+USE_L2_CACHE
endif

# NO_L2_CACHE -> Skip L2 (icache/dcache talk to memory_arbiter); for debugging L2 issues
ifeq ($(NO_L2_CACHE),1)
  SV_DEFINES += +define+NO_L2_CACHE
endif

# COVERAGE -> SIM_COVERAGE
ifeq ($(COVERAGE),1)
  COVERAGE_FLAGS := --coverage --coverage-line --coverage-toggle
  SV_DEFINES += +define+SIM_COVERAGE
endif

# Auto-enable for benchmark tests
ifeq ($(TEST_TYPE),bench)
  SV_DEFINES += +define+SIM_UART_MONITOR
endif

# ===========================================
# OTHER FLAGS
# ===========================================

# VPI support - VPI=1
ifeq ($(VPI),1)
  VPI_FLAGS := --vpi
else
  VPI_FLAGS :=
endif

# Hierarchical build - HIERARCHICAL=1
ifeq ($(HIERARCHICAL),1)
  HIER_FLAGS := --hierarchical
else
  HIER_FLAGS :=
endif

# Verilator waveform: enable unless SIM_FAST cleared TRACE_FLAGS (empty means "off";
# `ifndef TRACE_FLAGS` is true for empty vars and would wrongly re-enable FST).
ifeq ($(SIM_FAST),1)
else
  ifndef TRACE_FLAGS
    TRACE_FLAGS := --trace-fst --trace-structs --trace-params
    TRACE_DEFINE := +define+VM_TRACE_FST
  endif
endif

VERILATOR_DEFINE = $(TRACE_DEFINE) $(SV_DEFINES)

# Verilator: üst modül (level_wrapper) parametre geçersiz kılma — örnek:
#   make verilate VERILATOR_GFLAGS="-GVGA_EN=1 -GGPIO_EN=1 -GPLIC_EN=1"
VERILATOR_GFLAGS ?=

# Trace depth control
TRACE_DEPTH ?= 99
ifneq ($(TRACE_FLAGS),)
  TRACE_FLAGS += --trace-depth $(TRACE_DEPTH)
endif

# Multi-threaded FST writing
ifeq ($(TRACE_THREADS),1)
  TRACE_FLAGS += --trace-threads 2
endif

# -----------------------------------------
# Compiler Flags (based on MODE)
# -----------------------------------------
ifeq ($(MODE),debug)
    OPT_LEVEL     := -O0
    CFLAGS_DEBUG  := -g -DDEBUG
    # Debug mode specific verilator flags
    VERILATOR_DEBUG_FLAGS := --debug-check
else ifeq ($(MODE),profile)
    OPT_LEVEL     := -O2
    CFLAGS_DEBUG  := -pg -g
    # Profile mode for gprof/perf
    VERILATOR_DEBUG_FLAGS := --prof-cfuncs --prof-exec
else
    OPT_LEVEL     := -O3
    CFLAGS_DEBUG  :=
    VERILATOR_DEBUG_FLAGS :=
endif

# -----------------------------------------
# Advanced Optimization Flags
# -----------------------------------------
# Output splitting for faster compilation of large designs
OUTPUT_SPLIT       ?= 20000
OUTPUT_SPLIT_CFUNC ?= 5000

# Loop unrolling limits
UNROLL_COUNT       ?= 64
UNROLL_STMTS       ?= 30000

# X-state handling
X_ASSIGN           ?= fast
X_INITIAL          ?= 0

# Use x-initial-edge to better match event-driven simulators
X_INITIAL_EDGE     ?= 1

# -----------------------------------------
# Multi-threading Support
# -----------------------------------------
# THREADS=N enables multi-threaded simulation (N = number of threads)
# Default: 0 (single-threaded for determinism)
THREADS            ?= 0
ifneq ($(THREADS),0)
  THREAD_FLAGS     := --threads $(THREADS) --threads-dpi all
  THREAD_CFLAGS    := -pthread
  THREAD_LDFLAGS   := -lpthread -latomic
else
  THREAD_FLAGS     :=
  THREAD_CFLAGS    :=
  THREAD_LDFLAGS   :=
endif

# -----------------------------------------
# Warning Suppressions (organized by category)
# -----------------------------------------
# Critical warnings that should never be suppressed
# --Wno-fatal allows build to continue despite warnings

# Width-related warnings
NO_WARN_WIDTH = \
    --Wno-WIDTH \
    --Wno-WIDTHEXPAND \
    --Wno-WIDTHTRUNC \
    --Wno-WIDTHCONCAT

# Unused signal warnings
NO_WARN_UNUSED = \
    --Wno-UNDRIVEN \
    --Wno-UNUSED \
    --Wno-UNUSEDPARAM \
    --Wno-UNUSEDSIGNAL

# Style and naming warnings
NO_WARN_STYLE = \
    --Wno-style \
    --Wno-DECLFILENAME \
    --Wno-GENUNNAMED \
    --Wno-VARHIDDEN \
    --Wno-SYMRSVDWORD \
    --Wno-IMPORTSTAR

# Timing and synthesis warnings
NO_WARN_TIMING = \
    --Wno-ASSIGNDLY \
    --Wno-INITIALDLY \
    --Wno-BLKANDNBLK \
    --Wno-BLKLOOPINIT \
    --Wno-TIMESCALEMOD

# Structural warnings
NO_WARN_STRUCT = \
    --Wno-PINCONNECTEMPTY \
    --Wno-MODDUP \
    --Wno-IMPLICIT \
    --Wno-LATCH

# Optimization warnings
NO_WARN_OPT = \
    --Wno-UNOPTFLAT \
    --Wno-UNOPTTHREADS \
    --Wno-ALWCOMBORDER

# Case/enum warnings
NO_WARN_CASE = \
    --Wno-CASEINCOMPLETE \
    --Wno-ENUMVALUE

# Combined warning suppressions for simulation
NO_WARNING = \
    --Wno-fatal \
    --Wno-lint \
    $(NO_WARN_WIDTH) \
    $(NO_WARN_UNUSED) \
    $(NO_WARN_STYLE) \
    $(NO_WARN_TIMING) \
    $(NO_WARN_STRUCT) \
    $(NO_WARN_OPT) \
    $(NO_WARN_CASE)

# Lint-specific - minimal suppressions for maximum feedback
# Only suppress warnings that are truly not useful for lint
NO_WARNING_LINT = \
    --Wno-DECLFILENAME \
    --Wno-IMPORTSTAR

# -----------------------------------------
# Build Flags
# -----------------------------------------
# Lint flags: -Wall enables all warnings, no suppressions for real issues
LINT_FLAGS  = --lint-only -Wall -I$(INC_DIRS) --top-module $(RTL_LEVEL) $(VERILATOR_GFLAGS)
RUN_BIN     := $(OBJ_DIR)/V$(RTL_LEVEL)

# Common verilator flags
# --converge-limit: Allows more iterations for combinational loops
# --x-initial-edge: Triggers initial blocks on the edge for better compatibility
VERILATOR_COMMON_FLAGS = \
    --top-module $(RTL_LEVEL) \
    $(VERILATOR_GFLAGS) \
    $(VERILATOR_INCLUDES) \
    --timing \
    --x-assign $(X_ASSIGN) \
    --x-initial $(X_INITIAL) \
    $(if $(filter 1,$(X_INITIAL_EDGE)),--x-initial-edge,) \
    --converge-limit 100 \
    --error-limit 100 \
    $(if $(wildcard $(VERILATOR_WAIVER)),$(VERILATOR_WAIVER),) \
    $(THREAD_FLAGS) \
    --Mdir $(OBJ_DIR)

# Build-specific flags
VERILATOR_BUILD_FLAGS = \
    --cc \
    --exe $(CPP_TB_FILE) \
    --build \
    -j $(BUILD_JOBS) \
    --output-split $(OUTPUT_SPLIT) \
    --output-split-cfuncs $(OUTPUT_SPLIT_CFUNC) \
    --unroll-count $(UNROLL_COUNT) \
    --unroll-stmts $(UNROLL_STMTS) \
    $(TRACE_FLAGS) \
    $(COVERAGE_FLAGS) \
    $(VPI_FLAGS) \
    $(HIER_FLAGS) \
    $(VERILATOR_DEBUG_FLAGS) \
    --CFLAGS "$(OPT_LEVEL) $(CFLAGS_DEBUG) $(THREAD_CFLAGS) -std=c++17 -Wall -Wextra -Wno-unused-parameter" \
    --LDFLAGS "-lm $(THREAD_LDFLAGS)"

# =========================================
# Targets
# =========================================

.PHONY: dirs lint verilate verilate-fast run_verilator wave clean_verilator verilator_help stats

dirs:
	@$(MKDIR) "$(BUILD_DIR)" "$(OBJ_DIR)" "$(LOG_DIR)"

# ============================================================
# Lint — Verilator --lint-only -Wall (single pass; all warning classes)
# Log: $(LINT_DIR)/verilator/lint.log — filter e.g. grep WIDTH lint.log
# UNOPTFLAT graphs: $(OBJ_DIR)/*_unoptflat.dot after this run (--report-unoptflat)
# Waiver: $(LINT_DIR)/verilator/lint_waiver.vlt
# ============================================================
VERILATOR_LINT_DIR := $(LINT_DIR)/verilator

lint: dirs
	@printf "$(GREEN)[VERILATOR LINT]$(RESET)\n"
	@mkdir -p "$(VERILATOR_LINT_DIR)"
	@printf "$(CYAN)[INFO]$(RESET) Output: $(VERILATOR_LINT_DIR)/\n"
	-@$(VERILATOR) \
		$(LINT_FLAGS) $(VERILATOR_INCLUDES) \
		$(SV_SOURCES) \
		--timing \
		--Wno-fatal \
		--bbox-unsup \
		--report-unoptflat \
		--Mdir "$(OBJ_DIR)" \
		--waiver-output "$(VERILATOR_LINT_DIR)/lint_waiver.vlt" \
		2>&1 | tee "$(VERILATOR_LINT_DIR)/lint.log"
	@echo ""
	@printf "$(CYAN)════════════════════════════════════════$(RESET)\n"
	@printf "$(CYAN)  Lint Summary$(RESET)\n"
	@printf "$(CYAN)════════════════════════════════════════$(RESET)\n"
	@ERR=$$(grep -c "%Error" "$(VERILATOR_LINT_DIR)/lint.log" 2>/dev/null) || ERR=0; \
		if [ "$$ERR" != "0" ] && [ -n "$$ERR" ]; then \
			printf "  $(RED)Errors:   $$ERR$(RESET)\n"; \
		else \
			printf "  $(GREEN)Errors:   0$(RESET)\n"; \
		fi
	@WARN=$$(grep -c "%Warning" "$(VERILATOR_LINT_DIR)/lint.log" 2>/dev/null) || WARN=0; \
		if [ "$$WARN" != "0" ] && [ -n "$$WARN" ]; then \
			printf "  $(YELLOW)Warnings: $$WARN$(RESET)\n"; \
		else \
			printf "  $(GREEN)Warnings: 0$(RESET)\n"; \
		fi
	@printf "$(CYAN)════════════════════════════════════════$(RESET)\n"
	@printf "  Log:    $(VERILATOR_LINT_DIR)/lint.log\n"
	@printf "  Waiver: $(VERILATOR_LINT_DIR)/lint_waiver.vlt\n"
	@printf "$(CYAN)════════════════════════════════════════$(RESET)\n"

# ============================================================
# Verilate — Build C++ model
# VERILATE_FAST=1: dev shortcut — skip if $(RUN_BIN) is newer than first flist entry
#   (can miss edits to other RTL files; CI / tam rebuild: plain `make verilate`).
#   When a build runs, adds $(NO_WARNING) like the old verilate-fast.
#
# After toggling trace (SIM_FAST, TRACE, --trace-fst), Verilator regenerates
# Vlevel_wrapper_classes.mk with new VM_TRACE_FST, but tb_wrapper.o is not pulled in
# as a dependency — make leaves a stale object and the link step fails with
# undefined reference to VerilatedFst::*.  Drop tb_wrapper.o before each verilate.
# ============================================================
verilate: dirs
ifeq ($(VERILATE_FAST),1)
	@if [ -x "$(RUN_BIN)" ] && [ "$(RUN_BIN)" -nt "$(word 1,$(SV_SOURCES))" ]; then \
		printf "$(YELLOW)[SKIP]$(RESET) Binary up-to-date vs first flist source: $(RUN_BIN)\n"; \
	else \
		rm -f "$(OBJ_DIR)/tb_wrapper.o"; \
		printf "$(GREEN)[VERILATING RTL — VERILATE_FAST=1, $(MODE) mode]$(RESET)\n"; \
		$(VERILATOR) \
			$(SV_SOURCES) \
			$(VERILATOR_COMMON_FLAGS) \
			$(VERILATOR_BUILD_FLAGS) \
			$(NO_WARNING) \
			$(VERILATOR_DEFINE); \
		printf "$(GREEN)[SUCCESS]$(RESET) Built: $(RUN_BIN)\n"; \
	fi
else
	@rm -f "$(OBJ_DIR)/tb_wrapper.o"
	@printf "$(GREEN)[VERILATING RTL SOURCES — $(MODE) mode, $(VERILATOR_THREADS) threads]$(RESET)\n"
	$(VERILATOR) \
		$(SV_SOURCES) \
		$(VERILATOR_COMMON_FLAGS) \
		$(VERILATOR_BUILD_FLAGS) \
		$(NO_WARNING) \
		$(VERILATOR_DEFINE)
	@printf "$(GREEN)[SUCCESS]$(RESET) Built: $(RUN_BIN)\n"
endif

# Alias: same as `make verilate VERILATE_FAST=1`
verilate-fast:
	@$(MAKE) --no-print-directory verilate VERILATE_FAST=1

# Rebuild only C++ without re-verilating (for testbench changes)
rebuild-cpp: dirs
	@printf "$(GREEN)[REBUILDING C++ ONLY]$(RESET)\n"
	$(VERILATOR) \
		$(SV_SOURCES) \
		$(VERILATOR_COMMON_FLAGS) \
		$(VERILATOR_BUILD_FLAGS) \
		$(NO_WARNING) \
		$(VERILATOR_DEFINE) \
		--no-verilate
	@printf "$(GREEN)[SUCCESS]$(RESET) Rebuilt: $(RUN_BIN)\n"

# ============================================================
# Run Simulation
# ============================================================
# Coverage data directory
COVERAGE_DATA_DIR := $(LOG_DIR)/verilator/coverage_data

# Python runner
VERILATOR_RUNNER := $(ROOT_DIR)/script/python/makefile/verilator_runner.py

# Memory search directories
VERILATOR_MEM_DIRS := $(BUILD_DIR)/tests/riscv-tests/mem \
                      $(BUILD_DIR)/tests/riscv-arch-test/mem \
                      $(BUILD_DIR)/tests/imperas/mem \
                      $(BUILD_DIR)/tests/bench/mem

# Runner arguments
VERILATOR_RUNNER_ARGS := \
    --test $(TEST_NAME) \
    --bin-path $(RUN_BIN) \
    --log-dir $(VERILATOR_LOG_DIR) \
    --mem-dirs "$(VERILATOR_MEM_DIRS)" \
    --build-dir $(BUILD_DIR)/tests

# Optional arguments
ifdef VERILATOR_PROFILE
    VERILATOR_RUNNER_ARGS += --profile $(VERILATOR_PROFILE)
endif

ifdef MAX_CYCLES
    VERILATOR_RUNNER_ARGS += --max-cycles $(MAX_CYCLES)
endif

ifdef MEM_FILE
    VERILATOR_RUNNER_ARGS += --mem-file $(MEM_FILE)
endif

ifeq ($(TRACE),0)
    VERILATOR_RUNNER_ARGS += --no-trace
endif

ifeq ($(COVERAGE),1)
    VERILATOR_RUNNER_ARGS += --coverage --coverage-file $(COVERAGE_DATA_DIR)/$(TEST_NAME).dat
endif

# Runner "fast mode": no trace + disable coverage override (see verilator_runner merge_config)
ifneq ($(filter 1,$(FAST) $(SIM_FAST)),)
    VERILATOR_RUNNER_ARGS += --fast
endif

ifeq ($(NO_COLOR),1)
    VERILATOR_RUNNER_ARGS += --no-color
endif

ifdef EXCEPTION_PASS_ADDR
    VERILATOR_RUNNER_ARGS += --exception-pass-addr $(EXCEPTION_PASS_ADDR)
endif

ifdef EXCEPTION_FAIL_ADDR
    VERILATOR_RUNNER_ARGS += --exception-fail-addr $(EXCEPTION_FAIL_ADDR)
endif

# Main run target using Python runner
run_verilator: verilate
	@$(PYTHON) $(VERILATOR_RUNNER) $(VERILATOR_RUNNER_ARGS)

# Quick run — incremental verilate (VERILATE_FAST=1)
run_verilator_quick: verilate-fast
	@$(PYTHON) $(VERILATOR_RUNNER) $(VERILATOR_RUNNER_ARGS)

# Dry-run to see command
run_verilator_dry:
	@$(PYTHON) $(VERILATOR_RUNNER) $(VERILATOR_RUNNER_ARGS) --dry-run

# Show current config
verilator_show_config:
	@$(PYTHON) $(VERILATOR_RUNNER) $(VERILATOR_RUNNER_ARGS) --show-config

# Validate config
verilator_validate_config:
	@$(PYTHON) $(ROOT_DIR)/script/python/makefile/verilator_config.py --validate

# ============================================================
# Waveform Viewer
# ============================================================
wave:
	@echo -e "$(YELLOW)[INFO]$(RESET) Opening GTKWave..."
	@if [ -f "$(VERILATOR_LOG_DIR)/waveform.fst" ]; then \
		gtkwave "$(VERILATOR_LOG_DIR)/waveform.fst" & \
	else \
		echo -e "$(RED)[ERROR]$(RESET) No waveform file found at $(VERILATOR_LOG_DIR)/waveform.fst"; \
		echo -e "$(YELLOW)[TIP]$(RESET) Run simulation first with: make run_verilator TEST_NAME=<test>"; \
	fi

# ============================================================
# Statistics and Profiling
# ============================================================
stats: dirs
	@printf "$(GREEN)[GENERATING VERILATOR STATISTICS]$(RESET)\n"
	@mkdir -p "$(LOG_DIR)/verilator"
	$(VERILATOR) \
		--lint-only \
		$(SV_SOURCES) \
		$(VERILATOR_INCLUDES) \
		--top-module $(RTL_LEVEL) \
		--timing \
		--stats \
		--stats-vars \
		$(NO_WARNING) \
		--bbox-unsup \
		2>&1 | tee "$(LOG_DIR)/verilator/stats.log"
	@if [ -f "$(OBJ_DIR)/V$(RTL_LEVEL)__stats.txt" ]; then \
		cp "$(OBJ_DIR)/V$(RTL_LEVEL)__stats.txt" "$(LOG_DIR)/verilator/"; \
	fi
	@printf "$(GREEN)[DONE]$(RESET) Statistics saved to $(LOG_DIR)/verilator/\n"

# ============================================================
# Coverage Analysis
# ============================================================
# Build and run tests with coverage, then generate reports
# Usage:
#   make coverage          - Full coverage run (isa + arch tests)
#   make coverage-quick    - Quick coverage (ISA tests only)
#   make coverage-report   - Generate report from existing data
#   make coverage-html     - Generate HTML coverage report
# ============================================================

.PHONY: coverage coverage-quick coverage-report coverage-html coverage-clean

# Quick coverage with ISA tests only
coverage-quick:
	@echo -e "$(CYAN)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║           Level RISC-V — Quick Coverage Run                 ║$(RESET)"
	@echo -e "$(CYAN)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo -e "$(YELLOW)[1/3] Building with coverage enabled...$(RESET)"
	@$(MAKE) --no-print-directory clean_verilator
	@$(MAKE) --no-print-directory verilate COVERAGE=1
	@echo -e "$(YELLOW)[2/3] Running ISA tests...$(RESET)"
	@$(MAKE) --no-print-directory isa COVERAGE=1
	@echo -e "$(YELLOW)[3/3] Generating coverage report...$(RESET)"
	@$(MAKE) --no-print-directory coverage-html
	@echo -e "$(GREEN)$(SUCCESS) Coverage complete! Open results/coverage/index.html$(RESET)"

# Full coverage with all compliance tests
coverage:
	@echo -e "$(CYAN)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║           Level RISC-V — Full Coverage Analysis             ║$(RESET)"
	@echo -e "$(CYAN)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo -e "$(YELLOW)[1/4] Building with coverage enabled...$(RESET)"
	@$(MAKE) --no-print-directory clean_verilator
	@$(MAKE) --no-print-directory verilate COVERAGE=1
	@echo -e "$(YELLOW)[2/4] Running ISA tests...$(RESET)"
	@$(MAKE) --no-print-directory isa COVERAGE=1
	@echo -e "$(YELLOW)[3/4] Running Architecture tests...$(RESET)"
	@$(MAKE) --no-print-directory arch COVERAGE=1
	@echo -e "$(YELLOW)[4/4] Generating coverage report...$(RESET)"
	@$(MAKE) --no-print-directory coverage-html
	@echo -e "$(GREEN)$(SUCCESS) Coverage complete! Open results/coverage/index.html$(RESET)"

# Generate text-based coverage report
coverage-report:
	@if [ -f "$(LOG_DIR)/verilator/coverage.dat" ]; then \
		mkdir -p "$(LOG_DIR)/verilator/coverage_annotated"; \
		verilator_coverage --annotate "$(LOG_DIR)/verilator/coverage_annotated" \
			"$(LOG_DIR)/verilator/coverage.dat"; \
		echo -e "$(GREEN)[OK]$(RESET) Coverage annotations: $(LOG_DIR)/verilator/coverage_annotated/"; \
	else \
		echo -e "$(RED)[ERROR]$(RESET) No coverage data. Run: make coverage"; \
	fi

# Generate HTML coverage report
COVERAGE_HTML_DIR := $(RESULTS_DIR)/coverage

coverage-html:
	@mkdir -p $(COVERAGE_HTML_DIR)
	@# First, merge all individual coverage files
	@if [ -d "$(COVERAGE_DATA_DIR)" ] && [ -n "$$(ls -A $(COVERAGE_DATA_DIR)/*.dat 2>/dev/null)" ]; then \
		echo -e "$(YELLOW)[COV] Merging coverage data files...$(RESET)"; \
		verilator_coverage --write "$(LOG_DIR)/verilator/coverage.dat" \
			$(COVERAGE_DATA_DIR)/*.dat 2>/dev/null; \
		COV_COUNT=$$(ls -1 $(COVERAGE_DATA_DIR)/*.dat 2>/dev/null | wc -l); \
		echo -e "$(GREEN)[OK]$(RESET) Merged $$COV_COUNT coverage files"; \
	fi
	@if [ -f "$(LOG_DIR)/verilator/coverage.dat" ]; then \
		echo -e "$(YELLOW)[COV] Generating HTML coverage report...$(RESET)"; \
		verilator_coverage --annotate-all --annotate-min 1 \
			--write-info "$(COVERAGE_HTML_DIR)/coverage.info" \
			"$(LOG_DIR)/verilator/coverage.dat" 2>/dev/null || true; \
		if command -v genhtml >/dev/null 2>&1; then \
			genhtml "$(COVERAGE_HTML_DIR)/coverage.info" \
				--output-directory "$(COVERAGE_HTML_DIR)" \
				--title "Level RISC-V Coverage" \
				--legend --highlight 2>/dev/null; \
			echo -e "$(GREEN)[OK]$(RESET) HTML report: $(COVERAGE_HTML_DIR)/index.html"; \
		else \
			echo -e "$(YELLOW)[INFO]$(RESET) Install lcov for HTML reports: sudo apt install lcov"; \
			verilator_coverage --annotate "$(COVERAGE_HTML_DIR)/annotated" \
				"$(LOG_DIR)/verilator/coverage.dat"; \
			echo -e "$(GREEN)[OK]$(RESET) Text annotations: $(COVERAGE_HTML_DIR)/annotated/"; \
		fi; \
		echo -e "$(CYAN)[COV] Coverage Summary:$(RESET)"; \
		verilator_coverage --rank "$(LOG_DIR)/verilator/coverage.dat" 2>/dev/null | head -30 || true; \
	else \
		echo -e "$(RED)[ERROR]$(RESET) No coverage data found."; \
		echo -e "$(YELLOW)[HINT]$(RESET) Run: make coverage-quick"; \
	fi

# Clean coverage data
coverage-clean:
	@echo -e "$(RED)[CLEAN]$(RESET) Removing coverage data..."
	@$(RM) "$(LOG_DIR)/verilator/coverage.dat"
	@$(RM) "$(LOG_DIR)/verilator/coverage_annotated"
	@$(RM) "$(COVERAGE_DATA_DIR)"
	@$(RM) "$(COVERAGE_HTML_DIR)"
	@echo -e "$(GREEN)[OK]$(RESET) Coverage data cleaned"

# ============================================================
# Clean
# ============================================================
clean_verilator:
	@echo -e "$(RED)[CLEANING VERILATOR]$(RESET)"
	@$(RM) "$(OBJ_DIR)"
	@$(RM) "$(LOG_DIR)/verilator"
	@echo -e "$(GREEN)Clean complete.$(RESET)"

# Deep clean - also remove dependency files (obj_dir only; never scan build/tests)
clean_verilator_deep: clean_verilator
	@echo -e "$(RED)[DEEP CLEANING]$(RESET)"
	@find "$(OBJ_DIR)" -name "*.d" -delete 2>/dev/null || true
	@find "$(OBJ_DIR)" -name "*.o" -delete 2>/dev/null || true

# Clean ccache - use this when encountering strange C++ compilation errors
# after Verilator upgrade or when build fails with "invalid preprocessing directive"
clean_ccache:
	@echo -e "$(YELLOW)[CLEANING CCACHE]$(RESET) Clearing compiler cache..."
	@if command -v ccache >/dev/null 2>&1; then \
		ccache -C; \
		echo -e "$(GREEN)[OK]$(RESET) ccache cleared successfully"; \
		ccache -s | head -15; \
	else \
		echo -e "$(YELLOW)[INFO]$(RESET) ccache not installed"; \
	fi

# Nuclear clean - everything including ccache
clean_verilator_nuclear: clean_verilator_deep clean_ccache
	@echo -e "$(RED)[NUCLEAR CLEAN COMPLETE]$(RESET)"

# UART programmer: payload .mem → binary stream; Verilator tb_uart_programmer RAM R/W + optional UART golden
.PHONY: uart_programmer_verify
uart_programmer_verify:
	bash "$(ROOT_DIR)/script/shell/uart_programmer_verify.sh"

# ============================================================
# Help
# ============================================================
verilator_help:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)            Level RISC-V — Verilator Simulation               $(RESET)"
	@echo -e "$(GREEN)              Verilator 5.x + Python Runner                   $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Lint Targets:$(RESET)"
	@echo -e "  $(GREEN)lint              $(RESET)– Verilator --lint-only -Wall (all classes, one pass)"
	@echo -e ""
	@echo -e "$(YELLOW)Build Targets:$(RESET)"
	@echo -e "  $(GREEN)verilate          $(RESET)– Build C++ simulation model"
	@echo -e "  $(GREEN)verilate-fast     $(RESET)– Alias for VERILATE_FAST=1 (see verilate)"
	@echo -e "  $(GREEN)rebuild-cpp       $(RESET)– Rebuild C++ without re-verilating"
	@echo -e "  $(GREEN)stats             $(RESET)– Generate design statistics"
	@echo -e ""
	@echo -e "$(YELLOW)Run Targets:$(RESET)"
	@echo -e "  $(GREEN)run_verilator       $(RESET)– Build and run simulation (Python runner)"
	@echo -e "  $(GREEN)run_verilator_quick $(RESET)– Quick run (skip rebuild if up-to-date)"
	@echo -e "  $(GREEN)run_verilator_dry   $(RESET)– Show command without running"
	@echo -e "  $(GREEN)wave                $(RESET)– Open GTKWave waveform viewer"
	@echo -e ""
	@echo -e "$(YELLOW)Config Targets:$(RESET)"
	@echo -e "  $(GREEN)verilator_show_config    $(RESET)– Show current JSON config"
	@echo -e "  $(GREEN)verilator_validate_config$(RESET)– Validate JSON config"
	@echo -e ""
	@echo -e "$(YELLOW)Coverage Targets:$(RESET)"
	@echo -e "  $(GREEN)coverage          $(RESET)– Full coverage run"
	@echo -e "  $(GREEN)coverage-quick    $(RESET)– Quick coverage (ISA only)"
	@echo -e "  $(GREEN)coverage-html     $(RESET)– Generate HTML report"
	@echo -e ""
	@echo -e "$(YELLOW)Clean Targets:$(RESET)"
	@echo -e "  $(GREEN)clean_verilator      $(RESET)– Clean build files"
	@echo -e "  $(GREEN)clean_verilator_deep $(RESET)– Deep clean including .d/.o files"
	@echo -e "  $(GREEN)clean_ccache         $(RESET)– Clear compiler cache (fix build errors)"
	@echo -e "  $(GREEN)clean_verilator_nuclear$(RESET)– Nuclear clean (everything + ccache)"
	@echo -e ""
	@echo -e "$(YELLOW)Configuration:$(RESET)"
	@echo -e "  $(CYAN)Config file$(RESET): script/config/verilator.json"
	@echo -e "  $(CYAN)Local override$(RESET): script/config/verilator.local.json"
	@echo -e ""
	@echo -e "$(YELLOW)CLI Parameters (override JSON):$(RESET)"
	@echo -e "  $(CYAN)VERILATOR_PROFILE$(RESET)=<name>  – Use profile (fast/debug/coverage/benchmark)"
	@echo -e "  $(CYAN)TEST_NAME$(RESET)=<name>         – Test to run"
	@echo -e "  $(CYAN)MAX_CYCLES$(RESET)=<n>           – Max cycles (default: from JSON)"
	@echo -e "  $(CYAN)FAST$(RESET)=1                   – Fast mode (no trace)"
	@echo -e "  $(CYAN)COVERAGE$(RESET)=1               – Enable coverage"
	@echo -e "  $(CYAN)TRACE$(RESET)=0                  – Disable trace"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make run_verilator TEST_NAME=rv32ui-p-add"
	@echo -e "  make run_verilator TEST_NAME=coremark VERILATOR_PROFILE=benchmark"
	@echo -e "  make run_verilator TEST_NAME=dhrystone FAST=1 MAX_CYCLES=1000000"
	@echo -e ""
	@echo -e "  $(CYAN)VPI$(RESET)=1                  – Enable VPI support"
	@echo -e "  $(CYAN)HIERARCHICAL$(RESET)=1         – Enable hierarchical build"
	@echo -e "  $(CYAN)TRACE_DEPTH$(RESET)=<n>        – Signal trace depth (default: 99)"
	@echo -e "  $(CYAN)TRACE_THREADS$(RESET)=1        – Multi-threaded FST writing"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make run_verilator TEST_NAME=rv32ui-p-add"
	@echo -e "  make run_verilator TEST_NAME=rv32ui-p-add PROFILE=debug"
	@echo -e "  make bench PROFILE=fast                        # Fast benchmark"
	@echo -e "  make isa PROFILE=coverage                      # With coverage"
	@echo -e "  make verilate PROFILE=benchmark BP_LOG=1       # Profile + override"
	@echo -e ""

# ============================================================
# Configuration Management (Python-based)
# ============================================================
.PHONY: config-show config-profiles config-edit

config-show: verilator_show_config

config-profiles:
	@$(PYTHON) $(ROOT_DIR)/script/python/makefile/verilator_config.py --help | grep -A20 "Profiller:"

config-edit:
	@echo -e "$(CYAN)[INFO]$(RESET) Edit config: $(VERILATOR_CONFIG_FILE)"
	@echo -e "$(CYAN)[INFO]$(RESET) For local overrides, create: $(ROOT_DIR)/script/config/verilator.local.json"
	@$${EDITOR:-nano} "$(VERILATOR_CONFIG_FILE)"

# ====== sim/spike.mk ======
# =========================================
# Level RISC-V — Spike Golden Model
# =========================================
# Spike simulator is only used via run_test.mk.
# This file is only for standalone Spike runs and help.
# =========================================

.PHONY: spike_run spike_all spike_help clean_spike

# -----------------------------------------
# Spike Log Directory
# -----------------------------------------
SPIKE_LOG_DIR := $(LOG_DIR)/spike/$(TEST_NAME)

# ============================================================
# Run Spike for a specific test
# ============================================================
spike_run:
	@echo -e "$(YELLOW)[SPIKE] Running test: $(TEST_NAME)$(RESET)"
	@ELF_FILE="$(ELF_DIR)/$(TEST_NAME)"; \
	if [ ! -f "$$ELF_FILE" ]; then \
		echo -e "$(RED)[ERROR] ELF not found: $$ELF_FILE$(RESET)"; \
		exit 1; \
	fi; \
	mkdir -p "$(SPIKE_LOG_DIR)"; \
	echo -e "$(YELLOW)[INFO]$(RESET) Log file -> $(SPIKE_LOG_DIR)/spike.log"; \
	$(SPIKE) $(SPIKE_ARGS) "$$ELF_FILE" 2>&1 | tee "$(SPIKE_LOG_DIR)/spike.log"

# ============================================================
# Run all ISA ELF tests
# ============================================================
spike_all:
	@echo -e "$(YELLOW)[SPIKE] Running all ISA ELF tests...$(RESET)"
	@mkdir -p "$(LOG_DIR)/spike"
	@for f in $(BUILD_DIR)/tests/riscv-tests/elf/*; do \
		if [ -f "$$f" ]; then \
			name=$$(basename "$$f"); \
			echo -e "$(CYAN) Running $$name$(RESET)"; \
			$(SPIKE) $(SPIKE_ARGS) "$$f" > "$(LOG_DIR)/spike/$${name}_spike.log" 2>&1 || true; \
		fi; \
	done
	@echo -e "$(GREEN)[DONE] All Spike runs completed.$(RESET)"

# ============================================================
# Clean Spike logs
# ============================================================
clean_spike:
	@echo -e "$(RED)[CLEANING SPIKE LOGS]$(RESET)"
	@$(RM) "$(LOG_DIR)/spike"
	@echo -e "$(GREEN)Spike clean complete.$(RESET)"

# ============================================================
# Help
# ============================================================
spike_help:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)              Level RISC-V — Spike Golden Model               $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Main Targets:$(RESET)"
	@echo -e "  $(GREEN)spike_run    $(RESET)– Run a specific test on Spike"
	@echo -e "  $(GREEN)spike_all    $(RESET)– Run all ELF tests"
	@echo -e "  $(GREEN)clean_spike  $(RESET)– Clean Spike logs"
	@echo -e ""
	@echo -e "$(YELLOW)Parameters:$(RESET)"
	@echo -e "  TEST_NAME=<name>  – Select specific ISA test"
	@echo -e "  SPIKE_ISA=<arch>  – ISA mode (default: RV32IMC)"
	@echo -e "  SPIKE_PC=<addr>   – Start address (default: 0x80000000)"
	@echo -e ""
	@echo -e "$(YELLOW)Example:$(RESET)"
	@echo -e "  make spike_run TEST_NAME=rv32ui-p-add"
	@echo -e ""
	@echo -e "$(YELLOW)Note:$(RESET)"
	@echo -e "  For RTL vs Spike comparison, use: make run TEST_NAME=..."
	@echo -e ""

# ====== test/run_test.mk ======
# ============================================================
# Level RISC-V Test Runner
# ============================================================
# Usage:
#   make run T=rv32ui-p-add         # Auto-detects TEST_TYPE=isa
#   make run T=C-ADDI-01            # Auto-detects TEST_TYPE=arch
#   make run T=median               # Auto-detects TEST_TYPE=bench
#   make run T=I-ADD-01             # Auto-detects TEST_TYPE=imperas
#   make run TEST_NAME=xxx TEST_TYPE=yyy  # Manual override
#
# Python Mode (recommended):
#   make run T=rv32ui-p-add USE_PYTHON=1
#   LEVEL_DEBUG=1 make run T=rv32ui-p-add USE_PYTHON=1  # With debug log
# ============================================================

# Python Test Runner
TEST_RUNNER_SCRIPT := $(SCRIPT_DIR)/python/makefile/test_runner.py
USE_PYTHON ?= 1

# Allow short form variable `T` to specify the test name (e.g. `make run T=rv32ui-p-add`).
# Prefer `T` if provided; otherwise fall back to any pre-existing `TEST_NAME`.
TEST_NAME := $(if $(T),$(T),$(TEST_NAME))

# Recompute per-test paths now that TEST_NAME is finalized so CLI `T=` works
TEST_LOG_DIR := $(RESULTS_DIR)/logs/$(SIM)/$(TEST_NAME)
RTL_LOG_DIR  := $(TEST_LOG_DIR)
# Sim outputs (commit trace, UART, …) live here; Verilator runner wipes this dir before sim.
SPIKE_LOG    := $(TEST_LOG_DIR)/spike.log
DIFF_LOG     := $(TEST_LOG_DIR)/diff.log
# Must NOT live under TEST_LOG_DIR — prepare_log_dir removes that tree before RTL sim.
TEST_ARTIFACT_DIR := $(TEST_WORK_DIR)/$(TEST_NAME)
RTL_CONSOLE_LOG   := $(TEST_ARTIFACT_DIR)/rtl_console.log
REPORT_FILE       := $(TEST_ARTIFACT_DIR)/test_report.txt

# -----------------------------------------
# File-based TEST_TYPE Auto-detection
# -----------------------------------------
# If TEST_TYPE was auto-detected (not user-specified), verify by checking
# if the test file actually exists in the expected directory.
# This provides a fallback if pattern matching fails.

define DETECT_TEST_TYPE_FROM_FILES
$(if $(wildcard $(BUILD_DIR)/tests/riscv-tests/elf/$(TEST_NAME)),isa,\
$(if $(wildcard $(BUILD_DIR)/tests/riscv-tests/elf/$(TEST_NAME).elf),isa,\
$(if $(wildcard $(BUILD_DIR)/tests/riscv-arch-test/elf/$(TEST_NAME).elf),arch,\
$(if $(wildcard $(BUILD_DIR)/tests/imperas/elf/$(TEST_NAME).elf),imperas,\
$(if $(wildcard $(BUILD_DIR)/tests/riscv-benchmarks/elf/$(TEST_NAME)),bench,\
$(if $(wildcard $(BUILD_DIR)/tests/dhrystone/$(TEST_NAME).elf),dhrystone,\
$(if $(wildcard $(BUILD_DIR)/tests/coremark/$(TEST_NAME).elf),coremark,\
$(if $(wildcard $(BUILD_DIR)/tests/embench/elf/$(TEST_NAME).elf),embench,\
$(if $(wildcard $(BUILD_DIR)/tests/torture/elf/$(TEST_NAME).elf),torture,\
$(if $(wildcard $(BUILD_DIR)/tests/custom/$(TEST_NAME).elf),custom,\
$(TEST_TYPE)))))))))))
endef

# Apply file-based detection as a verification/fallback
TEST_TYPE := $(strip $(call DETECT_TEST_TYPE_FROM_FILES))

# -----------------------------------------
# Test Type Based Paths
# -----------------------------------------
ifeq ($(TEST_TYPE),bench)
    TEST_ROOT := $(BUILD_DIR)/tests/riscv-benchmarks
else ifeq ($(TEST_TYPE),isa)
    TEST_ROOT := $(BUILD_DIR)/tests/riscv-tests
else ifeq ($(TEST_TYPE),arch)
    TEST_ROOT := $(BUILD_DIR)/tests/riscv-arch-test
else ifeq ($(TEST_TYPE),imperas)
    TEST_ROOT := $(BUILD_DIR)/tests/imperas
else ifeq ($(TEST_TYPE),dhrystone)
    TEST_ROOT := $(BUILD_DIR)/tests/dhrystone
else ifeq ($(TEST_TYPE),coremark)
    TEST_ROOT := $(BUILD_DIR)/tests/coremark
else ifeq ($(TEST_TYPE),embench)
    TEST_ROOT := $(BUILD_DIR)/tests/embench
else ifeq ($(TEST_TYPE),torture)
    TEST_ROOT := $(BUILD_DIR)/tests/torture
else ifeq ($(TEST_TYPE),riscv-dv)
    TEST_ROOT := $(BUILD_DIR)/tests/riscv-dv
else ifeq ($(TEST_TYPE),custom)
    TEST_ROOT := $(BUILD_DIR)/tests/custom
else ifneq ($(MEM_DIR),)
    # If MEM_DIR is provided, skip TEST_TYPE validation (custom paths)
    TEST_ROOT := $(dir $(MEM_DIR))
else
    $(error Invalid TEST_TYPE="$(TEST_TYPE)". Use: isa, bench, arch, imperas, dhrystone, embench, torture, riscv-dv, or custom)
endif

# Derived paths from TEST_ROOT (can be overridden)
ELF_DIR  ?= $(TEST_ROOT)/elf
MEM_DIR  ?= $(TEST_ROOT)/mem
HEX_DIR  ?= $(TEST_ROOT)/hex
DUMP_DIR ?= $(TEST_ROOT)/dump
ADDR_DIR ?= $(TEST_ROOT)/pass_fail_addr

# ELF file extension (arch, imperas, dhrystone, embench, torture, riscv-dv, custom use .elf)
ifeq ($(TEST_TYPE),arch)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),imperas)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),dhrystone)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),embench)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),torture)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),riscv-dv)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),custom)
    ELF_EXT := .elf
else
    ELF_EXT :=
endif
ELF_FILE := $(ELF_DIR)/$(TEST_NAME)$(ELF_EXT)

# -----------------------------------------
# Exception Address Override
# -----------------------------------------
EXCEPTION_ADDR_FILE := $(SIM_DIR)/test/exception_test.flist

define GET_EXCEPTION_ADDR
$(shell awk '$$1=="$(1)" {print $$2" " $$3}' $(EXCEPTION_ADDR_FILE) 2>/dev/null)
endef

# =========================================
# Targets
# =========================================

.PHONY: run run_python run_make test_prepare run_rtl run_spike compare_logs test_report clean_test list_tests help_test run_flist


# ============================================================
# Main Pipeline
# ============================================================
ifeq ($(USE_PYTHON),1)
run: run_python
else
run: run_make
endif

# Ordered chain (safe with make -j): RTL wipes TEST_LOG_DIR; REPORT_FILE/RTL_CONSOLE_LOG stay in TEST_ARTIFACT_DIR
run_make: test_report
run_rtl: test_prepare
run_spike: run_rtl
compare_logs: run_spike
test_report: compare_logs

# Python-based test runner (USE_PYTHON=1)
run_python:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Level RISC-V Test Runner (Python Mode)$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@EXC_ADDRS="$(call GET_EXCEPTION_ADDR,$(TEST_NAME))"; \
	if [ -n "$$EXC_ADDRS" ]; then \
		echo -e "$(YELLOW)[INFO]$(RESET) Exception override for $(TEST_NAME): $$EXC_ADDRS"; \
		set -- $$EXC_ADDRS; \
		python3 $(TEST_RUNNER_SCRIPT) \
			--test-name "$(TEST_NAME)" \
			--test-type "$(TEST_TYPE)" \
			--simulator "$(SIM)" \
			--build-dir "$(BUILD_DIR)" \
			--sim-dir "$(SIM_DIR)" \
			--results-dir "$(RESULTS_DIR)" \
			--test-log-dir "$(TEST_LOG_DIR)" \
			--max-cycles $(MAX_CYCLES) \
			--exception-pass-addr "$$1" \
			--exception-fail-addr "$$2" \
			$(if $(filter 1,$(LOG_COMMIT)),--log-commit,) \
			$(if $(filter 1,$(LOG_BP)),--log-bp,) \
			$(if $(filter 1,$(KONATA_TRACER)),--konata-tracer,) \
			$(if $(filter 1,$(TRACE)),--trace,) \
			$(if $(filter 1,$(CFG_SPIKE)),--enable-spike,--no-spike) \
			$(if $(filter 1,$(CFG_COMPARE)),--enable-compare,--no-compare) \
			$(if $(SKIP_CSR),--skip-csr,) \
			$(if $(RESYNC),--resync --resync-window $(or $(RESYNC_WINDOW),8),); \
	else \
		python3 $(TEST_RUNNER_SCRIPT) \
			--test-name "$(TEST_NAME)" \
			--test-type "$(TEST_TYPE)" \
			--simulator "$(SIM)" \
			--build-dir "$(BUILD_DIR)" \
			--sim-dir "$(SIM_DIR)" \
			--results-dir "$(RESULTS_DIR)" \
			--test-log-dir "$(TEST_LOG_DIR)" \
			--max-cycles $(MAX_CYCLES) \
			$(if $(filter 1,$(LOG_COMMIT)),--log-commit,) \
			$(if $(filter 1,$(LOG_BP)),--log-bp,) \
			$(if $(filter 1,$(KONATA_TRACER)),--konata-tracer,) \
			$(if $(filter 1,$(TRACE)),--trace,) \
			$(if $(filter 1,$(CFG_SPIKE)),--enable-spike,--no-spike) \
			$(if $(filter 1,$(CFG_COMPARE)),--enable-compare,--no-compare) \
			$(if $(SKIP_CSR),--skip-csr,) \
			$(if $(RESYNC),--resync --resync-window $(or $(RESYNC_WINDOW),8),); \
	fi
	@echo -e "$(GREEN)$(SUCCESS) Python test runner completed$(RESET)"

# ============================================================
# 1 Prepare Test Environment
# ============================================================
test_prepare:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Level RISC-V Test Runner$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Test Name   : $(TEST_NAME)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Simulator   : $(SIM)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Max Cycles  : $(MAX_CYCLES)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Test Log Dir: $(TEST_LOG_DIR)"
	@echo -e "$(YELLOW)[INFO]$(RESET) RTL Log Dir : $(RTL_LOG_DIR)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Artifacts   : $(TEST_ARTIFACT_DIR)"
	@echo -e "$(YELLOW)[INFO]$(RESET) ELF File     : $(ELF_FILE)"
	@echo -e "$(YELLOW)[INFO]$(RESET) MEM File     : $(MEM_DIR)/$(TEST_NAME).mem"
	@echo -e "$(YELLOW)[INFO]$(RESET) HEX File     : $(HEX_DIR)/$(TEST_NAME).hex"
	@echo -e "$(YELLOW)[INFO]$(RESET) DUMP File    : $(DUMP_DIR)/$(TEST_NAME).dump"
	@echo -e "$(YELLOW)[INFO]$(RESET) ADDR File    : $(ADDR_DIR)/$(TEST_NAME)_addr.txt"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@# Clean previous test logs to avoid stale data
	@if [ -d "$(RTL_LOG_DIR)" ]; then \
		echo -e "$(CYAN)[CLEAN]$(RESET) Removing previous logs: $(RTL_LOG_DIR)"; \
		rm -rf "$(RTL_LOG_DIR)"; \
	fi
	@rm -rf "$(TEST_ARTIFACT_DIR)"
	@$(MKDIR) "$(TEST_LOG_DIR)" "$(TEST_WORK_DIR)" "$(TEST_ARTIFACT_DIR)"
	@echo "=== Level Test Report ==="        >  $(REPORT_FILE)
	@echo "Test: $(TEST_NAME)"              >> $(REPORT_FILE)
	@echo "Date: $$(date)"                  >> $(REPORT_FILE)
	@echo "Simulator: $(SIM)"               >> $(REPORT_FILE)
	@echo ""                                >> $(REPORT_FILE)

# ============================================================
# 2 Run RTL Simulation
# ============================================================
run_rtl:
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Step 1/3: Running RTL Simulation$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
ifeq ($(SIM),verilator)
	@EXC_ADDRS="$(call GET_EXCEPTION_ADDR,$(TEST_NAME))"; \
	if [ -n "$$EXC_ADDRS" ]; then \
		echo -e "$(YELLOW)[INFO]$(RESET) Exception override for $(TEST_NAME): $$EXC_ADDRS"; \
		set -- $$EXC_ADDRS; \
		$(MAKE) --no-print-directory run_verilator \
			TEST_NAME=$(TEST_NAME) MAX_CYCLES=$(MAX_CYCLES) \
			VERILATOR_LOG_DIR=$(RTL_LOG_DIR) \
			MEM_FILE=$(MEM_DIR)/$(TEST_NAME).mem \
			ADDR_FILE=$(ADDR_DIR)/$(TEST_NAME)_addr.txt \
			EXCEPTION_PASS_ADDR="$$1" \
			EXCEPTION_FAIL_ADDR="$$2" \
			2>&1 | tee $(RTL_CONSOLE_LOG); \
	else \
		$(MAKE) --no-print-directory run_verilator \
			TEST_NAME=$(TEST_NAME) MAX_CYCLES=$(MAX_CYCLES) \
			VERILATOR_LOG_DIR=$(RTL_LOG_DIR) \
			MEM_FILE=$(MEM_DIR)/$(TEST_NAME).mem \
			ADDR_FILE=$(ADDR_DIR)/$(TEST_NAME)_addr.txt \
			2>&1 | tee $(RTL_CONSOLE_LOG); \
	fi; \
	RTL_EXIT=$$?; \
	echo "RTL_EXIT_CODE=$$RTL_EXIT" >> $(REPORT_FILE); \
	if [ $$RTL_EXIT -ne 0 ]; then \
		echo -e "$(RED)[ERROR]$(RESET) RTL simulation failed with exit code $$RTL_EXIT"; \
		exit $$RTL_EXIT; \
	fi
else ifeq ($(SIM),modelsim)
	@$(MAKE) --no-print-directory simulate TEST_NAME=$(TEST_NAME) GUI=0 \
		2>&1 | tee $(RTL_CONSOLE_LOG); \
	RTL_EXIT=$$?; \
	echo "RTL_EXIT_CODE=$$RTL_EXIT" >> $(REPORT_FILE); \
	if [ $$RTL_EXIT -ne 0 ]; then \
		echo -e "$(RED)[ERROR]$(RESET) RTL simulation failed with exit code $$RTL_EXIT"; \
		exit $$RTL_EXIT; \
	fi
else
	@echo -e "$(RED)$(ERROR) Unknown simulator: $(SIM)$(RESET)"
	@echo -e "   Valid options: verilator, modelsim"
	@exit 1
endif
	@echo -e "$(GREEN)$(SUCCESS) RTL simulation complete$(RESET)"

# ============================================================
# 3 Run Spike Golden Reference
# ============================================================
run_spike:
ifeq ($(CFG_SPIKE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)  Step 2/3: Spike comparison disabled (benchmark mode)$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
else
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Step 2/3: Running Spike Golden Model$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MKDIR) "$(dir $(SPIKE_LOG))"

	@EXC_ADDRS="$(call GET_EXCEPTION_ADDR,$(TEST_NAME))"; \
	if [ -n "$$EXC_ADDRS" ]; then \
		echo -e "$(YELLOW)[INFO]$(RESET) Exception override for $(TEST_NAME): $$EXC_ADDRS"; \
		set -- $$EXC_ADDRS; \
		PASS_ADDR="$$1"; \
		FAIL_ADDR="$$2"; \
	else \
		ADDR_FILE="$(ADDR_DIR)/$(TEST_NAME)_addr.txt"; \
		if [ ! -f "$$ADDR_FILE" ]; then \
			echo -e "$(RED)[ERROR]$(RESET) Address file not found: $$ADDR_FILE"; \
			exit 1; \
		fi; \
		read PASS_ADDR FAIL_ADDR < "$$ADDR_FILE"; \
	fi; \
	echo -e "$(GREEN)$(SUCCESS) Using PASS address: $$PASS_ADDR$(RESET)"; \
	DEBUG_CMD="$(BUILD_DIR)/test_work/$(TEST_NAME)_spike.cmd"; \
	echo -e "until pc 0 $$PASS_ADDR\nquit" > "$$DEBUG_CMD"; \
	echo -e "$(CYAN)[DEBUG]$(RESET) Spike args: $(SPIKE_ARGS)"; \
	$(SPIKE) -d $(SPIKE_ARGS) \
		--debug-cmd="$$DEBUG_CMD" \
		$(ELF_FILE) \
		2>&1 | tee $(SPIKE_LOG); \
	SPIKE_EXIT=$$?; \
	echo "SPIKE_EXIT_CODE=$$SPIKE_EXIT" >> $(REPORT_FILE); \
	if [ $$SPIKE_EXIT -ne 0 ]; then \
		echo -e "$(YELLOW)[WARNING]$(RESET) Spike exited with code $$SPIKE_EXIT (may be normal)"; \
	fi; \
	echo -e "$(GREEN)$(SUCCESS) Spike execution complete$(RESET)"
endif

# ============================================================
# 4 Compare Logs
# ============================================================
compare_logs:
ifeq ($(CFG_COMPARE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)  Step 3/3: Log comparison disabled (benchmark mode)$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo "COMPARE_STATUS=SKIPPED" >> $(REPORT_FILE)
else ifeq ($(CFG_SPIKE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)  Step 3/3: Log comparison skipped (no Spike run)$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo "COMPARE_STATUS=SKIPPED" >> $(REPORT_FILE)
else
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Step 3/3: Comparing RTL vs Spike$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@RTL_LOG_PATH="$(RTL_LOG_DIR)/commit_trace.log"; \
	echo -e "$(CYAN)[DEBUG]$(RESET) RTL log: $$RTL_LOG_PATH"; \
	echo -e "$(CYAN)[DEBUG]$(RESET) Spike log: $(SPIKE_LOG)"; \
	if [ ! -f "$$RTL_LOG_PATH" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) RTL log not found"; \
		echo "COMPARE_STATUS=RTL_LOG_MISSING" >> $(REPORT_FILE); \
		exit 1; \
	fi; \
	if [ ! -f "$(SPIKE_LOG)" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Spike log not found"; \
		echo "COMPARE_STATUS=SPIKE_LOG_MISSING" >> $(REPORT_FILE); \
		exit 1; \
	fi; \
	EXTRA_ARGS=""; \
	[ -f "$(DUMP_DIR)/$(TEST_NAME).dump" ] && EXTRA_ARGS="$$EXTRA_ARGS --dump $(DUMP_DIR)/$(TEST_NAME).dump"; \
	[ -f "$(ADDR_DIR)/$(TEST_NAME)_addr.txt" ] && EXTRA_ARGS="$$EXTRA_ARGS --addr $(ADDR_DIR)/$(TEST_NAME)_addr.txt"; \
	$(MKDIR) "$(dir $(DIFF_LOG))"; \
	python3 $(SCRIPT_DIR)/python/makefile/compare_logs.py \
		--rtl "$$RTL_LOG_PATH" \
		--spike "$(SPIKE_LOG)" \
		--output "$(DIFF_LOG)" \
		--test-name "$(TEST_NAME)" \
		$$EXTRA_ARGS \
		$(if $(SKIP_CSR),--skip-csr,) \
		$(if $(RESYNC),--resync --window $(or $(RESYNC_WINDOW),8),) \
		2>&1 | tee -a $(REPORT_FILE); \
	COMPARE_EXIT=$$?; \
	if [ $$COMPARE_EXIT -eq 0 ]; then \
		echo "COMPARE_STATUS=MATCH" >> $(REPORT_FILE); \
		echo -e "$(GREEN)$(SUCCESS) Logs match!$(RESET)"; \
	else \
		echo "COMPARE_STATUS=MISMATCH" >> $(REPORT_FILE); \
		echo -e "$(RED)✗ Logs differ$(RESET)"; \
		exit $$COMPARE_EXIT; \
	fi
endif


# ============================================================
# 5 Generate Final Test Report
# ============================================================
test_report:
ifeq ($(CFG_COMPARE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Benchmark Run Complete$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo "BENCHMARK_STATUS=COMPLETE" >> $(REPORT_FILE)
	@echo -e "$(GREEN)$(SUCCESS) RTL simulation finished$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Check UART log for benchmark output"
else ifeq ($(CFG_SPIKE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Benchmark Run Complete$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo "BENCHMARK_STATUS=COMPLETE" >> $(REPORT_FILE)
	@echo -e "$(GREEN)$(SUCCESS) RTL simulation finished$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Check UART log for benchmark output"
else
	@if grep -q "PASS" $(REPORT_FILE); then \
		echo -e "$(GREEN)TEST PASSED$(RESET)"; \
		exit 0; \
	elif grep -q "FAIL" $(REPORT_FILE); then \
		echo -e "$(RED)TEST FAILED$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(YELLOW)TEST STATUS UNKNOWN$(RESET)"; \
		exit 1; \
	fi
endif
# ============================================================
# 6 Batch Test Execution from File
# ============================================================
run_flist:
	@if [ ! -f "$(FLIST)" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Test list file not found: $(FLIST)"; \
		exit 1; \
	fi
	@$(MKDIR) "$(LOG_DIR)"
	@# Clean all logs for this simulator if CLEAN_LOGS=1
	@if [ "$(CLEAN_LOGS)" = "1" ]; then \
		echo -e "$(CYAN)[CLEAN]$(RESET) Removing all previous logs: $(RESULTS_DIR)/logs/$(SIM)/"; \
		rm -rf "$(RESULTS_DIR)/logs/$(SIM)/"*; \
	fi
	@echo -n "" > $(PASS_LIST_FILE)
	@echo -n "" > $(FAIL_LIST_FILE)
	@echo -e "$(GREEN)Running tests from list file:$(RESET) $(FLIST)"
	@echo -e "$(CYAN)Output directory:$(RESET) $(RESULTS_DIR)/logs/$(SIM)/"
	@PASS=0; FAIL=0; TOTAL=0; \
	while IFS= read -r test || [ -n "$${test}" ]; do \
		test="$${test%% }"; test="$${test## }"; \
		if echo "$${test}" | grep -E '^\s*#' >/dev/null || [ -z "$${test}" ]; then continue; fi; \
		TOTAL=$$(( $${TOTAL} + 1 )); \
		TEST_LOG_DIR="$(RESULTS_DIR)/logs/$(SIM)/$${test}"; \
		if [ -d "$${TEST_LOG_DIR}" ]; then \
			rm -rf "$${TEST_LOG_DIR}"; \
		fi; \
		mkdir -p "$${TEST_LOG_DIR}"; \
		echo -e ""; \
		echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		echo -e "$(CYAN)[FLIST] Test $${TOTAL}: $${test}$(RESET)"; \
		echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		echo -e "$(CYAN)[INFO]$(RESET) Log directory: $$TEST_LOG_DIR"; \
		echo -e "$(CYAN)[INFO]$(RESET) ELF  : $(ELF_DIR)/$${test}"; \
		echo -e "$(CYAN)[INFO]$(RESET) MEM  : $(MEM_DIR)/$${test}.mem"; \
		echo -e "$(CYAN)[INFO]$(RESET) HEX  : $(HEX_DIR)/$${test}.hex"; \
		echo -e "$(CYAN)[INFO]$(RESET) DUMP : $(DUMP_DIR)/$${test}.dump"; \
		echo -e "$(CYAN)[INFO]$(RESET) ADDR : $(ADDR_DIR)/$${test}_addr.txt"; \
		if $(MAKE) --no-print-directory run \
			TEST_NAME=$${test} \
			SIM=$(SIM) \
			MAX_CYCLES=$(MAX_CYCLES) \
			SKIP_CSR=$(SKIP_CSR) \
			RESYNC=$(RESYNC) \
			RESYNC_WINDOW=$(RESYNC_WINDOW) \
			TEST_LOG_DIR=$${TEST_LOG_DIR} \
			RTL_LOG_DIR=$${TEST_LOG_DIR} > "$${TEST_LOG_DIR}/summary.log" 2>&1; then \
			PASS=$$(( $${PASS} + 1 )); \
			echo "$${test}" >> "$(PASS_LIST_FILE)"; \
			if [ -f "$${TEST_LOG_DIR}/diff.log" ]; then \
				RTL_EXTRA=$$(grep "RTL Extra Entries" "$${TEST_LOG_DIR}/diff.log" | awk '{print $$NF}'); \
				SPIKE_EXTRA=$$(grep "Spike Extra Entries" "$${TEST_LOG_DIR}/diff.log" | awk '{print $$NF}'); \
				if [ "$${RTL_EXTRA:-0}" != "0" ] || [ "$${SPIKE_EXTRA:-0}" != "0" ]; then \
					echo -e "$(YELLOW)⚠ $${test} PASSED (RTL: $$RTL_EXTRA extra, Spike: $$SPIKE_EXTRA extra)$(RESET)"; \
				else \
					echo -e "$(GREEN)$(SUCCESS) $${test} PASSED$(RESET)"; \
				fi; \
			else \
				echo -e "$(GREEN)$(SUCCESS) $${test} PASSED$(RESET)"; \
			fi; \
		else \
			TEST_EXIT=$$?; \
			FAIL=$$(( $${FAIL} + 1 )); \
			echo "$${test}" >> "$(FAIL_LIST_FILE)"; \
			echo -e "$(RED)✗ $${test} FAILED (exit code: $${TEST_EXIT})$(RESET)"; \
			echo -e "$(YELLOW)  ↳ Summary log: $${TEST_LOG_DIR}/summary.log$(RESET)"; \
			echo -e "$(YELLOW)  ↳ HTML report: $${TEST_LOG_DIR}/diff.html$(RESET)"; \
			RPT="$(BUILD_DIR)/test_work/$${test}/test_report.txt"; \
			if [ -f "$$RPT" ]; then \
				echo -e "$(CYAN)[DEBUG]$(RESET) Report file preview:"; \
				head -20 "$$RPT"; \
			fi; \
		fi; \
	done < "$(FLIST)"; \
	echo -e ""; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN) File-Based Batch Summary$(RESET)"; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN)✅ Passed: $${PASS}$(RESET)"; \
	echo -e "$(RED)$(ERROR) Failed: $${FAIL}$(RESET)"; \
	echo -e "$(CYAN)📊 Total:  $${TOTAL}$(RESET)"; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN)Passed tests:$(RESET) $(PASS_LIST_FILE)"; \
	echo -e "$(RED)Failed tests:$(RESET) $(FAIL_LIST_FILE)"; \
	if [ $${FAIL} -gt 0 ]; then \
		echo -e "$(RED)$(WARN)  $${FAIL} test(s) failed$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)🎉 All tests passed!$(RESET)"; \
	fi


# ============================================================
# 7 Generate HTML Test Dashboard
# ============================================================
# Usage:
#   make html                    # Generate dashboard for verilator results
#   make html SIM=modelsim       # Generate dashboard for modelsim results
#   make html DASHBOARD_TITLE="My Tests"  # Custom title
# ============================================================
DASHBOARD_OUTPUT ?= $(RESULTS_DIR)/logs/dashboard.html
DASHBOARD_TITLE  ?= Level Test Dashboard
DASHBOARD_SCRIPT := $(SCRIPT_DIR)/python/makefile/generate_test_dashboard.py

.PHONY: html dashboard open_dashboard

html: dashboard

dashboard:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Generating HTML Test Dashboard$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Results Dir : $(RESULTS_DIR)"
	@echo -e "$(CYAN)[INFO]$(RESET) Simulator   : $(SIM)"
	@echo -e "$(CYAN)[INFO]$(RESET) Output      : $(DASHBOARD_OUTPUT)"
	@python3 $(DASHBOARD_SCRIPT) \
		--results-dir "$(RESULTS_DIR)" \
		--simulator "$(SIM)" \
		--output "$(DASHBOARD_OUTPUT)" \
		--title "$(DASHBOARD_TITLE)"
	@echo -e "$(GREEN)$(SUCCESS) Dashboard generated successfully$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Open with: xdg-open $(DASHBOARD_OUTPUT)"

open_dashboard: dashboard
	@xdg-open "$(DASHBOARD_OUTPUT)" 2>/dev/null || open "$(DASHBOARD_OUTPUT)" 2>/dev/null || echo "Please open $(DASHBOARD_OUTPUT) in a browser"

# ====== test/isa_import.mk ======
# ============================================================
# Level RISC-V ISA & Benchmark Tests — Auto Clone & Build Pipeline
# Submodule Version
# ============================================================

.PHONY: isa_auto isa_clone isa_configure isa_my_configure isa_build isa_import \
        isa_clean isa_check isa_reset isa_help \
        bench_auto bench_build bench_import

# ============================================================
# 1 ISA PIPELINE
# ============================================================

isa_auto: isa_clone isa_configure isa_my_configure isa_build isa_import

isa_clone:
	@echo -e "$(YELLOW)[CHECK] riscv-tests source availability...$(RESET)"

	@bash -c '\
		ISA_ROOT="$(ISA_ROOT)"; \
		SUBDIR="$(SUBREPO_DIR)"; \
		URL="$(ISA_REPO_URL)"; \
		\
		# Is the submodule path defined in .gitmodules? \
		if grep -q "path = $${ISA_ROOT}" .gitmodules 2>/dev/null; then \
			echo -e "$(YELLOW)[SUBMODULE] riscv-tests found in .gitmodules$(RESET)"; \
			\
			echo -e "$(YELLOW)[INIT+UPDATE] git submodule update --init --recursive$(RESET)"; \
			git submodule update --init --recursive -- "$${ISA_ROOT}"; \
			\
			echo -e "$(GREEN)[OK] Submodule ready (with nested submodules).$(RESET)"; \
			exit 0; \
		fi; \
		\
		# No submodule entry — fallback clone \
		echo -e "$(RED)[WARN] Submodule NOT defined. Falling back to git clone.$(RESET)"; \
		mkdir -p "$${SUBDIR}"; \
		\
		if [ ! -d "$${ISA_ROOT}" ] || [ -z "$$(ls -A "$${ISA_ROOT}" 2>/dev/null)" ]; then \
			echo -e "$(YELLOW)[CLONE] git clone --recursive $${URL} → $${ISA_ROOT}$(RESET)"; \
			cd "$${SUBDIR}" && git clone --recursive "$${URL}"; \
			echo -e "$(GREEN)[DONE] Repository cloned (recursive).$(RESET)"; \
		else \
			echo -e "$(GREEN)[SKIP] Repo folder already exists.$(RESET)"; \
		fi; \
	'

isa_configure:
	@echo -e "$(YELLOW)[BUILD] Configuring riscv-tests for RV$(XLEN)...$(RESET)"
	@cd $(ISA_ROOT) && \
		if [ ! -f configure ]; then \
			echo -e "$(YELLOW)[STEP] Running autoconf...$(RESET)"; \
			autoconf; \
		fi; \
		if [ ! -f Makefile ]; then \
			echo -e "$(YELLOW)[STEP] Running ./configure...$(RESET)"; \
			./configure --prefix=$(RISCV_TARGET) \
						--host=$(RISCV_PREFIX) \
						--target=$(RISCV_PREFIX) \
						--with-xlen=$(XLEN); \
		fi

isa_my_configure:
	@echo -e "$(YELLOW)[LEVEL ENV] Linking Level environment → riscv-tests/env$(RESET)"
	@LEVEL_ENV_SRC="$(ROOT_DIR)/env/riscv-test/level"; \
	LEVEL_ENV_DST="$(ISA_ROOT)/env"; \
	if [ ! -d "$$LEVEL_ENV_SRC" ]; then \
		echo -e "$(RED)[ERROR] Missing environment at: $$LEVEL_ENV_SRC$(RESET)"; \
		exit 1; \
	fi; \
	mkdir -p $$LEVEL_ENV_DST/level; \
	cp -r $$LEVEL_ENV_SRC/* $$LEVEL_ENV_DST/level/; \
	rm -rf $$LEVEL_ENV_DST/p; \
	ln -sfn level $$LEVEL_ENV_DST/p; \
	echo -e "$(GREEN)[DONE] Level test env active.$(RESET)"

isa_build:
	@echo -e "$(YELLOW)[STEP] make isa$(RESET)"
	@$(MAKE) -C $(ISA_ROOT) -j$(MAKE_JOBS) isa || { echo -e "$(RED)ISA build failed$(RESET)"; exit 1; }
	@echo -e "$(GREEN)ISA build complete.$(RESET)"

isa_import:
	@echo -e "$(YELLOW)[IMPORT] Importing ISA tests via pipeline$(RESET)"
	@$(PYTHON) $(PIPELINE_PY) --isa-dir $(ISA_SRC_DIR) --level-root $(ROOT_DIR)
	@echo -e "$(GREEN)ISA import complete.$(RESET)"

# ============================================================
# 2 BENCHMARK PIPELINE
# ============================================================

bench_auto: isa_clone bench_build bench_import

bench_build:
	@echo -e "$(YELLOW)[STEP] make benchmarks$(RESET)"
	@$(MAKE) -C $(ISA_ROOT) -j$(MAKE_JOBS) benchmarks || { echo -e "$(RED)Benchmarks failed$(RESET)"; exit 1; }
	@echo -e "$(GREEN)Benchmarks build complete.$(RESET)"

bench_import:
	@echo -e "$(YELLOW)[IMPORT] Importing Benchmarks via pipeline$(RESET)"
	@$(PYTHON) $(PIPELINE_PY) --bench-dir $(ISA_ROOT)/benchmarks --level-root $(ROOT_DIR)
	@echo -e "$(GREEN)Benchmark import complete.$(RESET)"

# ============================================================
# 3 HELPERS
# ============================================================

isa_clean:
	@echo -e "$(RED)[CLEAN] Removing ISA outputs$(RESET)"
	@rm -rf $(ISA_OUT_DIR)

isa_check:
	@echo -e "$(GREEN)[CHECK] Listing ISA ELF & DUMP$(RESET)"
	@ls -lh $(ISA_SRC_DIR) | grep -E "riscv|dump" || echo "No files."

isa_reset:
	@echo -e "$(RED)[RESET] Removing submodule: $(ISA_ROOT)$(RESET)"
	@rm -rf $(ISA_ROOT)

isa_help:
	@echo -e "$(GREEN)Level RISC-V ISA Test Management$(RESET)"
	@echo -e "  isa_auto     – Full ISA pipeline"
	@echo -e "  bench_auto   – Full Benchmark pipeline"
	@echo -e "  isa_build    – make isa"
	@echo -e "  bench_build  – make benchmarks"
	@echo -e "  isa_import   – Import ISA ELF → HEX → MEM → ADDR"
	@echo -e "  bench_import – Import Benchmark tests"

# ====== test/arch_test.mk ======
.PHONY: arch_auto arch_clone arch_setup arch_build arch_import arch_reset arch_help arch_list
.PHONY: arch_build_I arch_build_M arch_build_C arch_build_Zicsr

# ============================================================
# 1 Level RISC-V Architecture Test Pipeline
# ============================================================
# Direct compilation approach (no RISCOF dependency)
# Similar to riscv-tests import pipeline

# ============================================================
# Configuration
# ============================================================

# Supported extensions for Level RV32IMC_Zicsr
ARCH_EXTENSIONS := I M C Zicsr Zifencei

# Paths
ARCH_ENV_SRC     := $(ENV_DIR)/riscv-arch-test/level
ARCH_SUITE_DIR   := $(ARCH_ROOT)/riscv-test-suite/rv32i_m
ARCH_BUILD_DIR   := $(BUILD_DIR)/tests/riscv-arch-test

# Output directories
ARCH_ELF_DIR     := $(ARCH_BUILD_DIR)/elf
ARCH_DUMP_DIR    := $(ARCH_BUILD_DIR)/dump
ARCH_HEX_DIR     := $(ARCH_BUILD_DIR)/hex
ARCH_MEM_DIR     := $(ARCH_BUILD_DIR)/mem
ARCH_ADDR_DIR    := $(ARCH_BUILD_DIR)/pass_fail_addr
ARCH_REF_DIR     := $(ARCH_BUILD_DIR)/reference

# Compiler settings
ARCH_CC          := $(RISCV_PREFIX)-gcc
ARCH_OBJCOPY     := $(RISCV_PREFIX)-objcopy
ARCH_OBJDUMP     := $(RISCV_PREFIX)-objdump

# Architecture flags for RV32IMC_Zicsr
ARCH_MARCH       := rv32imc_zicsr_zifencei
ARCH_MABI        := ilp32

# Compiler flags
ARCH_CFLAGS      := -march=$(ARCH_MARCH) -mabi=$(ARCH_MABI) -static -mcmodel=medany \
                    -fvisibility=hidden -nostdlib -nostartfiles -fno-builtin \
                    -DXLEN=32 -DTEST_CASE_1=True

# Include paths - arch_test.h, encoding.h from official suite + model_test.h from level
ARCH_INCLUDES    := -I$(ARCH_ROOT)/riscv-test-suite/env \
                    -I$(ARCH_ENV_SRC)

# Linker script
ARCH_LDSCRIPT    := $(ARCH_ENV_SRC)/link.ld
ARCH_LDFLAGS     := -T$(ARCH_LDSCRIPT)

# Python scripts
HEX_TO_MEM_PY    := $(SCRIPT_DIR)/python/makefile/hex_to_mem.py

# ============================================================
# 2 Main Pipeline (Clone → Setup → Build → Import)
# ============================================================

arch_auto: arch_clone arch_setup arch_build arch_import

# ------------------------------------------------------------
# 1. Clone riscv-arch-test repository
# ------------------------------------------------------------
arch_clone:
	@echo -e "$(YELLOW)[ARCH-TEST] Checking riscv-arch-test repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(ARCH_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(ARCH_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone --depth=1 $(ARCH_REPO_URL); \
		echo -e "$(GREEN)[OK] riscv-arch-test cloned.$(RESET)"; \
	else \
		echo -e "$(GREEN)[SKIP] riscv-arch-test already exists.$(RESET)"; \
	fi

# ------------------------------------------------------------
# 2. Setup - Verify environment files exist
# ------------------------------------------------------------
arch_setup:
	@echo -e "$(YELLOW)[ARCH-TEST] Verifying Level environment...$(RESET)"
	@if [ ! -f "$(ARCH_ENV_SRC)/model_test.h" ]; then \
		echo -e "$(RED)[ERROR] model_test.h not found at $(ARCH_ENV_SRC)$(RESET)"; \
		exit 1; \
	fi
	@if [ ! -f "$(ARCH_ENV_SRC)/link.ld" ]; then \
		echo -e "$(RED)[ERROR] link.ld not found at $(ARCH_ENV_SRC)$(RESET)"; \
		exit 1; \
	fi
	@mkdir -p $(ARCH_ELF_DIR) $(ARCH_DUMP_DIR) $(ARCH_HEX_DIR) $(ARCH_MEM_DIR) $(ARCH_ADDR_DIR) $(ARCH_REF_DIR)
	@echo -e "$(GREEN)[OK] Environment verified.$(RESET)"

# ------------------------------------------------------------
# 3. Build all supported extensions
# ------------------------------------------------------------
arch_build: arch_setup arch_build_I arch_build_M arch_build_C arch_build_Zicsr arch_build_Zifencei
	@echo -e "$(GREEN)[ARCH-TEST] All tests built successfully.$(RESET)"

# Build I extension tests
arch_build_I:
	@echo -e "$(YELLOW)[BUILD] Compiling I extension tests...$(RESET)"
	@$(MAKE) --no-print-directory _arch_build_ext EXT=I

# Build M extension tests
arch_build_M:
	@echo -e "$(YELLOW)[BUILD] Compiling M extension tests...$(RESET)"
	@$(MAKE) --no-print-directory _arch_build_ext EXT=M

# Build C extension tests
arch_build_C:
	@echo -e "$(YELLOW)[BUILD] Compiling C extension tests...$(RESET)"
	@$(MAKE) --no-print-directory _arch_build_ext EXT=C

# Build Zicsr extension tests (privilege)
arch_build_Zicsr:
	@echo -e "$(YELLOW)[BUILD] Compiling Zicsr tests...$(RESET)"
	@if [ -d "$(ARCH_SUITE_DIR)/privilege/src" ]; then \
		$(MAKE) --no-print-directory _arch_build_ext EXT=privilege; \
	else \
		echo -e "$(YELLOW)[SKIP] No privilege tests found.$(RESET)"; \
	fi

# Build Zifencei extension tests
arch_build_Zifencei:
	@echo -e "$(YELLOW)[BUILD] Compiling Zifencei tests...$(RESET)"
	@if [ -d "$(ARCH_SUITE_DIR)/Zifencei/src" ]; then \
		$(MAKE) --no-print-directory _arch_build_ext EXT=Zifencei; \
	else \
		echo -e "$(YELLOW)[SKIP] No Zifencei tests found.$(RESET)"; \
	fi

# Internal target: Build tests for a specific extension
_arch_build_ext:
	@mkdir -p $(ARCH_ELF_DIR) $(ARCH_DUMP_DIR) $(ARCH_HEX_DIR) $(ARCH_MEM_DIR) $(ARCH_ADDR_DIR)
	@EXT_SRC_DIR="$(ARCH_SUITE_DIR)/$(EXT)/src"; \
	if [ ! -d "$$EXT_SRC_DIR" ]; then \
		echo -e "$(RED)[ERROR] Source dir not found: $$EXT_SRC_DIR$(RESET)"; \
		exit 1; \
	fi; \
	PASS=0; FAIL=0; \
	for src in $$EXT_SRC_DIR/*.S; do \
		if [ -f "$$src" ]; then \
			name=$$(basename $$src .S); \
			elf="$(ARCH_ELF_DIR)/$(EXT)-$${name}.elf"; \
			dump="$(ARCH_DUMP_DIR)/$(EXT)-$${name}.dump"; \
			hex="$(ARCH_HEX_DIR)/$(EXT)-$${name}.hex"; \
			echo -e "  $(YELLOW)→ Compiling: $(EXT)-$${name}$(RESET)"; \
			if $(ARCH_CC) $(ARCH_CFLAGS) $(ARCH_INCLUDES) $(ARCH_LDFLAGS) -o $$elf $$src 2>&1 | grep -v "warning:"; then \
				: ; \
			fi; \
			if [ -f "$$elf" ]; then \
				$(ARCH_OBJDUMP) -D $$elf > $$dump; \
				$(ARCH_OBJCOPY) -O verilog $$elf $$hex; \
				echo -e "  $(GREEN)$(SUCCESS) Built: $(EXT)-$${name}$(RESET)"; \
				PASS=$$((PASS + 1)); \
			else \
				echo -e "  $(RED)✗ Failed: $(EXT)-$${name}$(RESET)"; \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[$(EXT)] Compiled: $$PASS passed, $$FAIL failed$(RESET)"

# ------------------------------------------------------------
# 4. Import: Convert HEX → MEM and extract PASS/FAIL addresses
# ------------------------------------------------------------
arch_import:
	@echo -e "$(YELLOW)[IMPORT] Converting HEX → MEM and extracting addresses...$(RESET)"
	@for hex in $(ARCH_HEX_DIR)/*.hex; do \
		if [ -f "$$hex" ]; then \
			name=$$(basename $$hex .hex); \
			mem="$(ARCH_MEM_DIR)/$${name}.mem"; \
			dump="$(ARCH_DUMP_DIR)/$${name}.dump"; \
			addr="$(ARCH_ADDR_DIR)/$${name}_addr.txt"; \
			echo -e "  → Processing: $${name}"; \
			python3 $(HEX_TO_MEM_PY) $$hex $$mem 2>/dev/null || \
				{ echo -e "  $(RED)✗ HEX→MEM failed: $${name}$(RESET)"; continue; }; \
			if [ -f "$$dump" ]; then \
				exit_addr=$$(grep -m1 '<exit_cleanup>:' $$dump | cut -d' ' -f1); \
				halt_addr=$$(grep -m1 '<halt_loop>:' $$dump | cut -d' ' -f1); \
				pass_addr=$$(grep -m1 '<pass>:' $$dump | cut -d' ' -f1); \
				if [ -n "$$exit_addr" ]; then \
					p="0x$$exit_addr"; \
				elif [ -n "$$halt_addr" ]; then \
					p="0x$$halt_addr"; \
				elif [ -n "$$pass_addr" ]; then \
					p="0x$$pass_addr"; \
				else \
					p="0x0"; \
				fi; \
				fail_addr=$$(grep -m1 '<fail>:' $$dump | cut -d' ' -f1); \
				if [ -n "$$fail_addr" ]; then \
					f="0x$$fail_addr"; \
				else \
					f=$$(printf "0x%x" $$(($$p + 0x1000))); \
				fi; \
				echo "$$p $$f" > $$addr; \
			fi; \
		fi; \
	done
	@echo -e "$(GREEN)[IMPORT] Complete.$(RESET)"
	@echo -e "  ELF  → $(ARCH_ELF_DIR)"
	@echo -e "  DUMP → $(ARCH_DUMP_DIR)"
	@echo -e "  HEX  → $(ARCH_HEX_DIR)"
	@echo -e "  MEM  → $(ARCH_MEM_DIR)"
	@echo -e "  ADDR → $(ARCH_ADDR_DIR)"

# ------------------------------------------------------------
# 5. Copy reference signatures (for future comparison)
# ------------------------------------------------------------
arch_refs:
	@echo -e "$(YELLOW)[REFS] Copying reference signatures...$(RESET)"
	@for ext in $(ARCH_EXTENSIONS); do \
		ref_dir="$(ARCH_SUITE_DIR)/$$ext/references"; \
		if [ -d "$$ref_dir" ]; then \
			cp -r $$ref_dir/* $(ARCH_REF_DIR)/ 2>/dev/null || true; \
		fi; \
	done
	@echo -e "$(GREEN)[OK] References copied to $(ARCH_REF_DIR)$(RESET)"

# ------------------------------------------------------------
# 6. List available tests
# ------------------------------------------------------------
arch_list:
	@echo -e "$(GREEN)Available riscv-arch-test extensions:$(RESET)"
	@if [ -d "$(ARCH_SUITE_DIR)" ]; then \
		for ext in $(ARCH_SUITE_DIR)/*/; do \
			name=$$(basename $$ext); \
			count=$$(ls $$ext/src/*.S 2>/dev/null | wc -l); \
			echo -e "  $$name: $$count tests"; \
		done; \
	else \
		echo -e "  $(RED)Repository not cloned. Run 'make arch_clone' first.$(RESET)"; \
	fi

# ------------------------------------------------------------
# 7. Cleanup
# ------------------------------------------------------------
arch_reset:
	@echo -e "$(RED)[RESET] Removing riscv-arch-test repo and build artifacts$(RESET)"
	@rm -rf $(ARCH_ROOT)
	@rm -rf $(ARCH_BUILD_DIR)

arch_clean:
	@echo -e "$(RED)[CLEAN] Removing build artifacts$(RESET)"
	@rm -rf $(ARCH_BUILD_DIR)

# ------------------------------------------------------------
# 8. Help
# ------------------------------------------------------------
arch_help:
	@echo -e "$(GREEN)Level RISC-V Architecture Test Pipeline$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Main Targets:$(RESET)"
	@echo -e "  make arch_auto       # Full pipeline: Clone → Setup → Build → Import"
	@echo -e "  make arch_clone      # Clone riscv-arch-test repository"
	@echo -e "  make arch_setup      # Verify environment files"
	@echo -e "  make arch_build      # Build all supported extension tests"
	@echo -e "  make arch_import     # Convert HEX→MEM and extract addresses"
	@echo -e ""
	@echo -e "$(YELLOW)Extension-Specific Builds:$(RESET)"
	@echo -e "  make arch_build_I       # Build I extension tests"
	@echo -e "  make arch_build_M       # Build M extension tests"
	@echo -e "  make arch_build_C       # Build C extension tests"
	@echo -e "  make arch_build_Zicsr   # Build Zicsr (privilege) tests"
	@echo -e ""
	@echo -e "$(YELLOW)Utilities:$(RESET)"
	@echo -e "  make arch_list       # List available test extensions"
	@echo -e "  make arch_refs       # Copy reference signatures"
	@echo -e "  make arch_clean      # Remove build artifacts"
	@echo -e "  make arch_reset      # Remove repo and artifacts"
	@echo -e ""
	@echo -e "$(GREEN)Output Directories:$(RESET)"
	@echo -e "  ELF:  $(ARCH_ELF_DIR)"
	@echo -e "  DUMP: $(ARCH_DUMP_DIR)"
	@echo -e "  HEX:  $(ARCH_HEX_DIR)"
	@echo -e "  MEM:  $(ARCH_MEM_DIR)"
	@echo -e "  ADDR: $(ARCH_ADDR_DIR)"
# ====== test/imperas_test.mk ======
.PHONY: imperas_auto imperas_clone imperas_setup imperas_build imperas_import imperas_reset imperas_help imperas_list
.PHONY: imperas_build_I imperas_build_M imperas_build_C imperas_build_Zicsr imperas_build_Zifencei

# ============================================================
# 1 Level RISC-V Imperas Test Pipeline
# ============================================================
# Direct compilation approach for Imperas RISC-V tests
# (riscv-ovpsim/imperas-riscv-tests)
#
# NOTE: The free/public Imperas repo only includes RV32I base tests.
# For M, C, Zicsr extensions, use riscv-arch-test (make arch_auto)
#
# ============================================================
# Configuration
# ============================================================

# Available extensions in free Imperas repo (only I has source code)
IMPERAS_EXTENSIONS := I

# Repository URL
IMPERAS_REPO_URL := https://github.com/riscv-ovpsim/imperas-riscv-tests.git
IMPERAS_ROOT     := $(SUBREPO_DIR)/imperas-riscv-tests

# Paths
IMPERAS_ENV_SRC    := $(ENV_DIR)/imperas
IMPERAS_SUITE_DIR  := $(IMPERAS_ROOT)/riscv-test-suite/rv32i_m
IMPERAS_ENV_DIR    := $(IMPERAS_ROOT)/riscv-test-suite/env
IMPERAS_BUILD_DIR  := $(BUILD_DIR)/tests/imperas

# Output directories
IMPERAS_ELF_DIR    := $(IMPERAS_BUILD_DIR)/elf
IMPERAS_DUMP_DIR   := $(IMPERAS_BUILD_DIR)/dump
IMPERAS_HEX_DIR    := $(IMPERAS_BUILD_DIR)/hex
IMPERAS_MEM_DIR    := $(IMPERAS_BUILD_DIR)/mem
IMPERAS_ADDR_DIR   := $(IMPERAS_BUILD_DIR)/pass_fail_addr
IMPERAS_REF_DIR    := $(IMPERAS_BUILD_DIR)/reference

# Compiler settings
IMPERAS_CC         := $(RISCV_PREFIX)-gcc
IMPERAS_OBJCOPY    := $(RISCV_PREFIX)-objcopy
IMPERAS_OBJDUMP    := $(RISCV_PREFIX)-objdump

# Architecture flags for RV32IMC_Zicsr
IMPERAS_MARCH      := rv32imc_zicsr
IMPERAS_MABI       := ilp32

# Compiler flags (TEST_CASE_1 is defined in arch_test.h, don't define it again)
IMPERAS_CFLAGS     := -march=$(IMPERAS_MARCH) -mabi=$(IMPERAS_MABI) -static -mcmodel=medany \
                      -fvisibility=hidden -nostdlib -nostartfiles -fno-builtin \
                      -DXLEN=32

# Include paths - arch_test.h from Imperas suite + model_test.h from level env
IMPERAS_INCLUDES   := -I$(IMPERAS_ENV_DIR) \
                      -I$(IMPERAS_ENV_SRC)

# Linker script
IMPERAS_LDSCRIPT   := $(IMPERAS_ENV_SRC)/link.ld
IMPERAS_LDFLAGS    := -T$(IMPERAS_LDSCRIPT)

# Python scripts
HEX_TO_MEM_PY      := $(SCRIPT_DIR)/python/makefile/hex_to_mem.py

# ============================================================
# 2 Main Pipeline (Clone → Setup → Build → Import)
# ============================================================

imperas_auto: imperas_clone imperas_setup imperas_build imperas_import

# ------------------------------------------------------------
# 1. Clone imperas-riscv-tests repository
# ------------------------------------------------------------
imperas_clone:
	@echo -e "$(YELLOW)[IMPERAS] Checking imperas-riscv-tests repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(IMPERAS_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(IMPERAS_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone --depth=1 $(IMPERAS_REPO_URL); \
		echo -e "$(GREEN)[OK] imperas-riscv-tests cloned.$(RESET)"; \
	else \
		echo -e "$(GREEN)[SKIP] imperas-riscv-tests already exists.$(RESET)"; \
	fi

# ------------------------------------------------------------
# 2. Setup - Verify environment files exist
# ------------------------------------------------------------
imperas_setup:
	@echo -e "$(YELLOW)[IMPERAS] Verifying Level environment...$(RESET)"
	@if [ ! -f "$(IMPERAS_ENV_SRC)/model_test.h" ]; then \
		echo -e "$(RED)[ERROR] model_test.h not found at $(IMPERAS_ENV_SRC)$(RESET)"; \
		exit 1; \
	fi
	@if [ ! -f "$(IMPERAS_ENV_SRC)/link.ld" ]; then \
		echo -e "$(RED)[ERROR] link.ld not found at $(IMPERAS_ENV_SRC)$(RESET)"; \
		exit 1; \
	fi
	@if [ ! -f "$(IMPERAS_ENV_DIR)/arch_test.h" ]; then \
		echo -e "$(RED)[ERROR] arch_test.h not found in Imperas suite.$(RESET)"; \
		echo -e "$(RED)       Run 'make imperas_clone' first.$(RESET)"; \
		exit 1; \
	fi
	@mkdir -p $(IMPERAS_ELF_DIR) $(IMPERAS_DUMP_DIR) $(IMPERAS_HEX_DIR) $(IMPERAS_MEM_DIR) $(IMPERAS_ADDR_DIR) $(IMPERAS_REF_DIR)
	@echo -e "$(GREEN)[OK] Environment verified.$(RESET)"

# ------------------------------------------------------------
# 3. Build all supported extensions
# ------------------------------------------------------------
# Note: Free Imperas repo only has I extension source code
# For M, C, Zicsr tests use: make arch_auto
imperas_build: imperas_setup imperas_build_I
	@echo -e "$(GREEN)[IMPERAS] All available tests built successfully.$(RESET)"
	@echo -e "$(YELLOW)[INFO] Imperas free repo only includes I extension tests.$(RESET)"
	@echo -e "$(YELLOW)[INFO] For M, C, Zicsr tests, use: make arch_auto$(RESET)"

# Build I extension tests (main tests available in free repo)
imperas_build_I:
	@echo -e "$(YELLOW)[BUILD] Compiling I extension tests...$(RESET)"
	@$(MAKE) --no-print-directory _imperas_build_ext EXT=I

# Internal target: Build tests for a specific extension
# Note: Some tests are skipped:
# - MISALIGN tests: use deprecated 'mbadaddr' CSR and require misaligned access support
# - EBREAK test: requires specific exception handling that may not match Spike behavior
IMPERAS_SKIP_TESTS := I-MISALIGN_JMP-01 I-MISALIGN_LDST-01 I-EBREAK-01

_imperas_build_ext:
	@mkdir -p $(IMPERAS_ELF_DIR) $(IMPERAS_DUMP_DIR) $(IMPERAS_HEX_DIR) $(IMPERAS_MEM_DIR) $(IMPERAS_ADDR_DIR)
	@EXT_SRC_DIR="$(IMPERAS_SUITE_DIR)/$(EXT)/src"; \
	if [ ! -d "$$EXT_SRC_DIR" ]; then \
		echo -e "$(RED)[ERROR] Source dir not found: $$EXT_SRC_DIR$(RESET)"; \
		exit 1; \
	fi; \
	PASS=0; FAIL=0; SKIP=0; \
	for src in $$EXT_SRC_DIR/*.S; do \
		if [ -f "$$src" ]; then \
			name=$$(basename $$src .S); \
			skip=0; \
			for skiptest in $(IMPERAS_SKIP_TESTS); do \
				if [ "$$name" = "$$skiptest" ]; then skip=1; break; fi; \
			done; \
			if [ $$skip -eq 1 ]; then \
				echo -e "  $(CYAN)⊘ Skipped: $(EXT)-$${name} (requires mbadaddr CSR)$(RESET)"; \
				SKIP=$$((SKIP + 1)); \
				continue; \
			fi; \
			elf="$(IMPERAS_ELF_DIR)/$(EXT)-$${name}.elf"; \
			dump="$(IMPERAS_DUMP_DIR)/$(EXT)-$${name}.dump"; \
			hex="$(IMPERAS_HEX_DIR)/$(EXT)-$${name}.hex"; \
			echo -e "  $(YELLOW)→ Compiling: $(EXT)-$${name}$(RESET)"; \
			if $(IMPERAS_CC) $(IMPERAS_CFLAGS) $(IMPERAS_INCLUDES) $(IMPERAS_LDFLAGS) -o $$elf $$src 2>&1 | grep -v "warning:"; then \
				: ; \
			fi; \
			if [ -f "$$elf" ]; then \
				$(IMPERAS_OBJDUMP) -D $$elf > $$dump; \
				$(IMPERAS_OBJCOPY) -O verilog $$elf $$hex; \
				echo -e "  $(GREEN)$(SUCCESS) Built: $(EXT)-$${name}$(RESET)"; \
				PASS=$$((PASS + 1)); \
			else \
				echo -e "  $(RED)✗ Failed: $(EXT)-$${name}$(RESET)"; \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[$(EXT)] Compiled: $$PASS passed, $$FAIL failed, $$SKIP skipped$(RESET)"

# ------------------------------------------------------------
# 4. Import: Convert HEX → MEM and extract PASS/FAIL addresses
# ------------------------------------------------------------
imperas_import:
	@echo -e "$(YELLOW)[IMPORT] Converting HEX → MEM and extracting addresses...$(RESET)"
	@for hex in $(IMPERAS_HEX_DIR)/*.hex; do \
		if [ -f "$$hex" ]; then \
			name=$$(basename $$hex .hex); \
			mem="$(IMPERAS_MEM_DIR)/$${name}.mem"; \
			dump="$(IMPERAS_DUMP_DIR)/$${name}.dump"; \
			addr="$(IMPERAS_ADDR_DIR)/$${name}_addr.txt"; \
			echo -e "  → Processing: $${name}"; \
			python3 $(HEX_TO_MEM_PY) $$hex $$mem 2>/dev/null || \
				{ echo -e "  $(RED)✗ HEX→MEM failed: $${name}$(RESET)"; continue; }; \
			if [ -f "$$dump" ]; then \
				exit_addr=$$(grep -m1 '<exit_cleanup>:' $$dump | cut -d' ' -f1); \
				halt_addr=$$(grep -m1 '<halt_loop>:' $$dump | cut -d' ' -f1); \
				pass_addr=$$(grep -m1 '<pass>:' $$dump | cut -d' ' -f1); \
				if [ -n "$$exit_addr" ]; then \
					p="0x$$exit_addr"; \
				elif [ -n "$$halt_addr" ]; then \
					p="0x$$halt_addr"; \
				elif [ -n "$$pass_addr" ]; then \
					p="0x$$pass_addr"; \
				else \
					p="0x0"; \
				fi; \
				fail_addr=$$(grep -m1 '<fail>:' $$dump | cut -d' ' -f1); \
				if [ -n "$$fail_addr" ]; then \
					f="0x$$fail_addr"; \
				else \
					f=$$(printf "0x%x" $$(($$p + 0x1000))); \
				fi; \
				echo "$$p $$f" > $$addr; \
			fi; \
		fi; \
	done
	@echo -e "$(GREEN)[IMPORT] Complete.$(RESET)"
	@echo -e "  ELF  → $(IMPERAS_ELF_DIR)"
	@echo -e "  DUMP → $(IMPERAS_DUMP_DIR)"
	@echo -e "  HEX  → $(IMPERAS_HEX_DIR)"
	@echo -e "  MEM  → $(IMPERAS_MEM_DIR)"
	@echo -e "  ADDR → $(IMPERAS_ADDR_DIR)"

# ------------------------------------------------------------
# 5. Copy reference signatures (for future comparison)
# ------------------------------------------------------------
imperas_refs:
	@echo -e "$(YELLOW)[REFS] Copying reference signatures...$(RESET)"
	@for ext in $(IMPERAS_EXTENSIONS); do \
		ref_dir="$(IMPERAS_SUITE_DIR)/$$ext/references"; \
		if [ -d "$$ref_dir" ]; then \
			cp -r $$ref_dir/* $(IMPERAS_REF_DIR)/ 2>/dev/null || true; \
		fi; \
	done
	@echo -e "$(GREEN)[OK] References copied to $(IMPERAS_REF_DIR)$(RESET)"

# ------------------------------------------------------------
# 6. List available tests
# ------------------------------------------------------------
imperas_list:
	@echo -e "$(GREEN)Available imperas-riscv-tests extensions:$(RESET)"
	@if [ -d "$(IMPERAS_SUITE_DIR)" ]; then \
		for ext in $(IMPERAS_SUITE_DIR)/*/; do \
			name=$$(basename $$ext); \
			if [ -d "$$ext/src" ]; then \
				count=$$(ls $$ext/src/*.S 2>/dev/null | wc -l); \
				echo -e "  $$name: $$count tests"; \
			fi; \
		done; \
	else \
		echo -e "  $(RED)Repository not cloned. Run 'make imperas_clone' first.$(RESET)"; \
	fi

# ------------------------------------------------------------
# 7. Cleanup
# ------------------------------------------------------------
imperas_reset:
	@echo -e "$(RED)[RESET] Removing imperas-riscv-tests repo and build artifacts$(RESET)"
	@rm -rf $(IMPERAS_ROOT)
	@rm -rf $(IMPERAS_BUILD_DIR)

imperas_clean:
	@echo -e "$(RED)[CLEAN] Removing build artifacts$(RESET)"
	@rm -rf $(IMPERAS_BUILD_DIR)

# ------------------------------------------------------------
# 8. Generate test list for batch runs
# ------------------------------------------------------------
imperas_flist:
	@echo -e "$(YELLOW)[FLIST] Generating Imperas test list...$(RESET)"
	@mkdir -p $(SIM_DIR)/test
	@> $(SIM_DIR)/test/imperas_test_list.flist
	@for mem in $(IMPERAS_MEM_DIR)/*.mem; do \
		if [ -f "$$mem" ]; then \
			name=$$(basename $$mem .mem); \
			echo "$$name" >> $(SIM_DIR)/test/imperas_test_list.flist; \
		fi; \
	done
	@count=$$(wc -l < $(SIM_DIR)/test/imperas_test_list.flist); \
	echo -e "$(GREEN)[OK] Generated imperas_test_list.flist with $$count tests$(RESET)"

# ------------------------------------------------------------
# 9. Run all Imperas tests (batch mode)
# ------------------------------------------------------------
.PHONY: imperas

# Run all Imperas tests (batch). MAX_CYCLES override: IMPERAS_MAX_CYCLES=N
IMPERAS_MAX_CYCLES ?= 200000

imperas: imperas_flist
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)  Running All Imperas RISC-V Tests$(RESET)"
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST="$(SIM_DIR)/test/imperas_test_list.flist" \
		TEST_TYPE=imperas \
		MEM_DIR="$(IMPERAS_MEM_DIR)" \
		ADDR_DIR="$(IMPERAS_ADDR_DIR)" \
		MAX_CYCLES=$(IMPERAS_MAX_CYCLES) \
		NO_ADDR=0

# Run single Imperas test
# Usage: make ti T=I-ADD-01
ti:
ifndef T
	$(error Usage: make ti T=<test_name>  Example: make ti T=I-ADD-01)
endif
	@$(MAKE) --no-print-directory run \
		TEST_NAME=$(T) \
		TEST_TYPE=imperas \
		MEM_DIR="$(IMPERAS_MEM_DIR)" \
		ADDR_DIR="$(IMPERAS_ADDR_DIR)" \
		NO_ADDR=0

# ------------------------------------------------------------
# 10. Help
# ------------------------------------------------------------
imperas_help:
	@echo -e "$(GREEN)Level RISC-V Imperas Test Pipeline$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)NOTE: Free Imperas repo only includes RV32I base tests.$(RESET)"
	@echo -e "$(YELLOW)      For M, C, Zicsr extensions use: make arch_auto$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Main Targets:$(RESET)"
	@echo -e "  make imperas_auto    # Full pipeline: Clone → Setup → Build → Import"
	@echo -e "  make imperas_clone   # Clone imperas-riscv-tests repository"
	@echo -e "  make imperas_setup   # Verify environment files"
	@echo -e "  make imperas_build   # Build I extension tests"
	@echo -e "  make imperas_import  # Convert HEX→MEM and extract addresses"
	@echo -e ""
	@echo -e "$(YELLOW)Running Tests:$(RESET)"
	@echo -e "  make imperas          # Run all Imperas tests (batch)"
	@echo -e "  make ti T=<name>      # Run single Imperas test"
	@echo -e ""
	@echo -e "$(YELLOW)Utilities:$(RESET)"
	@echo -e "  make imperas_list    # List available test extensions"
	@echo -e "  make imperas_flist   # Generate test file list"
	@echo -e "  make imperas_refs    # Copy reference signatures"
	@echo -e "  make imperas_clean   # Remove build artifacts"
	@echo -e "  make imperas_reset   # Remove repo and artifacts"
	@echo -e ""
	@echo -e "$(GREEN)For M, C, Zicsr tests use riscv-arch-test:$(RESET)"
	@echo -e "  make arch_auto       # Full arch-test pipeline"
	@echo -e "  make arch            # Run all arch tests"
	@echo -e "  make arch_help       # Show arch-test help"
	@echo -e ""
	@echo -e "$(GREEN)Output Directories:$(RESET)"
	@echo -e "  ELF:  $(IMPERAS_ELF_DIR)"
	@echo -e "  DUMP: $(IMPERAS_DUMP_DIR)"
	@echo -e "  HEX:  $(IMPERAS_HEX_DIR)"
	@echo -e "  MEM:  $(IMPERAS_MEM_DIR)"
	@echo -e "  ADDR: $(IMPERAS_ADDR_DIR)"

# ====== test/coremark.mk ======
# ============================================================
# Level CoreMark Build Rules
# Level-V RV32IMC_Zicsr Processor CoreMark Benchmark
# ============================================================

.PHONY: coremark coremark_check coremark_setup coremark_build coremark_clean coremark_help
.PHONY: coremark_gen_linker run_coremark

# ============================================================
# Configuration
# ============================================================

# Default iteration count (adjust for ~10 second runtime)
COREMARK_ITERATIONS ?= 1

# Paths
COREMARK_SRC_DIR     := $(SUBREPO_DIR)/coremark
COREMARK_PORT_SRC    := $(ROOT_DIR)/env/coremark/levelv
COREMARK_PORT_DST    := $(COREMARK_SRC_DIR)/levelv
COREMARK_BUILD_DIR   := $(BUILD_DIR)/tests/coremark
COREMARK_REPO_URL    := https://github.com/eembc/coremark.git

# Memory Map and Linker Script
COREMARK_MEMORY_MAP  := $(COREMARK_PORT_SRC)/memory_map.yaml
COREMARK_LINKER_GEN  := $(SCRIPT_DIR)/python/gen_linker.py
COREMARK_LINKER_OUT  := $(COREMARK_PORT_DST)/link.ld
COREMARK_HEADER_OUT  := $(COREMARK_PORT_DST)/memory_map.h

# Output files
COREMARK_ELF      := $(COREMARK_BUILD_DIR)/coremark.elf
COREMARK_BIN      := $(COREMARK_BUILD_DIR)/coremark.bin
COREMARK_HEX      := $(COREMARK_BUILD_DIR)/coremark.hex
COREMARK_MEM      := $(COREMARK_BUILD_DIR)/coremark.mem
COREMARK_MEM_128  := $(COREMARK_BUILD_DIR)/coremark_128.mem
COREMARK_DUMP     := $(COREMARK_BUILD_DIR)/coremark.dump
# 0 = no padding (smaller .mem; BRAM depth can follow max benchmark size).
# Legacy: COREMARK_MEM_PAD_BYTES=34816 matched WRAPPER_RAM_SIZE_KB=34.
COREMARK_MEM_PAD_BYTES ?= 0
COREMARK_ELF_TO_MEM_EXTRA := $(shell [ "$(COREMARK_MEM_PAD_BYTES)" -gt 0 ] 2>/dev/null && echo --pad-to-size $(COREMARK_MEM_PAD_BYTES))

# ============================================================
# 1 Main Target - Full Pipeline
# ============================================================

coremark: coremark_check coremark_setup coremark_gen_linker coremark_build
	@echo -e "$(GREEN)[COREMARK] $(SUCCESS) Build complete$(RESET)"
	@echo -e "$(GREEN)[COREMARK] Output files:$(RESET)"
	@echo -e "  ELF:      $(COREMARK_ELF)"
	@echo -e "  BIN:      $(COREMARK_BIN)"
	@echo -e "  HEX:      $(COREMARK_HEX)"
	@echo -e "  MEM (32): $(COREMARK_MEM)"
	@echo -e "  MEM(128): $(COREMARK_MEM_128)"
	@echo -e "  DUMP:     $(COREMARK_DUMP)"

# ============================================================
# 2 Check CoreMark Source Availability
# ============================================================

coremark_check:
	@echo -e "$(YELLOW)[COREMARK] Checking source availability...$(RESET)"
	@if [ -d "$(COREMARK_SRC_DIR)" ] && [ -f "$(COREMARK_SRC_DIR)/coremark.h" ]; then \
		echo -e "$(GREEN)[COREMARK] $(SUCCESS) Source found at $(COREMARK_SRC_DIR)$(RESET)"; \
	else \
		echo -e "$(YELLOW)[COREMARK] Source not found, cloning...$(RESET)"; \
		if grep -q "path = $(COREMARK_SRC_DIR)" .gitmodules 2>/dev/null; then \
			echo -e "$(YELLOW)[COREMARK] Initializing submodule...$(RESET)"; \
			git submodule update --init --recursive -- $(COREMARK_SRC_DIR); \
		else \
			echo -e "$(YELLOW)[COREMARK] Cloning from $(COREMARK_REPO_URL)...$(RESET)"; \
			git clone $(COREMARK_REPO_URL) $(COREMARK_SRC_DIR); \
		fi; \
		if [ ! -f "$(COREMARK_SRC_DIR)/coremark.h" ]; then \
			echo -e "$(RED)[COREMARK] ✗ Failed to get CoreMark source$(RESET)"; \
			exit 1; \
		fi; \
		echo -e "$(GREEN)[COREMARK] $(SUCCESS) Source cloned successfully$(RESET)"; \
	fi

# ============================================================
# 3 Setup - Copy Level-V Port Files
# ============================================================

coremark_setup: coremark_check
	@echo -e "$(YELLOW)[COREMARK] Setting up Level-V port...$(RESET)"
	@if [ ! -d "$(COREMARK_PORT_SRC)" ]; then \
		echo -e "$(RED)[COREMARK] ✗ Port source not found: $(COREMARK_PORT_SRC)$(RESET)"; \
		exit 1; \
	fi
	@mkdir -p $(COREMARK_PORT_DST)
	@cp -r $(COREMARK_PORT_SRC)/* $(COREMARK_PORT_DST)/
	@echo -e "$(GREEN)[COREMARK] $(SUCCESS) Port files copied to $(COREMARK_PORT_DST)$(RESET)"

# ============================================================
# 3.5️ Generate Linker Script from Memory Map
# ============================================================

coremark_gen_linker: coremark_setup
	@echo -e "$(YELLOW)[COREMARK] Checking linker script...$(RESET)"
	@if [ -f "$(SUBREPO_DIR)/coremark/levelv/link.ld" ]; then \
		echo -e "$(CYAN)[COREMARK] Using manual linker script from subrepo (skipping auto-generation)$(RESET)"; \
	elif [ ! -f "$(COREMARK_MEMORY_MAP)" ]; then \
		echo -e "$(YELLOW)[COREMARK] No memory_map.yaml found, using default link.ld$(RESET)"; \
	else \
		echo -e "$(YELLOW)[COREMARK] Generating linker script from memory map...$(RESET)"; \
		python3 $(COREMARK_LINKER_GEN) \
			$(COREMARK_MEMORY_MAP) \
			$(COREMARK_LINKER_OUT) \
			--header $(COREMARK_HEADER_OUT) \
			--verbose; \
		echo -e "$(GREEN)[COREMARK] $(SUCCESS) Linker script generated$(RESET)"; \
	fi

# ============================================================
# 4 Build CoreMark for Level-V
# ============================================================

# ELF to MEM converter script
ELF_TO_MEM := $(SCRIPT_DIR)/python/elf_to_mem.py

coremark_build: coremark_gen_linker
	@echo -e "$(YELLOW)[COREMARK] Building with $(COREMARK_ITERATIONS) iterations...$(RESET)"
	@mkdir -p $(COREMARK_BUILD_DIR)
	@# Clean previous build in coremark source
	@env -u CC -u LD -u AS -u OBJCOPY -u OBJDUMP \
		$(MAKE) -C $(COREMARK_SRC_DIR) PORT_DIR=levelv clean 2>/dev/null || true
	@cd "$(COREMARK_SRC_DIR)" && (git checkout -- core_main.c 2>/dev/null || true)
	@# Build CoreMark - use env to unset variables that might interfere
	@echo -e "$(CYAN)[DEBUG] COREMARK_ITERATIONS=$(COREMARK_ITERATIONS)$(RESET)"
	@echo -e "$(CYAN)[DEBUG] Passing ITERATIONS=$(COREMARK_ITERATIONS) to subrepo Makefile$(RESET)"
	@env -u CC -u LD -u AS -u OBJCOPY -u OBJDUMP -u RISCV_PREFIX \
		$(MAKE) -C $(COREMARK_SRC_DIR) \
		PORT_DIR=levelv \
		ITERATIONS=$(COREMARK_ITERATIONS) \
		XCFLAGS="-DPERFORMANCE_RUN=1 $(LEVELV_CPU_CLK_CPPFLAGS)" \
		|| { echo -e "$(RED)[COREMARK] ✗ Build failed$(RESET)"; exit 1; }
	@# Copy output files to build directory
	@echo -e "$(YELLOW)[COREMARK] Copying output files...$(RESET)"
	@cp $(COREMARK_SRC_DIR)/coremark.elf $(COREMARK_ELF) 2>/dev/null || true
	@cp $(COREMARK_SRC_DIR)/coremark.bin $(COREMARK_BIN) 2>/dev/null || true
	@cp $(COREMARK_SRC_DIR)/coremark.hex $(COREMARK_HEX) 2>/dev/null || true
	@cp $(COREMARK_SRC_DIR)/coremark.dump $(COREMARK_DUMP) 2>/dev/null || true
	@# Generate proper .mem file using elf_to_mem.py (Verilog $readmemh compatible)
	@echo -e "$(YELLOW)[COREMARK] Generating Verilog-compatible .mem file (32-bit with heap+stack)...$(RESET)"
	@python3 $(ELF_TO_MEM) \
		--in $(COREMARK_BIN) \
		--out $(COREMARK_MEM) \
		--addr 0x80000000 \
		--block-bytes 4 \
		--word-size 4 \
		--word-endian little \
		--word-order high-to-low \
		$(COREMARK_ELF_TO_MEM_EXTRA)
	@# 128-bit cache line .mem (optional pad via COREMARK_MEM_PAD_BYTES)
	@echo -e "$(YELLOW)[COREMARK] Generating .mem file for 128-bit cache line...$(RESET)"
	@python3 $(ELF_TO_MEM) \
		--in $(COREMARK_BIN) \
		--out $(COREMARK_MEM_128) \
		--addr 0x80000000 \
		--block-bytes 16 \
		--word-size 4 \
		--word-endian little \
		--word-order high-to-low \
		$(COREMARK_ELF_TO_MEM_EXTRA)
	@echo -e "$(GREEN)[COREMARK] $(SUCCESS) Build successful$(RESET)"

# ============================================================
# 4.5 Run CoreMark Simulation
# ============================================================
# CoreMark log directory
COREMARK_LOG_DIR := $(RESULTS_DIR)/logs/$(SIM)/coremark

# Main run target - build if needed, then simulate
# CoreMark RTL sim needs tens of millions of cycles. Global MAX_CYCLES ?= 100000 is for ISA tests;
# if you did not pass MAX_CYCLES on the command line, use 50M (matches coremark.conf intent).
run_coremark: coremark
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running CoreMark Simulation$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@# Clean previous CoreMark logs
	@if [ -d "$(COREMARK_LOG_DIR)" ]; then \
		echo -e "$(CYAN)[CLEAN]$(RESET) Removing previous CoreMark logs: $(COREMARK_LOG_DIR)"; \
		rm -rf "$(COREMARK_LOG_DIR)"; \
	fi
	@$(MKDIR) "$(COREMARK_LOG_DIR)"
	@echo -e "$(YELLOW)[INFO]$(RESET) MEM File: $(COREMARK_MEM)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Log Dir:  $(COREMARK_LOG_DIR)"
	@set -e; \
	if [ "$(origin MAX_CYCLES)" = "command line" ]; then \
	  CM_MAX="$(MAX_CYCLES)"; \
	  if [ "$$CM_MAX" -lt 1000000 ] 2>/dev/null; then \
	    echo -e "$(YELLOW)[WARN]$(RESET) MAX_CYCLES=$$CM_MAX is very low — CoreMark will stop before UART prints Iterations/Sec / crc lines."; \
	  fi; \
	else \
	  CM_MAX=50000000; \
	fi; \
	echo -e "$(YELLOW)[INFO]$(RESET) Max Cycles: $$CM_MAX"; \
	$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=coremark \
		TEST_CONFIG=coremark \
		MEM_FILE=$(COREMARK_MEM) \
		NO_ADDR=1 \
		MAX_CYCLES=$$CM_MAX \
		VERILATOR_LOG_DIR=$(COREMARK_LOG_DIR)
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  CoreMark Simulation Complete$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@if [ -f "$(COREMARK_LOG_DIR)/uart_output.log" ]; then \
		echo -e "$(YELLOW)[UART OUTPUT]$(RESET)"; \
		cat "$(COREMARK_LOG_DIR)/uart_output.log"; \
	fi

# ============================================================
# 5 Clean
# ============================================================

coremark_clean:
	@echo -e "$(RED)[COREMARK] Cleaning build artifacts...$(RESET)"
	@rm -rf $(COREMARK_BUILD_DIR)
	@if [ -d "$(COREMARK_SRC_DIR)" ]; then \
		$(MAKE) -C $(COREMARK_SRC_DIR) PORT_DIR=levelv clean 2>/dev/null || true; \
	fi
	@rm -rf $(COREMARK_PORT_DST)
	@rm -rf $(COREMARK_SRC_DIR)/spike-pk 2>/dev/null || true
	@echo -e "$(GREEN)[COREMARK] $(SUCCESS) Clean complete$(RESET)"

# ============================================================
# 6 Help
# ============================================================

coremark_help:
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)  Level CoreMark Build & Run System$(RESET)"
	@echo -e "$(GREEN)  Target: Level-V RV32IMC_Zicsr Processor$(RESET)"
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Build Targets:$(RESET)"
	@echo -e "  make coremark              - Full build pipeline"
	@echo -e "  make coremark_check        - Check/clone CoreMark source"
	@echo -e "  make coremark_setup        - Copy Level-V port files"
	@echo -e "  make coremark_gen_linker   - Generate linker script from YAML"
	@echo -e "  make coremark_build        - Build CoreMark"
	@echo -e "  make coremark_clean        - Clean build artifacts"
	@echo ""
	@echo -e "$(YELLOW)Run Targets:$(RESET)"
	@echo -e "  make run_coremark          - Build (if needed) and run Verilator sim"
	@echo ""
	@echo -e "$(YELLOW)Configuration:$(RESET)"
	@echo -e "  CPU_CLK_HZ=N               - Bare-metal C clock (default: 25000000); match rtl/pkg/level_param.sv"
	@echo -e "  COREMARK_MEM_PAD_BYTES=N  - Pad coremark*.mem to N bytes (0=minimal; 34816=legacy 34KiB)"
	@echo -e "  COREMARK_ITERATIONS=N      - Set iteration count (default: 1)"
	@echo -e "  MAX_CYCLES=N               - Max simulation cycles (default: 5000000)"
	@echo -e "  $(CYAN)SIM_FAST=1$(RESET)               - $(CYAN)Disable trace and loggers$(RESET)"
	@echo -e "  $(CYAN)MINIMAL_SOC=1$(RESET)            - $(CYAN)Small cache/BP; L2 on by default$(RESET)"
	@echo -e "  $(CYAN)MINIMAL_NO_L2=1$(RESET)         - $(CYAN)With MINIMAL_SOC: direct mem arbiter (faster sim, no L2)$(RESET)"
	@echo -e "  $(CYAN)NO_L2_CACHE=1$(RESET)          - $(CYAN)Force memory arbiter instead of L2$(RESET)"
	@echo -e "  $(CYAN)+uart_finish_pattern=STR$(RESET) - $(CYAN)Verilator plusarg: stop sim after TX sends this substring (default: CoreMark Complete!)$(RESET)"
	@echo -e "  $(CYAN)THREADS=N$(RESET)                - $(CYAN)Enable multi-threaded simulation$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)MINIMAL_SOC Mode:$(RESET)"
	@echo -e "  Cache: 4KB I$ + 2KB D$ (instead of 8KB each; I$ sized for stable L2 sim)"
	@echo -e "  Memory: L2 on (use MINIMAL_NO_L2=1 to skip L2)"
	@echo -e "  BP: PHT=64, BTB=32, GHR=8 (instead of 512/256/24)"
	@echo -e "  Compile time: ~40-50%% faster"
	@echo -e "  Sim speed: ~20-30%% faster"
	@echo ""
	@echo -e "$(YELLOW)Memory Map:$(RESET)"
	@echo -e "  Edit: $(COREMARK_PORT_SRC)/memory_map.yaml"
	@echo -e "  Linker script is auto-generated from memory map"
	@echo ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make run_coremark"
	@echo -e "  make run_coremark MAX_CYCLES=10000000 SIM_FAST=1 TRACE=0"
	@echo -e "  make coremark COREMARK_ITERATIONS=0 && make run_coremark MAX_CYCLES=2000000 SIM_FAST=1 MINIMAL_SOC=1 TRACE=0"
	@echo -e "  make coremark COREMARK_ITERATIONS=2000"
	@echo -e "  make coremark_clean coremark         # Clean rebuild"
	@echo ""
	@echo -e "$(YELLOW)Output Files (in $(COREMARK_BUILD_DIR)):$(RESET)"
	@echo -e "  coremark.elf   - ELF executable"
	@echo -e "  coremark.bin   - Raw binary"
	@echo -e "  coremark.hex   - Intel HEX format"
	@echo -e "  coremark.mem   - Verilog memory file"
	@echo -e "  coremark.dump  - Disassembly listing"
	@echo ""
	@echo -e "$(YELLOW)Simulation Logs (in $(COREMARK_LOG_DIR)):$(RESET)"
	@echo -e "  uart_output.log  - UART output (CoreMark results)"
	@echo -e "  level.log        - Pipeline trace"
	@echo -e "  waveform.fst     - Waveform dump"
	@echo ""

# ====== test/test_lists.mk ======
# ============================================================
# Level RISC-V — Test List Shortcuts
# ============================================================
# Run test lists via short target names
#
# Usage:
#   make isa          - Run all ISA tests
#   make csr          - Run CSR tests
#   make bench        - Run benchmarks (NO_ADDR=1)
#   make all_tests    - Run all tests
#   make quick        - Quick smoke (~5 min): ISA + CSR
#   make full         - Full suite (~30 min): ISA + Arch + Imperas + CSR
#   make nightly      - Nightly build (full + CoreMark + benchmarks)
# ============================================================

# -----------------------------------------
# Regression Results Directory
# -----------------------------------------
REGRESSION_DIR     := $(RESULTS_DIR)/regression
REGRESSION_SUMMARY := $(REGRESSION_DIR)/latest_summary.txt

# -----------------------------------------
# Test List Paths
# -----------------------------------------
TEST_LIST_DIR := $(SIM_DIR)/test

# Test list files
FLIST_ISA       := $(TEST_LIST_DIR)/riscv_test_list.flist
FLIST_CSR       := $(TEST_LIST_DIR)/machine_csr_test.flist
FLIST_BENCH     := $(TEST_LIST_DIR)/riscv_benchmark.flist
FLIST_ALL       := $(TEST_LIST_DIR)/all_tests.flist
FLIST_EXCEPTION := $(TEST_LIST_DIR)/exception_test.flist
FLIST_ARCH      := $(TEST_LIST_DIR)/arch_test.flist
FLIST_BRANCH    := $(TEST_LIST_DIR)/branch_test.flist

# -----------------------------------------
# Batch suites → run_flist (single template)
# $(1)=target $(2)=banner $(3)=FLIST variable name $(4)=TEST_TYPE $(5)=MAX_* variable name $(6)=extra make arguments)
# -----------------------------------------
ISA_MAX_CYCLES ?= 10000
CSR_MAX_CYCLES ?= 10000
EXC_MAX_CYCLES ?= 10000
BRANCH_MAX_CYCLES ?= 100000

define SUITE_RUN_FLIST
.PHONY: $(1)
$(1):
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  $(2)$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$($(3)) \
		TEST_TYPE=$(4) \
		SIM=$(SIM) \
		MAX_CYCLES=$($(5)) \
		$(6)
endef

$(eval $(call SUITE_RUN_FLIST,isa,Running RISC-V ISA Tests,FLIST_ISA,isa,ISA_MAX_CYCLES,))
$(eval $(call SUITE_RUN_FLIST,csr,Running Machine CSR Tests,FLIST_CSR,isa,CSR_MAX_CYCLES,))
$(eval $(call SUITE_RUN_FLIST,all_tests,Running ALL Tests,FLIST_ALL,isa,ISA_MAX_CYCLES,))
$(eval $(call SUITE_RUN_FLIST,exc,Running Exception Tests,FLIST_EXCEPTION,isa,EXC_MAX_CYCLES,))
$(eval $(call SUITE_RUN_FLIST,branch,Running Branch Predictor Tests (ISA list),FLIST_BRANCH,isa,BRANCH_MAX_CYCLES,TEST_CONFIG=branch_test))

# -----------------------------------------
# Benchmarks (NO_ADDR=1)
# -----------------------------------------
.PHONY: bench

# Benchmark cycle limit (override with BENCH_MAX_CYCLES=N)
BENCH_MAX_CYCLES ?= 1000000

bench:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running RISC-V Benchmarks$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_bench_flist \
		FLIST=$(FLIST_BENCH) \
		SIM=$(SIM) \
		MAX_CYCLES=$(BENCH_MAX_CYCLES)

# -----------------------------------------
# Architecture Tests (riscv-arch-test)
# -----------------------------------------
.PHONY: arch

ARCH_MAX_CYCLES ?= 100000

arch:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running RISC-V Architecture Tests$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@if [ ! -f "$(FLIST_ARCH)" ]; then \
		echo -e "$(YELLOW)[INFO] Generating arch test list...$(RESET)"; \
		$(MAKE) --no-print-directory arch_gen_flist; \
	fi
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_ARCH) \
		TEST_TYPE=arch \
		SIM=$(SIM) \
		MAX_CYCLES=$(ARCH_MAX_CYCLES)

# Generate arch test flist from built tests
.PHONY: arch_gen_flist
arch_gen_flist:
	@echo -e "$(YELLOW)[GEN] Generating arch_test.flist...$(RESET)"
	@mkdir -p $(TEST_LIST_DIR)
	@echo "# RISC-V Architecture Tests" > $(FLIST_ARCH)
	@echo "# Auto-generated from build/tests/riscv-arch-test/elf" >> $(FLIST_ARCH)
	@if [ -d "$(BUILD_DIR)/tests/riscv-arch-test/elf" ]; then \
		for elf in $(BUILD_DIR)/tests/riscv-arch-test/elf/*.elf; do \
			if [ -f "$$elf" ]; then \
				basename $$elf .elf >> $(FLIST_ARCH); \
			fi; \
		done; \
		echo -e "$(GREEN)[OK] Generated $(FLIST_ARCH)$(RESET)"; \
	else \
		echo -e "$(RED)[ERROR] No arch tests found. Run 'make arch_auto' first.$(RESET)"; \
	fi

# Quick arch test: make ta T=I-add-01
.PHONY: ta
ta:
ifndef T
	$(error Usage: make ta T=<arch_test_name> (e.g., I-add-01))
endif
	@$(MAKE) --no-print-directory run \
		TEST_NAME=$(T) \
		TEST_TYPE=arch \
		MEM_DIR="$(BUILD_DIR)/tests/riscv-arch-test/mem" \
		ELF_DIR="$(BUILD_DIR)/tests/riscv-arch-test/elf" \
		DUMP_DIR="$(BUILD_DIR)/tests/riscv-arch-test/dump" \
		ADDR_DIR="$(BUILD_DIR)/tests/riscv-arch-test/pass_fail_addr" \
		TEST_LOG_DIR="$(RESULTS_DIR)/logs/verilator/arch/$(T)" \
		RTL_LOG_DIR="$(RESULTS_DIR)/logs/verilator/arch/$(T)" \
		SIM=verilator

# -----------------------------------------
# Universal Test Shortcut with Auto-Detection
# -----------------------------------------
# make test T=<test_name>   - Auto-detects test type and runs with Spike comparison
# 
# Detection patterns:
#   rv32*-p-*, rv64*-p-*  → ISA tests
#   *-01, *-02, etc.      → Arch tests
#   I-*, M-*, A-*, C-*    → Could be Imperas or Arch (file-based detection)
#   median, dhrystone     → Benchmarks
#
.PHONY: test
test:
ifndef T
	$(error Usage: make test T=<test_name>  (auto-detects type))
endif
	@echo -e "$(CYAN)[AUTO-DETECT]$(RESET) Searching for test: $(T)"
	@# File-based detection with priority: arch > imperas > isa > bench
	@if [ -f "$(BUILD_DIR)/tests/riscv-arch-test/elf/$(T).elf" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: arch (riscv-arch-test)"; \
		$(MAKE) --no-print-directory run TEST_NAME=$(T) TEST_TYPE=arch; \
	elif [ -f "$(BUILD_DIR)/tests/imperas/elf/$(T).elf" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: imperas"; \
		$(MAKE) --no-print-directory run TEST_NAME=$(T) TEST_TYPE=imperas; \
	elif [ -f "$(BUILD_DIR)/tests/riscv-tests/elf/$(T)" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: isa (riscv-tests)"; \
		$(MAKE) --no-print-directory run TEST_NAME=$(T) TEST_TYPE=isa; \
	elif [ -f "$(BUILD_DIR)/tests/riscv-benchmarks/elf/$(T)" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: bench (riscv-benchmarks)"; \
		$(MAKE) --no-print-directory run TEST_NAME=$(T) TEST_TYPE=bench NO_ADDR=1; \
	else \
		echo -e "$(RED)[ERROR]$(RESET) Test '$(T)' not found in any test directory."; \
		echo -e "$(YELLOW)Searched in:$(RESET)"; \
		echo -e "  - $(BUILD_DIR)/tests/riscv-arch-test/elf/$(T).elf"; \
		echo -e "  - $(BUILD_DIR)/tests/imperas/elf/$(T).elf"; \
		echo -e "  - $(BUILD_DIR)/tests/riscv-tests/elf/$(T)"; \
		echo -e "  - $(BUILD_DIR)/tests/riscv-benchmarks/elf/$(T)"; \
		echo -e "$(YELLOW)Available tests:$(RESET)"; \
		echo -e "  make list_tests    - List all ISA tests"; \
		echo -e "  make list_arch     - List all arch tests"; \
		echo -e "  make list_imperas  - List all Imperas tests"; \
		exit 1; \
	fi

# Quick version (Verilator only, no Spike comparison)
.PHONY: qt
qt:
ifndef T
	$(error Usage: make qt T=<test_name>  (quick test, auto-detects type))
endif
	@echo -e "$(CYAN)[AUTO-DETECT]$(RESET) Quick test: $(T)"
	@if [ -f "$(BUILD_DIR)/tests/riscv-arch-test/elf/$(T).elf" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: arch"; \
		$(MAKE) --no-print-directory run_verilator TEST_NAME=$(T) TEST_TYPE=arch; \
	elif [ -f "$(BUILD_DIR)/tests/imperas/elf/$(T).elf" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: imperas"; \
		$(MAKE) --no-print-directory run_verilator TEST_NAME=$(T) TEST_TYPE=imperas; \
	elif [ -f "$(BUILD_DIR)/tests/riscv-tests/elf/$(T)" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: isa"; \
		$(MAKE) --no-print-directory run_verilator TEST_NAME=$(T) TEST_TYPE=isa; \
	elif [ -f "$(BUILD_DIR)/tests/riscv-benchmarks/elf/$(T)" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: bench"; \
		$(MAKE) --no-print-directory run_verilator TEST_NAME=$(T) TEST_TYPE=bench NO_ADDR=1; \
	else \
		echo -e "$(RED)[ERROR]$(RESET) Test '$(T)' not found."; \
		exit 1; \
	fi

# ============================================================
# REGRESSION TEST SUITES
# ============================================================
# Commands for different test coverage levels
# ============================================================

# -----------------------------------------
# Quick Smoke Test (~5 min)
# -----------------------------------------
# Quick check of critical tests
.PHONY: quick

quick:
	@echo -e ""
	@echo -e "$(CYAN)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║           Level RISC-V — Quick Smoke Test                   ║$(RESET)"
	@echo -e "$(CYAN)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo -e ""
	@mkdir -p $(REGRESSION_DIR)
	@START_TIME=$$(date +%s); \
	TOTAL_PASS=0; TOTAL_FAIL=0; \
	echo -e "$(YELLOW)[1/2] Running ISA tests...$(RESET)"; \
	if $(MAKE) --no-print-directory isa CLEAN_LOGS=1 2>&1 | tee $(REGRESSION_DIR)/quick_isa.log | tail -5; then \
		ISA_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/quick_isa.log 2>/dev/null || echo 0); \
		ISA_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/quick_isa.log 2>/dev/null || echo 0); \
	else \
		ISA_PASS=0; ISA_FAIL=1; \
	fi; \
	echo -e "$(YELLOW)[2/2] Running CSR tests...$(RESET)"; \
	if $(MAKE) --no-print-directory csr 2>&1 | tee $(REGRESSION_DIR)/quick_csr.log | tail -5; then \
		CSR_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/quick_csr.log 2>/dev/null || echo 0); \
		CSR_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/quick_csr.log 2>/dev/null || echo 0); \
	else \
		CSR_PASS=0; CSR_FAIL=1; \
	fi; \
	END_TIME=$$(date +%s); \
	DURATION=$$((END_TIME - START_TIME)); \
	echo -e ""; \
	echo -e "$(GREEN)╔══════════════════════════════════════════════════════════════╗$(RESET)"; \
	echo -e "$(GREEN)║                    Quick Test Summary                        ║$(RESET)"; \
	echo -e "$(GREEN)╠══════════════════════════════════════════════════════════════╣$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  ISA Tests:  $$ISA_PASS passed, $$ISA_FAIL failed                       $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  CSR Tests:  $$CSR_PASS passed, $$CSR_FAIL failed                       $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)╠══════════════════════════════════════════════════════════════╣$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  Duration: $${DURATION}s                                              $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)╚══════════════════════════════════════════════════════════════╝$(RESET)"; \
	if [ $$ISA_FAIL -gt 0 ] || [ $$CSR_FAIL -gt 0 ]; then exit 1; fi

# -----------------------------------------
# Full Test Suite (~30 min)
# -----------------------------------------
# ISA + Arch + Imperas + CSR
.PHONY: full

full:
	@echo -e ""
	@echo -e "$(CYAN)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║           Level RISC-V — Full Regression Suite              ║$(RESET)"
	@echo -e "$(CYAN)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo -e ""
	@mkdir -p $(REGRESSION_DIR)
	@REPORT=$(REGRESSION_DIR)/report_$$(date +%Y%m%d_%H%M%S).txt; \
	echo "Level RISC-V Regression Report" > $$REPORT; \
	echo "Date: $$(date)" >> $$REPORT; \
	echo "============================================" >> $$REPORT; \
	START_TIME=$$(date +%s); \
	ISA_PASS=0; ISA_FAIL=0; \
	ARCH_PASS=0; ARCH_FAIL=0; \
	IMP_PASS=0; IMP_FAIL=0; \
	CSR_PASS=0; CSR_FAIL=0; \
	echo -e "$(YELLOW)[1/4] Running ISA tests...$(RESET)"; \
	if $(MAKE) --no-print-directory isa CLEAN_LOGS=1 2>&1 | tee $(REGRESSION_DIR)/reg_isa.log; then \
		ISA_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/reg_isa.log 2>/dev/null || true); \
		ISA_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/reg_isa.log 2>/dev/null || true); \
	fi; \
	ISA_PASS=$${ISA_PASS:-0}; ISA_FAIL=$${ISA_FAIL:-0}; \
	echo "ISA: $$ISA_PASS passed, $$ISA_FAIL failed" >> $$REPORT; \
	echo -e "$(YELLOW)[2/4] Running Architecture tests...$(RESET)"; \
	if $(MAKE) --no-print-directory arch 2>&1 | tee $(REGRESSION_DIR)/reg_arch.log; then \
		ARCH_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/reg_arch.log 2>/dev/null || true); \
		ARCH_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/reg_arch.log 2>/dev/null || true); \
	fi; \
	ARCH_PASS=$${ARCH_PASS:-0}; ARCH_FAIL=$${ARCH_FAIL:-0}; \
	echo "ARCH: $$ARCH_PASS passed, $$ARCH_FAIL failed" >> $$REPORT; \
	echo -e "$(YELLOW)[3/4] Running Imperas tests...$(RESET)"; \
	if $(MAKE) --no-print-directory imperas 2>&1 | tee $(REGRESSION_DIR)/reg_imperas.log; then \
		IMP_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/reg_imperas.log 2>/dev/null || true); \
		IMP_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/reg_imperas.log 2>/dev/null || true); \
	fi; \
	IMP_PASS=$${IMP_PASS:-0}; IMP_FAIL=$${IMP_FAIL:-0}; \
	echo "IMPERAS: $$IMP_PASS passed, $$IMP_FAIL failed" >> $$REPORT; \
	echo -e "$(YELLOW)[4/4] Running CSR tests...$(RESET)"; \
	if $(MAKE) --no-print-directory csr 2>&1 | tee $(REGRESSION_DIR)/reg_csr.log; then \
		CSR_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/reg_csr.log 2>/dev/null || true); \
		CSR_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/reg_csr.log 2>/dev/null || true); \
	fi; \
	CSR_PASS=$${CSR_PASS:-0}; CSR_FAIL=$${CSR_FAIL:-0}; \
	echo "CSR: $$CSR_PASS passed, $$CSR_FAIL failed" >> $$REPORT; \
	END_TIME=$$(date +%s); \
	DURATION=$$((END_TIME - START_TIME)); \
	TOTAL_PASS=$$((ISA_PASS + ARCH_PASS + IMP_PASS + CSR_PASS)); \
	TOTAL_FAIL=$$((ISA_FAIL + ARCH_FAIL + IMP_FAIL + CSR_FAIL)); \
	echo "============================================" >> $$REPORT; \
	echo "TOTAL: $$TOTAL_PASS passed, $$TOTAL_FAIL failed" >> $$REPORT; \
	echo "Duration: $${DURATION}s" >> $$REPORT; \
	cp $$REPORT $(REGRESSION_SUMMARY); \
	echo -e ""; \
	echo -e "$(GREEN)╔══════════════════════════════════════════════════════════════╗$(RESET)"; \
	echo -e "$(GREEN)║                 Full Regression Summary                      ║$(RESET)"; \
	echo -e "$(GREEN)╠══════════════════════════════════════════════════════════════╣$(RESET)"; \
	printf "$(GREEN)║$(RESET)  %-12s  %3d passed, %3d failed                      $(GREEN)║$(RESET)\n" "ISA:" $$ISA_PASS $$ISA_FAIL; \
	printf "$(GREEN)║$(RESET)  %-12s  %3d passed, %3d failed                      $(GREEN)║$(RESET)\n" "ARCH:" $$ARCH_PASS $$ARCH_FAIL; \
	printf "$(GREEN)║$(RESET)  %-12s  %3d passed, %3d failed                      $(GREEN)║$(RESET)\n" "IMPERAS:" $$IMP_PASS $$IMP_FAIL; \
	printf "$(GREEN)║$(RESET)  %-12s  %3d passed, %3d failed                      $(GREEN)║$(RESET)\n" "CSR:" $$CSR_PASS $$CSR_FAIL; \
	echo -e "$(GREEN)╠══════════════════════════════════════════════════════════════╣$(RESET)"; \
	printf "$(GREEN)║$(RESET)  %-12s  %3d passed, %3d failed                      $(GREEN)║$(RESET)\n" "TOTAL:" $$TOTAL_PASS $$TOTAL_FAIL; \
	echo -e "$(GREEN)║$(RESET)  Duration: $${DURATION}s                                             $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  Report: $$REPORT  $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)╚══════════════════════════════════════════════════════════════╝$(RESET)"; \
	if [ $$TOTAL_FAIL -gt 0 ]; then \
		echo -e "$(RED)$(WARN)  $$TOTAL_FAIL test(s) failed!$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)🎉 All tests passed!$(RESET)"; \
	fi

# -----------------------------------------
# Nightly Build (Full + Benchmarks + CoreMark)
# -----------------------------------------
.PHONY: nightly

nightly:
	@echo -e ""
	@echo -e "$(CYAN)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║           Level RISC-V — Nightly Build Suite                ║$(RESET)"
	@echo -e "$(CYAN)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo -e ""
	@mkdir -p $(REGRESSION_DIR)
	@REPORT=$(REGRESSION_DIR)/nightly_$$(date +%Y%m%d_%H%M%S).txt; \
	START_TIME=$$(date +%s); \
	echo "Level RISC-V Nightly Build Report" > $$REPORT; \
	echo "Date: $$(date)" >> $$REPORT; \
	echo "============================================" >> $$REPORT; \
	echo -e "$(YELLOW)[1/3] Running full regression...$(RESET)"; \
	$(MAKE) --no-print-directory full 2>&1 | tee -a $$REPORT || true; \
	echo -e "$(YELLOW)[2/3] Running benchmarks...$(RESET)"; \
	$(MAKE) --no-print-directory bench 2>&1 | tee $(REGRESSION_DIR)/nightly_bench.log || true; \
	BENCH_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/nightly_bench.log 2>/dev/null || echo 0); \
	BENCH_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/nightly_bench.log 2>/dev/null || echo 0); \
	echo "BENCH: $$BENCH_PASS passed, $$BENCH_FAIL failed" >> $$REPORT; \
	echo -e "$(YELLOW)[3/3] Running CoreMark...$(RESET)"; \
	$(MAKE) --no-print-directory run_coremark MAX_CYCLES=10000000 2>&1 | tee $(REGRESSION_DIR)/nightly_coremark.log || true; \
	if grep -q "CoreMark" $(REGRESSION_DIR)/nightly_coremark.log 2>/dev/null; then \
		COREMARK_SCORE=$$(grep -oP "CoreMark.*?:\s*\K[\d.]+" $(REGRESSION_DIR)/nightly_coremark.log 2>/dev/null || echo "N/A"); \
		echo "CoreMark Score: $$COREMARK_SCORE" >> $$REPORT; \
	fi; \
	END_TIME=$$(date +%s); \
	DURATION=$$((END_TIME - START_TIME)); \
	echo "============================================" >> $$REPORT; \
	echo "Total Duration: $${DURATION}s" >> $$REPORT; \
	echo -e ""; \
	echo -e "$(GREEN)╔══════════════════════════════════════════════════════════════╗$(RESET)"; \
	echo -e "$(GREEN)║                  Nightly Build Complete                      ║$(RESET)"; \
	echo -e "$(GREEN)╠══════════════════════════════════════════════════════════════╣$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  Duration: $${DURATION}s                                             $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  Report: $$REPORT  $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)╚══════════════════════════════════════════════════════════════╝$(RESET)"

# -----------------------------------------
# Benchmark List Runner (NO_ADDR=1)
# -----------------------------------------
.PHONY: run_bench_flist

run_bench_flist:
	@if [ ! -f "$(FLIST)" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Test list file not found: $(FLIST)"; \
		exit 1; \
	fi
	@$(MKDIR) "$(LOG_DIR)"
	@# Clean all logs for this simulator if CLEAN_LOGS=1
	@if [ "$(CLEAN_LOGS)" = "1" ]; then \
		echo -e "$(CYAN)[CLEAN]$(RESET) Removing all previous logs: $(RESULTS_DIR)/logs/$(SIM)/"; \
		rm -rf "$(RESULTS_DIR)/logs/$(SIM)/"*; \
	fi
	@echo -n "" > $(PASS_LIST_FILE)
	@echo -n "" > $(FAIL_LIST_FILE)
	@echo -e "$(GREEN)Running benchmarks from list file:$(RESET) $(FLIST)"
	@echo -e "$(CYAN)Output directory:$(RESET) $(RESULTS_DIR)/logs/$(SIM)/"
	@PASS=0; FAIL=0; TOTAL=0; \
	while IFS= read -r test || [ -n "$${test}" ]; do \
		test="$${test%% }"; test="$${test## }"; \
		if echo "$${test}" | grep -E '^\s*#' >/dev/null || [ -z "$${test}" ]; then continue; fi; \
		TOTAL=$$(( $${TOTAL} + 1 )); \
		TEST_LOG_DIR="$(RESULTS_DIR)/logs/$(SIM)/$${test}"; \
		if [ -d "$${TEST_LOG_DIR}" ]; then \
			rm -rf "$${TEST_LOG_DIR}"; \
		fi; \
		mkdir -p "$${TEST_LOG_DIR}"; \
		echo -e ""; \
		echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		echo -e "$(CYAN)[BENCH] Test $${TOTAL}: $${test}$(RESET)"; \
		echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		if $(MAKE) --no-print-directory run_verilator \
			TEST_NAME=$${test} \
			TEST_TYPE=bench \
			NO_ADDR=1 \
			MAX_CYCLES=$(MAX_CYCLES) \
			VERILATOR_LOG_DIR=$${TEST_LOG_DIR} > "$${TEST_LOG_DIR}/summary.log" 2>&1; then \
			PASS=$$(( $${PASS} + 1 )); \
			echo "$${test}" >> "$(PASS_LIST_FILE)"; \
			echo -e "$(GREEN)$(SUCCESS) $${test} PASSED$(RESET)"; \
		else \
			TEST_EXIT=$$?; \
			FAIL=$$(( $${FAIL} + 1 )); \
			echo "$${test}" >> "$(FAIL_LIST_FILE)"; \
			echo -e "$(RED)✗ $${test} FAILED (exit code: $${TEST_EXIT})$(RESET)"; \
			echo -e "$(YELLOW)  ↳ Summary log: $${TEST_LOG_DIR}/summary.log$(RESET)"; \
		fi; \
	done < "$(FLIST)"; \
	echo -e ""; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN) Benchmark Summary$(RESET)"; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN)✅ Passed: $${PASS}$(RESET)"; \
	echo -e "$(RED)$(ERROR) Failed: $${FAIL}$(RESET)"; \
	echo -e "$(CYAN)📊 Total:  $${TOTAL}$(RESET)"; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	if [ $${FAIL} -gt 0 ]; then \
		echo -e "$(RED)$(WARN)  $${FAIL} benchmark(s) failed$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)🎉 All benchmarks passed!$(RESET)"; \
	fi

# -----------------------------------------
# Quick Single Test Shortcuts
# -----------------------------------------
.PHONY: t tb

# Quick ISA test: make t T=rv32ui-p-add
t:
ifndef T
	$(error Usage: make t T=<test_name>)
endif
	@$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=$(T) \
		TEST_TYPE=isa \
		SIM=verilator

# Quick benchmark test: make tb T=dhrystone
tb:
ifndef T
	$(error Usage: make tb T=<benchmark_name>)
endif
	@$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=$(T) \
		TEST_TYPE=bench \
		NO_ADDR=1 \
		MAX_CYCLES=$(or $(MAX_CYCLES),1000000) \
		SIM=verilator

# -----------------------------------------
# Help
# -----------------------------------------
.PHONY: help_lists

help_lists:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)            Level RISC-V — Test Automation                    $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  REGRESSION SUITES$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make quick$(RESET)        – Quick smoke test (~5 min) [ISA + CSR]"
	@echo -e "  $(GREEN)make full$(RESET)         – Full regression (~30 min) [ISA + Arch + Imperas + CSR]"
	@echo -e "  $(GREEN)make nightly$(RESET)      – Nightly build (full + benchmarks + CoreMark)"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  INDIVIDUAL TEST SUITES$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make isa$(RESET)          – Run ISA tests (rv32ui, rv32um, rv32uc)"
	@echo -e "  $(GREEN)make csr$(RESET)          – Run machine CSR tests (rv32mi)"
	@echo -e "  $(GREEN)make arch$(RESET)         – Run architecture tests (I: 38, M: 8, C: 27)"
	@echo -e "  $(GREEN)make imperas$(RESET)      – Run Imperas tests (45 tests)"
	@echo -e "  $(GREEN)make bench$(RESET)        – Run benchmarks [NO_ADDR=1]"
	@echo -e "  $(GREEN)make exc$(RESET)          – Run exception tests"
	@echo -e "  $(GREEN)make branch$(RESET)       – Run branch predictor tests (30 tests, LOG_BP=1)"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  COREMARK$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make cm$(RESET)           – Build and run CoreMark"
	@echo -e "  $(GREEN)make run_coremark$(RESET) – CoreMark (Verilator)"
	@echo -e "  $(GREEN)make coremark_help$(RESET)– Detailed CoreMark help"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  QUICK SINGLE TEST$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make t T=rv32ui-p-add$(RESET)   – Quick ISA test"
	@echo -e "  $(GREEN)make ta T=I-add-01$(RESET)      – Quick arch test"
	@echo -e "  $(GREEN)make ti T=I-ADD-01$(RESET)      – Quick Imperas test"
	@echo -e "  $(GREEN)make tb T=dhrystone$(RESET)     – Quick benchmark [NO_ADDR=1]"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  COVERAGE$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make coverage$(RESET)      – Full coverage (ISA + Arch tests)"
	@echo -e "  $(GREEN)make coverage-quick$(RESET)– Quick coverage (ISA only)"
	@echo -e "  $(GREEN)make coverage-html$(RESET) – Generate HTML report"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  TEST PIPELINES$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make arch_auto$(RESET)     – Arch: Clone → Build → Import"
	@echo -e "  $(GREEN)make imperas_auto$(RESET)  – Imperas: Clone → Build → Import"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  OPTIONS$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  SIM=verilator|modelsim   – Simulator (default: verilator)"
	@echo -e "  CLEAN_LOGS=1             – Clear logs before batch run"
	@echo -e "  SIM_FAST=1               – Disable logging for speed"
	@echo -e "  COVERAGE=1               – Enable coverage collection"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make quick                        # Quick smoke test"
	@echo -e "  make full CLEAN_LOGS=1            # Full regression, clean logs first"
	@echo -e "  make coverage                     # Full coverage analysis"
	@echo -e "  make t T=rv32ui-p-add SIM_FAST=1  # Single fast test"
	@echo -e ""

# ====== custom_test.mk ======
# ============================================================================
# Custom Test Support - Makefile Integration
# ============================================================================
# Include this in your main makefile to support custom test building
# Usage: make custom_test TEST=my_test
#        make custom_help
# ============================================================================

# -----------------------------------------
# Custom Test Variables
# -----------------------------------------
CUSTOM_TEST_DIR    := $(SIM_DIR)/test/custom
CUSTOM_BUILD_DIR   := $(BUILD_DIR)/tests/custom
CUSTOM_SCRIPT      := $(SCRIPT_DIR)/shell/build_level_custom_c_test.sh
CUSTOM_CONFIG      := $(SCRIPT_DIR)/config/tests/custom.conf

# Load configuration if it exists
ifeq ($(wildcard $(CUSTOM_CONFIG)),$(CUSTOM_CONFIG))
  CUSTOM_MAX_CYCLES := $(shell awk -F= '/^MAX_CYCLES=/ {gsub(/^[[:space:]]+|[[:space:]]+$$/,"",$$2); print $$2; exit}' $(CUSTOM_CONFIG) 2>/dev/null)
  CUSTOM_MAX_CYCLES := $(or $(CUSTOM_MAX_CYCLES),100000)
else
  CUSTOM_MAX_CYCLES := 100000
endif

# Allow override from command line
MAX_CYCLES ?= $(CUSTOM_MAX_CYCLES)

# Coverage data directory
COVERAGE_DATA_DIR := $(RESULTS_DIR)/logs/verilator/coverage_data

# custom_run: level_wrapper parametreleri (Verilator -G). run_verilator → verilate
# her koşuda tetiklediği için burada bayrak yoksa model varsayılan (çoğu periph kapalı)
# ile yeniden derlenir. İsterseniz: make custom_run TEST=foo VERILATOR_GFLAGS="-G..."
TEST_VERILATOR_GFLAGS_gpio_test  := -GGPIO_EN=1
TEST_VERILATOR_GFLAGS_vga_test   := -GVGA_EN=1
TEST_VERILATOR_GFLAGS_pwm_test   := -GPWM_EN=1
TEST_VERILATOR_GFLAGS_plic_test  := -GPLIC_EN=1
TEST_VERILATOR_GFLAGS_wdt_test   := -GWDT_EN=1
TEST_VERILATOR_GFLAGS_dma_test   := -GDMA_EN=1
TEST_VERILATOR_GFLAGS_i2c_test   := -GI2C_EN=1
TEST_VERILATOR_GFLAGS_spi_test   := -GSPI_EN=1
TEST_VERILATOR_GFLAGS_timer_test := -GTIMER_EN=1
TEST_VERILATOR_GFLAGS_vga_demo  := -GVGA_EN=1

# Dynamically discover custom tests
CUSTOM_TESTS := $(patsubst $(CUSTOM_TEST_DIR)/%.c,%,$(wildcard $(CUSTOM_TEST_DIR)/*.c))


.PHONY: custom_help custom_test custom_build custom_run custom_clean custom_list custom_config

# Help
custom_help:
	@echo -e "$(CYAN)╔════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║$(RESET)  Custom UART Test Support$(RESET)"
	@echo -e "$(CYAN)╚════════════════════════════════════════════════════════════╝$(RESET)"
	@echo ""
	@echo -e "$(GREEN)Available Commands:$(RESET)"
	@echo -e "  $(YELLOW)make custom_list$(RESET)          - List available custom tests"
	@echo -e "  $(YELLOW)make custom_test TEST=<name>$(RESET) - Build and run custom test"
	@echo -e "  $(YELLOW)make custom_build TEST=<name>$(RESET) - Build custom test"
	@echo -e "  $(YELLOW)make custom_run TEST=<name>$(RESET) - Run custom test simulation"
	@echo -e "  $(YELLOW)(İpucu)$(RESET) peripheral testleri otomatik $(CYAN)-G…$(RESET) ile verilate eder; ek için $(CYAN)VERILATOR_GFLAGS$(RESET)"
	@echo -e "  $(YELLOW)make custom_clean TEST=<name>$(RESET) - Clean custom test artifacts"
	@echo -e "  $(YELLOW)make custom_config$(RESET)        - Show custom test configuration"
	@echo ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make custom_test TEST=uart_hello_test"
	@echo -e "  make custom_build TEST=my_test"
	@echo -e "  make custom_run TEST=my_test MAX_CYCLES=200000"
	@echo -e "  make custom_clean TEST=my_test"
	@echo ""
	@echo -e "$(YELLOW)Location:$(RESET)"
	@echo -e "  Source:  $(CUSTOM_TEST_DIR)/"
	@echo -e "  Build:   $(CUSTOM_BUILD_DIR)/"
	@echo ""

# List available tests
custom_list:
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)Available Custom Tests:$(RESET)"
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@if [ -z "$(CUSTOM_TESTS)" ]; then \
		echo -e "  $(YELLOW)No custom tests found in $(CUSTOM_TEST_DIR)$(RESET)"; \
	else \
		echo "$(CUSTOM_TESTS)" | tr ' ' '\n' | nl | awk '{printf "  %2d. %-30s\n", $$1, $$2}'; \
	fi
	@echo ""
	@echo -e "$(YELLOW)Usage:$(RESET)"
	@echo -e "  make custom_test TEST=<name>   - Build and run a test"
	@echo -e "  make custom_build TEST=<name>  - Build only"
	@echo -e "  make custom_run TEST=<name>    - Run only"
	@echo ""

# Build custom test
custom_build:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_build TEST=<test_name>"
	@echo -e "        Example: make custom_build TEST=uart_hello_test"
	@exit 1
endif
	@mkdir -p $(CUSTOM_BUILD_DIR)
	@echo -e "$(YELLOW)[BUILD]$(RESET) Compiling $(TEST)..."
	@if [ ! -f "$(CUSTOM_TEST_DIR)/$(TEST).c" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Test not found: $(CUSTOM_TEST_DIR)/$(TEST).c"; \
		exit 1; \
	fi
	@bash $(CUSTOM_SCRIPT) "$(TEST)" -n

# Run simulation
custom_run:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_run TEST=<test_name>"
	@exit 1
endif
	@echo -e "$(YELLOW)[RUN]$(RESET) Running $(TEST) simulation..."
	@if [ ! -f "$(CUSTOM_BUILD_DIR)/$(TEST).mem" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Memory file not found. Run 'make custom_build TEST=$(TEST)' first."; \
		exit 1; \
	fi
	@cd $(ROOT_DIR) && $(MAKE) run_verilator MEM_FILE="$(CUSTOM_BUILD_DIR)/$(TEST).mem" TEST_NAME="$(TEST)" MAX_CYCLES=$(MAX_CYCLES) LOG_UART=1 SIM_UART_MONITOR=1 COVERAGE_FILE="$(COVERAGE_DATA_DIR)/$(TEST).dat" VERILATOR_GFLAGS="$(strip $(VERILATOR_GFLAGS) $(TEST_VERILATOR_GFLAGS_$(TEST)))" 2>&1 | tee "$(CUSTOM_BUILD_DIR)/sim.log"
	@UART_LOG="$(LOG_DIR)/verilator/$(TEST)/uart_output.log"; \
	if [ -f "$$UART_LOG" ]; then \
		cp "$$UART_LOG" "$(CUSTOM_BUILD_DIR)/$(TEST)_uart.log"; \
		echo ""; \
		echo -e "$(CYAN)╔════════════════════════════════════════════╗$(RESET)"; \
		echo -e "$(CYAN)║$(RESET)  UART Output:                              $(CYAN)║$(RESET)"; \
		echo -e "$(CYAN)╚════════════════════════════════════════════╝$(RESET)"; \
		cat "$$UART_LOG"; \
	fi

# Build and Run (avoid double build)
custom_test:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_test TEST=<test_name>"
	@exit 1
endif
	@$(MAKE) custom_build TEST=$(TEST)
	@$(MAKE) custom_run TEST=$(TEST) MAX_CYCLES=$(MAX_CYCLES)

# Clean
custom_clean:
ifndef TEST
	@echo -e "$(YELLOW)[CLEAN]$(RESET) Removing all custom test artifacts..."
	@rm -rf $(CUSTOM_BUILD_DIR)/*
	@echo -e "$(GREEN)[OK]$(RESET) Cleaned"
else
	@echo -e "$(YELLOW)[CLEAN]$(RESET) Removing $(TEST) artifacts..."
	@rm -f $(CUSTOM_BUILD_DIR)/$(TEST).*
	@echo -e "$(GREEN)[OK]$(RESET) Cleaned $(TEST)"
endif
	@echo ""

# ============================================================================
# Utility Targets
# ============================================================================

.PHONY: custom_disass custom_size custom_hex

# Show disassembly
custom_disass:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_disass TEST=<test_name>"
	@exit 1
endif
	@if [ ! -f "$(CUSTOM_BUILD_DIR)/$(TEST).elf" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) ELF file not found"; \
		exit 1; \
	fi
	@riscv32-unknown-elf-objdump -d "$(CUSTOM_BUILD_DIR)/$(TEST).elf" | less

# Show size
custom_size:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_size TEST=<test_name>"
	@exit 1
endif
	@if [ ! -f "$(CUSTOM_BUILD_DIR)/$(TEST).elf" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) ELF file not found"; \
		exit 1; \
	fi
	@riscv32-unknown-elf-size "$(CUSTOM_BUILD_DIR)/$(TEST).elf"

# Show hex dump
custom_hex:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_hex TEST=<test_name>"
	@exit 1
endif
	@if [ ! -f "$(CUSTOM_BUILD_DIR)/$(TEST).elf" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) ELF file not found"; \
		exit 1; \
	fi
	@riscv32-unknown-elf-objdump -x "$(CUSTOM_BUILD_DIR)/$(TEST).elf" | head -40

# Print info
custom_info:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_info TEST=<test_name>"
	@exit 1
endif
	@mkdir -p $(CUSTOM_BUILD_DIR)
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)Custom Test Info: $(TEST)$(RESET)"
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Paths:$(RESET)"
	@echo "  Source:     $(CUSTOM_TEST_DIR)/$(TEST).c"
	@echo "  ELF:        $(CUSTOM_BUILD_DIR)/$(TEST).elf"
	@echo "  Binary:     $(CUSTOM_BUILD_DIR)/$(TEST).bin"
	@echo "  Memory:     $(CUSTOM_BUILD_DIR)/$(TEST).mem"
	@echo "  Disass:     $(CUSTOM_BUILD_DIR)/$(TEST).disass"
	@echo ""
	@echo -e "$(YELLOW)Build Status:$(RESET)"
	@if [ -f "$(CUSTOM_BUILD_DIR)/$(TEST).elf" ]; then \
		echo -e "  ELF:        $(GREEN)✓ Built$(RESET)"; \
		riscv32-unknown-elf-size "$(CUSTOM_BUILD_DIR)/$(TEST).elf" | tail -1 | \
			awk '{printf "  Size:       %s text + %s data + %s bss\n", $$1, $$2, $$3}'; \
	else \
		echo -e "  ELF:        $(RED)✗ Not built$(RESET)"; \
	fi
	@if [ -f "$(CUSTOM_BUILD_DIR)/$(TEST).mem" ]; then \
		echo -e "  Memory:     $(GREEN)✓ Generated$(RESET)"; \
	else \
		echo -e "  Memory:     $(RED)✗ Not generated$(RESET)"; \
	fi
	@echo ""

# Show configuration
custom_config:
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)Custom Test Configuration$(RESET)"
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Config File:$(RESET)"
	@echo "  $(CUSTOM_CONFIG)"
	@echo ""
	@echo -e "$(YELLOW)Simulation Settings:$(RESET)"
	@echo "  Max Cycles:    $(CUSTOM_MAX_CYCLES)"
	@echo "  Timeout:       30 seconds"
	@echo ""
	@echo -e "$(YELLOW)Directories:$(RESET)"
	@echo "  Source:        $(CUSTOM_TEST_DIR)/"
	@echo "  Build:         $(CUSTOM_BUILD_DIR)/"
	@echo ""
	@echo -e "$(YELLOW)Configuration Details:$(RESET)"
	@if [ -f "$(CUSTOM_CONFIG)" ]; then \
		echo "  UART Logging:  Enabled"; \
		echo "  Spike Compare: Disabled"; \
		echo "  Format:        .conf"; \
		echo "  File:          $(CUSTOM_CONFIG)"; \
	else \
		echo "  Config file not found"; \
	fi
	@echo ""

# ============================================================================
# Batch Operations
# ============================================================================

.PHONY: custom_run_all custom_build_all

# Build all custom tests
custom_build_all:
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)Building All Custom Tests$(RESET)"
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@if [ -z "$(CUSTOM_TESTS)" ]; then \
		echo -e "  $(YELLOW)No custom tests found$(RESET)"; \
	else \
		for test in $(CUSTOM_TESTS); do \
			echo -e "$(CYAN)[BUILD]$(RESET) $$test"; \
			$(MAKE) --no-print-directory custom_build TEST=$$test || exit 1; \
		done; \
	fi
	@echo -e "$(GREEN)[OK]$(RESET) All tests built"

# Run all custom tests from FLIST
custom_run_all:
	@if [ ! -f "$(SIM_DIR)/test/custom_tests.flist" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Test list not found: $(SIM_DIR)/test/custom_tests.flist"; \
		exit 1; \
	fi
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)Running Custom Tests from FLIST$(RESET)"
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@TOTAL=0; PASSED=0; FAILED=0; \
	while IFS= read -r test; do \
		[ -z "$$test" ] && continue; \
		TOTAL=$$((TOTAL + 1)); \
		echo -e ""; \
		echo -e "$(CYAN)[TEST $$TOTAL]$(RESET) Running $$test..."; \
		if [ ! -f "$(CUSTOM_BUILD_DIR)/$$test.mem" ]; then \
			echo -e "$(YELLOW)[BUILD]$(RESET) Building $$test..."; \
			$(MAKE) --no-print-directory custom_build TEST=$$test || { FAILED=$$((FAILED + 1)); continue; }; \
		fi; \
		if $(MAKE) --no-print-directory custom_run TEST=$$test MAX_CYCLES=$(MAX_CYCLES); then \
			PASSED=$$((PASSED + 1)); \
			echo -e "$(GREEN)[✓ PASS]$(RESET) $$test"; \
		else \
			FAILED=$$((FAILED + 1)); \
			echo -e "$(RED)[✗ FAIL]$(RESET) $$test"; \
		fi; \
	done < "$(SIM_DIR)/test/custom_tests.flist"; \
	echo ""; \
	echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"; \
	echo -e "$(CYAN)Test Results:$(RESET)"; \
	echo -e "  Total:   $$TOTAL"; \
	echo -e "  $(GREEN)Passed:  $$PASSED$(RESET)"; \
	if [ $$FAILED -gt 0 ]; then \
		echo -e "  $(RED)Failed:  $$FAILED$(RESET)"; \
	else \
		echo -e "  Failed:  $$FAILED"; \
	fi; \
	echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"

# ============================================================================
# Integration Targets
# ============================================================================

# Add to main help
help: custom_help_integration

custom_help_integration:
	@echo ""
	@echo -e "$(CYAN)Custom Tests:$(RESET)"
	@echo -e "  make custom_help             Show custom test help"
	@echo -e "  make custom_list             List available tests"
	@echo -e "  make custom_config           Show configuration"
	@echo -e "  make custom_test TEST=<name> Build and run single test"
	@echo -e "  make custom_build_all        Build all custom tests"
	@echo -e "  make custom_run_all          Run all custom tests from flist"
	@echo ""
	@echo -e "$(CYAN)BEEBS (submodule, GPL-3.0 — see env/beebs/README.md):$(RESET)"
	@echo -e "  make beebs_clone              git submodule update --init subrepo/beebs"
	@echo -e "  make beebs_build              ./configure && make (native host binaries)"
	@echo -e "  make beebs_help               Notes / RV32 port"
	@echo ""

.PHONY: custom_help_integration

# ====== BEEBS upstream (GPL-3.0) — git submodule + native host build ======
BEEBS_REPO_URL := https://github.com/mageec/beebs.git
BEEBS_ROOT     := $(SUBREPO_DIR)/beebs

.PHONY: beebs_clone beebs_build beebs_help beebs_distclean

beebs_clone:
	@echo -e "$(YELLOW)[BEEBS] git submodule update --init (shallow)$(RESET)"
	@cd "$(ROOT_DIR)" && git submodule update --init --depth 1 subrepo/beebs
	@echo -e "$(GREEN)[OK] subrepo/beebs ready. GPL-3.0 — see env/beebs/README.md$(RESET)"

# Native host build (gcc x86_64-linux-gnu). For RV32 bare-metal you still need a chip/board port.
beebs_build: beebs_clone
	@if [ ! -f "$(BEEBS_ROOT)/Makefile" ]; then \
		echo -e "$(YELLOW)[BEEBS] ./configure (first time)$(RESET)"; \
		cd "$(BEEBS_ROOT)" && ./configure; \
	fi
	@echo -e "$(YELLOW)[BEEBS] make -j$(RESET)"
	@$(MAKE) -C "$(BEEBS_ROOT)" -j $$(command -v nproc >/dev/null && nproc || echo 4)
	@echo -e "$(GREEN)[OK] BEEBS built under $(BEEBS_ROOT)/$(RESET)"

beebs_distclean:
	@if [ -f "$(BEEBS_ROOT)/Makefile" ]; then $(MAKE) -C "$(BEEBS_ROOT)" distclean; fi

beebs_help:
	@echo -e "$(CYAN)BEEBS — Bristol Embedded Energy Benchmark Suite$(RESET)"
	@echo -e "  Submodule: $(YELLOW)git submodule update --init --depth 1 subrepo/beebs$(RESET) or $(YELLOW)make beebs_clone$(RESET)"
	@echo -e "  Native build: $(YELLOW)make beebs_build$(RESET)  (./configure && make; host executables in src/*/)"
	@echo -e "  RV32 Level-V .mem: needs config/chip + config/board port — $(YELLOW)env/beebs/README.md$(RESET)"
	@echo -e "  Alternatives: $(YELLOW)make embench$(RESET) / $(YELLOW)make custom_build TEST=dsp_fir_mac_test$(RESET)"
	@echo ""

# ====== test/embench.mk ======
# ============================================================
# Embench-IoT Benchmark Suite for Level-V
# ============================================================
# Modern embedded benchmark suite from embench.org
# https://github.com/embench/embench-iot

.PHONY: embench embench_clone embench_setup embench_build embench_run embench_clean embench_help
.PHONY: embench_list embench_report

# ============================================================
# Configuration
# ============================================================

# Repository URL
EMBENCH_REPO_URL   := https://github.com/embench/embench-iot.git
EMBENCH_ROOT       := $(SUBREPO_DIR)/embench-iot

# Paths
EMBENCH_ENV_SRC    := $(ENV_DIR)/embench
EMBENCH_BUILD_DIR  := $(BUILD_DIR)/tests/embench
EMBENCH_LOG_DIR    := $(RESULTS_DIR)/logs/$(SIM)/embench

# Output directories
EMBENCH_ELF_DIR    := $(EMBENCH_BUILD_DIR)/elf
EMBENCH_HEX_DIR    := $(EMBENCH_BUILD_DIR)/hex
EMBENCH_MEM_DIR    := $(EMBENCH_BUILD_DIR)/mem
EMBENCH_DUMP_DIR   := $(EMBENCH_BUILD_DIR)/dump

# Compiler settings
EMBENCH_CC         := $(RISCV_PREFIX)-gcc
EMBENCH_OBJCOPY    := $(RISCV_PREFIX)-objcopy
EMBENCH_OBJDUMP    := $(RISCV_PREFIX)-objdump
EMBENCH_SIZE       := $(RISCV_PREFIX)-size

# Architecture flags
EMBENCH_MARCH      := rv32imc_zicsr
EMBENCH_MABI       := ilp32

# Compiler flags
EMBENCH_CFLAGS     := -march=$(EMBENCH_MARCH) -mabi=$(EMBENCH_MABI) \
                      -O2 -ffunction-sections -fdata-sections \
                      -static -nostdlib -nostartfiles \
                      $(LEVELV_CPU_CLK_CPPFLAGS)

# Linker flags (include libgcc for soft-float support)
EMBENCH_LDSCRIPT   := $(EMBENCH_ENV_SRC)/link.ld
EMBENCH_LDFLAGS    := -T$(EMBENCH_LDSCRIPT) -Wl,--gc-sections -lgcc

# Python scripts
ELF_TO_MEM         := $(SCRIPT_DIR)/python/elf_to_mem.py

# ============================================================
# Embench Benchmark Configuration
# ============================================================
# All available benchmarks:
#   aha-mont64, crc32, cubic, edn, huffbench, matmult-int, md5sum,
#   minver, nbody, nettle-aes, nettle-sha256, nsichneu, picojpeg,
#   qrduino, sglib-combined, slre, st, statemate,
#   tarfind, ud, wikisort
#
# Notes:
#   - wikisort: excluded (bool typedef conflict with stdbool.h)
#
# Floating-point benchmarks (require soft-float via -lgcc or FPU):
#   cubic, minver, nbody, st, ud
#   Uncomment below if your CPU supports floating-point
#
# EMBENCH_FP_BENCHMARKS := cubic minver nbody st ud
#
# Integer-only benchmarks (15 total - works on RV32IMC without FPU):
# primecount removed upstream from embench-iot (no src/primecount in current tree)
EMBENCH_BENCHMARKS := aha-mont64 crc32 edn huffbench matmult-int \
                      md5sum nettle-aes nettle-sha256 nsichneu picojpeg \
                      qrduino sglib-combined slre statemate tarfind
#
# Full benchmark list (uncomment if FPU available):
# EMBENCH_BENCHMARKS := aha-mont64 crc32 cubic edn huffbench matmult-int \
#                       md5sum minver nbody nettle-aes nettle-sha256 \
#                       nsichneu picojpeg primecount qrduino \
#                       sglib-combined slre st statemate tarfind ud

# ============================================================
# Main Targets
# ============================================================

embench: embench_clone embench_setup embench_build
	@echo -e "$(GREEN)[EMBENCH] $(SUCCESS) Build complete$(RESET)"
	@echo -e "$(GREEN)[EMBENCH] Built benchmarks:$(RESET)"
	@ls -1 $(EMBENCH_ELF_DIR)/*.elf 2>/dev/null | wc -l | xargs -I{} echo -e "  {} benchmarks ready"

# ============================================================
# Clone Repository
# ============================================================

embench_clone:
	@echo -e "$(YELLOW)[EMBENCH] Checking embench-iot repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(EMBENCH_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(EMBENCH_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone --depth=1 $(EMBENCH_REPO_URL); \
		echo -e "$(GREEN)[OK] embench-iot cloned.$(RESET)"; \
	else \
		echo -e "$(GREEN)[SKIP] embench-iot already exists.$(RESET)"; \
	fi

# ============================================================
# Setup Environment
# ============================================================

embench_setup: embench_clone
	@echo -e "$(YELLOW)[EMBENCH] Setting up Level-V environment...$(RESET)"
	@mkdir -p $(EMBENCH_ENV_SRC)
	@mkdir -p $(EMBENCH_ELF_DIR) $(EMBENCH_HEX_DIR) $(EMBENCH_MEM_DIR) $(EMBENCH_DUMP_DIR)
	@# Create environment files if not exists
	@if [ ! -f "$(EMBENCH_LDSCRIPT)" ]; then \
		$(MAKE) --no-print-directory _embench_gen_env; \
	fi
	@echo -e "$(GREEN)[OK] Environment ready.$(RESET)"

# Generate environment files
_embench_gen_env:
	@echo -e "$(YELLOW)[EMBENCH] Generating environment files...$(RESET)"
	@# Linker script will be created separately
	@# Startup file will be created separately

# ============================================================
# Build Benchmarks
# ============================================================

embench_build: embench_setup
	@echo -e "$(YELLOW)[EMBENCH] Building benchmarks...$(RESET)"
	@PASS=0; FAIL=0; \
	for bench in $(EMBENCH_BENCHMARKS); do \
		if $(MAKE) --no-print-directory _embench_build_one BENCH=$$bench; then \
			PASS=$$((PASS + 1)); \
		else \
			FAIL=$$((FAIL + 1)); \
		fi; \
	done; \
	echo -e "$(GREEN)[EMBENCH] Build complete: $$PASS passed, $$FAIL failed$(RESET)"

# Build single benchmark
# Embench structure: src/<bench>/*.c + support/main.c + support/board.c + support/beebsc.c
_embench_build_one:
	@SRC_DIR="$(EMBENCH_ROOT)/src/$(BENCH)"; \
	SUPPORT_DIR="$(EMBENCH_ROOT)/support"; \
	if [ ! -d "$$SRC_DIR" ]; then \
		echo -e "  $(RED)✗ $(BENCH): source not found$(RESET)"; \
		exit 1; \
	fi; \
	echo -e "  $(YELLOW)→ Building: $(BENCH)$(RESET)"; \
	BENCH_SRCS="$$(find $$SRC_DIR -name '*.c')"; \
	SUPPORT_SRCS="$$SUPPORT_DIR/main.c $$SUPPORT_DIR/beebsc.c $$SUPPORT_DIR/board.c"; \
	INCS="-I$$SRC_DIR -I$$SUPPORT_DIR -I$(EMBENCH_ENV_SRC) -DHAVE_BOARDSUPPORT_H"; \
	$(EMBENCH_CC) $(EMBENCH_CFLAGS) $$INCS $(EMBENCH_LDFLAGS) \
		-o $(EMBENCH_ELF_DIR)/$(BENCH).elf \
		$(EMBENCH_ENV_SRC)/crt0.S $$BENCH_SRCS $$SUPPORT_SRCS $(EMBENCH_ENV_SRC)/syscalls.c 2>&1 && \
	$(EMBENCH_OBJDUMP) -d $(EMBENCH_ELF_DIR)/$(BENCH).elf > $(EMBENCH_DUMP_DIR)/$(BENCH).dump && \
	$(EMBENCH_OBJCOPY) -O binary $(EMBENCH_ELF_DIR)/$(BENCH).elf $(EMBENCH_HEX_DIR)/$(BENCH).bin && \
	python3 $(ELF_TO_MEM) --in $(EMBENCH_HEX_DIR)/$(BENCH).bin --out $(EMBENCH_MEM_DIR)/$(BENCH).mem \
		--addr 0x80000000 --block-bytes 4 --word-size 4 --word-endian little --word-order high-to-low && \
	echo -e "  $(GREEN)$(SUCCESS) $(BENCH)$(RESET)"

# ============================================================
# Run Benchmarks
# ============================================================

embench_run: embench_build embench_verilate
	@echo -e "$(YELLOW)[EMBENCH] Running benchmarks...$(RESET)"
	@mkdir -p $(EMBENCH_LOG_DIR)
	@PASS=0; FAIL=0; TOTAL=0; \
	for bench in $(EMBENCH_BENCHMARKS); do \
		if [ -f "$(EMBENCH_MEM_DIR)/$$bench.mem" ]; then \
			TOTAL=$$((TOTAL + 1)); \
			echo -e "  $(YELLOW)→ Running: $$bench$(RESET)"; \
			if $(MAKE) --no-print-directory run \
				TEST_TYPE=embench \
				TEST_NAME=$$bench \
				MEM_DIR="$(EMBENCH_MEM_DIR)" \
				ELF_DIR="$(EMBENCH_ELF_DIR)" \
				DUMP_DIR="$(EMBENCH_DUMP_DIR)" \
				HEX_DIR="$(EMBENCH_HEX_DIR)" \
				TEST_LOG_DIR="$(EMBENCH_LOG_DIR)/$$bench" \
				RTL_LOG_DIR="$(EMBENCH_LOG_DIR)/$$bench" 2>&1; then \
				PASS=$$((PASS + 1)); \
				echo -e "  $(GREEN)$(SUCCESS) $$bench PASSED$(RESET)"; \
			else \
				FAIL=$$((FAIL + 1)); \
				echo -e "  $(RED)✗ $$bench FAILED$(RESET)"; \
			fi; \
		fi; \
	done; \
	echo ""; \
	echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"; \
	echo -e "$(CYAN)  EMBENCH RESULTS: $$PASS/$$TOTAL passed, $$FAIL failed$(RESET)"; \
	echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"; \
	if [ $$FAIL -gt 0 ]; then \
		echo -e "$(RED)[EMBENCH] ✗ Some benchmarks failed$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)[EMBENCH] $(SUCCESS) All benchmarks passed$(RESET)"; \
	fi

# ============================================================
# List and Report
# ============================================================

embench_list:
	@echo -e "$(CYAN)[EMBENCH] Available benchmarks:$(RESET)"
	@for bench in $(EMBENCH_BENCHMARKS); do \
		echo -e "  - $$bench"; \
	done

embench_report:
	@echo -e "$(CYAN)[EMBENCH] Size Report:$(RESET)"
	@if [ -d "$(EMBENCH_ELF_DIR)" ]; then \
		for elf in $(EMBENCH_ELF_DIR)/*.elf; do \
			if [ -f "$$elf" ]; then \
				name=$$(basename $$elf .elf); \
				size=$$($(EMBENCH_SIZE) $$elf | tail -1 | awk '{print $$1+$$2}'); \
				printf "  %-20s %8s bytes\n" "$$name" "$$size"; \
			fi; \
		done; \
	else \
		echo -e "  $(YELLOW)No builds found. Run 'make embench_build' first.$(RESET)"; \
	fi

# Full-tree ELF sizing (text/data/bss/dec + optional .mem line count). Tuning link.ld / BRAM.
.PHONY: levelv_memory_report
levelv_memory_report:
	@$(PYTHON) $(SCRIPT_DIR)/python/levelv_elf_memory_report.py $(BUILD_DIR)/tests $(RISCV_PREFIX)

# ============================================================
# Simulation with run_flist
# ============================================================

# Generate flist for run_flist compatibility
embench_flist: embench_build
	@echo -e "$(YELLOW)[EMBENCH] Generating test file list...$(RESET)"
	@> $(SIM_DIR)/test/embench.flist.tmp
	@for bench in $(EMBENCH_BENCHMARKS); do \
		if [ -f "$(EMBENCH_MEM_DIR)/$$bench.mem" ]; then \
			echo "$$bench" >> $(SIM_DIR)/test/embench.flist.tmp; \
		fi; \
	done
	@mv $(SIM_DIR)/test/embench.flist.tmp $(SIM_DIR)/test/embench.flist
	@count=$$(wc -l < $(SIM_DIR)/test/embench.flist); \
	echo -e "$(GREEN)[OK] Generated embench.flist with $$count benchmarks$(RESET)"

# Ensure verilator is built with config from JSON
embench_verilate:
	@echo -e "$(YELLOW)[EMBENCH] Building Verilator with embench config...$(RESET)"
	@$(MAKE) --no-print-directory verilate TEST_TYPE=embench

# Run all embench tests using run_flist
embench_run_all: embench_flist embench_verilate
	@echo -e "$(YELLOW)[EMBENCH] Running all benchmarks via run_flist...$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		TEST_TYPE=embench \
		FLIST="$(SIM_DIR)/test/embench.flist" \
		MEM_DIR="$(EMBENCH_MEM_DIR)" \
		ELF_DIR="$(EMBENCH_ELF_DIR)" \
		DUMP_DIR="$(EMBENCH_DUMP_DIR)" \
		HEX_DIR="$(EMBENCH_HEX_DIR)" \
		TEST_LOG_DIR="$(EMBENCH_LOG_DIR)" \
		RTL_LOG_DIR="$(EMBENCH_LOG_DIR)"

# Run single embench benchmark (builds BENCH if $(EMBENCH_MEM_DIR)/$(BENCH).mem is missing)
embench_run_one: embench_setup embench_verilate
	@if [ -z "$(BENCH)" ]; then \
		echo -e "$(RED)[ERROR] Specify benchmark: make embench_run_one BENCH=crc32$(RESET)"; \
		exit 1; \
	fi
	@if [ ! -f "$(EMBENCH_MEM_DIR)/$(BENCH).mem" ]; then \
		echo -e "$(YELLOW)[EMBENCH] No $(BENCH).mem — building benchmark...$(RESET)"; \
		$(MAKE) --no-print-directory _embench_build_one BENCH=$(BENCH) || exit 1; \
	fi
	@if [ ! -f "$(EMBENCH_MEM_DIR)/$(BENCH).mem" ]; then \
		echo -e "$(RED)[ERROR] Benchmark missing or build failed: $(BENCH) (expected $(EMBENCH_MEM_DIR)/$(BENCH).mem)$(RESET)"; \
		exit 1; \
	fi
	@echo -e "$(YELLOW)[EMBENCH] Running: $(BENCH)$(RESET)"
	@$(MAKE) --no-print-directory run \
		TEST_TYPE=embench \
		TEST_NAME=$(BENCH) \
		MEM_DIR="$(EMBENCH_MEM_DIR)" \
		ELF_DIR="$(EMBENCH_ELF_DIR)" \
		DUMP_DIR="$(EMBENCH_DUMP_DIR)" \
		HEX_DIR="$(EMBENCH_HEX_DIR)" \
		TEST_LOG_DIR="$(EMBENCH_LOG_DIR)/$(BENCH)" \
		RTL_LOG_DIR="$(EMBENCH_LOG_DIR)/$(BENCH)"

# ============================================================
# Clean
# ============================================================

embench_clean:
	@echo -e "$(YELLOW)[EMBENCH] Cleaning build files...$(RESET)"
	@rm -rf $(EMBENCH_BUILD_DIR)
	@echo -e "$(GREEN)[OK] Clean complete.$(RESET)"

# ============================================================
# Help
# ============================================================

embench_help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)        Embench-IoT Benchmark Suite$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Build:$(RESET)"
	@echo -e "  make embench              Build all benchmarks"
	@echo -e "  make embench_clean        Clean build files"
	@echo -e ""
	@echo -e "$(CYAN)Simulation:$(RESET)"
	@echo -e "  make embench_run          Build and run all benchmarks"
	@echo -e "  make embench_run_all      Run all benchmarks (via run_flist)"
	@echo -e "  make embench_run_one BENCH=<name>  Run single benchmark"
	@echo -e ""
	@echo -e "$(CYAN)Info:$(RESET)"
	@echo -e "  make embench_list         List available benchmarks"
	@echo -e "  make embench_report       Show code size report"
	@echo -e "  make embench_flist        Generate test file list"
	@echo -e ""
	@echo -e "$(CYAN)Config Files:$(RESET)"
	@echo -e "  sim/test/embench.flist           Test list"
	@echo -e "  script/config/tests/embench.conf Simulation config"
	@echo -e ""
	@echo -e "$(CYAN)Integer Benchmarks (15):$(RESET)"
	@echo -e "  aha-mont64, crc32, edn, huffbench, matmult-int, md5sum"
	@echo -e "  nettle-aes, nettle-sha256, nsichneu, picojpeg"
	@echo -e "  qrduino, sglib-combined, slre, statemate, tarfind"
	@echo -e ""
	@echo -e "$(CYAN)FP Benchmarks (requires FPU - commented out):$(RESET)"
	@echo -e "  cubic, minver, nbody, st, ud"
	@echo -e ""

# ====== test/dhrystone.mk ======
# ============================================================
# Dhrystone Benchmark for Level-V
# ============================================================
# Classic MIPS benchmark, useful for comparing CPU performance
# https://github.com/riscv-software-src/riscv-tests (benchmarks)

.PHONY: dhrystone dhrystone_clone dhrystone_setup dhrystone_build dhrystone_run dhrystone_clean dhrystone_help

# ============================================================
# Configuration
# ============================================================

# Paths
DHRYSTONE_ENV_SRC    := $(ENV_DIR)/dhrystone
DHRYSTONE_BUILD_DIR  := $(BUILD_DIR)/tests/dhrystone
DHRYSTONE_LOG_DIR    := $(RESULTS_DIR)/logs/$(SIM)/dhrystone

# Output
DHRYSTONE_ELF        := $(DHRYSTONE_BUILD_DIR)/dhrystone.elf
DHRYSTONE_HEX        := $(DHRYSTONE_BUILD_DIR)/dhrystone.bin
DHRYSTONE_MEM        := $(DHRYSTONE_BUILD_DIR)/dhrystone.mem
DHRYSTONE_DUMP       := $(DHRYSTONE_BUILD_DIR)/dhrystone.dump

# Compiler settings
DHRY_CC              := $(RISCV_PREFIX)-gcc
DHRY_OBJCOPY         := $(RISCV_PREFIX)-objcopy
DHRY_OBJDUMP         := $(RISCV_PREFIX)-objdump
DHRY_SIZE            := $(RISCV_PREFIX)-size

# Architecture flags
DHRY_MARCH           := rv32imc_zicsr
DHRY_MABI            := ilp32

# Iteration count (override: make dhrystone_build DHRY_ITERS=1)
DHRY_ITERS           ?= 100000

# Compiler flags (optimize for performance, avoid inline to keep structure)
DHRY_CFLAGS          := -march=$(DHRY_MARCH) -mabi=$(DHRY_MABI) \
                        -O3 -fno-inline -funroll-loops \
                        -static -nostdlib -nostartfiles \
                        -DTIME -DDHRY_ITERS=$(DHRY_ITERS) \
                        $(LEVELV_CPU_CLK_CPPFLAGS)

# Linker
DHRY_LDSCRIPT        := $(DHRYSTONE_ENV_SRC)/link.ld
DHRY_LDFLAGS         := -T$(DHRY_LDSCRIPT) -Wl,--gc-sections

# Python scripts
ELF_TO_MEM           := $(SCRIPT_DIR)/python/elf_to_mem.py

# ============================================================
# Main Targets
# ============================================================

dhrystone: dhrystone_setup dhrystone_build
	@echo -e "$(GREEN)[DHRYSTONE] $(SUCCESS) Build complete$(RESET)"

# ============================================================
# Setup Environment
# ============================================================

dhrystone_setup:
	@echo -e "$(YELLOW)[DHRYSTONE] Setting up environment...$(RESET)"
	@mkdir -p $(DHRYSTONE_BUILD_DIR)
	@mkdir -p $(DHRYSTONE_ENV_SRC)
	@if [ ! -f "$(DHRY_LDSCRIPT)" ]; then \
		echo -e "$(YELLOW)[DHRYSTONE] Environment files need to be created$(RESET)"; \
	fi
	@echo -e "$(GREEN)[OK] Setup complete$(RESET)"

# ============================================================
# Build
# ============================================================

dhrystone_build: dhrystone_setup
	@echo -e "$(YELLOW)[DHRYSTONE] Building benchmark...$(RESET)"
	@# Compile all source files
	$(DHRY_CC) $(DHRY_CFLAGS) $(DHRY_LDFLAGS) \
		-I$(DHRYSTONE_ENV_SRC) \
		$(DHRYSTONE_ENV_SRC)/crt0.S \
		$(DHRYSTONE_ENV_SRC)/syscalls.c \
		$(DHRYSTONE_ENV_SRC)/dhry_1.c \
		$(DHRYSTONE_ENV_SRC)/dhry_2.c \
		-o $(DHRYSTONE_ELF)
	@# Generate outputs
	$(DHRY_OBJDUMP) -d $(DHRYSTONE_ELF) > $(DHRYSTONE_DUMP)
	$(DHRY_OBJCOPY) -O binary $(DHRYSTONE_ELF) $(DHRYSTONE_HEX)
	@python3 $(ELF_TO_MEM) --in $(DHRYSTONE_HEX) --out $(DHRYSTONE_MEM) \
		--addr 0x80000000 --block-bytes 4 --word-size 4 --word-endian little --word-order high-to-low
	@# Show size
	$(DHRY_SIZE) $(DHRYSTONE_ELF)
	@echo -e "$(GREEN)[OK] Dhrystone built: $(DHRYSTONE_MEM)$(RESET)"

# ============================================================
# Run
# ============================================================

# Ensure verilator is built with config from JSON
dhrystone_verilate:
	@echo -e "$(YELLOW)[DHRYSTONE] Building Verilator with dhrystone config...$(RESET)"
	@$(MAKE) --no-print-directory verilate TEST_TYPE=dhrystone

dhrystone_run: dhrystone_build dhrystone_verilate
	@echo -e "$(YELLOW)[DHRYSTONE] Running benchmark...$(RESET)"
	@mkdir -p $(DHRYSTONE_LOG_DIR)
	$(MAKE) --no-print-directory run \
		TEST_TYPE=dhrystone \
		TEST_NAME=dhrystone \
		MEM_DIR="$(DHRYSTONE_BUILD_DIR)" \
		ELF_DIR="$(DHRYSTONE_BUILD_DIR)" \
		DUMP_DIR="$(DHRYSTONE_BUILD_DIR)" \
		HEX_DIR="$(DHRYSTONE_BUILD_DIR)" \
		TEST_LOG_DIR="$(DHRYSTONE_LOG_DIR)" \
		RTL_LOG_DIR="$(DHRYSTONE_LOG_DIR)"

# Generate flist for run_flist compatibility
dhrystone_flist: dhrystone_build
	@echo -e "$(YELLOW)[DHRYSTONE] Generating test file list...$(RESET)"
	@echo "dhrystone" > $(SIM_DIR)/test/dhrystone.flist
	@echo -e "$(GREEN)[OK] Generated dhrystone.flist$(RESET)"

# Run via run_flist (for batch processing)
dhrystone_run_all: dhrystone_flist dhrystone_verilate
	@echo -e "$(YELLOW)[DHRYSTONE] Running via run_flist...$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		TEST_TYPE=dhrystone \
		FLIST="$(SIM_DIR)/test/dhrystone.flist" \
		MEM_DIR="$(DHRYSTONE_BUILD_DIR)" \
		ELF_DIR="$(DHRYSTONE_BUILD_DIR)" \
		DUMP_DIR="$(DHRYSTONE_BUILD_DIR)" \
		HEX_DIR="$(DHRYSTONE_BUILD_DIR)" \
		TEST_LOG_DIR="$(DHRYSTONE_LOG_DIR)" \
		RTL_LOG_DIR="$(DHRYSTONE_LOG_DIR)"

# ============================================================
# Clean
# ============================================================

dhrystone_clean:
	@echo -e "$(YELLOW)[DHRYSTONE] Cleaning...$(RESET)"
	@rm -rf $(DHRYSTONE_BUILD_DIR)
	@echo -e "$(GREEN)[OK] Clean complete$(RESET)"

# ============================================================
# Help
# ============================================================

dhrystone_help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)           Dhrystone Benchmark$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Build:$(RESET)"
	@echo -e "  make dhrystone        Build Dhrystone benchmark"
	@echo -e "  make dhrystone_clean  Clean build files"
	@echo -e ""
	@echo -e "$(CYAN)Simulation:$(RESET)"
	@echo -e "  make dhrystone_run      Build and run benchmark"
	@echo -e "  make dhrystone_run_all  Run via run_flist"
	@echo -e ""
	@echo -e "$(CYAN)Config Files:$(RESET)"
	@echo -e "  sim/test/dhrystone.flist            Test list"
	@echo -e "  script/config/tests/dhrystone.conf  Simulation config"
	@echo -e ""
	@echo -e "$(CYAN)Configuration:$(RESET)"
	@echo -e "  DHRY_ITERS   Number of iterations (default: 100000)"
	@echo -e "  CPU_MHZ      CPU frequency for DMIPS calculation"
	@echo -e ""
	@echo -e "$(CYAN)Results:$(RESET)"
	@echo -e "  DMIPS/MHz = (Dhrystones/second) / 1757 / MHz"
	@echo -e ""

# ====== test/torture.mk ======
# ============================================================
# RISC-V Torture Test Generator for Level-V
# ============================================================
# Random instruction sequence generator for processor stress testing
# https://github.com/ucb-bar/riscv-torture

.PHONY: torture torture_clone torture_setup torture_gen torture_build torture_run
.PHONY: torture_clean torture_help torture_batch

# ============================================================
# Configuration
# ============================================================

# Repository
TORTURE_REPO_URL    := https://github.com/ucb-bar/riscv-torture.git
TORTURE_ROOT        := $(SUBREPO_DIR)/riscv-torture

# Paths
TORTURE_ENV_SRC     := $(ENV_DIR)/torture
TORTURE_BUILD_DIR   := $(BUILD_DIR)/tests/torture
TORTURE_LOG_DIR     := $(RESULTS_DIR)/logs/$(SIM)/torture

# Output directories
TORTURE_ELF_DIR     := $(TORTURE_BUILD_DIR)/elf
TORTURE_HEX_DIR     := $(TORTURE_BUILD_DIR)/hex
TORTURE_MEM_DIR     := $(TORTURE_BUILD_DIR)/mem
TORTURE_DUMP_DIR    := $(TORTURE_BUILD_DIR)/dump
TORTURE_SRC_DIR     := $(TORTURE_BUILD_DIR)/src
TORTURE_ADDR_DIR    := $(TORTURE_BUILD_DIR)/pass_fail_addr

# Compiler settings
TORTURE_CC          := $(RISCV_PREFIX)-gcc
TORTURE_OBJCOPY     := $(RISCV_PREFIX)-objcopy
TORTURE_OBJDUMP     := $(RISCV_PREFIX)-objdump

# Architecture
TORTURE_MARCH       := rv32imc_zicsr
TORTURE_MABI        := ilp32

# Compiler flags
TORTURE_CFLAGS      := -march=$(TORTURE_MARCH) -mabi=$(TORTURE_MABI) \
                       -static -nostdlib -nostartfiles -O0

# Linker
TORTURE_LDSCRIPT    := $(TORTURE_ENV_SRC)/link.ld
TORTURE_LDFLAGS     := -T$(TORTURE_LDSCRIPT)

# Python scripts
ELF_TO_MEM          := $(SCRIPT_DIR)/python/elf_to_mem.py
TORTURE_GEN_SCRIPT  := $(SCRIPT_DIR)/python/torture_gen.py
SIMPLE_TORTURE_GEN  := $(SCRIPT_DIR)/python/simple_torture_gen.py

# Test configuration
TORTURE_NUM_TESTS   ?= 10
TORTURE_SEED        ?= $(shell date +%s)
TORTURE_MAX_INSNS   ?= 1000

# ============================================================
# Main Targets
# ============================================================

torture: torture_setup torture_gen torture_build
	@echo -e "$(GREEN)[TORTURE] $(SUCCESS) Tests generated and built$(RESET)"

# ============================================================
# Clone Repository (optional - we can generate locally)
# ============================================================

torture_clone:
	@echo -e "$(YELLOW)[TORTURE] Checking riscv-torture repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(TORTURE_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(TORTURE_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone --depth=1 $(TORTURE_REPO_URL) || \
		echo -e "$(YELLOW)[WARN] Using local generator instead$(RESET)"; \
	else \
		echo -e "$(GREEN)[SKIP] riscv-torture already exists.$(RESET)"; \
	fi

# ============================================================
# Setup
# ============================================================

torture_setup:
	@echo -e "$(YELLOW)[TORTURE] Setting up environment...$(RESET)"
	@mkdir -p $(TORTURE_ENV_SRC)
	@mkdir -p $(TORTURE_ELF_DIR) $(TORTURE_HEX_DIR) $(TORTURE_MEM_DIR) \
		$(TORTURE_DUMP_DIR) $(TORTURE_SRC_DIR)
	@echo -e "$(GREEN)[OK] Setup complete$(RESET)"

# ============================================================
# Generate Tests
# ============================================================

torture_gen: torture_setup
	@echo -e "$(YELLOW)[TORTURE] Generating $(TORTURE_NUM_TESTS) random tests...$(RESET)"
	@for i in $$(seq 1 $(TORTURE_NUM_TESTS)); do \
		SEED=$$(($(TORTURE_SEED) + $$i)); \
		NAME="torture_$${SEED}"; \
		echo -e "  $(YELLOW)→ Generating: $$NAME$(RESET)"; \
		if [ -f "$(TORTURE_GEN_SCRIPT)" ]; then \
			python3 $(TORTURE_GEN_SCRIPT) \
				--seed $$SEED \
				--max-insns $(TORTURE_MAX_INSNS) \
				--output $(TORTURE_SRC_DIR)/$$NAME.S \
				--march rv32imc 2>/dev/null || \
			python3 $(SIMPLE_TORTURE_GEN) \
				--seed $$SEED \
				--name $$NAME \
				--output $(TORTURE_SRC_DIR)/$$NAME.S; \
		else \
			python3 $(SIMPLE_TORTURE_GEN) \
				--seed $$SEED \
				--name $$NAME \
				--output $(TORTURE_SRC_DIR)/$$NAME.S; \
		fi; \
	done
	@echo -e "$(GREEN)[OK] Tests generated$(RESET)"

# ============================================================
# Build Tests
# ============================================================

torture_build: torture_gen
	@echo -e "$(YELLOW)[TORTURE] Building tests...$(RESET)"
	@PASS=0; FAIL=0; \
	for src in $(TORTURE_SRC_DIR)/*.S; do \
		if [ -f "$$src" ]; then \
			name=$$(basename $$src .S); \
			if $(MAKE) --no-print-directory _torture_build_one SRC=$$src NAME=$$name 2>/dev/null; then \
				PASS=$$((PASS + 1)); \
			else \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[TORTURE] Build: $$PASS passed, $$FAIL failed$(RESET)"

_torture_build_one:
	@mkdir -p $(TORTURE_ADDR_DIR)
	@$(TORTURE_CC) $(TORTURE_CFLAGS) $(TORTURE_LDFLAGS) \
		-I$(TORTURE_ENV_SRC) \
		$(TORTURE_ENV_SRC)/crt0.S $(SRC) \
		-o $(TORTURE_ELF_DIR)/$(NAME).elf 2>&1 && \
	$(TORTURE_OBJDUMP) -d $(TORTURE_ELF_DIR)/$(NAME).elf > $(TORTURE_DUMP_DIR)/$(NAME).dump && \
	$(TORTURE_OBJCOPY) -O binary $(TORTURE_ELF_DIR)/$(NAME).elf $(TORTURE_HEX_DIR)/$(NAME).bin && \
	python3 $(ELF_TO_MEM) --in $(TORTURE_HEX_DIR)/$(NAME).bin --out $(TORTURE_MEM_DIR)/$(NAME).mem \
		--addr 0x80000000 --block-bytes 4 --word-size 4 --word-endian little --word-order high-to-low && \
	PASS_ADDR=$$(grep -E "<_pass>:|<pass>:" $(TORTURE_DUMP_DIR)/$(NAME).dump | head -1 | awk '{print $$1}' | sed 's/://') && \
	FAIL_ADDR=$$(grep -E "<_fail>:|<fail>:" $(TORTURE_DUMP_DIR)/$(NAME).dump | head -1 | awk '{print $$1}' | sed 's/://') && \
	if [ -z "$$FAIL_ADDR" ]; then FAIL_ADDR="0"; fi && \
	echo "0x$$PASS_ADDR 0x$$FAIL_ADDR" > $(TORTURE_ADDR_DIR)/$(NAME)_addr.txt && \
	echo -e "  $(GREEN)$(SUCCESS) $(NAME)$(RESET)"

# ============================================================
# Run Tests
# ============================================================

# Ensure verilator is built with torture config
torture_verilate:
	@echo -e "$(YELLOW)[TORTURE] Building Verilator with torture config...$(RESET)"
	@$(MAKE) --no-print-directory verilate TEST_TYPE=torture

torture_run: torture_build torture_verilate
	@echo -e "$(YELLOW)[TORTURE] Running tests...$(RESET)"
	@mkdir -p $(TORTURE_LOG_DIR)
	@PASS=0; FAIL=0; \
	for mem in $(TORTURE_MEM_DIR)/*.mem; do \
		if [ -f "$$mem" ]; then \
			name=$$(basename $$mem .mem); \
			echo -e "  $(YELLOW)→ Running: $$name$(RESET)"; \
			if $(MAKE) --no-print-directory run \
				TEST_TYPE=torture \
				TEST_NAME=$$name \
				MEM_DIR="$(TORTURE_MEM_DIR)" \
				ELF_DIR="$(TORTURE_ELF_DIR)" \
				DUMP_DIR="$(TORTURE_DUMP_DIR)" \
				ADDR_DIR="$(TORTURE_ADDR_DIR)" \
				TEST_LOG_DIR="$(TORTURE_LOG_DIR)/$$name" \
				RTL_LOG_DIR="$(TORTURE_LOG_DIR)/$$name" 2>/dev/null; then \
				echo -e "  $(GREEN)$(SUCCESS) $$name PASS$(RESET)"; \
				PASS=$$((PASS + 1)); \
			else \
				echo -e "  $(RED)✗ $$name FAIL$(RESET)"; \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[TORTURE] Results: $$PASS passed, $$FAIL failed$(RESET)"

# ============================================================
# Batch Testing
# ============================================================

torture_batch:
	@echo -e "$(YELLOW)[TORTURE] Running batch test ($(TORTURE_NUM_TESTS) tests)...$(RESET)"
	@$(MAKE) --no-print-directory torture TORTURE_SEED=$(TORTURE_SEED)
	@$(MAKE) --no-print-directory torture_run

# ============================================================
# Clean
# ============================================================

torture_clean:
	@echo -e "$(YELLOW)[TORTURE] Cleaning...$(RESET)"
	@rm -rf $(TORTURE_BUILD_DIR)
	@echo -e "$(GREEN)[OK] Clean complete$(RESET)"

# ============================================================
# Help
# ============================================================

torture_help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)     RISC-V Torture Test Generator$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Usage:$(RESET)"
	@echo -e "  make torture              Generate and build tests"
	@echo -e "  make torture_run          Run all torture tests"
	@echo -e "  make torture_batch        Full batch test cycle"
	@echo -e "  make torture_clean        Clean build files"
	@echo -e ""
	@echo -e "$(CYAN)Configuration:$(RESET)"
	@echo -e "  TORTURE_NUM_TESTS=N       Number of tests to generate (default: 10)"
	@echo -e "  TORTURE_SEED=N            Random seed (default: timestamp)"
	@echo -e "  TORTURE_MAX_INSNS=N       Max instructions per test (default: 1000)"
	@echo -e ""
	@echo -e "$(CYAN)Examples:$(RESET)"
	@echo -e "  make torture TORTURE_NUM_TESTS=100"
	@echo -e "  make torture_batch TORTURE_SEED=12345"
	@echo -e ""

# ====== test/riscv_dv.mk ======
# ============================================================
# RISC-V DV (Google's Random Test Generator) for Level-V
# ============================================================
# UVM-based instruction generator
# https://github.com/chipsalliance/riscv-dv

.PHONY: riscv_dv riscv_dv_clone riscv_dv_setup riscv_dv_gen riscv_dv_build
.PHONY: riscv_dv_run riscv_dv_clean riscv_dv_help riscv_dv_compare

# ============================================================
# Configuration
# ============================================================

# Repository
RISCV_DV_REPO_URL   := https://github.com/chipsalliance/riscv-dv.git
RISCV_DV_ROOT       := $(SUBREPO_DIR)/riscv-dv

# Paths
RISCV_DV_ENV_SRC    := $(ENV_DIR)/riscv-dv
RISCV_DV_BUILD_DIR  := $(BUILD_DIR)/tests/riscv-dv
RISCV_DV_LOG_DIR    := $(RESULTS_DIR)/logs/$(SIM)/riscv-dv

# Output directories
RISCV_DV_GEN_DIR    := $(RISCV_DV_BUILD_DIR)/gen
RISCV_DV_ELF_DIR    := $(RISCV_DV_BUILD_DIR)/elf
RISCV_DV_HEX_DIR    := $(RISCV_DV_BUILD_DIR)/hex
RISCV_DV_MEM_DIR    := $(RISCV_DV_BUILD_DIR)/mem
RISCV_DV_DUMP_DIR   := $(RISCV_DV_BUILD_DIR)/dump
RISCV_DV_ADDR_DIR   := $(RISCV_DV_BUILD_DIR)/pass_fail_addr
RISCV_DV_SIM_DIR    := $(RISCV_DV_BUILD_DIR)/sim
RISCV_DV_COV_DIR    := $(RISCV_DV_BUILD_DIR)/cov

# Compiler settings
RISCV_DV_CC         := $(RISCV_PREFIX)-gcc
RISCV_DV_OBJCOPY    := $(RISCV_PREFIX)-objcopy
RISCV_DV_OBJDUMP    := $(RISCV_PREFIX)-objdump

# Architecture
RISCV_DV_MARCH      := rv32imc_zicsr
RISCV_DV_MABI       := ilp32

# Compiler flags
RISCV_DV_CFLAGS     := -march=$(RISCV_DV_MARCH) -mabi=$(RISCV_DV_MABI) \
                       -static -nostdlib -nostartfiles -O0

# Linker
RISCV_DV_LDSCRIPT   := $(RISCV_DV_ENV_SRC)/link.ld
RISCV_DV_LDFLAGS    := -T$(RISCV_DV_LDSCRIPT)

# Python
ELF_TO_MEM          := $(SCRIPT_DIR)/python/elf_to_mem.py
RISCV_DV_SCRIPT     := $(RISCV_DV_ROOT)/run.py
RISCV_DV_FALLBACK   := $(SCRIPT_DIR)/python/riscv_dv_gen.py
RISCV_DV_CONFIG_RDR := $(SCRIPT_DIR)/python/riscv_dv_config.py

# JSON Configuration
RISCV_DV_CONFIG     := $(SCRIPT_DIR)/config/tests/riscv-dv.json

# Test configuration (can override from command line or use JSON defaults)
# Command line takes priority > JSON config
RISCV_DV_TEST       ?= $(shell python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-value -k tests.0.name -d riscv_arithmetic_basic_test)
RISCV_DV_ITER       ?= $(shell python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-iterations -t $(RISCV_DV_TEST) 2>/dev/null || echo 5)
RISCV_DV_SEED       ?= $(shell python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-value -k generator.seed -d 0)
RISCV_DV_ISA        ?= $(shell python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-value -k generator.isa -d rv32imc)
RISCV_DV_INSTR_CNT  ?= $(shell python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-value -k generator.instr_cnt -d 500)

# ============================================================
# Main Targets
# ============================================================

riscv_dv: riscv_dv_clone riscv_dv_setup riscv_dv_gen riscv_dv_build
	@echo -e "$(GREEN)[RISCV-DV] $(SUCCESS) Tests generated and built$(RESET)"

# ============================================================
# Clone Repository
# ============================================================

riscv_dv_clone:
	@echo -e "$(YELLOW)[RISCV-DV] Checking riscv-dv repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(RISCV_DV_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(RISCV_DV_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone --depth=1 $(RISCV_DV_REPO_URL); \
		echo -e "$(GREEN)[OK] riscv-dv cloned.$(RESET)"; \
	else \
		echo -e "$(GREEN)[SKIP] riscv-dv already exists.$(RESET)"; \
	fi

# ============================================================
# Setup Environment
# ============================================================

riscv_dv_setup: riscv_dv_clone
	@echo -e "$(YELLOW)[RISCV-DV] Setting up environment...$(RESET)"
	@mkdir -p $(RISCV_DV_ENV_SRC)
	@mkdir -p $(RISCV_DV_GEN_DIR) $(RISCV_DV_ELF_DIR) $(RISCV_DV_HEX_DIR) \
		$(RISCV_DV_MEM_DIR) $(RISCV_DV_DUMP_DIR) $(RISCV_DV_SIM_DIR) $(RISCV_DV_COV_DIR)
	@echo -e "$(GREEN)[OK] Setup complete$(RESET)"

# ============================================================
# Generate Tests
# ============================================================

riscv_dv_gen: riscv_dv_setup
	@echo -e "$(YELLOW)[RISCV-DV] Generating tests...$(RESET)"
	@echo -e "  Test: $(RISCV_DV_TEST)"
	@echo -e "  Iterations: $(RISCV_DV_ITER)"
	@echo -e "  ISA: $(RISCV_DV_ISA)"
	@GEN_SUCCESS=0; \
	if [ -f "$(RISCV_DV_SCRIPT)" ] && python3 -c "import vsc" 2>/dev/null; then \
		SEED_OPT=""; \
		if [ "$(RISCV_DV_ITER)" = "1" ]; then \
			SEED_OPT="--seed $(RISCV_DV_SEED)"; \
		fi; \
		cd $(RISCV_DV_ROOT) && python3 run.py \
			--test $(RISCV_DV_TEST) \
			--iterations $(RISCV_DV_ITER) \
			--isa $(RISCV_DV_ISA) \
			--mabi ilp32 \
			--simulator pyflow \
			$$SEED_OPT \
			--output $(RISCV_DV_GEN_DIR) \
			--steps gen 2>&1 | head -100 && GEN_SUCCESS=1; \
	fi; \
	if [ "$$GEN_SUCCESS" != "1" ]; then \
		echo -e "$(YELLOW)[RISCV-DV] Using fallback generator...$(RESET)"; \
		for i in $$(seq 0 $$(($(RISCV_DV_ITER) - 1))); do \
			python3 $(RISCV_DV_FALLBACK) \
				--test $(RISCV_DV_TEST) \
				--idx $$i \
				--seed $$(($(RISCV_DV_SEED) + $$i)) \
				--output $(RISCV_DV_GEN_DIR)/$(RISCV_DV_TEST)_$$i.S; \
		done; \
	fi
	@echo -e "$(GREEN)[OK] Generation complete$(RESET)"

# Fallback generator if riscv-dv not available
_riscv_dv_gen_fallback:
	@echo -e "$(YELLOW)[RISCV-DV] Using fallback generator...$(RESET)"
	@for i in $$(seq 0 $$(($(RISCV_DV_ITER) - 1))); do \
		python3 $(RISCV_DV_FALLBACK) \
			--test $(RISCV_DV_TEST) \
			--idx $$i \
			--seed $(RISCV_DV_SEED) \
			--output $(RISCV_DV_GEN_DIR)/$(RISCV_DV_TEST)_$$i.S; \
	done

# ============================================================
# Build Tests
# ============================================================

riscv_dv_build: riscv_dv_gen
	@echo -e "$(YELLOW)[RISCV-DV] Building tests...$(RESET)"
	@PASS=0; FAIL=0; \
	for src in $(RISCV_DV_GEN_DIR)/*.S; do \
		if [ -f "$$src" ]; then \
			name=$$(basename $$src .S); \
			if $(MAKE) --no-print-directory _riscv_dv_build_one SRC=$$src NAME=$$name 2>/dev/null; then \
				PASS=$$((PASS + 1)); \
			else \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[RISCV-DV] Build: $$PASS passed, $$FAIL failed$(RESET)"

_riscv_dv_build_one:
	@mkdir -p $(RISCV_DV_ADDR_DIR)
	@$(RISCV_DV_CC) $(RISCV_DV_CFLAGS) $(RISCV_DV_LDFLAGS) \
		-I$(RISCV_DV_ENV_SRC) \
		$(SRC) \
		-o $(RISCV_DV_ELF_DIR)/$(NAME).elf && \
	$(RISCV_DV_OBJDUMP) -d $(RISCV_DV_ELF_DIR)/$(NAME).elf > $(RISCV_DV_DUMP_DIR)/$(NAME).dump && \
	$(RISCV_DV_OBJCOPY) -O binary $(RISCV_DV_ELF_DIR)/$(NAME).elf $(RISCV_DV_HEX_DIR)/$(NAME).bin && \
	python3 $(ELF_TO_MEM) --in $(RISCV_DV_HEX_DIR)/$(NAME).bin --out $(RISCV_DV_MEM_DIR)/$(NAME).mem \
		--addr 0x80000000 --block-bytes 4 --word-size 4 --word-endian little --word-order high-to-low && \
	PASS_ADDR=$$(grep "^[0-9a-f]* <_pass>:" $(RISCV_DV_DUMP_DIR)/$(NAME).dump | awk '{print "0x" $$1}') && \
	FAIL_ADDR=$$(grep "^[0-9a-f]* <_fail>:" $(RISCV_DV_DUMP_DIR)/$(NAME).dump | awk '{print "0x" $$1}') && \
	echo "$$PASS_ADDR $$FAIL_ADDR" > $(RISCV_DV_ADDR_DIR)/$(NAME)_addr.txt && \
	echo -e "  $(GREEN)$(SUCCESS) $(NAME)$(RESET)"

# ============================================================
# Run Tests
# ============================================================

riscv_dv_run: riscv_dv_build riscv_dv_verilate
	@echo -e "$(YELLOW)[RISCV-DV] Running tests...$(RESET)"
	@mkdir -p $(RISCV_DV_LOG_DIR)
	@PASS=0; FAIL=0; \
	for mem in $(RISCV_DV_MEM_DIR)/*.mem; do \
		if [ -f "$$mem" ]; then \
			name=$$(basename $$mem .mem); \
			echo -e "  $(YELLOW)→ Running: $$name$(RESET)"; \
			if $(MAKE) --no-print-directory run \
				TEST_TYPE=riscv-dv \
				TEST_NAME=$$name \
				MEM_DIR="$(RISCV_DV_MEM_DIR)" \
				ELF_DIR="$(RISCV_DV_ELF_DIR)" \
				DUMP_DIR="$(RISCV_DV_DUMP_DIR)" \
				ADDR_DIR="$(RISCV_DV_ADDR_DIR)" \
				TEST_LOG_DIR="$(RISCV_DV_LOG_DIR)/$$name" \
				RTL_LOG_DIR="$(RISCV_DV_LOG_DIR)/$$name" \
				MAX_CYCLES=50000 2>/dev/null; then \
				echo -e "  $(GREEN)$(SUCCESS) $$name PASS$(RESET)"; \
				PASS=$$((PASS + 1)); \
			else \
				echo -e "  $(RED)✗ $$name FAIL$(RESET)"; \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[RISCV-DV] Results: $$PASS passed, $$FAIL failed$(RESET)"

# Build Verilator with riscv-dv config
riscv_dv_verilate:
	@echo -e "$(YELLOW)[RISCV-DV] Building Verilator...$(RESET)"
	@$(MAKE) --no-print-directory verilate TEST_TYPE=riscv-dv

# ============================================================
# Compare with Spike (ISS comparison)
# ============================================================

riscv_dv_compare:
	@echo -e "$(YELLOW)[RISCV-DV] Comparing with Spike reference...$(RESET)"
	@for elf in $(RISCV_DV_ELF_DIR)/*.elf; do \
		if [ -f "$$elf" ]; then \
			name=$$(basename $$elf .elf); \
			echo -e "  $(YELLOW)→ Comparing: $$name$(RESET)"; \
			spike --isa=$(RISCV_DV_ISA) $$elf > $(RISCV_DV_SIM_DIR)/$$name.spike.log 2>&1 || true; \
		fi; \
	done
	@echo -e "$(GREEN)[OK] Comparison complete$(RESET)"

# ============================================================
# List Available Tests (from JSON config)
# ============================================================

riscv_dv_list:
	@echo -e "$(CYAN)[RISCV-DV] Available tests (from $(RISCV_DV_CONFIG)):$(RESET)"
	@python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-all-tests | while read line; do \
		name=$$(echo $$line | cut -d: -f1); \
		iters=$$(echo $$line | cut -d: -f2); \
		echo -e "  - $$name ($$iters iterations)"; \
	done

# Show configuration summary
riscv_dv_config:
	@python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) summary

# ============================================================
# Run All Enabled Tests from JSON
# ============================================================

# Build all tests first, then run all
riscv_dv_run_all: riscv_dv_build_all riscv_dv_verilate _riscv_dv_run_only

# Run only (skip build) - useful if tests already built
riscv_dv_run_only: riscv_dv_verilate _riscv_dv_run_only

_riscv_dv_run_only:
	@echo -e "$(YELLOW)[RISCV-DV] Running all tests...$(RESET)"
	@mkdir -p $(RISCV_DV_LOG_DIR)
	@PASS=0; FAIL=0; \
	for mem in $(RISCV_DV_MEM_DIR)/*.mem; do \
		if [ -f "$$mem" ]; then \
			name=$$(basename $$mem .mem); \
			echo -e "  $(YELLOW)→ Running: $$name$(RESET)"; \
			if $(MAKE) --no-print-directory run \
				TEST_TYPE=riscv-dv \
				TEST_NAME=$$name \
				MEM_DIR="$(RISCV_DV_MEM_DIR)" \
				ELF_DIR="$(RISCV_DV_ELF_DIR)" \
				DUMP_DIR="$(RISCV_DV_DUMP_DIR)" \
				ADDR_DIR="$(RISCV_DV_ADDR_DIR)" \
				TEST_LOG_DIR="$(RISCV_DV_LOG_DIR)/$$name" \
				RTL_LOG_DIR="$(RISCV_DV_LOG_DIR)/$$name" \
				MAX_CYCLES=50000 2>/dev/null; then \
				echo -e "  $(GREEN)$(SUCCESS) $$name PASS$(RESET)"; \
				PASS=$$((PASS + 1)); \
			else \
				echo -e "  $(RED)✗ $$name FAIL$(RESET)"; \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e ""; \
	echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN) RISCV-DV Final Results: $$PASS passed, $$FAIL failed$(RESET)"; \
	echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"

# Build ALL enabled tests from JSON config
riscv_dv_build_all: riscv_dv_clone riscv_dv_setup
	@echo -e "$(YELLOW)[RISCV-DV] Building all enabled tests from config...$(RESET)"
	@python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-all-tests | while read line; do \
		test_name=$$(echo $$line | cut -d: -f1); \
		test_iter=$$(echo $$line | cut -d: -f2); \
		echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		echo -e "$(CYAN) Generating: $$test_name ($$test_iter iterations)$(RESET)"; \
		echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		$(MAKE) --no-print-directory _riscv_dv_gen_one TEST_NAME=$$test_name TEST_ITER=$$test_iter; \
	done
	@echo -e "$(YELLOW)[RISCV-DV] Compiling all tests...$(RESET)"
	@PASS=0; FAIL=0; \
	for src in $(RISCV_DV_GEN_DIR)/*.S; do \
		if [ -f "$$src" ]; then \
			name=$$(basename $$src .S); \
			if $(MAKE) --no-print-directory _riscv_dv_build_one SRC=$$src NAME=$$name 2>/dev/null; then \
				PASS=$$((PASS + 1)); \
			else \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[RISCV-DV] Build complete: $$PASS passed, $$FAIL failed$(RESET)"

# Generate tests for a specific test type
_riscv_dv_gen_one:
	@for i in $$(seq 0 $$(($(TEST_ITER) - 1))); do \
		python3 $(RISCV_DV_FALLBACK) \
			--test $(TEST_NAME) \
			--idx $$i \
			--seed $$(($(RISCV_DV_SEED) + $$i)) \
			--instr-cnt $(RISCV_DV_INSTR_CNT) \
			--output $(RISCV_DV_GEN_DIR)/$(TEST_NAME)_$$i.S; \
	done

# ============================================================
# Clean
# ============================================================

riscv_dv_clean:
	@echo -e "$(YELLOW)[RISCV-DV] Cleaning...$(RESET)"
	@rm -rf $(RISCV_DV_BUILD_DIR)
	@echo -e "$(GREEN)[OK] Clean complete$(RESET)"

# ============================================================
# Help
# ============================================================

riscv_dv_help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)     RISC-V DV Random Test Generator$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Configuration File:$(RESET)"
	@echo -e "  $(RISCV_DV_CONFIG)"
	@echo -e ""
	@echo -e "$(CYAN)Usage:$(RESET)"
	@echo -e "  make riscv_dv                    Build tests for default test type"
	@echo -e "  make riscv_dv_run                Run tests for default test type"
	@echo -e "  make riscv_dv_build_all          Build ALL tests from JSON (no run)"
	@echo -e "  make riscv_dv_run_all            Build & Run ALL tests from JSON"
	@echo -e "  make riscv_dv_run_only           Run only (skip build, tests must exist)"
	@echo -e "  make riscv_dv_compare            Compare with Spike ISS"
	@echo -e "  make riscv_dv_list               List available tests from config"
	@echo -e "  make riscv_dv_config             Show configuration summary"
	@echo -e "  make riscv_dv_clean              Clean build files"
	@echo -e ""
	@echo -e "$(CYAN)Configuration (override JSON):$(RESET)"
	@echo -e "  RISCV_DV_TEST=name               Test type"
	@echo -e "  RISCV_DV_ITER=N                  Number of iterations"
	@echo -e "  RISCV_DV_SEED=N                  Random seed"
	@echo -e "  RISCV_DV_ISA=rv32imc             Target ISA"
	@echo -e "  RISCV_DV_INSTR_CNT=N             Instructions per test (default: 500)"
	@echo -e ""
	@echo -e "$(CYAN)JSON Config Structure:$(RESET)"
	@echo -e "  generator.instr_cnt              Instructions per test"
	@echo -e "  generator.isa                    ISA configuration"
	@echo -e "  generator.seed                   Base random seed"
	@echo -e "  tests[].name                     Test name"
	@echo -e "  tests[].iterations               Number of iterations"
	@echo -e "  tests[].enabled                  Enable/disable test"
	@echo -e ""
	@echo -e "$(CYAN)Examples:$(RESET)"
	@echo -e "  make riscv_dv_run_all                              # Build & run all"
	@echo -e "  make riscv_dv_run_only                             # Run only (no build)"
	@echo -e "  make riscv_dv RISCV_DV_TEST=riscv_rand_instr_test  # Single test type"
	@echo -e ""

# ====== test/riscv_formal.mk ======
# ============================================================
# RISC-V Formal Verification Framework for Level-V
# ============================================================
# Formal verification using SymbiYosys and RISC-V Formal
# https://github.com/YosysHQ/riscv-formal

.PHONY: formal formal_clone formal_setup formal_run formal_clean formal_help
.PHONY: formal_check formal_cover formal_prove formal_bmc formal_report
.PHONY: formal_quick formal_standard formal_thorough formal_coverage formal_config formal_gen_sby

# ============================================================
# JSON Configuration
# ============================================================

FORMAL_CONFIG       := $(CONFIG_DIR)/tests/formal.json

# Helper to read JSON values
define read_formal_json
$(shell $(PYTHON) -c "import json; f=open('$(FORMAL_CONFIG)'); d=json.load(f); print($(1))" 2>/dev/null)
endef

# ============================================================
# Configuration from JSON
# ============================================================

# Repository
FORMAL_REPO_URL     := https://github.com/YosysHQ/riscv-formal.git
FORMAL_ROOT         := $(SUBREPO_DIR)/riscv-formal

# Paths from JSON (with defaults)
FORMAL_ENV_SRC      := $(ROOT_DIR)/$(or $(call read_formal_json,d.get('paths',{}).get('env_dir','')),env/riscv-formal)
FORMAL_BUILD_DIR    := $(ROOT_DIR)/$(or $(call read_formal_json,d.get('paths',{}).get('build_dir','')),build/formal)
FORMAL_WORK_DIR     := $(ROOT_DIR)/$(or $(call read_formal_json,d.get('paths',{}).get('work_dir','')),build/formal/work)
FORMAL_LOG_DIR      := $(ROOT_DIR)/$(or $(call read_formal_json,d.get('paths',{}).get('log_dir','')),results/logs/formal)

# Tool paths from JSON (with defaults)
YOSYS               ?= $(or $(call read_formal_json,d.get('tools',{}).get('yosys',{}).get('command','')),yosys)
SBY                 ?= $(or $(call read_formal_json,d.get('tools',{}).get('sby',{}).get('command','')),sby)
FORMAL_SOLVER_CMD   ?= $(or $(call read_formal_json,d.get('tools',{}).get('solver',{}).get('command','')),z3)

# RISC-V Formal configuration from JSON (with defaults)
FORMAL_MODE         ?= $(or $(call read_formal_json,d.get('verification',{}).get('mode','')),bmc)
FORMAL_DEPTH        ?= $(or $(call read_formal_json,d.get('verification',{}).get('depth','')),20)
FORMAL_ENGINE       ?= $(or $(call read_formal_json,d.get('verification',{}).get('engine','')),smtbmc)
FORMAL_SOLVER       ?= $(or $(call read_formal_json,d.get('verification',{}).get('solver','')),z3)
FORMAL_TIMEOUT      ?= $(or $(call read_formal_json,d.get('verification',{}).get('timeout','')),3600)

# ISA configuration from JSON
FORMAL_ISA_BASE     := $(or $(call read_formal_json,d.get('isa',{}).get('base','')),rv32i)
FORMAL_ISA_M        := $(call read_formal_json,d.get('isa',{}).get('extensions',{}).get('M',False))
FORMAL_ISA_C        := $(call read_formal_json,d.get('isa',{}).get('extensions',{}).get('C',False))

# CPU configuration from JSON
FORMAL_WRAPPER      := $(or $(call read_formal_json,d.get('cpu',{}).get('wrapper','')),rvfi_wrapper)
FORMAL_WRAPPER_FILE := $(ROOT_DIR)/$(or $(call read_formal_json,d.get('cpu',{}).get('wrapper_file','')),env/riscv-formal/rvfi_wrapper.sv)
FORMAL_XLEN         := $(or $(call read_formal_json,d.get('cpu',{}).get('xlen','')),32)

# Build ISA string
FORMAL_ISA          := $(FORMAL_ISA_BASE)
ifeq ($(FORMAL_ISA_M),True)
FORMAL_ISA          := $(FORMAL_ISA)m
endif
ifeq ($(FORMAL_ISA_C),True)
FORMAL_ISA          := $(FORMAL_ISA)c
endif

# Checks to run (from JSON)
FORMAL_CHECK_INSN   := $(call read_formal_json,d.get('checks',{}).get('instruction',{}).get('enabled',True))
FORMAL_CHECK_REG    := $(call read_formal_json,d.get('checks',{}).get('register',{}).get('enabled',True))
FORMAL_CHECK_PC_FWD := $(call read_formal_json,d.get('checks',{}).get('pc_forward',{}).get('enabled',True))
FORMAL_CHECK_PC_BWD := $(call read_formal_json,d.get('checks',{}).get('pc_backward',{}).get('enabled',True))
FORMAL_CHECK_MEM    := $(call read_formal_json,d.get('checks',{}).get('memory',{}).get('enabled',True))
FORMAL_CHECK_LIVE   := $(call read_formal_json,d.get('checks',{}).get('liveness',{}).get('enabled',False))
FORMAL_CHECK_UNIQUE := $(call read_formal_json,d.get('checks',{}).get('unique',{}).get('enabled',False))
FORMAL_CHECK_HANG   := $(call read_formal_json,d.get('checks',{}).get('hang',{}).get('enabled',True))
FORMAL_CHECK_COVER  := $(call read_formal_json,d.get('checks',{}).get('cover',{}).get('enabled',False))

# ============================================================
# Main Targets
# ============================================================

formal: formal_setup formal_run
	@echo -e "$(GREEN)[FORMAL] $(SUCCESS) Formal verification complete$(RESET)"

# ============================================================
# Clone Repository
# ============================================================

formal_clone:
	@echo -e "$(YELLOW)[FORMAL] Checking riscv-formal repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(FORMAL_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(FORMAL_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone --depth=1 $(FORMAL_REPO_URL); \
		echo -e "$(GREEN)[OK] riscv-formal cloned.$(RESET)"; \
	else \
		echo -e "$(GREEN)[SKIP] riscv-formal already exists.$(RESET)"; \
	fi

# ============================================================
# Setup Environment
# ============================================================

formal_setup: formal_clone
	@echo -e "$(YELLOW)[FORMAL] Setting up environment...$(RESET)"
	@mkdir -p $(FORMAL_ENV_SRC)
	@mkdir -p $(FORMAL_WORK_DIR) $(FORMAL_LOG_DIR)
	@# Check required tools
	@echo -e "$(YELLOW)[FORMAL] Checking required tools...$(RESET)"
	@if ! which $(YOSYS) > /dev/null 2>&1; then \
		echo -e "$(RED)[ERROR] yosys not found$(RESET)"; \
		echo -e "  Install: $(CYAN)apt install yosys$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)  $(SUCCESS) yosys found$(RESET)"; \
	fi
	@if ! which $(SBY) > /dev/null 2>&1; then \
		echo -e "$(RED)[ERROR] sby (SymbiYosys) not found$(RESET)"; \
		echo -e "  Install:"; \
		echo -e "    $(CYAN)git clone https://github.com/YosysHQ/sby.git$(RESET)"; \
		echo -e "    $(CYAN)cd sby && pip install .$(RESET)"; \
		echo -e "  Or via package manager:"; \
		echo -e "    $(CYAN)pip install sby$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)  $(SUCCESS) sby found$(RESET)"; \
	fi
	@if ! which $(FORMAL_SOLVER_CMD) > /dev/null 2>&1; then \
		echo -e "$(YELLOW)[WARN] SMT solver $(FORMAL_SOLVER_CMD) not found$(RESET)"; \
		echo -e "  Install: $(CYAN)apt install z3$(RESET) or $(CYAN)apt install boolector$(RESET)"; \
	else \
		echo -e "$(GREEN)  $(SUCCESS) SMT solver $(FORMAL_SOLVER_CMD) found$(RESET)"; \
	fi
	@# Check if wrapper exists
	@if [ ! -f "$(FORMAL_WRAPPER_FILE)" ]; then \
		echo -e "$(YELLOW)[WARN] RVFI wrapper not found at $(FORMAL_WRAPPER_FILE)$(RESET)"; \
		echo -e "$(YELLOW)       Generate with CPU integration.$(RESET)"; \
	else \
		echo -e "$(GREEN)  $(SUCCESS) RVFI wrapper found$(RESET)"; \
	fi
	@echo -e "$(GREEN)[OK] Setup complete$(RESET)"

# ============================================================
# Show Configuration
# ============================================================

formal_config:
	@echo -e "$(CYAN)[FORMAL] Current Configuration$(RESET)"
	@echo -e "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
	@echo -e "  Config file:    $(FORMAL_CONFIG)"
	@echo -e "  Mode:           $(FORMAL_MODE)"
	@echo -e "  Depth:          $(FORMAL_DEPTH)"
	@echo -e "  Engine:         $(FORMAL_ENGINE)"
	@echo -e "  Solver:         $(FORMAL_SOLVER)"
	@echo -e "  Timeout:        $(FORMAL_TIMEOUT)s"
	@echo -e "  ISA:            $(FORMAL_ISA)"
	@echo -e "  XLEN:           $(FORMAL_XLEN)"
	@echo -e "  Wrapper:        $(FORMAL_WRAPPER)"
	@echo -e "  Wrapper File:   $(FORMAL_WRAPPER_FILE)"
	@echo -e "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
	@echo -e "  Checks enabled:"
	@echo -e "    Instruction:  $(FORMAL_CHECK_INSN)"
	@echo -e "    Register:     $(FORMAL_CHECK_REG)"
	@echo -e "    PC Forward:   $(FORMAL_CHECK_PC_FWD)"
	@echo -e "    PC Backward:  $(FORMAL_CHECK_PC_BWD)"
	@echo -e "    Memory:       $(FORMAL_CHECK_MEM)"
	@echo -e "    Liveness:     $(FORMAL_CHECK_LIVE)"
	@echo -e "    Unique:       $(FORMAL_CHECK_UNIQUE)"
	@echo -e "    Hang:         $(FORMAL_CHECK_HANG)"
	@echo -e "    Cover:        $(FORMAL_CHECK_COVER)"
	@echo -e "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# ============================================================
# Generate SymbiYosys Script
# ============================================================

# Note: Full CPU verification requires Yosys-compatible RTL.
# Current Level-V uses advanced SystemVerilog features.
# For now, only wrapper module is verified.

formal_gen_sby:
	@echo -e "$(YELLOW)[FORMAL] Generating SymbiYosys config...$(RESET)"
	@echo "[options]" > $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "mode $(FORMAL_MODE)" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "depth $(FORMAL_DEPTH)" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "timeout $(FORMAL_TIMEOUT)" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "[engines]" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "$(FORMAL_ENGINE) $(FORMAL_SOLVER)" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "[script]" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "read_verilog -sv -DFORMAL $(FORMAL_WRAPPER_FILE)" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "prep -top $(FORMAL_WRAPPER)" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "[files]" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo "$(FORMAL_WRAPPER_FILE)" >> $(FORMAL_WORK_DIR)/level_formal.sby
	@echo -e "$(GREEN)[OK] SBY config generated at $(FORMAL_WORK_DIR)/level_formal.sby$(RESET)"

# ============================================================
# Run Formal Verification
# ============================================================

formal_run: formal_setup formal_gen_sby
	@echo -e "$(YELLOW)[FORMAL] Running formal verification...$(RESET)"
	@echo -e "  Mode:    $(FORMAL_MODE)"
	@echo -e "  Depth:   $(FORMAL_DEPTH)"
	@echo -e "  Engine:  $(FORMAL_ENGINE)"
	@echo -e "  Solver:  $(FORMAL_SOLVER)"
	@echo -e "  Timeout: $(FORMAL_TIMEOUT)s"
	@if [ -f "$(FORMAL_WRAPPER_FILE)" ]; then \
		cd $(FORMAL_WORK_DIR) && $(SBY) -f level_formal.sby 2>&1 | tee $(FORMAL_LOG_DIR)/formal.log; \
		if [ $${PIPESTATUS[0]} -ne 0 ]; then \
			echo -e "$(RED)[FAIL] Formal verification failed$(RESET)"; \
			exit 1; \
		fi; \
	else \
		echo -e "$(RED)[ERROR] RVFI wrapper not found$(RESET)"; \
		echo -e "$(YELLOW)Create $(FORMAL_WRAPPER_FILE) first$(RESET)"; \
		exit 1; \
	fi
	@echo -e "$(GREEN)[OK] Formal run complete$(RESET)"

# ============================================================
# Preset Targets (from JSON)
# ============================================================

formal_quick:
	@echo -e "$(CYAN)[FORMAL] Running quick preset...$(RESET)"
	$(MAKE) formal_run FORMAL_MODE=bmc FORMAL_DEPTH=10

formal_standard:
	@echo -e "$(CYAN)[FORMAL] Running standard preset...$(RESET)"
	$(MAKE) formal_run FORMAL_MODE=bmc FORMAL_DEPTH=20

formal_thorough:
	@echo -e "$(CYAN)[FORMAL] Running thorough preset...$(RESET)"
	$(MAKE) formal_run FORMAL_MODE=prove FORMAL_DEPTH=30

formal_coverage:
	@echo -e "$(CYAN)[FORMAL] Running coverage preset...$(RESET)"
	$(MAKE) formal_run FORMAL_MODE=cover FORMAL_DEPTH=50

# ============================================================
# Specific Formal Checks
# ============================================================

formal_bmc: FORMAL_MODE=bmc
formal_bmc: formal_run
	@echo -e "$(GREEN)[FORMAL] BMC complete$(RESET)"

formal_prove: FORMAL_MODE=prove
formal_prove: formal_run
	@echo -e "$(GREEN)[FORMAL] Prove complete$(RESET)"

formal_cover: FORMAL_MODE=cover
formal_cover: formal_run
	@echo -e "$(GREEN)[FORMAL] Cover complete$(RESET)"

# ============================================================
# Report
# ============================================================

formal_report:
	@echo -e "$(CYAN)[FORMAL] Verification Report$(RESET)"
	@echo -e "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
	@if [ -f "$(FORMAL_LOG_DIR)/formal.log" ]; then \
		grep -E "(PASS|FAIL|ERROR|TIMEOUT)" $(FORMAL_LOG_DIR)/formal.log || true; \
	else \
		echo -e "$(YELLOW)No logs found. Run 'make formal' first.$(RESET)"; \
	fi
	@echo -e "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# ============================================================
# Clean
# ============================================================

formal_clean:
	@echo -e "$(YELLOW)[FORMAL] Cleaning...$(RESET)"
	@rm -rf $(FORMAL_BUILD_DIR)
	@echo -e "$(GREEN)[OK] Clean complete$(RESET)"

# ============================================================
# Help
# ============================================================

formal_help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)     RISC-V Formal Verification Framework$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Configuration:$(RESET)"
	@echo -e "  Config file: $(FORMAL_CONFIG)"
	@echo -e ""
	@echo -e "$(CYAN)Main Commands:$(RESET)"
	@echo -e "  make formal              Run formal verification"
	@echo -e "  make formal_config       Show current configuration"
	@echo -e "  make formal_report       Show verification report"
	@echo -e "  make formal_clean        Clean build files"
	@echo -e ""
	@echo -e "$(CYAN)Modes:$(RESET)"
	@echo -e "  make formal_bmc          Bounded Model Checking"
	@echo -e "  make formal_prove        Inductive Proof"
	@echo -e "  make formal_cover        Coverage Analysis"
	@echo -e ""
	@echo -e "$(CYAN)Presets (from JSON):$(RESET)"
	@echo -e "  make formal_quick        Quick test (depth=10, bmc)"
	@echo -e "  make formal_standard     Standard (depth=20, bmc)"
	@echo -e "  make formal_thorough     Thorough (depth=30, prove)"
	@echo -e "  make formal_coverage     Coverage (depth=50, cover)"
	@echo -e ""
	@echo -e "$(CYAN)Override Options:$(RESET)"
	@echo -e "  FORMAL_DEPTH=N           Set BMC depth"
	@echo -e "  FORMAL_MODE=mode         bmc|prove|cover|live"
	@echo -e "  FORMAL_ENGINE=engine     smtbmc|btor|abc"
	@echo -e "  FORMAL_SOLVER=solver     z3|boolector|yices|bitwuzla"
	@echo -e "  FORMAL_TIMEOUT=N         Timeout in seconds"
	@echo -e ""
	@echo -e "$(CYAN)Examples:$(RESET)"
	@echo -e "  make formal FORMAL_DEPTH=30"
	@echo -e "  make formal_prove FORMAL_SOLVER=boolector"
	@echo -e "  make formal_quick FORMAL_TIMEOUT=600"
	@echo -e ""
	@echo -e "$(CYAN)Prerequisites:$(RESET)"
	@echo -e "  - Yosys:       apt install yosys"
	@echo -e "  - SymbiYosys:  pip3 install sby"
	@echo -e "  - SMT Solver:  apt install z3 (or boolector)"
	@echo -e ""
	@echo -e "$(CYAN)Note:$(RESET)"
	@echo -e "  Edit $(FORMAL_CONFIG) to change defaults."
	@echo -e "  Full verification requires RVFI interface in CPU."
	@echo -e ""

# ====== synth/yosys.mk ======
# =========================================
# Level RISC-V — Yosys Synthesis & Analysis
# =========================================
# Performs static design checks such as:
#   - Unconnected nets
#   - Multiple drivers
#   - Combinational loops
# Also supports synthesis and graphical netlist visualization.
# =========================================

# -----------------------------------------
# Yosys Configuration
# -----------------------------------------
YOSYS_FLAGS := -q
YOSYS_CMD   := read_verilog -sv $(SV_SOURCES) $(TB_FILE); \
               hierarchy -check -top $(RTL_LEVEL); \
               proc; opt; check

# =========================================
# Targets
# =========================================

# ---- Structural Check ----
yosys_check:
	@echo -e "$(YELLOW)[RUNNING YOSYS STRUCTURAL CHECKS — $(BUILD_MODE_NAME)]$(RESET)"
	@$(MKDIR) $(REPORT_DIR)
	@($(YOSYS) $(YOSYS_FLAGS) -p "$(YOSYS_CMD)" 2>&1 | tee $(REPORT_DIR)/yosys_check.log); \
	EXIT_CODE=$$?; \
	if grep -qi "ERROR:" $(REPORT_DIR)/yosys_check.log; then \
		echo "$(RED)TEST_NAME Yosys check failed (see yosys_check.log).$(RESET)"; \
		exit 1; \
	elif [ $$EXIT_CODE -ne 0 ]; then \
		echo "$(RED)TEST_NAME Yosys exited with code $$EXIT_CODE.$(RESET)"; \
		exit $$EXIT_CODE; \
	fi; \
	if grep -qi "Combinational loop" $(REPORT_DIR)/yosys_check.log; then \
		echo "$(RED)TEST_NAME Combinational loop(s) detected!$(RESET)"; \
		exit 1; \
	else \
		echo "$(GREEN)TEST_NAME No combinational loops detected.$(RESET)"; \
	fi; \
	if grep -qi "multiple drivers" $(REPORT_DIR)/yosys_check.log; then \
		echo "$(RED) TEST_NAME Multiple driver(s) detected!$(RESET)"; \
		exit 1; \
	else \
		echo "$(GREEN) TEST_NAME No multiple driver issues found.$(RESET)"; \
	fi; \
	if grep -qi "unconnected" $(REPORT_DIR)/yosys_check.log; then \
		echo "$(YELLOW) TEST_NAME  Some unconnected nets found — review yosys_check.log.$(RESET)"; \
	else \
		echo "$(GREEN) TEST_NAME No unconnected nets found.$(RESET)"; \
	fi; \
	echo "$(GREEN)[Yosys structural check completed successfully]$(RESET)"

# ---- Synthesis ----
yosys_synth:
	@echo -e "$(YELLOW)[RUNNING YOSYS SYNTHESIS — $(BUILD_MODE_NAME)]$(RESET)"
	@$(MKDIR) $(REPORT_DIR)
	@($(YOSYS) $(YOSYS_FLAGS) -p "read_verilog -sv $(SV_SOURCES); \
		hierarchy -check -top $(TOP_LEVEL); synth -top $(TOP_LEVEL); \
		write_json $(REPORT_DIR)/$(TOP_LEVEL)_netlist.json; \
		write_verilog $(REPORT_DIR)/$(TOP_LEVEL)_netlist.v" \
		2>&1 | tee $(REPORT_DIR)/yosys_synth.log); \
	EXIT_CODE=$$?; \
	if grep -qi "ERROR:" $(REPORT_DIR)/yosys_synth.log; then \
		echo "$(RED)TEST_NAME Yosys synthesis failed (see yosys_synth.log).$(RESET)"; \
		exit 1; \
	elif [ $$EXIT_CODE -ne 0 ]; then \
		echo "$(RED)TEST_NAME Yosys exited with error code $$EXIT_CODE.$(RESET)"; \
		exit $$EXIT_CODE; \
	else \
		echo "$(GREEN)TEST_NAME Yosys synthesis completed successfully — netlist written to $(REPORT_DIR).$(RESET)"; \
	fi

# ---- Visualization ----
yosys_show:
	@echo -e "$(YELLOW)[GENERATING YOSYS GRAPHICAL NETLIST — $(BUILD_MODE_NAME)]$(RESET)"
	@$(MKDIR) $(REPORT_DIR)
	@($(YOSYS) $(YOSYS_FLAGS) -p "read_verilog -sv $(SV_SOURCES); \
		hierarchy -top $(TOP_LEVEL); proc; opt; synth -top $(TOP_LEVEL); \
		show -format svg -prefix $(REPORT_DIR)/$(TOP_LEVEL)_graph" \
		2>&1 | tee $(REPORT_DIR)/yosys_show.log); \
	if grep -qi "ERROR:" $(REPORT_DIR)/yosys_show.log; then \
		echo "$(RED)TEST_NAME Graph generation failed (see yosys_show.log).$(RESET)"; \
		exit 1; \
	fi; \
	if [ -f $(REPORT_DIR)/$(TOP_LEVEL)_graph.svg ]; then \
		echo "$(GREEN)TEST_NAME Netlist visualization generated:$(RESET) $(REPORT_DIR)/$(TOP_LEVEL)_graph.svg"; \
		echo "🌐 Open with: xdg-open $(REPORT_DIR)/$(TOP_LEVEL)_graph.svg"; \
	else \
		echo "$(RED)TEST_NAME No SVG output found. Check yosys_show.log.$(RESET)"; \
		exit 1; \
	fi

# ---- Cleanup ----
clean_yosys:
	@echo -e "$(RED)[CLEANING YOSYS REPORT FILES]$(RESET)"
	rm -f $(REPORT_DIR)/yosys_check.log $(REPORT_DIR)/yosys_synth.log $(REPORT_DIR)/yosys_show.log
	rm -f $(REPORT_DIR)/$(TOP_LEVEL)_netlist.v $(REPORT_DIR)/$(TOP_LEVEL)_netlist.json
	rm -f $(REPORT_DIR)/$(TOP_LEVEL)_graph.svg
	@echo -e "$(GREEN)🧹 Yosys logs and visualizations cleaned.$(RESET)"

# ============================================================
# Yosys Help — Display available Yosys static & synthesis targets
# ============================================================
yosys_help:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)             Level RISC-V — Yosys Structural Analysis          $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Purpose:$(RESET)"
	@echo -e "  Run structural checks, synthesis, and visualization using Yosys."
	@echo -e "  Detects unconnected nets, multiple drivers, and combinational loops."
	@echo -e ""
	@echo -e "$(YELLOW)Main Targets:$(RESET)"
	@echo -e "  $(GREEN)yosys_check   $(RESET)– Run static structural analysis"
	@echo -e "  $(GREEN)yosys_synth   $(RESET)– Perform synthesis and export netlists"
	@echo -e "  $(GREEN)yosys_show    $(RESET)– Generate a graphical (SVG) netlist view"
	@echo -e "  $(GREEN)clean_yosys   $(RESET)– Remove Yosys reports, netlists, and graphs"
	@echo -e ""
	@echo -e "$(YELLOW)Reports:$(RESET)"
	@echo -e "  • yosys_check.log – Results of structural integrity checks"
	@echo -e "  • yosys_synth.log – Synthesis and netlist generation report"
	@echo -e "  • yosys_show.log  – SVG graph generation log"
	@echo -e ""
	@echo -e "$(YELLOW)Output Files:$(RESET)"
	@echo -e "  • $(REPORT_DIR)/$(TOP_LEVEL)_netlist.v"
	@echo -e "  • $(REPORT_DIR)/$(TOP_LEVEL)_netlist.json"
	@echo -e "  • $(REPORT_DIR)/$(TOP_LEVEL)_graph.svg"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make yosys_check TOP_LEVEL=level_wrapper"
	@echo -e "  make yosys_synth TOP_LEVEL=level_wrapper"
	@echo -e "  make yosys_show  TOP_LEVEL=level_wrapper"
	@echo -e "  make clean_yosys"
	@echo -e ""
	@echo -e "$(YELLOW)Tips:$(RESET)"
	@echo -e "  • Use yosys_show to visualize RTL hierarchy in SVG format."
	@echo -e "  • Run yosys_check regularly to catch structural design issues early."
	@echo -e "  • All generated reports are stored under $(REPORT_DIR)."
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)   Tip: You can open the SVG with 'xdg-open' or any browser.   $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"

# ====== synth/openlane.mk ======
# =========================================
# Level RISC-V — OpenLane ASIC Flow
# =========================================
#
# ┌─────────────────────────────────────────────────────────┐
# │  OpenLane flow stages (steps)                           │
# │                                                         │
# │   1. synthesis (Yosys)                                  │
# │   2. sta (OpenSTA - synthesis)                          │
# │   3. init_floorplan (area/die sizing)                   │
# │   4. ioplacer (pin placement)                           │
# │   5. ★ manual_macro_place (MACRO_PLACEMENT_CFG)         │
# │   6. pdn (power delivery network)                      │
# │   7. tap/decap cell insertion                           │
# │   8-10. global_placement (GPL)                          │
# │  11. resize/repair                                      │
# │  12-14. detailed_placement                              │
# │  15. cts (clock tree synthesis)                         │
# │  16-17. post-CTS optimization                          │
# │  18. global_routing (GRT)                               │
# │  19. fill_insertion                                     │
# │  20. detailed_routing (DRT)                             │
# │  21. spef_extraction                                    │
# │  22-23. sta (signoff)                                   │
# │  24-29. magic/klayout/lvs/drc/antenna                   │
# │  30. final views & summary                             │
# └─────────────────────────────────────────────────────────┘
#
# SRAM macro placement flow:
#   Done at Step 5 (manual_macro_place). Workflow:
#   1. make asic_sram       → download SRAM LEF/GDS/LIB
#   2. make asic_prep       → convert RTL with sv2v
#   3. make asic_synth_only → run synthesis + floorplan only
#   4. make asic_dump_names → extract real instance names from ODB
#   5. update macro_placement.cfg with real names
#   6. enable MACRO_PLACEMENT_CFG line in config.tcl
#   7. make asic_run        → start full flow
#
# =========================================

# -----------------------------------------
# Paths & Defaults
# -----------------------------------------
OPENLANE_SH       := $(SCRIPT_DIR)/shell/openlane_flow.sh
SRAM_GEN_SH       := $(SCRIPT_DIR)/shell/fetch_sky130_sram_macros_for_openlane.sh
ASIC_SUBREPO_SH   := $(SCRIPT_DIR)/shell/setup_asic_subrepos.sh

ASIC_DESIGN_DIR   := $(ROOT_DIR)/asic/openlane/designs/level_wrapper
ASIC_RUNS_DIR     := $(RESULTS_DIR)/asic/openlane/level_wrapper/runs
ASIC_CONFIG       := $(ASIC_DESIGN_DIR)/config.tcl
MACRO_CFG         := $(ASIC_DESIGN_DIR)/macro_placement.cfg
SRAM_MACRO_DIR    := $(ASIC_DESIGN_DIR)/macros/sky130_sram_1kbyte_1rw1r_32x256_8

# OpenLane / Docker settings (override via env or command line)
OPENLANE_IMAGE    ?= efabless/openlane:2023.09.07
PDK_ROOT          ?= $(HOME)/.volare
PDK               ?= sky130A
ASIC_TAG          ?= run_$(shell date +%Y%m%d_%H%M%S)
DOCKER_CPUS       ?=
DOCKER_CPU_SHARES ?=

# SRAM macro name
SRAM_MACRO_NAME   ?= sky130_sram_1kbyte_1rw1r_32x256_8
SRAM_MACRO_REPO   ?= https://github.com/efabless/sky130_sram_macros.git

# -----------------------------------------
# Docker helper
# -----------------------------------------
DOCKER_BASE = docker run --rm \
	-u "$$(id -u):$$(id -g)" \
	-e PDK_ROOT="$(PDK_ROOT)" \
	-e PDK="$(PDK)" \
	$(if $(DOCKER_CPUS),--cpus $(DOCKER_CPUS),) \
	$(if $(DOCKER_CPU_SHARES),--cpu-shares $(DOCKER_CPU_SHARES),) \
	-v "$(ROOT_DIR):$(ROOT_DIR)" \
	-v "$(PDK_ROOT):$(PDK_ROOT)" \
	-w "$(ROOT_DIR)"

DOCKER_RUN = $(DOCKER_BASE) $(OPENLANE_IMAGE)

# Interactive mode (with terminal)
DOCKER_RUN_IT = docker run --rm -it \
	-u "$$(id -u):$$(id -g)" \
	-e PDK_ROOT="$(PDK_ROOT)" \
	-e PDK="$(PDK)" \
	$(if $(DOCKER_CPUS),--cpus $(DOCKER_CPUS),) \
	$(if $(DOCKER_CPU_SHARES),--cpu-shares $(DOCKER_CPU_SHARES),) \
	-v "$(ROOT_DIR):$(ROOT_DIR)" \
	-v "$(PDK_ROOT):$(PDK_ROOT)" \
	-w "$(ROOT_DIR)" \
	$(OPENLANE_IMAGE)

# -----------------------------------------
# Latest run directory helper
# -----------------------------------------
LATEST_RUN = $(shell ls -1dt $(ASIC_RUNS_DIR)/* 2>/dev/null | head -n1)

# ==============================================================
# SRAM Macro Targets
# ==============================================================

.PHONY: asic_sram asic_sram_clean asic_sram_info sram

## Download and materialize SRAM macros (LEF/GDS/LIB/V)
asic_sram:
	@echo -e "$(CYAN)[SRAM]$(RESET) Generating SRAM macro: $(SRAM_MACRO_NAME)"
	@MACRO_NAME="$(SRAM_MACRO_NAME)" MACRO_REPO_URL="$(SRAM_MACRO_REPO)" \
		bash $(SRAM_GEN_SH)
	@echo -e "$(GREEN)$(SUCCESS) SRAM macro ready$(RESET)"

## Clean SRAM macro files
asic_sram_clean:
	@echo -e "$(YELLOW)[SRAM CLEAN]$(RESET)"
	@bash $(SRAM_GEN_SH) --clean
	@echo -e "$(GREEN)$(SUCCESS) SRAM macros cleaned$(RESET)"

## Show SRAM macro file status
asic_sram_info:
	@echo -e "$(CYAN)[SRAM INFO]$(RESET)"
	@echo "  Macro name : $(SRAM_MACRO_NAME)"
	@echo "  Macro dir  : $(SRAM_MACRO_DIR)"
	@if [ -d "$(SRAM_MACRO_DIR)" ]; then \
		echo -e "  Status     : $(GREEN)$(SUCCESS) Files present$(RESET)"; \
		ls -lh $(SRAM_MACRO_DIR)/ | tail -n +2 | sed 's/^/  /'; \
	else \
		echo -e "  Status     : $(RED)$(ERROR) Not found$(RESET)"; \
		echo "  Run: make asic_sram"; \
	fi

## Shortcut: make sram → make asic_sram
sram: asic_sram

# ==============================================================
# Source Preparation
# ==============================================================

.PHONY: asic_prep

## Copy RTL sources and run sv2v conversion
asic_prep:
	@echo -e "$(CYAN)[OPENLANE PREP]$(RESET) Preparing sources (sv2v)..."
	@bash $(OPENLANE_SH) prep
	@echo -e "$(GREEN)$(SUCCESS) Sources ready$(RESET)"

# ==============================================================
# Setup & Dependencies
# ==============================================================

.PHONY: asic_setup asic_subrepos asic_check

## Prepare OpenLane Docker image and SRAM macros
asic_setup: asic_sram
	@echo -e "$(CYAN)[OPENLANE SETUP]$(RESET)"
	@bash $(OPENLANE_SH) setup
	@echo -e "$(GREEN)$(SUCCESS) Setup complete$(RESET)"

## Set up ASIC tool subrepos
asic_subrepos:
	@echo -e "$(YELLOW)[ASIC TOOL SUBREPOS]$(RESET)"
	@bash $(ASIC_SUBREPO_SH)

## Check all dependencies required for the flow
asic_check:
	@echo -e "$(CYAN)[ASIC CHECK]$(RESET) Checking dependencies..."
	@echo -n "  Docker         : "; \
		command -v docker >/dev/null 2>&1 && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(RED)MISSING$(RESET)"
	@echo -n "  OpenLane image : "; \
		docker image inspect $(OPENLANE_IMAGE) >/dev/null 2>&1 && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(RED)MISSING → make asic_setup$(RESET)"
	@echo -n "  PDK ($(PDK))   : "; \
		[ -d "$(PDK_ROOT)/$(PDK)" ] && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(RED)MISSING$(RESET)"
	@echo -n "  SRAM macros    : "; \
		[ -f "$(SRAM_MACRO_DIR)/$(SRAM_MACRO_NAME).lef" ] && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(RED)MISSING → make asic_sram$(RESET)"
	@echo -n "  sv2v sources   : "; \
		[ -f "$(ASIC_DESIGN_DIR)/src/level_wrapper_sv2v.v" ] && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(YELLOW)Not prepared → make asic_prep$(RESET)"
	@echo -n "  config.tcl     : "; \
		[ -f "$(ASIC_CONFIG)" ] && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(RED)MISSING$(RESET)"
	@echo -n "  macro_place cfg: "; \
		[ -f "$(MACRO_CFG)" ] && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(YELLOW)Not found (optional)$(RESET)"

# ==============================================================
# Full Flow
# ==============================================================

.PHONY: asic_run asic_run_clean asic

## Full OpenLane flow: SRAM + sources + flow.tcl
asic_run: asic_sram asic_prep
	@echo -e "$(CYAN)[OPENLANE RUN]$(RESET) Starting full flow..."
	@echo "  Tag        : $(ASIC_TAG)"
	@echo "  Config     : $(ASIC_CONFIG)"
	@echo "  Runs dir   : $(ASIC_RUNS_DIR)"
	@mkdir -p $(ASIC_RUNS_DIR)
	@TAG="$(ASIC_TAG)" RESULTS_ROOT="$(RESULTS_DIR)/asic/openlane/level_wrapper" \
		bash $(OPENLANE_SH) run
	@echo -e "$(GREEN)$(SUCCESS) Flow completed$(RESET)"

## Start from scratch: clean + full run
asic_run_clean: asic_clean asic_run

## Shortcut: make asic → make asic_run
asic: asic_run

# ==============================================================
# Step-by-Step Interactive Flow
# ==============================================================

.PHONY: asic_interactive asic_interactive_raw asic_shell

## Open OpenLane in interactive mode (auto-prep: package require + prep automatic)
asic_interactive: asic_sram asic_prep
	@echo -e "$(CYAN)[OPENLANE INTERACTIVE]$(RESET) Auto-initializing..."
	@mkdir -p $(ASIC_RUNS_DIR)
	docker run --rm -it \
		-u "$$(id -u):$$(id -g)" \
		-e PDK_ROOT="$(PDK_ROOT)" \
		-e PDK="$(PDK)" \
		-e LEVEL_DESIGN_DIR="$(ASIC_DESIGN_DIR)" \
		-e LEVEL_RUN_TAG="$(ASIC_TAG)" \
		-e LEVEL_RUNS_DIR="$(ASIC_RUNS_DIR)" \
		$(if $(DOCKER_CPUS),--cpus $(DOCKER_CPUS),) \
		$(if $(DOCKER_CPU_SHARES),--cpu-shares $(DOCKER_CPU_SHARES),) \
		-v "$(ROOT_DIR):$(ROOT_DIR)" \
		-v "$(PDK_ROOT):$(PDK_ROOT)" \
		-w "$(ROOT_DIR)" \
		$(OPENLANE_IMAGE) \
		/bin/bash -lc '{ \
			echo "package require openlane" ; \
			echo "prep -design $(ASIC_DESIGN_DIR) -tag $(ASIC_TAG) -run_path $(ASIC_RUNS_DIR) -overwrite" ; \
			echo "puts \\\"\"" ; \
			echo "puts \\\"[LEVEL] Ready! Type: run_synthesis, run_floorplan, etc.\\\"" ; \
			echo "puts \\\"\"" ; \
			cat ; \
		} | tclsh /openlane/flow.tcl -interactive'

## Open OpenLane in interactive mode (bare — type your own prep commands)
asic_interactive_raw: asic_sram asic_prep
	@echo -e "$(CYAN)[OPENLANE INTERACTIVE RAW]$(RESET)"
	@echo "  Enter the following commands:"
	@echo "    package require openlane"
	@echo "    prep -design $(ASIC_DESIGN_DIR) -tag $(ASIC_TAG) -run_path $(ASIC_RUNS_DIR)"
	@echo "  Veya tek komutla:"
	@echo "    source $(ROOT_DIR)/asic/openlane/interactive_init.tcl"
	@echo ""
	@mkdir -p $(ASIC_RUNS_DIR)
	docker run --rm -it \
		-u "$$(id -u):$$(id -g)" \
		-e PDK_ROOT="$(PDK_ROOT)" \
		-e PDK="$(PDK)" \
		-e LEVEL_DESIGN_DIR="$(ASIC_DESIGN_DIR)" \
		-e LEVEL_RUN_TAG="$(ASIC_TAG)" \
		-e LEVEL_RUNS_DIR="$(ASIC_RUNS_DIR)" \
		$(if $(DOCKER_CPUS),--cpus $(DOCKER_CPUS),) \
		$(if $(DOCKER_CPU_SHARES),--cpu-shares $(DOCKER_CPU_SHARES),) \
		-v "$(ROOT_DIR):$(ROOT_DIR)" \
		-v "$(PDK_ROOT):$(PDK_ROOT)" \
		-w "$(ROOT_DIR)" \
		$(OPENLANE_IMAGE) \
		/bin/bash -lc "tclsh /openlane/flow.tcl -interactive"

## Open a bash shell in the OpenLane container (for debug/inspection)
asic_shell:
	@echo -e "$(CYAN)[OPENLANE SHELL]$(RESET) Opening bash in container..."
	$(DOCKER_RUN_IT) /bin/bash

# ==============================================================
# Synthesis-Only (for name discovery)
# ==============================================================

.PHONY: asic_synth_only

## Run synthesis + floorplan only (for instance name discovery)
asic_synth_only: asic_sram asic_prep
	@echo -e "$(CYAN)[SYNTH ONLY]$(RESET) Running synthesis + floorplan..."
	@mkdir -p $(ASIC_RUNS_DIR)
	docker run --rm \
		-u "$$(id -u):$$(id -g)" \
		-e PDK_ROOT="$(PDK_ROOT)" \
		-e PDK="$(PDK)" \
		-e LEVEL_DESIGN_DIR="$(ASIC_DESIGN_DIR)" \
		-e LEVEL_RUNS_DIR="$(ASIC_RUNS_DIR)" \
		$(if $(DOCKER_CPUS),--cpus $(DOCKER_CPUS),) \
		$(if $(DOCKER_CPU_SHARES),--cpu-shares $(DOCKER_CPU_SHARES),) \
		-v "$(ROOT_DIR):$(ROOT_DIR)" \
		-v "$(PDK_ROOT):$(PDK_ROOT)" \
		-w "$(ROOT_DIR)" \
		$(OPENLANE_IMAGE) \
		/bin/bash -lc "tclsh /openlane/flow.tcl -interactive -file $(ROOT_DIR)/asic/openlane/synth_only.tcl"
	@echo -e "$(GREEN)$(SUCCESS) Synthesis + floorplan done$(RESET)"
	@echo "  Run dir: $(ASIC_RUNS_DIR)/synth_discovery"
	@echo "  Next  : make asic_dump_names"

# ==============================================================
# Macro Instance Name Discovery
# ==============================================================

.PHONY: asic_dump_names

## Extract SRAM macro instance names from floorplan ODB
##   make asic_dump_names           → from synth_discovery or latest run
##   make asic_dump_names RUN=name  → from a specific run
asic_dump_names:
	@echo -e "$(CYAN)[DUMP NAMES]$(RESET) Extracting macro instance names from ODB..."
	@SEARCH_DIR=""; \
	if [ -n "$(RUN)" ] && [ -d "$(ASIC_RUNS_DIR)/$(RUN)" ]; then \
		SEARCH_DIR="$(ASIC_RUNS_DIR)/$(RUN)"; \
	elif [ -d "$(ASIC_RUNS_DIR)/synth_discovery" ]; then \
		SEARCH_DIR="$(ASIC_RUNS_DIR)/synth_discovery"; \
	elif [ -n "$(LATEST_RUN)" ]; then \
		SEARCH_DIR="$(LATEST_RUN)"; \
	else \
		echo -e "$(RED)$(ERROR) No run found. Run 'make asic_synth_only' first$(RESET)"; \
		exit 1; \
	fi; \
	echo "  Using run: $$SEARCH_DIR"; \
	ODB=$$(find "$$SEARCH_DIR" -name '*.odb' -path '*/floorplan/*' 2>/dev/null | sort | tail -1); \
	if [ -z "$$ODB" ]; then \
		ODB=$$(find "$$SEARCH_DIR" -name '*.odb' 2>/dev/null | sort | tail -1); \
	fi; \
	if [ -z "$$ODB" ]; then \
		echo -e "$(RED)$(ERROR) No ODB file found in $$SEARCH_DIR$(RESET)"; \
		exit 1; \
	fi; \
	echo "  ODB file: $$ODB"; \
	echo ""; \
	$(DOCKER_BASE) $(OPENLANE_IMAGE) /bin/bash -lc \
		"openroad -python $(ROOT_DIR)/script/python/openroad_list_block_macros_from_odb.py $$ODB"; \
	echo ""; \
	echo -e "$(GREEN)$(SUCCESS) Done. Copy the names above into macro_placement.cfg$(RESET)"

# ==============================================================
# Resume a Previous Run
# ==============================================================

.PHONY: asic_resume

## Resume a previous run from where it stopped
##   make asic_resume RUN=run_20260218_123456
##   make asic_resume  (resumes the latest run)
asic_resume:
	@echo -e "$(CYAN)[OPENLANE RESUME]$(RESET)"
	@RUN_DIR=""; \
	if [ -n "$(RUN)" ] && [ -d "$(ASIC_RUNS_DIR)/$(RUN)" ]; then \
		RUN_DIR="$(ASIC_RUNS_DIR)/$(RUN)"; \
	elif [ -n "$(LATEST_RUN)" ]; then \
		RUN_DIR="$(LATEST_RUN)"; \
	else \
		echo -e "$(RED)$(ERROR) No run found to resume$(RESET)"; \
		exit 1; \
	fi; \
	TAG_NAME=$$(basename "$$RUN_DIR"); \
	echo "  Resuming: $$RUN_DIR"; \
	echo "  Tag     : $$TAG_NAME"; \
	$(DOCKER_RUN_IT) /bin/bash -lc "\
		tclsh /openlane/flow.tcl -interactive << 'TCLEOF' \
\npackage require openlane \
\nprep -design $(ASIC_DESIGN_DIR) -tag $$TAG_NAME -run_path $(ASIC_RUNS_DIR) -overwrite \
\nputs \"CURRENT_INDEX = \\\$$::env(CURRENT_INDEX)\" \
\nputs \"CURRENT_DEF   = \\\$$::env(CURRENT_DEF)\" \
\nTCLEOF"

# ==============================================================
# Reports & Inspection
# ==============================================================

.PHONY: asic_report asic_runs asic_metrics asic_timing

## Show reports from the latest run
asic_report:
	@echo -e "$(CYAN)[OPENLANE REPORT]$(RESET)"
	@bash $(OPENLANE_SH) report

## List existing run directories
asic_runs:
	@echo -e "$(CYAN)[ASIC RUNS]$(RESET)"
	@if [ -d "$(ASIC_RUNS_DIR)" ]; then \
		for d in $(ASIC_RUNS_DIR)/*/; do \
			[ -d "$$d" ] || continue; \
			tag=$$(basename "$$d"); \
			step=$$(grep -oP 'Step \K[0-9]+' "$$d/openlane.log" 2>/dev/null | tail -1 || echo "?"); \
			done_mark=""; \
			[ -f "$$d/results/final/gds/level_wrapper.gds" ] && done_mark=" $(GREEN)$(SUCCESS)$(RESET)"; \
			echo -e "  $$tag  (last step: $$step)$$done_mark"; \
		done; \
	else \
		echo "  No runs yet."; \
	fi

## Show metrics from the latest run (area, cell count, etc.)
asic_metrics:
	@if [ -n "$(LATEST_RUN)" ] && [ -f "$(LATEST_RUN)/reports/metrics.csv" ]; then \
		echo -e "$(CYAN)[METRICS]$(RESET) $(LATEST_RUN)/reports/metrics.csv"; \
		head -2 "$(LATEST_RUN)/reports/metrics.csv" | column -t -s,; \
	else \
		echo -e "$(RED)No metrics found$(RESET)"; \
	fi

## Show timing report from the latest run
asic_timing:
	@if [ -n "$(LATEST_RUN)" ]; then \
		STA=$$(find "$(LATEST_RUN)" -name '*sta*summary*' -o -name '*timing*' 2>/dev/null | sort | tail -3); \
		if [ -n "$$STA" ]; then \
			echo -e "$(CYAN)[TIMING]$(RESET)"; \
			for f in $$STA; do echo "--- $$f ---"; head -30 "$$f"; echo ""; done; \
		else \
			echo -e "$(RED)No timing reports found$(RESET)"; \
		fi; \
	else \
		echo -e "$(RED)No runs found$(RESET)"; \
	fi

# ==============================================================
# GUI & Visualization
# ==============================================================
# Usage:
#   make asic_view_floorplan                 → Floorplan + SRAM macro placement
#   make asic_view_placement                 → Standard cell placement
#   make asic_view_cts                       → After clock tree synthesis
#   make asic_view_routing                   → After routing (if available)
#   make asic_view_final                     → Final GDS
#   make asic_view_all                       → Open all stages at once
#   make asic_gui                            → OpenROAD GUI (ODB, interactive)
#   make asic_gds                            → Final GDS (KLayout)
#
# To pick a specific run: RUN=run_name
# Viewer: VIEWER=klayout (default) | openroad
# ==============================================================

VIEWER ?= klayout
ASIC_VIEW_RUN = $(if $(RUN),$(ASIC_RUNS_DIR)/$(RUN),$(LATEST_RUN))

# ── Internal: resolve DEF/ODB for a given stage ──
# $(1) = stage name for display
# $(2) = search path fragment (e.g., floorplan, placement, cts, routing)
# $(3) = optional filename pattern
define _asic_find_def
$(shell \
	RD="$(ASIC_VIEW_RUN)"; \
	if [ -n "$$RD" ]; then \
		f=$$(find "$$RD" -name '*.def' -path '*/$(2)/*' 2>/dev/null | sort | tail -1); \
		echo "$$f"; \
	fi \
)
endef

define _asic_find_odb
$(shell \
	RD="$(ASIC_VIEW_RUN)"; \
	if [ -n "$$RD" ]; then \
		f=$$(find "$$RD" -name '*.odb' -path '*/$(2)/*' 2>/dev/null | sort | tail -1); \
		echo "$$f"; \
	fi \
)
endef

# ── Internal: open a file with the chosen viewer ──
# $(1) = stage description
# $(2) = DEF file path (for KLayout)
# $(3) = ODB file path (for OpenROAD)
define _asic_view_file
	@DEF_FILE="$(2)"; \
	ODB_FILE="$(3)"; \
	if [ "$(VIEWER)" = "openroad" ]; then \
		if [ -z "$$ODB_FILE" ]; then \
			echo -e "$(RED)$(ERROR) $(1): ODB file not found$(RESET)"; \
			if [ -z "$(ASIC_VIEW_RUN)" ]; then \
				echo "  No run yet. First: make asic_run"; \
			else \
				echo "  Run: $(ASIC_VIEW_RUN)"; \
				echo "  This stage may not have completed yet."; \
			fi; \
			exit 1; \
		fi; \
		echo -e "$(CYAN)[VIEW $(1)]$(RESET) $$ODB_FILE"; \
		echo "  Viewer: OpenROAD GUI (Docker)"; \
		TCL=$$(mktemp /tmp/asic_view_XXXXXX.tcl); \
		echo "read_db $$ODB_FILE" > "$$TCL"; \
		docker run --rm -it \
			-e DISPLAY=$$DISPLAY \
			-v /tmp/.X11-unix:/tmp/.X11-unix \
			-v "$(ROOT_DIR):$(ROOT_DIR):ro" \
			-v "$(PDK_ROOT):$(PDK_ROOT):ro" \
			-v "$$TCL:$$TCL:ro" \
			$(OPENLANE_IMAGE) \
			openroad -gui "$$TCL"; \
		rm -f "$$TCL"; \
	else \
		if [ -z "$$DEF_FILE" ]; then \
			echo -e "$(RED)$(ERROR) $(1): DEF file not found$(RESET)"; \
			if [ -z "$(ASIC_VIEW_RUN)" ]; then \
				echo "  No run yet. First: make asic_run"; \
			else \
				echo "  Run: $(ASIC_VIEW_RUN)"; \
				echo "  This stage may not have completed yet."; \
			fi; \
			exit 1; \
		fi; \
		echo -e "$(CYAN)[VIEW $(1)]$(RESET) $$DEF_FILE"; \
		echo "  Viewer: KLayout (arka planda)"; \
		klayout "$$DEF_FILE" & \
	fi
endef

.PHONY: asic_view_floorplan asic_view_placement asic_view_cts
.PHONY: asic_view_routing asic_view_final asic_view_all
.PHONY: asic_gui asic_gds

## View floorplan + SRAM macro placement (after Step 5)
##   VIEWER=klayout (default) | VIEWER=openroad
asic_view_floorplan:
	$(call _asic_view_file,FLOORPLAN,$(call _asic_find_def,floorplan,floorplan),$(call _asic_find_odb,floorplan,floorplan))

## View standard cell placement (after Step 11)
asic_view_placement:
	$(call _asic_view_file,PLACEMENT,$(call _asic_find_def,placement,placement),$(call _asic_find_odb,placement,placement))

## View placement after CTS (after Step 13)
asic_view_cts:
	$(call _asic_view_file,CTS,$(call _asic_find_def,cts,cts),$(call _asic_find_odb,cts,cts))

## View after routing (after Step 20)
asic_view_routing:
	$(call _asic_view_file,ROUTING,$(call _asic_find_def,routing,routing),$(call _asic_find_odb,routing,routing))

## View final GDS (after Step 30)
asic_view_final:
	@GDS=""; \
	if [ -n "$(ASIC_VIEW_RUN)" ]; then \
		GDS=$$(find "$(ASIC_VIEW_RUN)" -name '*.gds' -path '*/final/*' 2>/dev/null | head -1); \
	fi; \
	if [ -n "$$GDS" ]; then \
		echo -e "$(CYAN)[VIEW FINAL GDS]$(RESET) $$GDS"; \
		echo "  Viewer: KLayout (arka planda)"; \
		klayout "$$GDS" & \
	else \
		echo -e "$(RED)$(ERROR) Final GDS not found$(RESET)"; \
		echo "  Flow may not have completed."; \
	fi

## Open all available stages at once
##   VIEWER=klayout (default) | VIEWER=openroad
asic_view_all:
	@echo -e "$(CYAN)[VIEW ALL]$(RESET) Opening all available stages..."
	@RD="$(ASIC_VIEW_RUN)"; \
	if [ -z "$$RD" ]; then \
		echo -e "$(RED)$(ERROR) No run yet$(RESET)"; \
		exit 1; \
	fi; \
	echo "  Run   : $$RD"; \
	echo "  Viewer: $(VIEWER)"; \
	opened=0; \
	for stage in floorplan placement cts routing; do \
		if [ "$(VIEWER)" = "openroad" ]; then \
			FILE=$$(find "$$RD" -name '*.odb' -path "*results/$$stage/*" 2>/dev/null | sort | tail -1); \
		else \
			FILE=$$(find "$$RD" -name '*.def' -path "*results/$$stage/*" 2>/dev/null | sort | tail -1); \
		fi; \
		if [ -n "$$FILE" ]; then \
			echo -e "  $(GREEN)✓$(RESET) $$stage → $$FILE"; \
			if [ "$(VIEWER)" = "openroad" ]; then \
				TCL=$$(mktemp /tmp/asic_view_XXXXXX.tcl); \
				echo "read_db $$FILE" > "$$TCL"; \
				docker run --rm -d \
					-e DISPLAY=$$DISPLAY \
					-v /tmp/.X11-unix:/tmp/.X11-unix \
					-v "$(ROOT_DIR):$(ROOT_DIR):ro" \
					-v "$(PDK_ROOT):$(PDK_ROOT):ro" \
					-v "$$TCL:$$TCL:ro" \
					$(OPENLANE_IMAGE) \
					openroad -gui "$$TCL" >/dev/null 2>&1; \
			else \
				klayout "$$FILE" & \
			fi; \
			opened=$$((opened + 1)); \
			sleep 1; \
		else \
			echo -e "  $(DIM)·$(RESET) $$stage → (yok)"; \
		fi; \
	done; \
	GDS=$$(find "$$RD" -name '*.gds' -path '*/final/*' 2>/dev/null | head -1); \
	if [ -n "$$GDS" ]; then \
		echo -e "  $(GREEN)✓$(RESET) final/gds → $$GDS"; \
		klayout "$$GDS" & \
		opened=$$((opened + 1)); \
	else \
		echo -e "  $(DIM)·$(RESET) final/gds → (yok)"; \
	fi; \
	echo ""; \
	echo -e "$(GREEN)$(SUCCESS) $$opened window(s) opened$(RESET)"

## Open latest run in OpenROAD GUI (ODB, interactive TCL console)
asic_gui:
	@RD="$(ASIC_VIEW_RUN)"; \
	if [ -z "$$RD" ]; then \
		echo -e "$(RED)$(ERROR) No runs found$(RESET)"; \
		exit 1; \
	fi; \
	ODB=$$(find "$$RD" -name '*.odb' -path '*/results/*' 2>/dev/null | sort | tail -1); \
	if [ -z "$$ODB" ]; then \
		ODB=$$(find "$$RD" -name '*.odb' 2>/dev/null | sort | tail -1); \
	fi; \
	if [ -n "$$ODB" ]; then \
		echo -e "$(CYAN)[GUI]$(RESET) Opening: $$ODB"; \
		TCL=$$(mktemp /tmp/asic_gui_XXXXXX.tcl); \
		echo "read_db $$ODB" > "$$TCL"; \
		docker run --rm -it \
			-e DISPLAY=$$DISPLAY \
			-v /tmp/.X11-unix:/tmp/.X11-unix \
			-v "$(ROOT_DIR):$(ROOT_DIR):ro" \
			-v "$(PDK_ROOT):$(PDK_ROOT):ro" \
			-v "$$TCL:$$TCL:ro" \
			$(OPENLANE_IMAGE) \
			openroad -gui "$$TCL"; \
		rm -f "$$TCL"; \
	else \
		echo -e "$(RED)No ODB file found$(RESET)"; \
	fi

## Open GDS file with KLayout
asic_gds:
	@if [ -n "$(ASIC_VIEW_RUN)" ] && [ -f "$(ASIC_VIEW_RUN)/results/final/gds/level_wrapper.gds" ]; then \
		echo -e "$(CYAN)[GDS]$(RESET) Opening GDS..."; \
		klayout "$(ASIC_VIEW_RUN)/results/final/gds/level_wrapper.gds" & \
	else \
		echo -e "$(RED)No final GDS found$(RESET)"; \
	fi

# ==============================================================
# Clean
# ==============================================================

.PHONY: asic_clean asic_clean_runs asic_clean_src

## Clean all ASIC outputs (runs + sources)
asic_clean:
	@echo -e "$(YELLOW)[OPENLANE CLEAN]$(RESET)"
	@bash $(OPENLANE_SH) clean
	@echo -e "$(GREEN)$(SUCCESS) Cleaned$(RESET)"

## Clean run outputs only (keep sources)
asic_clean_runs:
	@echo -e "$(YELLOW)[CLEAN RUNS]$(RESET)"
	@if [ -d "$(ASIC_RUNS_DIR)" ]; then \
		rm -rf $(ASIC_RUNS_DIR); \
		echo -e "$(GREEN)$(SUCCESS) Runs cleaned$(RESET)"; \
	else \
		echo "  Nothing to clean."; \
	fi

## Clean sv2v sources only
asic_clean_src:
	@echo -e "$(YELLOW)[CLEAN SRC]$(RESET)"
	@rm -rf $(ASIC_DESIGN_DIR)/src $(ASIC_DESIGN_DIR)/sources_manifest.txt
	@echo -e "$(GREEN)$(SUCCESS) Sources cleaned$(RESET)"

# ==============================================================
# Help
# ==============================================================

.PHONY: asic_help

asic_help:
	@echo ""
	@echo -e "$(BOLD)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(BOLD)║          Level RISC-V — OpenLane ASIC Flow                  ║$(RESET)"
	@echo -e "$(BOLD)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo ""
	@echo -e "$(CYAN)SRAM Macro:$(RESET)"
	@echo "  make asic_sram           Download SRAM macros (LEF/GDS/LIB/V)"
	@echo "  make sram                Shortcut (= asic_sram)"
	@echo "  make asic_sram_clean     Remove SRAM files"
	@echo "  make asic_sram_info      Show SRAM file status"
	@echo ""
	@echo -e "$(CYAN)Source prep:$(RESET)"
	@echo "  make asic_prep           RTL → sv2v conversion"
	@echo "  make asic_check          Verify all dependencies"
	@echo "  make asic_setup          Docker image + SRAM prep"
	@echo ""
	@echo -e "$(CYAN)Full flow:$(RESET)"
	@echo "  make asic_run            SRAM + prep + full OpenLane flow"
	@echo "  make asic_run_clean      Clean + full flow from scratch"
	@echo "  make asic                Shortcut (= asic_run)"
	@echo ""
	@echo -e "$(CYAN)Step by step / Interactive:$(RESET)"
	@echo "  make asic_interactive    OpenLane tclsh interactive mode"
	@echo "  make asic_shell          Container bash shell"
	@echo "  make asic_synth_only     Synthesis + floorplan only"
	@echo "  make asic_resume         Resume from last checkpoint"
	@echo "    RUN=run_name             Resume a specific run"
	@echo ""
	@echo -e "$(CYAN)Macro placement:$(RESET)"
	@echo "  make asic_dump_names     Extract SRAM instance names from ODB"
	@echo "    RUN=run_name             Read from a specific run"
	@echo ""
	@echo -e "$(CYAN)Reports:$(RESET)"
	@echo "  make asic_report         Last run report"
	@echo "  make asic_runs           List all runs"
	@echo "  make asic_metrics        Metrics (area, cell count)"
	@echo "  make asic_timing         Timing report"
	@echo ""
	@echo -e "$(CYAN)Visualization:$(RESET)"
	@echo "  make asic_view_floorplan  Floorplan + SRAM macro placement"
	@echo "  make asic_view_placement  Standard-cell placement"
	@echo "  make asic_view_cts        After CTS"
	@echo "  make asic_view_routing    After routing"
	@echo "  make asic_view_final      Final GDS"
	@echo "  make asic_view_all        Open all stages at once"
	@echo "  make asic_gui             OpenROAD GUI (ODB, interactive)"
	@echo "  make asic_gds             Open final GDS in KLayout"
	@echo "    RUN=run_name              Open from a specific run"
	@echo "    VIEWER=openroad           Use OpenROAD GUI (default: klayout)"
	@echo ""
	@echo -e "$(CYAN)Cleanup:$(RESET)"
	@echo "  make asic_clean          Clean all ASIC outputs"
	@echo "  make asic_clean_runs     Clean runs only"
	@echo "  make asic_clean_src      Clean sv2v sources only"
	@echo ""
	@echo -e "$(CYAN)Environment variables:$(RESET)"
	@echo "  ASIC_TAG=name            Run label (default: timestamp)"
	@echo "  OPENLANE_IMAGE=img       Docker image"
	@echo "  PDK_ROOT=path            PDK root directory"
	@echo "  PDK=variant              PDK variant (sky130A)"
	@echo "  DOCKER_CPUS=N            Docker CPU limit"
	@echo "  SRAM_MACRO_NAME=name     SRAM macro name"
	@echo "  SRAM_MACRO_REPO=url      SRAM macro repo URL"
	@echo ""
	@echo -e "$(BOLD)Macro placement flow (Step 5):$(RESET)"
	@echo "  ┌─────────────────────────────────────────────────────────┐"
	@echo "  │ 1. make asic_sram          → Download SRAM files        │"
	@echo "  │ 2. make asic_synth_only    → Synthesis + floorplan     │"
	@echo "  │ 3. make asic_dump_names    → Actual instance names      │"
	@echo "  │ 4. Edit macro_placement.cfg (names + coordinates)      │"
	@echo "  │ 5. Enable MACRO_PLACEMENT_CFG line in config.tcl       │"
	@echo "  │ 6. make asic_run           → Start full flow           │"
	@echo "  └─────────────────────────────────────────────────────────┘"
	@echo ""

# ====== tools/clean.mk ======
# =========================================
# Level RISC-V — Clean Rules
# =========================================

.PHONY: clean clean_all clean_nuclear

# ============================================================
# Standard Clean (simulation/build artifacts + results)
# Preserves $(BUILD_DIR)/tests (compiled ISA, arch-test, Imperas, benchmarks, …).
# For a full wipe including those: make clean_nuclear
# ============================================================
ifeq ($(OS),Windows_NT)
clean:
	@echo -e "$(RED)[CLEANING BUILD & RESULTS]$(RESET)"
	@$(RM) "$(BUILD_DIR)"
	@$(RM) "$(RESULTS_DIR)"
	@$(RM) transcript *.wlf *.vcd *.vstf wlft*
	@echo -e "$(GREEN)Clean complete.$(RESET)"
else
clean:
	@echo -e "$(RED)[CLEANING BUILD & RESULTS]$(RESET) $(CYAN)(keeps $(BUILD_DIR)/tests)$(RESET)"
	@if [ -d "$(BUILD_DIR)" ]; then \
		find "$(BUILD_DIR)" -mindepth 1 -maxdepth 1 ! -name tests -exec rm -rf {} + 2>/dev/null || true; \
	fi
	@$(RM) "$(RESULTS_DIR)"
	@$(RM) transcript *.wlf *.vcd *.vstf wlft*
	@echo -e "$(GREEN)Clean complete.$(RESET)"
endif

# ============================================================
# Nuclear clean — entire build/ including compiled test programs
# ============================================================
clean_nuclear:
	@echo -e "$(RED)[NUCLEAR CLEAN]$(RESET) $(BUILD_DIR) + $(RESULTS_DIR)"
	@$(RM) "$(BUILD_DIR)"
	@$(RM) "$(RESULTS_DIR)"
	@$(RM) transcript *.wlf *.vcd *.vstf wlft*
	@echo -e "$(GREEN)Nuclear clean complete.$(RESET)"

# ============================================================
# Full Clean (includes subrepos)
# ============================================================
clean_all: clean
	@echo -e "$(RED)[CLEANING SUBREPOS]$(RESET)"
	@$(RM) "$(ISA_ROOT)"
	@$(RM) "$(ARCH_ROOT)"
	@echo -e "$(GREEN)Full clean complete.$(RESET)"

# ====== tools/konata.mk ======
# ============================================================
# Konata Log Viewer Makefile
# Usage:
#   make konata SIM=verilator TEST_NAME=rv32ui-p-add
# ============================================================

# Path where logs live
LOG_ROOT   := $(RESULTS_DIR)/logs

# Parameters
SIM        ?= verilator
TEST_NAME  ?= rv32ui-p-add

# Generated log file
KONATA_LOG := $(LOG_ROOT)/$(SIM)/$(TEST_NAME)/level.log

# Konata binary (if symlink exists, /usr/local/bin/konata is used)
KONATA_BIN ?= konata   # runs konata directly
# or an explicit path:
# KONATA_BIN ?= $(HOME)/tools/konata/konata.sh

.PHONY: konata show-log check-log

# --------------------------------------------------------------------------
# Open log with Konata
# --------------------------------------------------------------------------
konata: check-log
	@echo ""
	@echo "🔍 Opening Konata for:"
	@echo "   SIM       = $(SIM)"
	@echo "   TEST_NAME = $(TEST_NAME)"
	@echo "   LOG FILE  = $(KONATA_LOG)"
	@echo ""
	$(KONATA_BIN) $(KONATA_LOG)

# --------------------------------------------------------------------------
# Check whether the log file exists
# --------------------------------------------------------------------------
check-log:
	@if [ ! -f "$(KONATA_LOG)" ]; then \
		echo "$(ERROR) Log not found:"; \
		echo "   $(KONATA_LOG)"; \
		echo ""; \
		echo "ℹ️  Run a test first:"; \
		echo "   make sim SIM=$(SIM) TEST_NAME=$(TEST_NAME)"; \
		exit 1; \
	fi

# --------------------------------------------------------------------------
# Print log file to terminal (for debugging)
# --------------------------------------------------------------------------
show-log: check-log
	@echo "-----------------------------------------"
	@echo "Log File: $(KONATA_LOG)"
	@echo "-----------------------------------------"
	@cat $(KONATA_LOG)

# ====== tools/surfer.mk ======
# =========================================
# Level RISC-V — Surfer Waveform Viewer
# Modern waveform viewer (Rust-based)
# =========================================
# Usage:
#   make surfer                - Open waveform with Surfer
#   make surfer_install        - Install Surfer
# =========================================
# Surfer: https://surfer-project.org/
# - Fast rendering (GPU accelerated)
# - Supports VCD, FST, GHW formats
# - Modern UI with signal search
# =========================================

# -----------------------------------------
# Configuration
# -----------------------------------------
SURFER         ?= surfer

# Default waveform files
SURFER_VCD     ?= $(BUILD_DIR)/verilator/waveform.vcd
SURFER_FST     ?= $(BUILD_DIR)/verilator/waveform.fst

# -----------------------------------------
# Targets
# -----------------------------------------
.PHONY: surfer surfer_install surfer_help

# Check if Surfer is installed
check_surfer:
	@command -v $(SURFER) >/dev/null 2>&1 || { \
		echo -e "$(RED)$(ERROR) Surfer not found$(RESET)"; \
		echo -e "$(YELLOW)Install with:$(RESET)"; \
		echo -e "  cargo install --git https://gitlab.com/surfer-project/surfer surfer"; \
		echo -e "  # Or download from: https://surfer-project.org/"; \
		exit 1; \
	}

# Open waveform with Surfer
surfer: check_surfer
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Surfer Waveform Viewer$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@if [ -f "$(SURFER_FST)" ]; then \
		echo -e "$(CYAN)[INFO]$(RESET) Opening FST: $(SURFER_FST)"; \
		$(SURFER) $(SURFER_FST) &; \
	elif [ -f "$(SURFER_VCD)" ]; then \
		echo -e "$(CYAN)[INFO]$(RESET) Opening VCD: $(SURFER_VCD)"; \
		$(SURFER) $(SURFER_VCD) &; \
	else \
		echo -e "$(RED)$(ERROR) No waveform file found$(RESET)"; \
		echo -e "$(YELLOW)Run simulation first with TRACE=1:$(RESET)"; \
		echo -e "  make run_verilator TEST_NAME=rv32ui-p-add TRACE=1"; \
		exit 1; \
	fi

# Open specific waveform file
surfer_file: check_surfer
ifndef WAVE_FILE
	@echo -e "$(RED)$(ERROR) WAVE_FILE not specified$(RESET)"
	@echo -e "$(YELLOW)Usage: make surfer_file WAVE_FILE=path/to/file.vcd$(RESET)"
	@exit 1
endif
	@echo -e "$(CYAN)[INFO]$(RESET) Opening: $(WAVE_FILE)"
	@$(SURFER) $(WAVE_FILE) &

# Install Surfer
surfer_install:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Installing Surfer$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@if command -v cargo >/dev/null 2>&1; then \
		echo -e "$(CYAN)[INFO]$(RESET) Installing via cargo..."; \
		cargo install --git https://gitlab.com/surfer-project/surfer surfer; \
	else \
		echo -e "$(RED)$(ERROR) Cargo not found$(RESET)"; \
		echo -e "$(YELLOW)Install Rust first: https://rustup.rs/$(RESET)"; \
		echo -e ""; \
		echo -e "$(YELLOW)Alternative: Download AppImage from:$(RESET)"; \
		echo -e "  https://surfer-project.org/"; \
		exit 1; \
	fi
	@echo -e ""
	@echo -e "$(GREEN)$(SUCCESS) Surfer installed$(RESET)"
	@surfer --version 2>/dev/null || true

# Compare with GTKWave
wave_compare:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Waveform Viewers Comparison$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)GTKWave$(RESET) (Traditional)"
	@echo -e "  $(SUCCESS) Mature, well-documented"
	@echo -e "  $(SUCCESS) TCL scripting support"
	@echo -e "  ✗ Older UI, slower with large files"
	@echo -e "  Command: make gtkwave"
	@echo -e ""
	@echo -e "$(CYAN)Surfer$(RESET) (Modern)"
	@echo -e "  $(SUCCESS) GPU accelerated, very fast"
	@echo -e "  $(SUCCESS) Modern UI, signal search"
	@echo -e "  $(SUCCESS) VCD/FST/GHW support"
	@echo -e "  ✗ Newer, less documentation"
	@echo -e "  Command: make surfer"
	@echo -e ""

# Help
surfer_help:
	@echo -e ""
	@echo -e "$(GREEN)Surfer Waveform Viewer$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Commands:$(RESET)"
	@echo -e "  make surfer              - Open default waveform"
	@echo -e "  make surfer_file WAVE_FILE=path  - Open specific file"
	@echo -e "  make surfer_install      - Install Surfer"
	@echo -e "  make wave_compare        - Compare GTKWave vs Surfer"
	@echo -e ""
	@echo -e "$(CYAN)Supported Formats:$(RESET)"
	@echo -e "  VCD  - Value Change Dump (standard)"
	@echo -e "  FST  - Fast Signal Trace (compressed)"
	@echo -e "  GHW  - GHDL Waveform"
	@echo -e ""
	@echo -e "$(CYAN)Website:$(RESET)"
	@echo -e "  https://surfer-project.org/"
	@echo -e ""

# ====== tools/help.mk ======
# =========================================
# Level RISC-V — Centralized Help System
# =========================================
# Manage all help targets from one place

.PHONY: help help_all help_tests help_sim help_build help_utils

# Main help (default)
help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)                    Level RISC-V Makefile Help$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Quick Reference:$(RESET)"
	@echo -e "  help            Show this help message"
	@echo -e "  help_sim        Show simulation targets"
	@echo -e "  help_tests      Show test commands and suites"
	@echo -e "  help_build      Show build and synthesis targets"
	@echo -e "  help_utils      Show utility commands"
	@echo -e "  help_all        Show complete help (all sections)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Most Common Commands:$(RESET)"
	@echo -e "  make verilate         Build Verilator model"
	@echo -e "  make run T=<test>     Run single test"
	@echo -e "  make isa              Run all ISA tests"
	@echo -e "  make cm               Run CoreMark benchmark"
	@echo -e "  make clean            Clean build (keeps build/tests)"
	@echo -e "  make clean_nuclear    Full build wipe including tests"
	@echo -e ""
	@echo -e "$(YELLOW)For detailed help on specific topics, use:$(RESET)"
	@echo -e "  make help_sim     → Simulation and waveform commands"
	@echo -e "  make help_tests   → Test suites and configurations"
	@echo -e "  make help_build   → Build modes and synthesis"
	@echo -e "  make help_utils   → Linting, cleaning, and tools"
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""

# Detailed simulation help
help_sim:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)                    Simulation Targets$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Verilator (Primary Simulator):$(RESET)"
	@echo -e "  verilate        Build Verilator C++ model"
	@echo -e "  verilate-fast   Same as verilate VERILATE_FAST=1 (incremental dev shortcut)"
	@echo -e "  run_verilator   Run Verilator simulation"
	@echo -e "  rebuild-cpp     Rebuild C++ testbench only"
	@echo -e ""
	@echo -e "$(CYAN)▶ ModelSim:$(RESET)"
	@echo -e "  compile         Compile RTL with ModelSim"
	@echo -e "  simulate        Run simulation (GUI=1 for Questa GUI)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Waveform Viewers:$(RESET)"
	@echo -e "  gtkwave         Open waveform with GTKWave"
	@echo -e "  surfer          Open waveform with Surfer"
	@echo -e "  konata          Open Konata pipeline visualizer"
	@echo -e ""
	@echo -e "$(CYAN)▶ Trace & Debug Options:$(RESET)"
	@echo -e "  LOG_COMMIT=1        Spike-compatible commit trace"
	@echo -e "  LOG_PIPELINE=1      Konata pipeline trace file"
	@echo -e "  LOG_RAM=1           RAM initialization messages"
	@echo -e "  LOG_UART=1          UART TX file logging"
	@echo -e "  LOG_GPTIMER_ARR=1   GPTimer TIMx_ARR RD/WR (\$$display)"
	@echo -e "  LOG_BP=1            Branch predictor statistics"
	@echo -e "  LOG_BP_VERBOSE=1    Per-branch verbose logging"
	@echo -e "  KONATA_TRACER=1     Enable Konata visualizer"
	@echo -e "  TRACE=1             Enable waveform tracing"
	@echo -e "  SIM_FAST=1          Fast mode (disable all logs)"
	@echo -e "  SIM_UART_MONITOR=1  UART monitoring + auto-stop"
	@echo -e "  SIM_COVERAGE=1      Enable coverage collection"
	@echo -e ""
	@echo -e "$(CYAN)▶ Examples:$(RESET)"
	@echo -e "  make verilate LOG_COMMIT=1 TRACE=1"
	@echo -e "  make run_verilator LOG_BP=1 SIM_FAST=1"
	@echo -e "  make simulate GUI=1"
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""

# Detailed test help
help_tests:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)                    Test Commands$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Basic Test Commands:$(RESET)"
	@echo -e "  run T=<name>    Run single test with RTL+Spike comparison"
	@echo -e "  quick_test      Run RTL only (skip Spike)"
	@echo -e "  run_batch       Run multiple tests from list"
	@echo -e "  list_tests      List available tests"
	@echo -e ""
	@echo -e "$(CYAN)▶ Test Suites (Standard):$(RESET)"
	@echo -e "  isa             All ISA tests (riscv-tests)"
	@echo -e "  arch            Architecture tests (riscv-arch-test)"
	@echo -e "  imperas         Imperas tests"
	@echo -e "  bench           Benchmarks"
	@echo -e "  csr             CSR tests"
	@echo -e "  all_tests       Run ALL tests"
	@echo -e ""
	@echo -e "$(CYAN)▶ Quick Test Shortcuts:$(RESET)"
	@echo -e "  t T=<name>      Quick ISA test    (e.g., make t T=rv32ui-p-add)"
	@echo -e "  tb T=<name>     Quick benchmark   (e.g., make tb T=dhrystone)"
	@echo -e "  ti T=<name>     Quick Imperas test"
	@echo -e ""
	@echo -e "$(CYAN)▶ Benchmarks:$(RESET)"
	@echo -e "  run_coremark    Build + run CoreMark on Verilator"
	@echo -e "  coremark_help   Show CoreMark detailed help"
	@echo -e "  dhrystone       Build Dhrystone"
	@echo -e "  dhrystone_run   Run Dhrystone"
	@echo -e "  dhrystone_help  Show Dhrystone detailed help"
	@echo -e "  embench         Build Embench-IoT"
	@echo -e "  embench_run     Run Embench benchmarks"
	@echo -e "  beebs_clone     Init subrepo/beebs (GPL-3.0)"
	@echo -e "  beebs_build     Native BEEBS compile under subrepo/beebs"
	@echo -e "  beebs_help      BEEBS + Level-V (RV32 needs port)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Extended Test Suites:$(RESET)"
	@echo -e "  torture         Generate & build torture tests"
	@echo -e "  torture_run     Run torture tests"
	@echo -e "  torture_help    Show torture detailed help"
	@echo -e "  riscv_dv        Build RISCV-DV tests"
	@echo -e "  riscv_dv_run    Run RISCV-DV tests"
	@echo -e "  riscv_dv_help   Show RISCV-DV detailed help"
	@echo -e "  formal          Run formal verification"
	@echo -e ""
	@echo -e "$(CYAN)▶ Test Suite Management:$(RESET)"
	@echo -e "  isa_help        ISA test import help"
	@echo -e "  arch_help       Architecture test help"
	@echo -e "  imperas_help    Imperas test help"
	@echo -e ""
	@echo -e "$(CYAN)▶ Examples:$(RESET)"
	@echo -e "  make run T=rv32ui-p-add LOG_COMMIT=1"
	@echo -e "  make isa LOG_BP=1"
	@echo -e "  make run_coremark SIM_FAST=1 SIM_UART_MONITOR=1"
	@echo -e "  make run_batch TEST_LIST=my_tests.list"
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""

# Build and synthesis help
help_build:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)                    Build & Synthesis$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Build Modes (Verilator C++/opt — see Compiler Flags):$(RESET)"
	@echo -e "  MODE=debug      -O0, --debug-check (default)"
	@echo -e "  MODE=profile    -O2, profiling flags"
	@echo -e "  MODE=release    -O3 (or any other value)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Synthesis:$(RESET)"
	@echo -e "  yosys           Run Yosys synthesis"
	@echo -e "  yosys_check     Run Yosys structural checks"
	@echo -e "  yosys_clean     Clean Yosys build artifacts"
	@echo -e "  asic_subrepos   Clone/update ASIC GitHub repos under subrepo/"
	@echo -e "  asic_setup      Pull OpenLane image and check PDK path"
	@echo -e "  asic_prep       Prepare OpenLane source set"
	@echo -e "  asic_run        Run OpenLane full RTL→GDS flow"
	@echo -e "  asic_report     Show latest OpenLane run artifacts"
	@echo -e "  asic_clean      Clean OpenLane runs and prepared sources"
	@echo -e ""
	@echo -e "$(CYAN)▶ Configuration:$(RESET)"
	@echo -e "  TEST_CONFIG=X   Test profile (script/config/tests/X.conf)"
	@echo -e "  list-configs    List available test configurations"
	@echo -e "  show-config     Show current config values"
	@echo -e "  MAX_CYCLES=N    Set max simulation cycles"
	@echo -e ""
	@echo -e "$(CYAN)▶ Examples:$(RESET)"
	@echo -e "  make verilate MODE=release"
	@echo -e "  make run T=rv32ui-p-add MAX_CYCLES=10000"
	@echo -e "  make yosys"
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""

# Utilities help
help_utils:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)                    Utility Commands$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Linting & Verification:$(RESET)"
	@echo -e "  lint            Verilator lint (--lint-only -Wall; log under results/lint/verilator/)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Cleaning:$(RESET)"
	@echo -e "  clean           Clean build (keeps build/tests compiled ELFs/mem)"
	@echo -e "  clean_nuclear   Remove entire build/ including build/tests"
	@echo -e "  clean_verilator Clean Verilator build"
	@echo -e "  clean_modelsim  Clean ModelSim build"
	@echo -e "  clean_tests     Clean test artifacts"
	@echo -e "  clean_logs      Clean simulation logs"
	@echo -e ""
	@echo -e "$(CYAN)▶ Waveform & Visualization:$(RESET)"
	@echo -e "  gtkwave         Open waveform with GTKWave"
	@echo -e "  surfer          Open waveform with Surfer"
	@echo -e "  konata          Open Konata pipeline visualizer"
	@echo -e ""
	@echo -e "$(CYAN)▶ Statistics & Reports:$(RESET)"
	@echo -e "  stats           Show Verilator statistics"
	@echo -e "  verilator_help  Verilator-specific help"
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""

# Show all help sections
help_all: help help_sim help_tests help_build help_utils
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)End of complete help. For specific suite help, use:$(RESET)"
	@echo -e "  make isa_help, arch_help, imperas_help, dhrystone_help,"
	@echo -e "  make torture_help, riscv_dv_help, coremark_help"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""

# ====== lint/lint.mk ======
# =========================================
# Level RISC-V — Linting Tools
# svlint, Slang, Verilator lint
# =========================================
# Usage:
#   make svlint                - Run svlint on RTL
#   make slang_lint            - Run Slang linter
#   make lint_all              - Run all linters
#   make lint_install          - Install lint tools
# =========================================

# -----------------------------------------
# Tool Paths
# -----------------------------------------
SVLINT         ?= svlint

# -----------------------------------------
# Lint Output Directories (LINT_DIR from paths.mk)
# Each tool gets its own subdirectory:
#   results/lint/svlint/    - svlint style checker
#   results/lint/slang/     - Slang compiler lint
#   results/lint/verilator/ - Verilator static analysis
# -----------------------------------------
SVLINT_OUT_DIR   := $(LINT_DIR)/svlint
SLANG_OUT_DIR    := $(LINT_DIR)/slang

# -----------------------------------------
# Source Files for Linting
# -----------------------------------------
LINT_SOURCES   := $(SV_SOURCES)
LINT_INCLUDES  := $(addprefix -I, $(INC_DIRS))

# -----------------------------------------
# svlint Configuration
# -----------------------------------------
SVLINT_CONFIG  := $(ROOT_DIR)/.svlint.toml

# Create default config if not exists
$(SVLINT_CONFIG):
	@echo -e "$(CYAN)[svlint]$(RESET) Creating default configuration..."
	@echo '[option]' > $@
	@echo 'exclude_paths = ["subrepo/", "build/"]' >> $@
	@echo '' >> $@
	@echo '[rules]' >> $@
	@echo '# Naming conventions' >> $@
	@echo 'prefix_module = false' >> $@
	@echo 'prefix_interface = false' >> $@
	@echo '' >> $@
	@echo '# Style rules' >> $@
	@echo 'style_keyword_0or1space = true' >> $@
	@echo 'style_keyword_1space = true' >> $@
	@echo '' >> $@
	@echo '# Relaxed rules for generated code' >> $@
	@echo 'generate_keyword_forbidden = false' >> $@

# -----------------------------------------
# Targets
# -----------------------------------------
.PHONY: svlint slang_lint lint_all lint_install lint_clean lint_help

# Check if svlint is installed
check_svlint:
	@command -v $(SVLINT) >/dev/null 2>&1 || { \
		echo -e "$(RED)$(ERROR) svlint not found$(RESET)"; \
		echo -e "$(YELLOW)Install with:$(RESET)"; \
		echo -e "  cargo install svlint"; \
		echo -e "  # or download from: https://github.com/dalance/svlint/releases"; \
		exit 1; \
	}

# Check if Slang/pyslang is installed
check_slang:
	@python3 -c "import pyslang" 2>/dev/null || { \
		echo -e "$(RED)$(ERROR) pyslang not found$(RESET)"; \
		echo -e "$(YELLOW)Install with:$(RESET)"; \
		echo -e "  pip install pyslang"; \
		exit 1; \
	}

# Run svlint
svlint: check_svlint $(SVLINT_CONFIG)
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  svlint - SystemVerilog Style Linter$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MKDIR) $(SVLINT_OUT_DIR)
	@echo -e "$(CYAN)[INFO]$(RESET) Config: $(SVLINT_CONFIG)"
	@echo -e "$(CYAN)[INFO]$(RESET) Output: $(SVLINT_OUT_DIR)/"
	@echo -e "$(CYAN)[INFO]$(RESET) Files: $(words $(LINT_SOURCES)) source files"
	@echo -e ""
	@$(SVLINT) --config $(SVLINT_CONFIG) $(LINT_INCLUDES) $(LINT_SOURCES) 2>&1 | tee $(SVLINT_OUT_DIR)/svlint.log; \
	EXIT_CODE=$${PIPESTATUS[0]}; \
	if [ $$EXIT_CODE -eq 0 ]; then \
		echo -e ""; \
		echo -e "$(GREEN)$(SUCCESS) svlint passed - no issues found$(RESET)"; \
	else \
		echo -e ""; \
		echo -e "$(YELLOW)⚠ svlint found issues$(RESET)"; \
		echo -e "$(CYAN)[LOG]$(RESET) $(SVLINT_OUT_DIR)/svlint.log"; \
	fi

# Run Slang linter (via pyslang)
slang_lint: check_slang
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Slang - SystemVerilog Compiler & Linter$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MKDIR) $(SLANG_OUT_DIR)
	@echo -e "$(CYAN)[INFO]$(RESET) Output: $(SLANG_OUT_DIR)/"
	@echo -e "$(CYAN)[INFO]$(RESET) Files: $(words $(LINT_SOURCES)) source files"
	@echo -e "$(CYAN)[INFO]$(RESET) Using pyslang v$$(python3 -c \"import importlib.metadata as m; print(m.version('pyslang'))\")"
	@echo -e ""
	@python3 $(ROOT_DIR)/script/python/slang_lint.py \
		$(addprefix -I , $(INC_DIRS)) \
		$(LINT_SOURCES) 2>&1 | tee $(SLANG_OUT_DIR)/slang.log; \
	EXIT_CODE=$${PIPESTATUS[0]}; \
	if [ $$EXIT_CODE -eq 0 ]; then \
		echo -e ""; \
		echo -e "$(GREEN)$(SUCCESS) Slang lint passed$(RESET)"; \
	else \
		echo -e ""; \
		echo -e "$(YELLOW)⚠ Slang found issues$(RESET)"; \
		echo -e "$(CYAN)[LOG]$(RESET) $(SLANG_OUT_DIR)/slang.log"; \
	fi

# Run Slang with more detailed output (via pyslang)
slang_check: check_slang
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Slang - Full Compilation Check$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MKDIR) $(SLANG_OUT_DIR)
	@echo -e "$(CYAN)[INFO]$(RESET) Output: $(SLANG_OUT_DIR)/"
	@echo -e "$(CYAN)[INFO]$(RESET) Using pyslang for full check"
	@python3 $(ROOT_DIR)/script/python/slang_lint.py \
		--top level_wrapper \
		-v \
		$(addprefix -I , $(INC_DIRS)) \
		$(LINT_SOURCES) 2>&1 | tee $(SLANG_OUT_DIR)/slang_full.log
	@echo -e "$(CYAN)[LOG]$(RESET) $(SLANG_OUT_DIR)/slang_full.log"

# Run all linters
lint_all: 
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running All Linters$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Output directory: $(LINT_DIR)/"
	@echo -e ""
	@$(MAKE) --no-print-directory svlint || true
	@echo -e ""
	@$(MAKE) --no-print-directory slang_lint || true
	@echo -e ""
	@$(MAKE) --no-print-directory lint || true
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Lint Summary$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)Output Structure:$(RESET)"
	@echo -e "  $(LINT_DIR)/"
	@echo -e "  ├── svlint/      - Style & naming checks"
	@echo -e "  ├── slang/       - Semantic analysis"
	@echo -e "  └── verilator/   - Static analysis & loops"
	@echo -e ""
	@find $(LINT_DIR) -name "*.log" -type f 2>/dev/null | while read f; do echo "  $$f"; done || true

# Install lint tools (Linux)
lint_install:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Installing Lint Tools$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)[1/2]$(RESET) Installing svlint..."
	@cd /tmp && \
	rm -rf svlint-install && mkdir -p svlint-install && cd svlint-install && \
	curl -sLO https://github.com/dalance/svlint/releases/download/v0.9.5/svlint-v0.9.5-x86_64-lnx.zip && \
	unzip -o svlint-v0.9.5-x86_64-lnx.zip && \
	sudo cp bin/svlint /usr/local/bin/ && \
	cd /tmp && rm -rf svlint-install
	@echo -e ""
	@echo -e "$(CYAN)[2/2]$(RESET) Installing pyslang (Slang Python bindings)..."
	@pip install --quiet pyslang
	@echo -e ""
	@echo -e "$(GREEN)$(SUCCESS) Installation complete$(RESET)"
	@echo -e ""
	@echo -e "Versions installed:"
	@svlint --version 2>/dev/null || echo "  svlint: not found"
	@python3 -c "import importlib.metadata as m; print('  pyslang:', m.version('pyslang'))" 2>/dev/null || echo "  pyslang: not found"

# Clean lint outputs
lint_clean:
	@echo -e "$(CYAN)[CLEAN]$(RESET) Removing lint outputs..."
	@rm -rf $(LINT_DIR)
	@echo -e "$(GREEN)$(SUCCESS) Clean complete$(RESET)"

# Help
lint_help:
	@echo -e ""
	@echo -e "$(GREEN)Linting Tools$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Available Linters:$(RESET)"
	@echo -e "  make svlint              - Run svlint (style & naming)"
	@echo -e "  make slang_lint          - Run Slang (parsing & semantics)"
	@echo -e "  make slang_check         - Run Slang full check"
	@echo -e "  make lint                - Run Verilator lint (static analysis)"
	@echo -e "  make lint_all            - Run all linters"
	@echo -e ""
	@echo -e "$(CYAN)Setup:$(RESET)"
	@echo -e "  make lint_install        - Install svlint & Slang"
	@echo -e "  make lint_clean          - Clean lint outputs"
	@echo -e ""
	@echo -e "$(CYAN)Tool Descriptions:$(RESET)"
	@echo -e "  $(GREEN)svlint$(RESET)     - Fast SV linter, style/naming rules"
	@echo -e "               https://github.com/dalance/svlint"
	@echo -e ""
	@echo -e "  $(GREEN)Slang$(RESET)      - Full SV compiler, best parsing"
	@echo -e "               https://github.com/MikePopoloski/slang"
	@echo -e ""
	@echo -e "  $(GREEN)Verilator$(RESET)  - Static analysis, loop detection"
	@echo -e "               https://verilator.org"
	@echo -e ""
	@echo -e "$(CYAN)Output Structure:$(RESET)"
	@echo -e "  results/lint/"
	@echo -e "  ├── svlint/      - svlint logs"
	@echo -e "  ├── slang/       - Slang logs"
	@echo -e "  └── verilator/   - Verilator logs & diagrams"
	@echo -e ""


# ==================================================
# Top-level targets (legacy root makefile)
# ==================================================
.PHONY: all compile simulate lint verilate run_verilator yosys_check clean

# Default top-level: same as historical simulate_gui (Questa GUI)
all:
	@$(MAKE) --no-print-directory simulate GUI=1
