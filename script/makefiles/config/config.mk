# =========================================
# CERES RISC-V Project Configuration
# =========================================
# Bu dosya tüm alt makefile'lar tarafından include edilir.
# Modüler yapı için ayrı dosyalara bölünmüştür.
# =========================================

# -----------------------------------------
# Default Parameters (must be set BEFORE profiles.mk)
# -----------------------------------------
MODE          ?= debug
TEST_NAME     ?= rv32ui-p-add
SIM_TIME      := 20000ns

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
VERBOSE       ?= 0
NO_ADDR       ?= 0
FAST_SIM      ?= 0

# MAX_CYCLES defaults based on TEST_TYPE
# - isa:     10000  (fast ISA tests)
# - arch:   100000  (longer arch compliance tests)
# - imperas: 200000 (comprehensive Imperas tests)
# - bench: 1000000  (benchmarks need more cycles)
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
# Core Configuration Modules
# -----------------------------------------
include $(dir $(lastword $(MAKEFILE_LIST)))paths.mk
include $(dir $(lastword $(MAKEFILE_LIST)))toolchain.mk
include $(dir $(lastword $(MAKEFILE_LIST)))sources.mk
include $(dir $(lastword $(MAKEFILE_LIST)))colors.mk
include $(dir $(lastword $(MAKEFILE_LIST)))profiles.mk

# -----------------------------------------
# Test Configuration (JSON-based)
# -----------------------------------------
# Merkezi test konfigürasyonu - TEST_TYPE'a göre otomatik yüklenir
include $(dir $(lastword $(MAKEFILE_LIST)))test_config.mk

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
# Test Runner Paths
# -----------------------------------------
TEST_LIST         ?= riscv_test_list.flist
FLIST             ?= $(SIM_DIR)/test/$(TEST_LIST)
PASS_LIST_FILE    := $(LOG_DIR)/tests_passed.list
FAIL_LIST_FILE    := $(LOG_DIR)/tests_failed.list

# Unified log directory per simulator and test
TEST_LOG_DIR      := $(LOG_DIR)/$(SIM)/$(TEST_NAME)
RTL_LOG_DIR       := $(TEST_LOG_DIR)

# Test output files
RTL_LOG           := $(TEST_LOG_DIR)/rtl_sim.log
SPIKE_LOG         := $(TEST_LOG_DIR)/spike.log
DIFF_LOG          := $(TEST_LOG_DIR)/diff.log
REPORT_FILE       := $(TEST_LOG_DIR)/test_report.txt
PASS_FAIL_FILE    := $(TEST_LOG_DIR)/pass_fail.txt

# -----------------------------------------
# External Repository URLs
# -----------------------------------------
ISA_REPO_URL      := https://github.com/riscv-software-src/riscv-tests.git
ARCH_REPO_URL     := https://github.com/riscv-non-isa/riscv-arch-test.git
COREMARK_REPO_URL := https://github.com/eembc/coremark.git
KONATA_REPO_URL   := https://github.com/shioyadan/Konata.git

# -----------------------------------------
# ISA Test Pipeline
# -----------------------------------------
ISA_SRC_DIR       := $(ISA_ROOT)/isa
ISA_OUT_DIR       := $(BUILD_DIR)/tests
PIPELINE_PY       := $(SCRIPT_DIR)/python/makefile/isa_pipeline.py

# -----------------------------------------
# RISC-V Arch Test (RISCOF)
# -----------------------------------------
ARCH_DEVICE       ?= I
ARCH_TARGET       ?= ceres
RISCOF            ?= $(HOME)/.venv/riscof/bin/riscof
RISCOF_CONFIG     := $(ARCH_ROOT)/config/config.ini

# -----------------------------------------
# CoreMark
# -----------------------------------------
COREMARK_SUBDIR   := $(SUBREPO_DIR)/coremark

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
