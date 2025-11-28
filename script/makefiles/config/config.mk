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
TEST_TYPE     ?= isa
MAX_CYCLES    ?= 10000
SIM_TIME      := 20000000ns
SIM           ?= verilator
GUI           ?= 0
TRACE         ?= 0
VERBOSE       ?= 0
NO_ADDR       ?= 0
FAST_SIM      ?= 0

# -----------------------------------------
# Core Configuration Modules
# -----------------------------------------
include $(dir $(lastword $(MAKEFILE_LIST)))paths.mk
include $(dir $(lastword $(MAKEFILE_LIST)))toolchain.mk
include $(dir $(lastword $(MAKEFILE_LIST)))sources.mk
include $(dir $(lastword $(MAKEFILE_LIST)))colors.mk
include $(dir $(lastword $(MAKEFILE_LIST)))profiles.mk

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
