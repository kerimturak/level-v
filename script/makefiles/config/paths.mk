# =========================================
# CERES RISC-V — Directory Paths
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

# -----------------------------------------
# Clean Targets
# -----------------------------------------
CLEAN_DIRS    := $(OBJ_DIR) $(WORK_DIR) $(LOG_DIR) $(REPORT_DIR)
