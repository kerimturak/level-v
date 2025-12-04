# =========================================
# CERES RISC-V — Icarus Verilog Simulation
# Alternative simulator for compatibility
# =========================================
# IMPORTANT: Icarus Verilog has LIMITED SystemVerilog 2012 support.
# The following features used in CERES RTL are NOT supported:
#   - `inside` operator
#   - `automatic` function/task variables
#   - Struct/union type parameters
#   - Some advanced type definitions
#
# For CERES simulation, please use:
#   - Verilator (recommended): make verilate; make run_verilator
#   - QuestaSim/ModelSim: make vsim
#
# This makefile is kept for reference and potential future use
# with simpler RTL designs.
# =========================================
# Usage:
#   make iverilog              - Compile with Icarus
#   make run_icarus            - Run simulation
#   make run_icarus_gui        - Run and open GTKWave
#   make SIM=icarus run        - Use in test pipeline
# =========================================

# NOT: LOG/SIM/TRACE kontrolleri sim/common.mk'de merkezi olarak yönetiliyor.
#      common.mk ana makefile tarafından include edilir.

# -----------------------------------------
# Icarus Paths & Configuration
# -----------------------------------------
IVERILOG       ?= iverilog
VVP            ?= vvp
GTKWAVE        ?= gtkwave

ICARUS_DIR     := $(BUILD_DIR)/icarus
ICARUS_OUT     := $(ICARUS_DIR)/ceres_tb.vvp
ICARUS_VCD     := $(ICARUS_DIR)/$(TEST_NAME).vcd
ICARUS_FST     := $(ICARUS_DIR)/$(TEST_NAME).fst
ICARUS_LOG_DIR := $(LOG_DIR)/icarus/$(TEST_NAME)

# -----------------------------------------
# Source Files
# -----------------------------------------
ICARUS_INCLUDES := $(addprefix -I, $(INC_DIRS))

# RTL source list (same as Verilator, uses SV_SOURCES from sources.mk)
ICARUS_RTL_SRCS := $(SV_SOURCES)

# Testbench for Icarus (SystemVerilog compatible)
ICARUS_TB      := $(SIM_DIR)/tb/tb_icarus.sv

# Fallback to wrapper if icarus-specific TB doesn't exist
ifeq ($(wildcard $(ICARUS_TB)),)
    ICARUS_TB  := $(SIM_DIR)/tb/tb_wrapper.sv
endif

# -----------------------------------------
# Icarus Flags
# -----------------------------------------
# Language standard
ICARUS_STD     := -g2012

# Warning flags
ICARUS_WARN    := -Wall -Wno-timescale

# Defines
ICARUS_DEFINES := \
    -DICARUS \
    -DSIMULATION \
    -DTEST_NAME=\"$(TEST_NAME)\" \
    -DMAX_CYCLES=$(MAX_CYCLES)

ifeq ($(TRACE),1)
    ICARUS_DEFINES += -DTRACE_EN
endif

ifeq ($(TEST_TYPE),bench)
    ICARUS_DEFINES += -DBENCHMARK
endif

# Memory initialization
ifdef MEM_FILE
    ICARUS_DEFINES += -DMEM_FILE=\"$(MEM_FILE)\"
endif

# Combined flags
ICARUS_FLAGS := \
    $(ICARUS_STD) \
    $(ICARUS_WARN) \
    $(ICARUS_INCLUDES) \
    $(ICARUS_DEFINES)

# -----------------------------------------
# VVP Runtime Flags
# -----------------------------------------
VVP_FLAGS := -n

ifeq ($(TRACE),1)
    VVP_FLAGS += +trace
endif

# Plusargs
VVP_PLUSARGS := \
    +test_name=$(TEST_NAME) \
    +max_cycles=$(MAX_CYCLES) \
    +log_dir=$(ICARUS_LOG_DIR)

ifdef MEM_FILE
    VVP_PLUSARGS += +mem_file=$(MEM_FILE)
endif

ifdef HEX_FILE
    VVP_PLUSARGS += +hex_file=$(HEX_FILE)
endif

# -----------------------------------------
# Targets
# -----------------------------------------
.PHONY: iverilog run_icarus run_icarus_gui clean_icarus icarus_help

# Check if Icarus is installed
check_icarus:
	@command -v $(IVERILOG) >/dev/null 2>&1 || { \
		echo -e "$(RED)❌ Icarus Verilog not found$(RESET)"; \
		echo -e "$(YELLOW)Install with: sudo apt install iverilog$(RESET)"; \
		exit 1; \
	}

# Compile with Icarus Verilog
iverilog: check_icarus dirs
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Icarus Verilog Compilation$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Test: $(TEST_NAME)"
	@echo -e "$(CYAN)[INFO]$(RESET) Output: $(ICARUS_OUT)"
	@$(MKDIR) $(ICARUS_DIR) $(ICARUS_LOG_DIR)
	@echo -e "$(CYAN)[COMPILE]$(RESET) Running iverilog..."
	$(IVERILOG) $(ICARUS_FLAGS) \
		-o $(ICARUS_OUT) \
		-s tb_wrapper \
		$(ICARUS_RTL_SRCS) \
		$(ICARUS_TB)
	@echo -e "$(GREEN)✓ Compilation successful$(RESET)"

# Run Icarus simulation
run_icarus: iverilog
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running Icarus Simulation$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Max Cycles: $(MAX_CYCLES)"
	@echo -e "$(CYAN)[INFO]$(RESET) Log Dir: $(ICARUS_LOG_DIR)"
	@cd $(ICARUS_DIR) && $(VVP) $(VVP_FLAGS) $(ICARUS_OUT) $(VVP_PLUSARGS) \
		2>&1 | tee $(ICARUS_LOG_DIR)/simulation.log
	@if [ -f $(ICARUS_VCD) ]; then \
		echo -e "$(GREEN)✓ VCD generated: $(ICARUS_VCD)$(RESET)"; \
	fi
	@echo -e "$(GREEN)✓ Simulation complete$(RESET)"

# Run and open GTKWave
run_icarus_gui: run_icarus
	@echo -e "$(CYAN)[INFO]$(RESET) Opening GTKWave..."
	@if [ -f $(ICARUS_VCD) ]; then \
		$(GTKWAVE) $(ICARUS_VCD) &; \
	elif [ -f $(ICARUS_FST) ]; then \
		$(GTKWAVE) $(ICARUS_FST) &; \
	else \
		echo -e "$(YELLOW)⚠️  No waveform file found$(RESET)"; \
	fi

# Quick Icarus test (compile only, fast check)
icarus_check: check_icarus dirs
	@echo -e "$(CYAN)[CHECK]$(RESET) Quick syntax check with Icarus..."
	@$(MKDIR) $(ICARUS_DIR)
	@$(IVERILOG) $(ICARUS_FLAGS) -t null \
		$(ICARUS_RTL_SRCS) \
		$(ICARUS_TB) 2>&1 | head -50
	@echo -e "$(GREEN)✓ Syntax check complete$(RESET)"

# Clean Icarus outputs
clean_icarus:
	@echo -e "$(CYAN)[CLEAN]$(RESET) Removing Icarus build files..."
	@rm -rf $(ICARUS_DIR)
	@rm -rf $(LOG_DIR)/icarus
	@echo -e "$(GREEN)✓ Clean complete$(RESET)"

# Help
icarus_help:
	@echo -e ""
	@echo -e "$(GREEN)Icarus Verilog Simulation$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(RED)⚠ WARNING: CERES RTL uses advanced SystemVerilog 2012 features$(RESET)"
	@echo -e "$(RED)  that are NOT supported by Icarus Verilog:$(RESET)"
	@echo -e "$(RED)  - 'inside' operator$(RESET)"
	@echo -e "$(RED)  - 'automatic' function/task variables$(RESET)"
	@echo -e "$(RED)  - Struct/union type parameters$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Recommended simulators for CERES:$(RESET)"
	@echo -e "  make verilate; make run_verilator  - Verilator (free)"
	@echo -e "  make vsim                          - QuestaSim/ModelSim"
	@echo -e ""
	@echo -e "$(CYAN)Icarus Targets (for simpler designs):$(RESET)"
	@echo -e "  make iverilog                 - Compile design"
	@echo -e "  make icarus_check             - Quick syntax check"
	@echo -e "  make run_icarus               - Run simulation"
	@echo -e "  make run_icarus_gui           - Run and open GTKWave"
	@echo -e ""
	@echo -e "$(CYAN)Options:$(RESET)"
	@echo -e "  TEST_NAME=<name>              - Test to run"
	@echo -e "  MAX_CYCLES=<n>                - Max simulation cycles"
	@echo -e "  TRACE=1                       - Enable waveform dump"
	@echo -e ""

