# =========================================
# DCache Self-Checking Testbench Makefile
# =========================================

SHELL := /bin/bash
.SHELLFLAGS := -e -u -o pipefail -c

# Paths
ROOT_DIR := $(shell cd ../../../.. && pwd)
RTL_DIR := $(ROOT_DIR)/rtl
INC_DIR := $(RTL_DIR)/include
TB_DIR := $(ROOT_DIR)/sim/tb/mmu/dcache
BUILD_DIR := $(ROOT_DIR)/build/tb_dcache
OBJ_DIR := $(BUILD_DIR)/obj_dir
RESULTS_DIR := $(ROOT_DIR)/results/tb_dcache

# Testbench sources
TB_SV := $(TB_DIR)/tb_dcache_selfcheck.sv
TB_CPP := $(TB_DIR)/tb_main.cpp

# RTL sources needed for cache
RTL_SOURCES := \
	$(RTL_DIR)/pkg/ceres_param.sv \
	$(RTL_DIR)/core/mmu/cache.sv \
	$(RTL_DIR)/ram/sp_bram.sv

# Verilator settings
VERILATOR := verilator

# Test configuration
NUM_ITERATIONS ?= 100

VERILATOR_FLAGS := \
	--cc \
	--exe \
	--build \
	-j 4 \
	--top-module tb_dcache_selfcheck \
	-I$(INC_DIR) \
	--timing \
	--trace-fst \
	--trace-structs \
	--trace-params \
	--trace-depth 99 \
	--public \
	--Mdir $(OBJ_DIR) \
	-CFLAGS "-std=c++17 -O2" \
	-LDFLAGS "-lm" \
	-GNUM_RANDOM_ITERATIONS=$(NUM_ITERATIONS)

# Binary
BIN := $(OBJ_DIR)/Vtb_dcache_selfcheck

# Colors
GREEN := \033[0;32m
YELLOW := \033[1;33m
CYAN := \033[0;36m
RED := \033[0;31m
RESET := \033[0m

.PHONY: all clean run wave help dirs quick stress full

# Default target
all: run

# Create directories
dirs:
	@mkdir -p $(BUILD_DIR) $(OBJ_DIR) $(RESULTS_DIR)

# Build testbench
build: dirs
	@echo -e "$(GREEN)[BUILD]$(RESET) Building DCache self-checking testbench..."
	@$(VERILATOR) \
		$(VERILATOR_FLAGS) \
		$(RTL_SOURCES) \
		$(TB_SV) \
		$(TB_CPP)
	@echo -e "$(GREEN)[SUCCESS]$(RESET) Build complete: $(BIN)"

# Run simulation
run: build
	@echo -e "$(CYAN)[RUN]$(RESET) Running DCache testbench ($(NUM_ITERATIONS) iterations)..."
	@cd $(RESULTS_DIR) && $(BIN) +trace 2>&1 | tee simulation.log
	@echo -e "$(GREEN)[DONE]$(RESET) Simulation complete"
	@echo -e "$(CYAN)[INFO]$(RESET) Output saved to: $(RESULTS_DIR)/simulation.log"
	@echo -e "$(CYAN)[INFO]$(RESET) Waveform saved to: $(RESULTS_DIR)/waveform.fst"
	@if grep -q "ALL TESTS PASSED" $(RESULTS_DIR)/simulation.log 2>/dev/null; then \
		echo -e "$(GREEN)✓ All tests passed!$(RESET)"; \
	else \
		echo -e "$(RED)✗ Some tests failed - check logs$(RESET)"; \
		exit 1; \
	fi

# Run with timeout (for debugging hangs)
run-timeout: build
	@echo -e "$(CYAN)[RUN]$(RESET) Running DCache testbench with 3s timeout ($(NUM_ITERATIONS) iterations)..."
	@cd $(RESULTS_DIR) && timeout 3s $(BIN) +trace 2>&1 | tee simulation.log || true
	@echo -e "$(YELLOW)[TIMEOUT]$(RESET) Simulation stopped after 3 seconds"
	@echo -e "$(CYAN)[INFO]$(RESET) Output saved to: $(RESULTS_DIR)/simulation.log"
	@echo -e "$(CYAN)[INFO]$(RESET) Last 50 lines:"
	@tail -50 $(RESULTS_DIR)/simulation.log

# Quick test (10 iterations)
quick:
	@$(MAKE) clean
	@$(MAKE) run NUM_ITERATIONS=10

# Stress test (1000 iterations)
stress:
	@$(MAKE) clean
	@$(MAKE) run NUM_ITERATIONS=1000

# Full test (10000 iterations)
full:
	@$(MAKE) clean
	@$(MAKE) run NUM_ITERATIONS=10000

# Open waveform
wave:
	@if [ -f "$(RESULTS_DIR)/waveform.fst" ]; then \
		echo -e "$(CYAN)[WAVE]$(RESET) Opening GTKWave..."; \
		gtkwave $(RESULTS_DIR)/waveform.fst & \
	else \
		echo -e "$(RED)[ERROR]$(RESET) Waveform not found"; \
		exit 1; \
	fi

# Clean
clean:
	@echo -e "$(YELLOW)[CLEAN]$(RESET) Removing build artifacts..."
	@rm -rf $(BUILD_DIR) $(RESULTS_DIR)
	@echo -e "$(GREEN)[DONE]$(RESET) Clean complete"

# Help
help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  DCache Self-Checking Testbench$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Targets:$(RESET)"
	@echo -e "  $(CYAN)all$(RESET)      - Build and run testbench (default, 100 iter)"
	@echo -e "  $(CYAN)build$(RESET)    - Build testbench only"
	@echo -e "  $(CYAN)run$(RESET)      - Build and run simulation (configurable)"
	@echo -e "  $(CYAN)quick$(RESET)    - Quick test (10 iterations)"
	@echo -e "  $(CYAN)stress$(RESET)   - Stress test (1000 iterations)"
	@echo -e "  $(CYAN)full$(RESET)     - Full test (10000 iterations)"
	@echo -e "  $(CYAN)wave$(RESET)     - Open waveform in GTKWave"
	@echo -e "  $(CYAN)clean$(RESET)    - Clean build artifacts"
	@echo -e "  $(CYAN)help$(RESET)     - Show this help"
	@echo -e ""
	@echo -e "$(YELLOW)Configuration:$(RESET)"
	@echo -e "  NUM_ITERATIONS=N  - Set number of random iterations (default: 100)"
	@echo -e "  Example: make run NUM_ITERATIONS=500"
	@echo -e ""
	@echo -e "$(YELLOW)Test Suite (8 Tests):$(RESET)"
	@echo -e "  1. Sequential way filling (PLRU verification)"
	@echo -e "  2. Writeback stress test (dirty evictions)"
	@echo -e "  3. PLRU replacement pattern verification"
	@echo -e "  4. Read-modify-write dirty bit handling"
	@echo -e "  5. Fence.i writeback verification"
	@echo -e "  6. Random access pattern (configurable iterations)"
	@echo -e "  7. Sequential set walking (all sets)"
	@echo -e "  8. Eviction storm (thrashing)"
	@echo -e ""
	@echo -e "$(YELLOW)Verification Features:$(RESET)"
	@echo -e "  ✓ Hierarchical references to internal cache state"
	@echo -e "  ✓ LRU/Tag/Dirty/Data verification via BRAM access"
	@echo -e "  ✓ Protocol checking (pulse/hold/handshake)"
	@echo -e "  ✓ Expected model sync from actual hardware"
	@echo -e "  ✓ Automatic pass/fail reporting"
	@echo -e ""
