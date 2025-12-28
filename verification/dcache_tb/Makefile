# =============================================================================
# DCache Standalone Verification Makefile
# =============================================================================

# Tools
VLOG = vlog
VSIM = vsim
VERILATOR = verilator

# Directories
RTL_DIR = ../../rtl
CORE_DIR = $(RTL_DIR)/core
PKG_DIR = $(RTL_DIR)/pkg
TB_DIR = .

# Source files
PKG_FILES = \
	$(PKG_DIR)/ceres_param.sv

RTL_FILES = \
	$(RTL_DIR)/ram/sp_bram.sv \
	$(CORE_DIR)/mmu/dcache.sv

TB_FILES = \
	dcache_model.sv \
	tb_dcache.sv

# Compile flags
VLOG_FLAGS = -sv -work work +incdir+$(PKG_DIR) +incdir+$(RTL_DIR)/include -timescale=1ns/1ps

# Simulation flags
VSIM_FLAGS =  -do "run -all; quit"
VSIM_GUI_FLAGS = -do "add wave -r /*; run -all"

# Targets
.PHONY: all clean compile sim gui verilator help

all: compile sim

help:
	@echo "DCache Verification Makefile"
	@echo "============================"
	@echo "Targets:"
	@echo "  compile   - Compile RTL and testbench with ModelSim"
	@echo "  sim       - Run simulation in batch mode"
	@echo "  gui       - Run simulation with GUI"
	@echo "  verilator - Lint check with Verilator"
	@echo "  clean     - Remove generated files"
	@echo ""

# Create work library and compile
compile:
	@echo "Creating work library..."
	@vlib work 2>/dev/null || true
	@echo "Compiling packages..."
	$(VLOG) $(VLOG_FLAGS) $(PKG_FILES)
	@echo "Compiling RTL..."
	$(VLOG) $(VLOG_FLAGS) $(RTL_FILES)
	@echo "Compiling testbench..."
	$(VLOG) $(VLOG_FLAGS) $(TB_FILES)
	@echo "Compilation complete!"

# Run simulation (batch mode)
sim: compile
	@echo "Running simulation..."
	$(VSIM) $(VSIM_FLAGS) work.tb_dcache

# Run simulation (GUI mode)
gui: compile
	@echo "Launching ModelSim GUI..."
	$(VSIM) $(VSIM_GUI_FLAGS) work.tb_dcache &

# Verilator lint check
verilator:
	@echo "Running Verilator lint check..."
	$(VERILATOR) --lint-only -Wall \
		-I$(PKG_DIR) \
		$(PKG_FILES) \
		$(RTL_FILES) \
		$(TB_FILES)

# Clean generated files
clean:
	@echo "Cleaning..."
	@rm -rf work
	@rm -f transcript
	@rm -f vsim.wlf
	@rm -f *.vcd
	@rm -f *.log
	@echo "Clean complete!"

# Quick test (minimal cache size)
test_min:
	@echo "Testing with minimum cache (512 bits = 2 sets, 2 ways)..."
	@grep "DC_CAPACITY = 512" $(PKG_DIR)/ceres_param.sv || \
		(echo "ERROR: Set DC_CAPACITY = 512 in ceres_param.sv first!"; exit 1)
	$(MAKE) sim

# Test with 1KB cache
test_1kb:
	@echo "Testing with 1KB cache (4 sets, 2 ways)..."
	@grep "DC_CAPACITY = 1024" $(PKG_DIR)/ceres_param.sv || \
		(echo "ERROR: Set DC_CAPACITY = 1024 in ceres_param.sv first!"; exit 1)
	$(MAKE) sim

# Simple test (single address)
simple: compile
	@echo "Running simple test..."
	$(VLOG) $(VLOG_FLAGS) tb_dcache_simple.sv
	$(VSIM) $(VSIM_FLAGS) work.tb_dcache_simple

# Detailed test (cycle-by-cycle with backdoor monitoring)
detailed: compile
	@echo "Running detailed test..."
	$(VLOG) $(VLOG_FLAGS) tb_dcache_detailed.sv
	$(VSIM) $(VSIM_FLAGS) work.tb_dcache_detailed

# Comprehensive test (all sizes, random patterns)
comprehensive: compile
	@echo "Running comprehensive test..."
	$(VLOG) $(VLOG_FLAGS) tb_dcache_comprehensive.sv
	$(VSIM) $(VSIM_FLAGS) work.tb_dcache_comprehensive

# Single set test (all requests target same set for n-way analysis)
single_set: compile
	@echo "Running single set test..."
	$(VLOG) $(VLOG_FLAGS) tb_dcache_single_set.sv
	$(VSIM) $(VSIM_FLAGS) work.tb_dcache_single_set

# Single set test with GUI
single_set_gui: compile
	@echo "Running single set test with GUI..."
	$(VLOG) $(VLOG_FLAGS) tb_dcache_single_set.sv
	$(VSIM) $(VSIM_GUI_FLAGS) work.tb_dcache_single_set &
