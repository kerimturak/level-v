# L2 Cache Testbench Makefile

PROJ_ROOT := $(shell git rev-parse --show-toplevel 2>/dev/null || echo ../..)

# RTL sources
RTL_PKG := $(PROJ_ROOT)/rtl/pkg/ceres_param.sv
RTL_SOURCES := \
	$(PROJ_ROOT)/rtl/core/mmu/l2_cache.sv \
	$(PROJ_ROOT)/rtl/core/mmu/l2_bank_multiport.sv \
	$(PROJ_ROOT)/rtl/core/mmu/l2_cache_multibank.sv

TB_TOP := l2_cache_tb.sv

# Verilator settings
VERILATOR := verilator
VERILATOR_FLAGS := --binary --timing -j 0 \
	-I$(PROJ_ROOT)/rtl/include \
	--trace-fst \
	-Wno-fatal \
	--top-module l2_cache_tb

# Output directory
BUILD_DIR := build

.PHONY: all clean run view_wave

all: $(BUILD_DIR)/Vl2_cache_tb

$(BUILD_DIR)/Vl2_cache_tb: $(RTL_PKG) $(RTL_SOURCES) $(TB_TOP)
	@mkdir -p $(BUILD_DIR)
	$(VERILATOR) $(VERILATOR_FLAGS) \
		--Mdir $(BUILD_DIR) \
		$(RTL_PKG) $(RTL_SOURCES) $(TB_TOP)

run: $(BUILD_DIR)/Vl2_cache_tb
	@echo "Running L2 Cache Testbench..."
	cd $(BUILD_DIR) && ./Vl2_cache_tb
	@echo ""
	@echo "Log file: $(BUILD_DIR)/l2_cache_tb.log"
	@cat $(BUILD_DIR)/l2_cache_tb.log

clean:
	rm -rf $(BUILD_DIR) l2_cache_tb.log *.fst

view_wave:
	gtkwave $(BUILD_DIR)/dump.fst &

# Quick test
test: clean all run
