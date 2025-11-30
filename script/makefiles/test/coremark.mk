# ============================================================
# CERES CoreMark Build Rules
# Ceres-V RV32IMC_Zicsr Processor CoreMark Benchmark
# ============================================================

.PHONY: coremark coremark_check coremark_setup coremark_build coremark_clean coremark_help
.PHONY: coremark_gen_linker run_coremark cm cm_run

# ============================================================
# Configuration
# ============================================================

# Default iteration count (adjust for ~10 second runtime)
COREMARK_ITERATIONS ?= 1

# Paths
COREMARK_SRC_DIR     := $(SUBREPO_DIR)/coremark
COREMARK_PORT_SRC    := $(ROOT_DIR)/env/coremark/ceresv
COREMARK_PORT_DST    := $(COREMARK_SRC_DIR)/ceresv
COREMARK_BUILD_DIR   := $(BUILD_DIR)/tests/coremark
COREMARK_REPO_URL    := https://github.com/eembc/coremark.git

# Memory Map and Linker Script
COREMARK_MEMORY_MAP  := $(COREMARK_PORT_SRC)/memory_map.yaml
COREMARK_LINKER_GEN  := $(SCRIPT_DIR)/python/gen_linker.py
COREMARK_LINKER_OUT  := $(COREMARK_PORT_DST)/link.ld
COREMARK_HEADER_OUT  := $(COREMARK_PORT_DST)/memory_map.h

# Output files
COREMARK_ELF  := $(COREMARK_BUILD_DIR)/coremark.elf
COREMARK_BIN  := $(COREMARK_BUILD_DIR)/coremark.bin
COREMARK_HEX  := $(COREMARK_BUILD_DIR)/coremark.hex
COREMARK_MEM  := $(COREMARK_BUILD_DIR)/coremark.mem
COREMARK_DUMP := $(COREMARK_BUILD_DIR)/coremark.dump

# ============================================================
# 1️⃣ Main Target - Full Pipeline
# ============================================================

coremark: coremark_check coremark_setup coremark_gen_linker coremark_build
	@echo -e "$(GREEN)[COREMARK] ✓ Build complete$(RESET)"
	@echo -e "$(GREEN)[COREMARK] Output files:$(RESET)"
	@echo -e "  ELF:  $(COREMARK_ELF)"
	@echo -e "  BIN:  $(COREMARK_BIN)"
	@echo -e "  HEX:  $(COREMARK_HEX)"
	@echo -e "  MEM:  $(COREMARK_MEM)"
	@echo -e "  DUMP: $(COREMARK_DUMP)"

# ============================================================
# 2️⃣ Check CoreMark Source Availability
# ============================================================

coremark_check:
	@echo -e "$(YELLOW)[COREMARK] Checking source availability...$(RESET)"
	@if [ -d "$(COREMARK_SRC_DIR)" ] && [ -f "$(COREMARK_SRC_DIR)/coremark.h" ]; then \
		echo -e "$(GREEN)[COREMARK] ✓ Source found at $(COREMARK_SRC_DIR)$(RESET)"; \
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
		echo -e "$(GREEN)[COREMARK] ✓ Source cloned successfully$(RESET)"; \
	fi

# ============================================================
# 3️⃣ Setup - Copy Ceres-V Port Files
# ============================================================

coremark_setup: coremark_check
	@echo -e "$(YELLOW)[COREMARK] Setting up Ceres-V port...$(RESET)"
	@if [ ! -d "$(COREMARK_PORT_SRC)" ]; then \
		echo -e "$(RED)[COREMARK] ✗ Port source not found: $(COREMARK_PORT_SRC)$(RESET)"; \
		exit 1; \
	fi
	@mkdir -p $(COREMARK_PORT_DST)
	@cp -r $(COREMARK_PORT_SRC)/* $(COREMARK_PORT_DST)/
	@echo -e "$(GREEN)[COREMARK] ✓ Port files copied to $(COREMARK_PORT_DST)$(RESET)"

# ============================================================
# 3.5️⃣ Generate Linker Script from Memory Map
# ============================================================

coremark_gen_linker: coremark_setup
	@echo -e "$(YELLOW)[COREMARK] Generating linker script from memory map...$(RESET)"
	@if [ ! -f "$(COREMARK_MEMORY_MAP)" ]; then \
		echo -e "$(YELLOW)[COREMARK] No memory_map.yaml found, using default link.ld$(RESET)"; \
	else \
		python3 $(COREMARK_LINKER_GEN) \
			$(COREMARK_MEMORY_MAP) \
			$(COREMARK_LINKER_OUT) \
			--header $(COREMARK_HEADER_OUT) \
			--verbose; \
		echo -e "$(GREEN)[COREMARK] ✓ Linker script generated$(RESET)"; \
	fi

# ============================================================
# 4️⃣ Build CoreMark for Ceres-V
# ============================================================

# ELF to MEM converter script
ELF_TO_MEM := $(SCRIPT_DIR)/python/elf_to_mem.py

coremark_build: coremark_gen_linker
	@echo -e "$(YELLOW)[COREMARK] Building with $(COREMARK_ITERATIONS) iterations...$(RESET)"
	@mkdir -p $(COREMARK_BUILD_DIR)
	@# Clean previous build in coremark source
	@env -u CC -u LD -u AS -u OBJCOPY -u OBJDUMP \
		$(MAKE) -C $(COREMARK_SRC_DIR) PORT_DIR=ceresv clean 2>/dev/null || true
	@# Build CoreMark - use env to unset variables that might interfere
	@env -u CC -u LD -u AS -u OBJCOPY -u OBJDUMP -u RISCV_PREFIX \
		$(MAKE) -C $(COREMARK_SRC_DIR) \
		PORT_DIR=ceresv \
		ITERATIONS=$(COREMARK_ITERATIONS) \
		XCFLAGS="-DPERFORMANCE_RUN=1" \
		|| { echo -e "$(RED)[COREMARK] ✗ Build failed$(RESET)"; exit 1; }
	@# Copy output files to build directory
	@echo -e "$(YELLOW)[COREMARK] Copying output files...$(RESET)"
	@cp $(COREMARK_SRC_DIR)/coremark.elf $(COREMARK_ELF) 2>/dev/null || true
	@cp $(COREMARK_SRC_DIR)/coremark.bin $(COREMARK_BIN) 2>/dev/null || true
	@cp $(COREMARK_SRC_DIR)/coremark.hex $(COREMARK_HEX) 2>/dev/null || true
	@cp $(COREMARK_SRC_DIR)/coremark.dump $(COREMARK_DUMP) 2>/dev/null || true
	@# Generate proper .mem file using elf_to_mem.py (Verilog $readmemh compatible)
	@echo -e "$(YELLOW)[COREMARK] Generating Verilog-compatible .mem file...$(RESET)"
	@python3 $(ELF_TO_MEM) \
		--in $(COREMARK_BIN) \
		--out $(COREMARK_MEM) \
		--addr 0x80000000 \
		--block-bytes 4 \
		--word-size 4 \
		--word-endian little \
		--word-order high-to-low
	@echo -e "$(GREEN)[COREMARK] ✓ Build successful$(RESET)"

# ============================================================
# 4.5️⃣ Run CoreMark Simulation
# ============================================================
# CoreMark log directory
COREMARK_LOG_DIR := $(RESULTS_DIR)/logs/$(SIM)/coremark

# Main run target - build if needed, then simulate
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
	@echo -e "$(YELLOW)[INFO]$(RESET) Max Cycles: $(or $(MAX_CYCLES),5000000)"
	@$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=coremark \
		TEST_CONFIG=coremark \
		MEM_FILE=$(COREMARK_MEM) \
		NO_ADDR=1 \
		MAX_CYCLES=$(or $(MAX_CYCLES),5000000) \
		VERILATOR_LOG_DIR=$(COREMARK_LOG_DIR)
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  CoreMark Simulation Complete$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@if [ -f "$(COREMARK_LOG_DIR)/uart_output.log" ]; then \
		echo -e "$(YELLOW)[UART OUTPUT]$(RESET)"; \
		cat "$(COREMARK_LOG_DIR)/uart_output.log"; \
	fi

# Short alias for run_coremark
cm: run_coremark

# Even shorter - just run (assumes already built)
cm_run:
	@if [ ! -f "$(COREMARK_MEM)" ]; then \
		echo -e "$(YELLOW)[INFO]$(RESET) CoreMark not built yet, building first..."; \
		$(MAKE) --no-print-directory coremark; \
	fi
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running CoreMark (Quick Mode)$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@if [ -d "$(COREMARK_LOG_DIR)" ]; then \
		rm -rf "$(COREMARK_LOG_DIR)"; \
	fi
	@$(MKDIR) "$(COREMARK_LOG_DIR)"
	@$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=coremark \
		TEST_CONFIG=coremark \
		MEM_FILE=$(COREMARK_MEM) \
		NO_ADDR=1 \
		MAX_CYCLES=$(or $(MAX_CYCLES),5000000) \
		VERILATOR_LOG_DIR=$(COREMARK_LOG_DIR)

# ============================================================
# 5️⃣ Clean
# ============================================================

coremark_clean:
	@echo -e "$(RED)[COREMARK] Cleaning build artifacts...$(RESET)"
	@rm -rf $(COREMARK_BUILD_DIR)
	@if [ -d "$(COREMARK_SRC_DIR)" ]; then \
		$(MAKE) -C $(COREMARK_SRC_DIR) PORT_DIR=ceresv clean 2>/dev/null || true; \
	fi
	@rm -rf $(COREMARK_PORT_DST)
	@echo -e "$(GREEN)[COREMARK] ✓ Clean complete$(RESET)"

# ============================================================
# 6️⃣ Help
# ============================================================

coremark_help:
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)  CERES CoreMark Build & Run System$(RESET)"
	@echo -e "$(GREEN)  Target: Ceres-V RV32IMC_Zicsr Processor$(RESET)"
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Build Targets:$(RESET)"
	@echo -e "  make coremark              - Full build pipeline"
	@echo -e "  make coremark_check        - Check/clone CoreMark source"
	@echo -e "  make coremark_setup        - Copy Ceres-V port files"
	@echo -e "  make coremark_gen_linker   - Generate linker script from YAML"
	@echo -e "  make coremark_build        - Build CoreMark"
	@echo -e "  make coremark_clean        - Clean build artifacts"
	@echo ""
	@echo -e "$(YELLOW)Run Targets:$(RESET)"
	@echo -e "  make run_coremark          - Build (if needed) and run simulation"
	@echo -e "  make cm                    - Short alias for run_coremark"
	@echo -e "  make cm_run                - Quick run (skip rebuild if exists)"
	@echo ""
	@echo -e "$(YELLOW)Configuration:$(RESET)"
	@echo -e "  COREMARK_ITERATIONS=N      - Set iteration count (default: 1)"
	@echo -e "  MAX_CYCLES=N               - Max simulation cycles (default: 5000000)"
	@echo ""
	@echo -e "$(YELLOW)Memory Map:$(RESET)"
	@echo -e "  Edit: $(COREMARK_PORT_SRC)/memory_map.yaml"
	@echo -e "  Linker script is auto-generated from memory map"
	@echo ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make cm                              # Build & run CoreMark"
	@echo -e "  make cm MAX_CYCLES=10000000          # Run with more cycles"
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
	@echo -e "  ceres.log        - Pipeline trace"
	@echo -e "  waveform.fst     - Waveform dump"
	@echo ""
