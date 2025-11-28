# ============================================================
# CERES CoreMark Build Rules
# Ceres-V RV32IMC_Zicsr Processor CoreMark Benchmark
# ============================================================

.PHONY: coremark coremark_check coremark_setup coremark_build coremark_clean coremark_help

# ============================================================
# Configuration
# ============================================================

# Default iteration count (adjust for ~10 second runtime)
COREMARK_ITERATIONS ?= 1000

# Paths
COREMARK_SRC_DIR     := $(SUBREPO_DIR)/coremark
COREMARK_PORT_SRC    := $(ROOT_DIR)/env/coremark/ceresv
COREMARK_PORT_DST    := $(COREMARK_SRC_DIR)/ceresv
COREMARK_BUILD_DIR   := $(BUILD_DIR)/tests/coremark
COREMARK_REPO_URL    := https://github.com/eembc/coremark.git

# Output files
COREMARK_ELF  := $(COREMARK_BUILD_DIR)/coremark.elf
COREMARK_BIN  := $(COREMARK_BUILD_DIR)/coremark.bin
COREMARK_HEX  := $(COREMARK_BUILD_DIR)/coremark.hex
COREMARK_MEM  := $(COREMARK_BUILD_DIR)/coremark.mem
COREMARK_DUMP := $(COREMARK_BUILD_DIR)/coremark.dump

# ============================================================
# 1️⃣ Main Target - Full Pipeline
# ============================================================

coremark: coremark_check coremark_setup coremark_build
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
# 4️⃣ Build CoreMark for Ceres-V
# ============================================================

coremark_build: coremark_setup
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
	@cp $(COREMARK_SRC_DIR)/coremark.mem $(COREMARK_MEM) 2>/dev/null || true
	@cp $(COREMARK_SRC_DIR)/coremark.dump $(COREMARK_DUMP) 2>/dev/null || true
	@echo -e "$(GREEN)[COREMARK] ✓ Build successful$(RESET)"

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
	@echo -e "$(GREEN)  CERES CoreMark Build System$(RESET)"
	@echo -e "$(GREEN)  Target: Ceres-V RV32IMC_Zicsr Processor$(RESET)"
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Targets:$(RESET)"
	@echo -e "  make coremark              - Full build pipeline"
	@echo -e "  make coremark_check        - Check/clone CoreMark source"
	@echo -e "  make coremark_setup        - Copy Ceres-V port files"
	@echo -e "  make coremark_build        - Build CoreMark"
	@echo -e "  make coremark_clean        - Clean build artifacts"
	@echo -e "  make coremark_help         - Show this help"
	@echo ""
	@echo -e "$(YELLOW)Configuration:$(RESET)"
	@echo -e "  COREMARK_ITERATIONS=N      - Set iteration count (default: 1000)"
	@echo ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make coremark COREMARK_ITERATIONS=2000"
	@echo -e "  make coremark_clean coremark"
	@echo ""
	@echo -e "$(YELLOW)Output Files (in $(COREMARK_BUILD_DIR)):$(RESET)"
	@echo -e "  coremark.elf   - ELF executable"
	@echo -e "  coremark.bin   - Raw binary"
	@echo -e "  coremark.hex   - Intel HEX format"
	@echo -e "  coremark.mem   - Verilog memory file"
	@echo -e "  coremark.dump  - Disassembly listing"
	@echo ""
