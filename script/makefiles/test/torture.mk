# ============================================================
# RISC-V Torture Test Generator for Ceres-V
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
