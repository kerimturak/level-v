# ============================================================
# RISC-V DV (Google's Random Test Generator) for Ceres-V
# ============================================================
# UVM-based instruction generator
# https://github.com/chipsalliance/riscv-dv

.PHONY: riscv_dv riscv_dv_clone riscv_dv_setup riscv_dv_gen riscv_dv_build
.PHONY: riscv_dv_run riscv_dv_clean riscv_dv_help riscv_dv_compare

# ============================================================
# Configuration
# ============================================================

# Repository
RISCV_DV_REPO_URL   := https://github.com/chipsalliance/riscv-dv.git
RISCV_DV_ROOT       := $(SUBREPO_DIR)/riscv-dv

# Paths
RISCV_DV_ENV_SRC    := $(ENV_DIR)/riscv-dv
RISCV_DV_BUILD_DIR  := $(BUILD_DIR)/tests/riscv-dv
RISCV_DV_LOG_DIR    := $(RESULTS_DIR)/logs/$(SIM)/riscv-dv

# Output directories
RISCV_DV_GEN_DIR    := $(RISCV_DV_BUILD_DIR)/gen
RISCV_DV_ELF_DIR    := $(RISCV_DV_BUILD_DIR)/elf
RISCV_DV_HEX_DIR    := $(RISCV_DV_BUILD_DIR)/hex
RISCV_DV_MEM_DIR    := $(RISCV_DV_BUILD_DIR)/mem
RISCV_DV_DUMP_DIR   := $(RISCV_DV_BUILD_DIR)/dump
RISCV_DV_ADDR_DIR   := $(RISCV_DV_BUILD_DIR)/pass_fail_addr
RISCV_DV_SIM_DIR    := $(RISCV_DV_BUILD_DIR)/sim
RISCV_DV_COV_DIR    := $(RISCV_DV_BUILD_DIR)/cov

# Compiler settings
RISCV_DV_CC         := $(RISCV_PREFIX)-gcc
RISCV_DV_OBJCOPY    := $(RISCV_PREFIX)-objcopy
RISCV_DV_OBJDUMP    := $(RISCV_PREFIX)-objdump

# Architecture
RISCV_DV_MARCH      := rv32imc_zicsr
RISCV_DV_MABI       := ilp32

# Compiler flags
RISCV_DV_CFLAGS     := -march=$(RISCV_DV_MARCH) -mabi=$(RISCV_DV_MABI) \
                       -static -nostdlib -nostartfiles -O0

# Linker
RISCV_DV_LDSCRIPT   := $(RISCV_DV_ENV_SRC)/link.ld
RISCV_DV_LDFLAGS    := -T$(RISCV_DV_LDSCRIPT)

# Python
ELF_TO_MEM          := $(SCRIPT_DIR)/python/elf_to_mem.py
RISCV_DV_SCRIPT     := $(RISCV_DV_ROOT)/run.py
RISCV_DV_FALLBACK   := $(SCRIPT_DIR)/python/riscv_dv_gen.py
RISCV_DV_CONFIG_RDR := $(SCRIPT_DIR)/python/riscv_dv_config.py

# JSON Configuration
RISCV_DV_CONFIG     := $(SCRIPT_DIR)/config/tests/riscv-dv.json

# Test configuration (can override from command line or use JSON defaults)
# Command line takes priority > JSON config
RISCV_DV_TEST       ?= $(shell python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-value -k tests.0.name -d riscv_arithmetic_basic_test)
RISCV_DV_ITER       ?= $(shell python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-iterations -t $(RISCV_DV_TEST) 2>/dev/null || echo 5)
RISCV_DV_SEED       ?= $(shell python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-value -k generator.seed -d 0)
RISCV_DV_ISA        ?= $(shell python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-value -k generator.isa -d rv32imc)
RISCV_DV_INSTR_CNT  ?= $(shell python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-value -k generator.instr_cnt -d 500)
RISCV_DV_MMODE      ?= 1

# ============================================================
# Main Targets
# ============================================================

riscv_dv: riscv_dv_clone riscv_dv_setup riscv_dv_gen riscv_dv_build
	@echo -e "$(GREEN)[RISCV-DV] $(SUCCESS) Tests generated and built$(RESET)"

# ============================================================
# Clone Repository
# ============================================================

riscv_dv_clone:
	@echo -e "$(YELLOW)[RISCV-DV] Checking riscv-dv repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(RISCV_DV_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(RISCV_DV_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone --depth=1 $(RISCV_DV_REPO_URL); \
		echo -e "$(GREEN)[OK] riscv-dv cloned.$(RESET)"; \
	else \
		echo -e "$(GREEN)[SKIP] riscv-dv already exists.$(RESET)"; \
	fi

# ============================================================
# Setup Environment
# ============================================================

riscv_dv_setup: riscv_dv_clone
	@echo -e "$(YELLOW)[RISCV-DV] Setting up environment...$(RESET)"
	@mkdir -p $(RISCV_DV_ENV_SRC)
	@mkdir -p $(RISCV_DV_GEN_DIR) $(RISCV_DV_ELF_DIR) $(RISCV_DV_HEX_DIR) \
		$(RISCV_DV_MEM_DIR) $(RISCV_DV_DUMP_DIR) $(RISCV_DV_SIM_DIR) $(RISCV_DV_COV_DIR)
	@echo -e "$(GREEN)[OK] Setup complete$(RESET)"

# ============================================================
# Generate Tests
# ============================================================

riscv_dv_gen: riscv_dv_setup
	@echo -e "$(YELLOW)[RISCV-DV] Generating tests...$(RESET)"
	@echo -e "  Test: $(RISCV_DV_TEST)"
	@echo -e "  Iterations: $(RISCV_DV_ITER)"
	@echo -e "  ISA: $(RISCV_DV_ISA)"
	@GEN_SUCCESS=0; \
	if [ -f "$(RISCV_DV_SCRIPT)" ] && python3 -c "import vsc" 2>/dev/null; then \
		SEED_OPT=""; \
		if [ "$(RISCV_DV_ITER)" = "1" ]; then \
			SEED_OPT="--seed $(RISCV_DV_SEED)"; \
		fi; \
		cd $(RISCV_DV_ROOT) && python3 run.py \
			--test $(RISCV_DV_TEST) \
			--iterations $(RISCV_DV_ITER) \
			--isa $(RISCV_DV_ISA) \
			--mabi ilp32 \
			--simulator pyflow \
			$$SEED_OPT \
			--output $(RISCV_DV_GEN_DIR) \
			--steps gen 2>&1 | head -100 && GEN_SUCCESS=1; \
	fi; \
	if [ "$$GEN_SUCCESS" != "1" ]; then \
		echo -e "$(YELLOW)[RISCV-DV] Using fallback generator...$(RESET)"; \
		for i in $$(seq 0 $$(($(RISCV_DV_ITER) - 1))); do \
			python3 $(RISCV_DV_FALLBACK) \
				--test $(RISCV_DV_TEST) \
				--idx $$i \
				--seed $$(($(RISCV_DV_SEED) + $$i)) \
				--output $(RISCV_DV_GEN_DIR)/$(RISCV_DV_TEST)_$$i.S; \
		done; \
	fi
	@echo -e "$(GREEN)[OK] Generation complete$(RESET)"

# Fallback generator if riscv-dv not available
_riscv_dv_gen_fallback:
	@echo -e "$(YELLOW)[RISCV-DV] Using fallback generator...$(RESET)"
	@for i in $$(seq 0 $$(($(RISCV_DV_ITER) - 1))); do \
		python3 $(RISCV_DV_FALLBACK) \
			--test $(RISCV_DV_TEST) \
			--idx $$i \
			--seed $(RISCV_DV_SEED) \
			--output $(RISCV_DV_GEN_DIR)/$(RISCV_DV_TEST)_$$i.S; \
	done

# ============================================================
# Build Tests
# ============================================================

riscv_dv_build: riscv_dv_gen
	@echo -e "$(YELLOW)[RISCV-DV] Building tests...$(RESET)"
	@PASS=0; FAIL=0; \
	for src in $(RISCV_DV_GEN_DIR)/*.S; do \
		if [ -f "$$src" ]; then \
			name=$$(basename $$src .S); \
			if $(MAKE) --no-print-directory _riscv_dv_build_one SRC=$$src NAME=$$name 2>/dev/null; then \
				PASS=$$((PASS + 1)); \
			else \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[RISCV-DV] Build: $$PASS passed, $$FAIL failed$(RESET)"

_riscv_dv_build_one:
	@mkdir -p $(RISCV_DV_ADDR_DIR)
	@$(RISCV_DV_CC) $(RISCV_DV_CFLAGS) $(RISCV_DV_LDFLAGS) \
		-I$(RISCV_DV_ENV_SRC) \
		$(SRC) \
		-o $(RISCV_DV_ELF_DIR)/$(NAME).elf && \
	$(RISCV_DV_OBJDUMP) -d $(RISCV_DV_ELF_DIR)/$(NAME).elf > $(RISCV_DV_DUMP_DIR)/$(NAME).dump && \
	$(RISCV_DV_OBJCOPY) -O binary $(RISCV_DV_ELF_DIR)/$(NAME).elf $(RISCV_DV_HEX_DIR)/$(NAME).bin && \
	python3 $(ELF_TO_MEM) --in $(RISCV_DV_HEX_DIR)/$(NAME).bin --out $(RISCV_DV_MEM_DIR)/$(NAME).mem \
		--addr 0x80000000 --block-bytes 4 --word-size 4 --word-endian little --word-order high-to-low && \
	PASS_ADDR=$$(grep "^[0-9a-f]* <_pass>:" $(RISCV_DV_DUMP_DIR)/$(NAME).dump | awk '{print "0x" $$1}') && \
	FAIL_ADDR=$$(grep "^[0-9a-f]* <_fail>:" $(RISCV_DV_DUMP_DIR)/$(NAME).dump | awk '{print "0x" $$1}') && \
	echo "$$PASS_ADDR $$FAIL_ADDR" > $(RISCV_DV_ADDR_DIR)/$(NAME)_addr.txt && \
	echo -e "  $(GREEN)$(SUCCESS) $(NAME)$(RESET)"

# ============================================================
# Run Tests
# ============================================================

riscv_dv_run: riscv_dv_build riscv_dv_verilate
	@echo -e "$(YELLOW)[RISCV-DV] Running tests...$(RESET)"
	@mkdir -p $(RISCV_DV_LOG_DIR)
	@PASS=0; FAIL=0; \
	for mem in $(RISCV_DV_MEM_DIR)/*.mem; do \
		if [ -f "$$mem" ]; then \
			name=$$(basename $$mem .mem); \
			echo -e "  $(YELLOW)→ Running: $$name$(RESET)"; \
			if $(MAKE) --no-print-directory run \
				TEST_TYPE=riscv-dv \
				TEST_NAME=$$name \
				MEM_DIR="$(RISCV_DV_MEM_DIR)" \
				ELF_DIR="$(RISCV_DV_ELF_DIR)" \
				DUMP_DIR="$(RISCV_DV_DUMP_DIR)" \
				ADDR_DIR="$(RISCV_DV_ADDR_DIR)" \
				TEST_LOG_DIR="$(RISCV_DV_LOG_DIR)/$$name" \
				RTL_LOG_DIR="$(RISCV_DV_LOG_DIR)/$$name" \
				MAX_CYCLES=50000 2>/dev/null; then \
				echo -e "  $(GREEN)$(SUCCESS) $$name PASS$(RESET)"; \
				PASS=$$((PASS + 1)); \
			else \
				echo -e "  $(RED)✗ $$name FAIL$(RESET)"; \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[RISCV-DV] Results: $$PASS passed, $$FAIL failed$(RESET)"

# Build Verilator with riscv-dv config
riscv_dv_verilate:
	@echo -e "$(YELLOW)[RISCV-DV] Building Verilator...$(RESET)"
	@$(MAKE) --no-print-directory verilate TEST_TYPE=riscv-dv

# ============================================================
# Compare with Spike (ISS comparison)
# ============================================================

riscv_dv_compare:
	@echo -e "$(YELLOW)[RISCV-DV] Comparing with Spike reference...$(RESET)"
	@for elf in $(RISCV_DV_ELF_DIR)/*.elf; do \
		if [ -f "$$elf" ]; then \
			name=$$(basename $$elf .elf); \
			echo -e "  $(YELLOW)→ Comparing: $$name$(RESET)"; \
			spike --isa=$(RISCV_DV_ISA) $$elf > $(RISCV_DV_SIM_DIR)/$$name.spike.log 2>&1 || true; \
		fi; \
	done
	@echo -e "$(GREEN)[OK] Comparison complete$(RESET)"

# ============================================================
# List Available Tests (from JSON config)
# ============================================================

riscv_dv_list:
	@echo -e "$(CYAN)[RISCV-DV] Available tests (from $(RISCV_DV_CONFIG)):$(RESET)"
	@python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-all-tests | while read line; do \
		name=$$(echo $$line | cut -d: -f1); \
		iters=$$(echo $$line | cut -d: -f2); \
		echo -e "  - $$name ($$iters iterations)"; \
	done

# Show configuration summary
riscv_dv_config:
	@python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) summary

# ============================================================
# Run All Enabled Tests from JSON
# ============================================================

# Build all tests first, then run all
riscv_dv_run_all: riscv_dv_build_all riscv_dv_verilate _riscv_dv_run_only

# Run only (skip build) - useful if tests already built
riscv_dv_run_only: riscv_dv_verilate _riscv_dv_run_only

_riscv_dv_run_only:
	@echo -e "$(YELLOW)[RISCV-DV] Running all tests...$(RESET)"
	@mkdir -p $(RISCV_DV_LOG_DIR)
	@PASS=0; FAIL=0; \
	for mem in $(RISCV_DV_MEM_DIR)/*.mem; do \
		if [ -f "$$mem" ]; then \
			name=$$(basename $$mem .mem); \
			echo -e "  $(YELLOW)→ Running: $$name$(RESET)"; \
			if $(MAKE) --no-print-directory run \
				TEST_TYPE=riscv-dv \
				TEST_NAME=$$name \
				MEM_DIR="$(RISCV_DV_MEM_DIR)" \
				ELF_DIR="$(RISCV_DV_ELF_DIR)" \
				DUMP_DIR="$(RISCV_DV_DUMP_DIR)" \
				ADDR_DIR="$(RISCV_DV_ADDR_DIR)" \
				TEST_LOG_DIR="$(RISCV_DV_LOG_DIR)/$$name" \
				RTL_LOG_DIR="$(RISCV_DV_LOG_DIR)/$$name" \
				MAX_CYCLES=50000 2>/dev/null; then \
				echo -e "  $(GREEN)$(SUCCESS) $$name PASS$(RESET)"; \
				PASS=$$((PASS + 1)); \
			else \
				echo -e "  $(RED)✗ $$name FAIL$(RESET)"; \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e ""; \
	echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN) RISCV-DV Final Results: $$PASS passed, $$FAIL failed$(RESET)"; \
	echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"

# Build ALL enabled tests from JSON config
riscv_dv_build_all: riscv_dv_clone riscv_dv_setup
	@echo -e "$(YELLOW)[RISCV-DV] Building all enabled tests from config...$(RESET)"
	@python3 $(RISCV_DV_CONFIG_RDR) -c $(RISCV_DV_CONFIG) get-all-tests | while read line; do \
		test_name=$$(echo $$line | cut -d: -f1); \
		test_iter=$$(echo $$line | cut -d: -f2); \
		echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		echo -e "$(CYAN) Generating: $$test_name ($$test_iter iterations)$(RESET)"; \
		echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		$(MAKE) --no-print-directory _riscv_dv_gen_one TEST_NAME=$$test_name TEST_ITER=$$test_iter; \
	done
	@echo -e "$(YELLOW)[RISCV-DV] Compiling all tests...$(RESET)"
	@PASS=0; FAIL=0; \
	for src in $(RISCV_DV_GEN_DIR)/*.S; do \
		if [ -f "$$src" ]; then \
			name=$$(basename $$src .S); \
			if $(MAKE) --no-print-directory _riscv_dv_build_one SRC=$$src NAME=$$name 2>/dev/null; then \
				PASS=$$((PASS + 1)); \
			else \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[RISCV-DV] Build complete: $$PASS passed, $$FAIL failed$(RESET)"

# Generate tests for a specific test type
_riscv_dv_gen_one:
	@for i in $$(seq 0 $$(($(TEST_ITER) - 1))); do \
		python3 $(RISCV_DV_FALLBACK) \
			--test $(TEST_NAME) \
			--idx $$i \
			--seed $$(($(RISCV_DV_SEED) + $$i)) \
			--instr-cnt $(RISCV_DV_INSTR_CNT) \
			--output $(RISCV_DV_GEN_DIR)/$(TEST_NAME)_$$i.S; \
	done

# ============================================================
# Clean
# ============================================================

riscv_dv_clean:
	@echo -e "$(YELLOW)[RISCV-DV] Cleaning...$(RESET)"
	@rm -rf $(RISCV_DV_BUILD_DIR)
	@echo -e "$(GREEN)[OK] Clean complete$(RESET)"

# ============================================================
# Help
# ============================================================

riscv_dv_help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)     RISC-V DV Random Test Generator$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Configuration File:$(RESET)"
	@echo -e "  $(RISCV_DV_CONFIG)"
	@echo -e ""
	@echo -e "$(CYAN)Usage:$(RESET)"
	@echo -e "  make riscv_dv                    Build tests for default test type"
	@echo -e "  make riscv_dv_run                Run tests for default test type"
	@echo -e "  make riscv_dv_build_all          Build ALL tests from JSON (no run)"
	@echo -e "  make riscv_dv_run_all            Build & Run ALL tests from JSON"
	@echo -e "  make riscv_dv_run_only           Run only (skip build, tests must exist)"
	@echo -e "  make riscv_dv_compare            Compare with Spike ISS"
	@echo -e "  make riscv_dv_list               List available tests from config"
	@echo -e "  make riscv_dv_config             Show configuration summary"
	@echo -e "  make riscv_dv_clean              Clean build files"
	@echo -e ""
	@echo -e "$(CYAN)Configuration (override JSON):$(RESET)"
	@echo -e "  RISCV_DV_TEST=name               Test type"
	@echo -e "  RISCV_DV_ITER=N                  Number of iterations"
	@echo -e "  RISCV_DV_SEED=N                  Random seed"
	@echo -e "  RISCV_DV_ISA=rv32imc             Target ISA"
	@echo -e "  RISCV_DV_INSTR_CNT=N             Instructions per test (default: 500)"
	@echo -e ""
	@echo -e "$(CYAN)JSON Config Structure:$(RESET)"
	@echo -e "  generator.instr_cnt              Instructions per test"
	@echo -e "  generator.isa                    ISA configuration"
	@echo -e "  generator.seed                   Base random seed"
	@echo -e "  tests[].name                     Test name"
	@echo -e "  tests[].iterations               Number of iterations"
	@echo -e "  tests[].enabled                  Enable/disable test"
	@echo -e ""
	@echo -e "$(CYAN)Examples:$(RESET)"
	@echo -e "  make riscv_dv_run_all                              # Build & run all"
	@echo -e "  make riscv_dv_run_only                             # Run only (no build)"
	@echo -e "  make riscv_dv RISCV_DV_TEST=riscv_rand_instr_test  # Single test type"
	@echo -e ""
