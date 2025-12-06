.PHONY: imperas_auto imperas_clone imperas_setup imperas_build imperas_import imperas_reset imperas_help imperas_list
.PHONY: imperas_build_I imperas_build_M imperas_build_C imperas_build_Zicsr imperas_build_Zifencei

# ============================================================
# 1 Ceres RISC-V Imperas Test Pipeline
# ============================================================
# Direct compilation approach for Imperas RISC-V tests
# (riscv-ovpsim/imperas-riscv-tests)
#
# NOTE: The free/public Imperas repo only includes RV32I base tests.
# For M, C, Zicsr extensions, use riscv-arch-test (make arch_auto)
#
# ============================================================
# Configuration
# ============================================================

# Available extensions in free Imperas repo (only I has source code)
IMPERAS_EXTENSIONS := I

# Repository URL
IMPERAS_REPO_URL := https://github.com/riscv-ovpsim/imperas-riscv-tests.git
IMPERAS_ROOT     := $(SUBREPO_DIR)/imperas-riscv-tests

# Paths
IMPERAS_ENV_SRC    := $(ENV_DIR)/imperas
IMPERAS_SUITE_DIR  := $(IMPERAS_ROOT)/riscv-test-suite/rv32i_m
IMPERAS_ENV_DIR    := $(IMPERAS_ROOT)/riscv-test-suite/env
IMPERAS_BUILD_DIR  := $(BUILD_DIR)/tests/imperas
IMPERAS_WORK_DIR   := $(IMPERAS_BUILD_DIR)/work

# Output directories
IMPERAS_ELF_DIR    := $(IMPERAS_BUILD_DIR)/elf
IMPERAS_DUMP_DIR   := $(IMPERAS_BUILD_DIR)/dump
IMPERAS_HEX_DIR    := $(IMPERAS_BUILD_DIR)/hex
IMPERAS_MEM_DIR    := $(IMPERAS_BUILD_DIR)/mem
IMPERAS_ADDR_DIR   := $(IMPERAS_BUILD_DIR)/pass_fail_addr
IMPERAS_REF_DIR    := $(IMPERAS_BUILD_DIR)/reference

# Compiler settings
IMPERAS_CC         := $(RISCV_PREFIX)-gcc
IMPERAS_OBJCOPY    := $(RISCV_PREFIX)-objcopy
IMPERAS_OBJDUMP    := $(RISCV_PREFIX)-objdump

# Architecture flags for RV32IMC_Zicsr
IMPERAS_MARCH      := rv32imc_zicsr
IMPERAS_MABI       := ilp32

# Compiler flags (TEST_CASE_1 is defined in arch_test.h, don't define it again)
IMPERAS_CFLAGS     := -march=$(IMPERAS_MARCH) -mabi=$(IMPERAS_MABI) -static -mcmodel=medany \
                      -fvisibility=hidden -nostdlib -nostartfiles -fno-builtin \
                      -DXLEN=32

# Include paths - arch_test.h from Imperas suite + model_test.h from ceres env
IMPERAS_INCLUDES   := -I$(IMPERAS_ENV_DIR) \
                      -I$(IMPERAS_ENV_SRC)

# Linker script
IMPERAS_LDSCRIPT   := $(IMPERAS_ENV_SRC)/link.ld
IMPERAS_LDFLAGS    := -T$(IMPERAS_LDSCRIPT)

# Python scripts
HEX_TO_MEM_PY      := $(SCRIPT_DIR)/python/makefile/hex_to_mem.py

# ============================================================
# 2 Main Pipeline (Clone → Setup → Build → Import)
# ============================================================

imperas_auto: imperas_clone imperas_setup imperas_build imperas_import

# ------------------------------------------------------------
# 1. Clone imperas-riscv-tests repository
# ------------------------------------------------------------
imperas_clone:
	@echo -e "$(YELLOW)[IMPERAS] Checking imperas-riscv-tests repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(IMPERAS_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(IMPERAS_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone --depth=1 $(IMPERAS_REPO_URL); \
		echo -e "$(GREEN)[OK] imperas-riscv-tests cloned.$(RESET)"; \
	else \
		echo -e "$(GREEN)[SKIP] imperas-riscv-tests already exists.$(RESET)"; \
	fi

# ------------------------------------------------------------
# 2. Setup - Verify environment files exist
# ------------------------------------------------------------
imperas_setup:
	@echo -e "$(YELLOW)[IMPERAS] Verifying Ceres environment...$(RESET)"
	@if [ ! -f "$(IMPERAS_ENV_SRC)/model_test.h" ]; then \
		echo -e "$(RED)[ERROR] model_test.h not found at $(IMPERAS_ENV_SRC)$(RESET)"; \
		exit 1; \
	fi
	@if [ ! -f "$(IMPERAS_ENV_SRC)/link.ld" ]; then \
		echo -e "$(RED)[ERROR] link.ld not found at $(IMPERAS_ENV_SRC)$(RESET)"; \
		exit 1; \
	fi
	@if [ ! -f "$(IMPERAS_ENV_DIR)/arch_test.h" ]; then \
		echo -e "$(RED)[ERROR] arch_test.h not found in Imperas suite.$(RESET)"; \
		echo -e "$(RED)       Run 'make imperas_clone' first.$(RESET)"; \
		exit 1; \
	fi
	@mkdir -p $(IMPERAS_ELF_DIR) $(IMPERAS_DUMP_DIR) $(IMPERAS_HEX_DIR) $(IMPERAS_MEM_DIR) $(IMPERAS_ADDR_DIR) $(IMPERAS_REF_DIR)
	@echo -e "$(GREEN)[OK] Environment verified.$(RESET)"

# ------------------------------------------------------------
# 3. Build all supported extensions
# ------------------------------------------------------------
# Note: Free Imperas repo only has I extension source code
# For M, C, Zicsr tests use: make arch_auto
imperas_build: imperas_setup imperas_build_I
	@echo -e "$(GREEN)[IMPERAS] All available tests built successfully.$(RESET)"
	@echo -e "$(YELLOW)[INFO] Imperas free repo only includes I extension tests.$(RESET)"
	@echo -e "$(YELLOW)[INFO] For M, C, Zicsr tests, use: make arch_auto$(RESET)"

# Build I extension tests (main tests available in free repo)
imperas_build_I:
	@echo -e "$(YELLOW)[BUILD] Compiling I extension tests...$(RESET)"
	@$(MAKE) --no-print-directory _imperas_build_ext EXT=I

# Internal target: Build tests for a specific extension
# Note: Some tests are skipped:
# - MISALIGN tests: use deprecated 'mbadaddr' CSR and require misaligned access support
# - EBREAK test: requires specific exception handling that may not match Spike behavior
IMPERAS_SKIP_TESTS := I-MISALIGN_JMP-01 I-MISALIGN_LDST-01 I-EBREAK-01

_imperas_build_ext:
	@mkdir -p $(IMPERAS_ELF_DIR) $(IMPERAS_DUMP_DIR) $(IMPERAS_HEX_DIR) $(IMPERAS_MEM_DIR) $(IMPERAS_ADDR_DIR)
	@EXT_SRC_DIR="$(IMPERAS_SUITE_DIR)/$(EXT)/src"; \
	if [ ! -d "$$EXT_SRC_DIR" ]; then \
		echo -e "$(RED)[ERROR] Source dir not found: $$EXT_SRC_DIR$(RESET)"; \
		exit 1; \
	fi; \
	PASS=0; FAIL=0; SKIP=0; \
	for src in $$EXT_SRC_DIR/*.S; do \
		if [ -f "$$src" ]; then \
			name=$$(basename $$src .S); \
			skip=0; \
			for skiptest in $(IMPERAS_SKIP_TESTS); do \
				if [ "$$name" = "$$skiptest" ]; then skip=1; break; fi; \
			done; \
			if [ $$skip -eq 1 ]; then \
				echo -e "  $(CYAN)⊘ Skipped: $(EXT)-$${name} (requires mbadaddr CSR)$(RESET)"; \
				SKIP=$$((SKIP + 1)); \
				continue; \
			fi; \
			elf="$(IMPERAS_ELF_DIR)/$(EXT)-$${name}.elf"; \
			dump="$(IMPERAS_DUMP_DIR)/$(EXT)-$${name}.dump"; \
			hex="$(IMPERAS_HEX_DIR)/$(EXT)-$${name}.hex"; \
			echo -e "  $(YELLOW)→ Compiling: $(EXT)-$${name}$(RESET)"; \
			if $(IMPERAS_CC) $(IMPERAS_CFLAGS) $(IMPERAS_INCLUDES) $(IMPERAS_LDFLAGS) -o $$elf $$src 2>&1 | grep -v "warning:"; then \
				: ; \
			fi; \
			if [ -f "$$elf" ]; then \
				$(IMPERAS_OBJDUMP) -D $$elf > $$dump; \
				$(IMPERAS_OBJCOPY) -O verilog $$elf $$hex; \
				echo -e "  $(GREEN)$(SUCCESS) Built: $(EXT)-$${name}$(RESET)"; \
				PASS=$$((PASS + 1)); \
			else \
				echo -e "  $(RED)✗ Failed: $(EXT)-$${name}$(RESET)"; \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[$(EXT)] Compiled: $$PASS passed, $$FAIL failed, $$SKIP skipped$(RESET)"

# ------------------------------------------------------------
# 4. Import: Convert HEX → MEM and extract PASS/FAIL addresses
# ------------------------------------------------------------
imperas_import:
	@echo -e "$(YELLOW)[IMPORT] Converting HEX → MEM and extracting addresses...$(RESET)"
	@for hex in $(IMPERAS_HEX_DIR)/*.hex; do \
		if [ -f "$$hex" ]; then \
			name=$$(basename $$hex .hex); \
			mem="$(IMPERAS_MEM_DIR)/$${name}.mem"; \
			dump="$(IMPERAS_DUMP_DIR)/$${name}.dump"; \
			addr="$(IMPERAS_ADDR_DIR)/$${name}_addr.txt"; \
			echo -e "  → Processing: $${name}"; \
			python3 $(HEX_TO_MEM_PY) $$hex $$mem 2>/dev/null || \
				{ echo -e "  $(RED)✗ HEX→MEM failed: $${name}$(RESET)"; continue; }; \
			if [ -f "$$dump" ]; then \
				exit_addr=$$(grep -m1 '<exit_cleanup>:' $$dump | cut -d' ' -f1); \
				halt_addr=$$(grep -m1 '<halt_loop>:' $$dump | cut -d' ' -f1); \
				pass_addr=$$(grep -m1 '<pass>:' $$dump | cut -d' ' -f1); \
				if [ -n "$$exit_addr" ]; then \
					p="0x$$exit_addr"; \
				elif [ -n "$$halt_addr" ]; then \
					p="0x$$halt_addr"; \
				elif [ -n "$$pass_addr" ]; then \
					p="0x$$pass_addr"; \
				else \
					p="0x0"; \
				fi; \
				fail_addr=$$(grep -m1 '<fail>:' $$dump | cut -d' ' -f1); \
				if [ -n "$$fail_addr" ]; then \
					f="0x$$fail_addr"; \
				else \
					f=$$(printf "0x%x" $$(($$p + 0x1000))); \
				fi; \
				echo "$$p $$f" > $$addr; \
			fi; \
		fi; \
	done
	@echo -e "$(GREEN)[IMPORT] Complete.$(RESET)"
	@echo -e "  ELF  → $(IMPERAS_ELF_DIR)"
	@echo -e "  DUMP → $(IMPERAS_DUMP_DIR)"
	@echo -e "  HEX  → $(IMPERAS_HEX_DIR)"
	@echo -e "  MEM  → $(IMPERAS_MEM_DIR)"
	@echo -e "  ADDR → $(IMPERAS_ADDR_DIR)"

# ------------------------------------------------------------
# 5. Copy reference signatures (for future comparison)
# ------------------------------------------------------------
imperas_refs:
	@echo -e "$(YELLOW)[REFS] Copying reference signatures...$(RESET)"
	@for ext in $(IMPERAS_EXTENSIONS); do \
		ref_dir="$(IMPERAS_SUITE_DIR)/$$ext/references"; \
		if [ -d "$$ref_dir" ]; then \
			cp -r $$ref_dir/* $(IMPERAS_REF_DIR)/ 2>/dev/null || true; \
		fi; \
	done
	@echo -e "$(GREEN)[OK] References copied to $(IMPERAS_REF_DIR)$(RESET)"

# ------------------------------------------------------------
# 6. List available tests
# ------------------------------------------------------------
imperas_list:
	@echo -e "$(GREEN)Available imperas-riscv-tests extensions:$(RESET)"
	@if [ -d "$(IMPERAS_SUITE_DIR)" ]; then \
		for ext in $(IMPERAS_SUITE_DIR)/*/; do \
			name=$$(basename $$ext); \
			if [ -d "$$ext/src" ]; then \
				count=$$(ls $$ext/src/*.S 2>/dev/null | wc -l); \
				echo -e "  $$name: $$count tests"; \
			fi; \
		done; \
	else \
		echo -e "  $(RED)Repository not cloned. Run 'make imperas_clone' first.$(RESET)"; \
	fi

# ------------------------------------------------------------
# 7. Cleanup
# ------------------------------------------------------------
imperas_reset:
	@echo -e "$(RED)[RESET] Removing imperas-riscv-tests repo and build artifacts$(RESET)"
	@rm -rf $(IMPERAS_ROOT)
	@rm -rf $(IMPERAS_BUILD_DIR)

imperas_clean:
	@echo -e "$(RED)[CLEAN] Removing build artifacts$(RESET)"
	@rm -rf $(IMPERAS_BUILD_DIR)

# ------------------------------------------------------------
# 8. Generate test list for batch runs
# ------------------------------------------------------------
imperas_flist:
	@echo -e "$(YELLOW)[FLIST] Generating Imperas test list...$(RESET)"
	@mkdir -p $(SIM_DIR)/test
	@> $(SIM_DIR)/test/imperas_test_list.flist
	@for mem in $(IMPERAS_MEM_DIR)/*.mem; do \
		if [ -f "$$mem" ]; then \
			name=$$(basename $$mem .mem); \
			echo "$$name" >> $(SIM_DIR)/test/imperas_test_list.flist; \
		fi; \
	done
	@count=$$(wc -l < $(SIM_DIR)/test/imperas_test_list.flist); \
	echo -e "$(GREEN)[OK] Generated imperas_test_list.flist with $$count tests$(RESET)"

# ------------------------------------------------------------
# 9. Run all Imperas tests (batch mode)
# ------------------------------------------------------------
.PHONY: imperas run_imperas

# Quick shortcut
imperas: imperas_run_all

# Run all Imperas tests
# Force MAX_CYCLES=200000 for comprehensive Imperas tests (override config.mk default)
IMPERAS_MAX_CYCLES ?= 200000

imperas_run_all: imperas_flist
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)  Running All Imperas RISC-V Tests$(RESET)"
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST="$(SIM_DIR)/test/imperas_test_list.flist" \
		TEST_TYPE=imperas \
		MEM_DIR="$(IMPERAS_MEM_DIR)" \
		ADDR_DIR="$(IMPERAS_ADDR_DIR)" \
		MAX_CYCLES=$(IMPERAS_MAX_CYCLES) \
		NO_ADDR=0

# Run single Imperas test
# Usage: make ti T=I-ADD-01
ti:
ifndef T
	$(error Usage: make ti T=<test_name>  Example: make ti T=I-ADD-01)
endif
	@$(MAKE) --no-print-directory run \
		TEST_NAME=$(T) \
		TEST_TYPE=imperas \
		MEM_DIR="$(IMPERAS_MEM_DIR)" \
		ADDR_DIR="$(IMPERAS_ADDR_DIR)" \
		NO_ADDR=0

# ------------------------------------------------------------
# 10. Help
# ------------------------------------------------------------
imperas_help:
	@echo -e "$(GREEN)CERES RISC-V Imperas Test Pipeline$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)NOTE: Free Imperas repo only includes RV32I base tests.$(RESET)"
	@echo -e "$(YELLOW)      For M, C, Zicsr extensions use: make arch_auto$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Main Targets:$(RESET)"
	@echo -e "  make imperas_auto    # Full pipeline: Clone → Setup → Build → Import"
	@echo -e "  make imperas_clone   # Clone imperas-riscv-tests repository"
	@echo -e "  make imperas_setup   # Verify environment files"
	@echo -e "  make imperas_build   # Build I extension tests"
	@echo -e "  make imperas_import  # Convert HEX→MEM and extract addresses"
	@echo -e ""
	@echo -e "$(YELLOW)Running Tests:$(RESET)"
	@echo -e "  make imperas          # Run all Imperas tests (batch)"
	@echo -e "  make imperas_run_all  # Run all Imperas tests (batch)"
	@echo -e "  make ti T=<name>      # Run single Imperas test"
	@echo -e ""
	@echo -e "$(YELLOW)Utilities:$(RESET)"
	@echo -e "  make imperas_list    # List available test extensions"
	@echo -e "  make imperas_flist   # Generate test file list"
	@echo -e "  make imperas_refs    # Copy reference signatures"
	@echo -e "  make imperas_clean   # Remove build artifacts"
	@echo -e "  make imperas_reset   # Remove repo and artifacts"
	@echo -e ""
	@echo -e "$(GREEN)For M, C, Zicsr tests use riscv-arch-test:$(RESET)"
	@echo -e "  make arch_auto       # Full arch-test pipeline"
	@echo -e "  make arch            # Run all arch tests"
	@echo -e "  make arch_help       # Show arch-test help"
	@echo -e ""
	@echo -e "$(GREEN)Output Directories:$(RESET)"
	@echo -e "  ELF:  $(IMPERAS_ELF_DIR)"
	@echo -e "  DUMP: $(IMPERAS_DUMP_DIR)"
	@echo -e "  HEX:  $(IMPERAS_HEX_DIR)"
	@echo -e "  MEM:  $(IMPERAS_MEM_DIR)"
	@echo -e "  ADDR: $(IMPERAS_ADDR_DIR)"
