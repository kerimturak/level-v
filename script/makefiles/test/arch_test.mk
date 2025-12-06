.PHONY: arch_auto arch_clone arch_setup arch_build arch_import arch_reset arch_help arch_list
.PHONY: arch_build_I arch_build_M arch_build_C arch_build_Zicsr

# ============================================================
# 1 Ceres RISC-V Architecture Test Pipeline
# ============================================================
# Direct compilation approach (no RISCOF dependency)
# Similar to riscv-tests import pipeline

# ============================================================
# Configuration
# ============================================================

# Supported extensions for Ceres RV32IMC_Zicsr
ARCH_EXTENSIONS := I M C Zicsr Zifencei

# Paths
ARCH_ENV_SRC     := $(ENV_DIR)/riscv-arch-test/ceres
ARCH_SUITE_DIR   := $(ARCH_ROOT)/riscv-test-suite/rv32i_m
ARCH_BUILD_DIR   := $(BUILD_DIR)/tests/riscv-arch-test
ARCH_WORK_DIR    := $(ARCH_BUILD_DIR)/work

# Output directories
ARCH_ELF_DIR     := $(ARCH_BUILD_DIR)/elf
ARCH_DUMP_DIR    := $(ARCH_BUILD_DIR)/dump
ARCH_HEX_DIR     := $(ARCH_BUILD_DIR)/hex
ARCH_MEM_DIR     := $(ARCH_BUILD_DIR)/mem
ARCH_ADDR_DIR    := $(ARCH_BUILD_DIR)/pass_fail_addr
ARCH_REF_DIR     := $(ARCH_BUILD_DIR)/reference

# Compiler settings
ARCH_CC          := $(RISCV_PREFIX)-gcc
ARCH_OBJCOPY     := $(RISCV_PREFIX)-objcopy
ARCH_OBJDUMP     := $(RISCV_PREFIX)-objdump

# Architecture flags for RV32IMC_Zicsr
ARCH_MARCH       := rv32imc_zicsr_zifencei
ARCH_MABI        := ilp32

# Compiler flags
ARCH_CFLAGS      := -march=$(ARCH_MARCH) -mabi=$(ARCH_MABI) -static -mcmodel=medany \
                    -fvisibility=hidden -nostdlib -nostartfiles -fno-builtin \
                    -DXLEN=32 -DTEST_CASE_1=True

# Include paths - arch_test.h, encoding.h from official suite + model_test.h from ceres
ARCH_INCLUDES    := -I$(ARCH_ROOT)/riscv-test-suite/env \
                    -I$(ARCH_ENV_SRC)

# Linker script
ARCH_LDSCRIPT    := $(ARCH_ENV_SRC)/link.ld
ARCH_LDFLAGS     := -T$(ARCH_LDSCRIPT)

# Python scripts
ARCH_PIPELINE_PY := $(SCRIPT_DIR)/python/makefile/arch_pipeline.py
HEX_TO_MEM_PY    := $(SCRIPT_DIR)/python/makefile/hex_to_mem.py

# ============================================================
# 2 Main Pipeline (Clone → Setup → Build → Import)
# ============================================================

arch_auto: arch_clone arch_setup arch_build arch_import

# ------------------------------------------------------------
# 1. Clone riscv-arch-test repository
# ------------------------------------------------------------
arch_clone:
	@echo -e "$(YELLOW)[ARCH-TEST] Checking riscv-arch-test repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(ARCH_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(ARCH_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone --depth=1 $(ARCH_REPO_URL); \
		echo -e "$(GREEN)[OK] riscv-arch-test cloned.$(RESET)"; \
	else \
		echo -e "$(GREEN)[SKIP] riscv-arch-test already exists.$(RESET)"; \
	fi

# ------------------------------------------------------------
# 2. Setup - Verify environment files exist
# ------------------------------------------------------------
arch_setup:
	@echo -e "$(YELLOW)[ARCH-TEST] Verifying Ceres environment...$(RESET)"
	@if [ ! -f "$(ARCH_ENV_SRC)/model_test.h" ]; then \
		echo -e "$(RED)[ERROR] model_test.h not found at $(ARCH_ENV_SRC)$(RESET)"; \
		exit 1; \
	fi
	@if [ ! -f "$(ARCH_ENV_SRC)/link.ld" ]; then \
		echo -e "$(RED)[ERROR] link.ld not found at $(ARCH_ENV_SRC)$(RESET)"; \
		exit 1; \
	fi
	@mkdir -p $(ARCH_ELF_DIR) $(ARCH_DUMP_DIR) $(ARCH_HEX_DIR) $(ARCH_MEM_DIR) $(ARCH_ADDR_DIR) $(ARCH_REF_DIR)
	@echo -e "$(GREEN)[OK] Environment verified.$(RESET)"

# ------------------------------------------------------------
# 3. Build all supported extensions
# ------------------------------------------------------------
arch_build: arch_setup arch_build_I arch_build_M arch_build_C arch_build_Zicsr arch_build_Zifencei
	@echo -e "$(GREEN)[ARCH-TEST] All tests built successfully.$(RESET)"

# Build I extension tests
arch_build_I:
	@echo -e "$(YELLOW)[BUILD] Compiling I extension tests...$(RESET)"
	@$(MAKE) --no-print-directory _arch_build_ext EXT=I

# Build M extension tests
arch_build_M:
	@echo -e "$(YELLOW)[BUILD] Compiling M extension tests...$(RESET)"
	@$(MAKE) --no-print-directory _arch_build_ext EXT=M

# Build C extension tests
arch_build_C:
	@echo -e "$(YELLOW)[BUILD] Compiling C extension tests...$(RESET)"
	@$(MAKE) --no-print-directory _arch_build_ext EXT=C

# Build Zicsr extension tests (privilege)
arch_build_Zicsr:
	@echo -e "$(YELLOW)[BUILD] Compiling Zicsr tests...$(RESET)"
	@if [ -d "$(ARCH_SUITE_DIR)/privilege/src" ]; then \
		$(MAKE) --no-print-directory _arch_build_ext EXT=privilege; \
	else \
		echo -e "$(YELLOW)[SKIP] No privilege tests found.$(RESET)"; \
	fi

# Build Zifencei extension tests
arch_build_Zifencei:
	@echo -e "$(YELLOW)[BUILD] Compiling Zifencei tests...$(RESET)"
	@if [ -d "$(ARCH_SUITE_DIR)/Zifencei/src" ]; then \
		$(MAKE) --no-print-directory _arch_build_ext EXT=Zifencei; \
	else \
		echo -e "$(YELLOW)[SKIP] No Zifencei tests found.$(RESET)"; \
	fi

# Internal target: Build tests for a specific extension
_arch_build_ext:
	@mkdir -p $(ARCH_ELF_DIR) $(ARCH_DUMP_DIR) $(ARCH_HEX_DIR) $(ARCH_MEM_DIR) $(ARCH_ADDR_DIR)
	@EXT_SRC_DIR="$(ARCH_SUITE_DIR)/$(EXT)/src"; \
	if [ ! -d "$$EXT_SRC_DIR" ]; then \
		echo -e "$(RED)[ERROR] Source dir not found: $$EXT_SRC_DIR$(RESET)"; \
		exit 1; \
	fi; \
	PASS=0; FAIL=0; \
	for src in $$EXT_SRC_DIR/*.S; do \
		if [ -f "$$src" ]; then \
			name=$$(basename $$src .S); \
			elf="$(ARCH_ELF_DIR)/$(EXT)-$${name}.elf"; \
			dump="$(ARCH_DUMP_DIR)/$(EXT)-$${name}.dump"; \
			hex="$(ARCH_HEX_DIR)/$(EXT)-$${name}.hex"; \
			echo -e "  $(YELLOW)→ Compiling: $(EXT)-$${name}$(RESET)"; \
			if $(ARCH_CC) $(ARCH_CFLAGS) $(ARCH_INCLUDES) $(ARCH_LDFLAGS) -o $$elf $$src 2>&1 | grep -v "warning:"; then \
				: ; \
			fi; \
			if [ -f "$$elf" ]; then \
				$(ARCH_OBJDUMP) -D $$elf > $$dump; \
				$(ARCH_OBJCOPY) -O verilog $$elf $$hex; \
				echo -e "  $(GREEN)$(SUCCESS) Built: $(EXT)-$${name}$(RESET)"; \
				PASS=$$((PASS + 1)); \
			else \
				echo -e "  $(RED)✗ Failed: $(EXT)-$${name}$(RESET)"; \
				FAIL=$$((FAIL + 1)); \
			fi; \
		fi; \
	done; \
	echo -e "$(GREEN)[$(EXT)] Compiled: $$PASS passed, $$FAIL failed$(RESET)"

# ------------------------------------------------------------
# 4. Import: Convert HEX → MEM and extract PASS/FAIL addresses
# ------------------------------------------------------------
arch_import:
	@echo -e "$(YELLOW)[IMPORT] Converting HEX → MEM and extracting addresses...$(RESET)"
	@for hex in $(ARCH_HEX_DIR)/*.hex; do \
		if [ -f "$$hex" ]; then \
			name=$$(basename $$hex .hex); \
			mem="$(ARCH_MEM_DIR)/$${name}.mem"; \
			dump="$(ARCH_DUMP_DIR)/$${name}.dump"; \
			addr="$(ARCH_ADDR_DIR)/$${name}_addr.txt"; \
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
	@echo -e "  ELF  → $(ARCH_ELF_DIR)"
	@echo -e "  DUMP → $(ARCH_DUMP_DIR)"
	@echo -e "  HEX  → $(ARCH_HEX_DIR)"
	@echo -e "  MEM  → $(ARCH_MEM_DIR)"
	@echo -e "  ADDR → $(ARCH_ADDR_DIR)"

# ------------------------------------------------------------
# 5. Copy reference signatures (for future comparison)
# ------------------------------------------------------------
arch_refs:
	@echo -e "$(YELLOW)[REFS] Copying reference signatures...$(RESET)"
	@for ext in $(ARCH_EXTENSIONS); do \
		ref_dir="$(ARCH_SUITE_DIR)/$$ext/references"; \
		if [ -d "$$ref_dir" ]; then \
			cp -r $$ref_dir/* $(ARCH_REF_DIR)/ 2>/dev/null || true; \
		fi; \
	done
	@echo -e "$(GREEN)[OK] References copied to $(ARCH_REF_DIR)$(RESET)"

# ------------------------------------------------------------
# 6. List available tests
# ------------------------------------------------------------
arch_list:
	@echo -e "$(GREEN)Available riscv-arch-test extensions:$(RESET)"
	@if [ -d "$(ARCH_SUITE_DIR)" ]; then \
		for ext in $(ARCH_SUITE_DIR)/*/; do \
			name=$$(basename $$ext); \
			count=$$(ls $$ext/src/*.S 2>/dev/null | wc -l); \
			echo -e "  $$name: $$count tests"; \
		done; \
	else \
		echo -e "  $(RED)Repository not cloned. Run 'make arch_clone' first.$(RESET)"; \
	fi

# ------------------------------------------------------------
# 7. Cleanup
# ------------------------------------------------------------
arch_reset:
	@echo -e "$(RED)[RESET] Removing riscv-arch-test repo and build artifacts$(RESET)"
	@rm -rf $(ARCH_ROOT)
	@rm -rf $(ARCH_BUILD_DIR)

arch_clean:
	@echo -e "$(RED)[CLEAN] Removing build artifacts$(RESET)"
	@rm -rf $(ARCH_BUILD_DIR)

# ------------------------------------------------------------
# 8. Help
# ------------------------------------------------------------
arch_help:
	@echo -e "$(GREEN)CERES RISC-V Architecture Test Pipeline$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Main Targets:$(RESET)"
	@echo -e "  make arch_auto       # Full pipeline: Clone → Setup → Build → Import"
	@echo -e "  make arch_clone      # Clone riscv-arch-test repository"
	@echo -e "  make arch_setup      # Verify environment files"
	@echo -e "  make arch_build      # Build all supported extension tests"
	@echo -e "  make arch_import     # Convert HEX→MEM and extract addresses"
	@echo -e ""
	@echo -e "$(YELLOW)Extension-Specific Builds:$(RESET)"
	@echo -e "  make arch_build_I       # Build I extension tests"
	@echo -e "  make arch_build_M       # Build M extension tests"
	@echo -e "  make arch_build_C       # Build C extension tests"
	@echo -e "  make arch_build_Zicsr   # Build Zicsr (privilege) tests"
	@echo -e ""
	@echo -e "$(YELLOW)Utilities:$(RESET)"
	@echo -e "  make arch_list       # List available test extensions"
	@echo -e "  make arch_refs       # Copy reference signatures"
	@echo -e "  make arch_clean      # Remove build artifacts"
	@echo -e "  make arch_reset      # Remove repo and artifacts"
	@echo -e ""
	@echo -e "$(GREEN)Output Directories:$(RESET)"
	@echo -e "  ELF:  $(ARCH_ELF_DIR)"
	@echo -e "  DUMP: $(ARCH_DUMP_DIR)"
	@echo -e "  HEX:  $(ARCH_HEX_DIR)"
	@echo -e "  MEM:  $(ARCH_MEM_DIR)"
	@echo -e "  ADDR: $(ARCH_ADDR_DIR)"