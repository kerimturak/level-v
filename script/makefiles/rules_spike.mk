# ============================================================
# 1️ Run Spike for a specific test
# ============================================================
.PHONY: spike_run ceres_run spike_diff spike_all spike_help clean_spike

spike_run:
	@echo -e "$(YELLOW)[SPIKE] Running test: $(TEST_NAME)$(RESET)"

	# ELF file path
	ELF_FILE="$(ELF_DIR)/$(TEST_NAME)"; \
	if [ ! -f "$$ELF_FILE" ]; then \
		echo -e "$(RED) ELF not found: $$ELF_FILE$(RESET)"; exit 1; \
	fi; \
	mkdir -p "$(SPIKE_LOG_DIR)"; \
	echo -e "$(YELLOW)[INFO]$(RESET) Log file -> $(SPIKE_LOG)"; \
	$(SPIKE) $(SPIKE_FLAGS) $$ELF_FILE | tee "$(SPIKE_LOG)"

# ============================================================
# 2️ Run Ceres simulation for the same test
# ============================================================
ceres_run:
	@echo -e "$(YELLOW)[CERES] Running simulation for: $(TEST_NAME)$(RESET)"
	@if [ ! -f "$(ISA_ELF)" ]; then \
		echo -e "$(RED) MEM not found: $(ISA_MEM)$(RESET)"; exit 1; \
	fi
	@mkdir -p "$(SPIKE_LOG_DIR)"; \
	@$(OBJ_DIR)/V$(RTL_LEVEL) +mem=$(ISA_MEM) > "$(CERES_LOG_FILE)"; \
	@echo -e "$(GREEN) Ceres simulation log saved: $(CERES_LOG_FILE)$(RESET)"

# ============================================================
# 3️ Compare Spike vs Ceres logs
# ============================================================
spike_diff: spike_run ceres_run
	@echo -e "$(YELLOW)[DIFF] Comparing Spike vs Ceres outputs for $(TEST_NAME)...$(RESET)"
	@python3 script/python/makefile/compare_logs.py \
		$(SPIKE_LOG_FILE) \
		$(CERES_LOG_FILE)

# ============================================================
# 4️ Run all ISA ELF tests under build/tests/riscv-tests/elf
# ============================================================
spike_all:
	@echo -e "$(YELLOW)[SPIKE] Running all ISA ELF tests...$(RESET)"
	@mkdir -p "$(SPIKE_LOG_DIR)"; \
	@for f in $(wildcard $(ROOT_DIR)/build/tests/riscv-tests/elf/*); do \
		name=$$(basename $$f); \
		echo -e "$(YELLOW) Running $$name$(RESET)"; \
		$(SPIKE) --isa=$(SPIKE_ISA) --pc=$(SPIKE_PC) --log-commits \
			--log=$(SPIKE_LOG_DIR)/$$name_spike.log $$f || true; \
	done
	@echo -e "$(GREEN) All Spike runs completed.$(RESET)"

# ============================================================
# Clean Spike logs
# ============================================================
clean_spike:
	@echo -e "$(RED)[CLEANING SPIKE LOGS]$(RESET)"; \
	@$(RM) -rf "$(SPIKE_LOG_DIR)" "$(LOG_DIR)/spike" || true; \
	@echo -e "$(GREEN) Spike clean complete.$(RESET)"

# ============================================================
# Spike Help — Display available Spike & Ceres simulation targets
# ============================================================
spike_help:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)              CERES RISC-V — Spike Golden Model               $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Purpose:$(RESET)"
	@echo -e "  Run RISC-V ISA ELF tests on Spike (golden model)"
	@echo -e "  Compare Spike results with CERES RTL simulation logs."
	@echo -e ""
	@echo -e "$(YELLOW)Main Targets:$(RESET)"
	@echo -e "  $(GREEN)spike_run    $(RESET)– Run a specific test on Spike"
	@echo -e "  $(GREEN)ceres_run    $(RESET)– Run the same test on CERES RTL binary"
	@echo -e "  $(GREEN)spike_diff   $(RESET)– Compare Spike vs CERES outputs"
	@echo -e "  $(GREEN)spike_all    $(RESET)– Run all ELF tests under build/tests/riscv-tests/elf"
	@echo -e ""
	@echo -e "$(YELLOW)Helper Variables:$(RESET)"
	@echo -e "  TEST_NAME=<name>  – Select specific ISA test (default: rv32ui-p-add)"
	@echo -e "  SPIKE_ISA=<arch>  – ISA mode (default: RV32IMC)"
	@echo -e "  SPIKE_PC=<addr>   – Program start address (default: 0x80000000)"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make spike_run TEST_NAME=rv32ui-p-add"
	@echo -e "  make ceres_run TEST_NAME=rv32ui-p-sub"
	@echo -e "  make spike_diff TEST_NAME=rv32ui-p-or"
	@echo -e "  make spike_all"
	@echo -e ""
	@echo -e "$(YELLOW)Tips:$(RESET)"
	@echo -e "  • Use spike_diff to validate RTL commit logs vs Spike commits."
	@echo -e "  • Generated logs are saved under: $(LOG_DIR)/spike and $(TEST_LOG_DIR)"
	@echo -e "  • Customize SPIKE_FLAGS for debug or log-commit filtering."
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)     Tip: Ensure riscv-tests are built via 'make isa_auto'     $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
