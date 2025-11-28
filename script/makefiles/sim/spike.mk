# =========================================
# CERES RISC-V — Spike Golden Model
# =========================================
# Spike simülatör sadece run_test.mk üzerinden kullanılır.
# Bu dosya yalnızca bağımsız Spike çalıştırma ve yardım içindir.
# =========================================

.PHONY: spike_run spike_all spike_help clean_spike

# -----------------------------------------
# Spike Log Directory
# -----------------------------------------
SPIKE_LOG_DIR := $(LOG_DIR)/spike/$(TEST_NAME)

# ============================================================
# Run Spike for a specific test
# ============================================================
spike_run:
	@echo -e "$(YELLOW)[SPIKE] Running test: $(TEST_NAME)$(RESET)"
	@ELF_FILE="$(ELF_DIR)/$(TEST_NAME)"; \
	if [ ! -f "$$ELF_FILE" ]; then \
		echo -e "$(RED)[ERROR] ELF not found: $$ELF_FILE$(RESET)"; \
		exit 1; \
	fi; \
	mkdir -p "$(SPIKE_LOG_DIR)"; \
	echo -e "$(YELLOW)[INFO]$(RESET) Log file -> $(SPIKE_LOG_DIR)/spike.log"; \
	$(SPIKE) $(SPIKE_FLAGS) "$$ELF_FILE" 2>&1 | tee "$(SPIKE_LOG_DIR)/spike.log"

# ============================================================
# Run all ISA ELF tests
# ============================================================
spike_all:
	@echo -e "$(YELLOW)[SPIKE] Running all ISA ELF tests...$(RESET)"
	@mkdir -p "$(LOG_DIR)/spike"
	@for f in $(BUILD_DIR)/tests/riscv-tests/elf/*; do \
		if [ -f "$$f" ]; then \
			name=$$(basename "$$f"); \
			echo -e "$(CYAN) Running $$name$(RESET)"; \
			$(SPIKE) $(SPIKE_FLAGS) "$$f" > "$(LOG_DIR)/spike/$${name}_spike.log" 2>&1 || true; \
		fi; \
	done
	@echo -e "$(GREEN)[DONE] All Spike runs completed.$(RESET)"

# ============================================================
# Clean Spike logs
# ============================================================
clean_spike:
	@echo -e "$(RED)[CLEANING SPIKE LOGS]$(RESET)"
	@$(RM) "$(LOG_DIR)/spike"
	@echo -e "$(GREEN)Spike clean complete.$(RESET)"

# ============================================================
# Help
# ============================================================
spike_help:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)              CERES RISC-V — Spike Golden Model               $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Main Targets:$(RESET)"
	@echo -e "  $(GREEN)spike_run    $(RESET)– Run a specific test on Spike"
	@echo -e "  $(GREEN)spike_all    $(RESET)– Run all ELF tests"
	@echo -e "  $(GREEN)clean_spike  $(RESET)– Clean Spike logs"
	@echo -e ""
	@echo -e "$(YELLOW)Parameters:$(RESET)"
	@echo -e "  TEST_NAME=<name>  – Select specific ISA test"
	@echo -e "  SPIKE_ISA=<arch>  – ISA mode (default: RV32IMC)"
	@echo -e "  SPIKE_PC=<addr>   – Start address (default: 0x80000000)"
	@echo -e ""
	@echo -e "$(YELLOW)Example:$(RESET)"
	@echo -e "  make spike_run TEST_NAME=rv32ui-p-add"
	@echo -e ""
	@echo -e "$(YELLOW)Note:$(RESET)"
	@echo -e "  For RTL vs Spike comparison, use: make run TEST_NAME=..."
	@echo -e ""
