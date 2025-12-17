# ============================================================
# CERES CoreMark Minimal Build and Comparison Rules
# Run minimal CoreMark on both Ceres-V and Spike for comparison
# ============================================================

.PHONY: coremark_minimal coremark_minimal_setup coremark_minimal_build coremark_minimal_run
.PHONY: coremark_minimal_compare cm_minimal cm_minimal_compare

# ============================================================
# Configuration
# ============================================================

# Minimal port paths
COREMARK_MINIMAL_PORT_SRC := $(ROOT_DIR)/env/coremark/minimal
COREMARK_MINIMAL_PORT_DST := $(COREMARK_SRC_DIR)/minimal
COREMARK_MINIMAL_BUILD_DIR := $(BUILD_DIR)/tests/coremark-minimal

# Spike configuration
SPIKE_BIN := $(shell which spike || echo /home/kerim/tools/spike/bin/spike)
SPIKE_ISA := rv32imc_zicsr

# Log directories
COREMARK_MINIMAL_LOG_DIR := $(RESULTS_DIR)/logs/minimal
COREMARK_CERES_LOG_DIR := $(RESULTS_DIR)/logs/verilator/coremark

# Output files for minimal
COREMARK_MINIMAL_EXE := $(COREMARK_MINIMAL_BUILD_DIR)/coremark
COREMARK_MINIMAL_MEM := $(COREMARK_MINIMAL_BUILD_DIR)/coremark.mem
COREMARK_MINIMAL_DUMP := $(COREMARK_MINIMAL_BUILD_DIR)/coremark.dump
COREMARK_SPIKE_OUTPUT := $(COREMARK_MINIMAL_LOG_DIR)/spike_output.log
COREMARK_SPIKE_COMMITS := $(COREMARK_MINIMAL_LOG_DIR)/spike_commits.log

# Ceres-V output
COREMARK_CERES_COMMITS := $(COREMARK_CERES_LOG_DIR)/commit_trace.log

# Comparison output
COREMARK_MINIMAL_COMPARE_DIR := $(RESULTS_DIR)/comparison/minimal
COREMARK_MINIMAL_COMPARE_REPORT := $(COREMARK_MINIMAL_COMPARE_DIR)/minimal_comparison.log
COREMARK_MINIMAL_DIFF_LOG := $(COREMARK_MINIMAL_COMPARE_DIR)/commit_diff.log

# Comparison script
COMPARE_MINIMAL_SCRIPT := $(ROOT_DIR)/script/python/makefile/compare_coremark_commits.py

# ============================================================
# 1. Setup Minimal Port
# ============================================================

coremark_minimal_setup: coremark_check
	@echo -e "$(YELLOW)[COREMARK-MINIMAL] Setting up minimal port...$(RESET)"
	@if [ ! -d "$(COREMARK_MINIMAL_PORT_SRC)" ]; then \
		echo -e "$(RED)[COREMARK-MINIMAL] ✗ minimal port not found: $(COREMARK_MINIMAL_PORT_SRC)$(RESET)"; \
		exit 1; \
	fi
	@mkdir -p $(COREMARK_MINIMAL_PORT_DST)
	@cp -r $(COREMARK_MINIMAL_PORT_SRC)/* $(COREMARK_MINIMAL_PORT_DST)/
	@echo -e "$(GREEN)[COREMARK-MINIMAL] $(SUCCESS) minimal port files copied$(RESET)"

# ============================================================
# 2. Build CoreMark Minimal
# ============================================================

coremark_minimal_build: coremark_minimal_setup
	@echo -e "$(YELLOW)[COREMARK-MINIMAL] Building CoreMark with minimal port...$(RESET)"
	@mkdir -p $(COREMARK_MINIMAL_BUILD_DIR)
	@cd $(COREMARK_SRC_DIR) && \
	$(MAKE) PORT_DIR=minimal clean && \
	$(MAKE) PORT_DIR=minimal \
		ITERATIONS=$(COREMARK_ITERATIONS) \
		XCFLAGS="-DPERFORMANCE_RUN=1" && \
	cp coremark $(COREMARK_MINIMAL_BUILD_DIR)/ && \
	if [ -f coremark.bin ]; then cp coremark.bin $(COREMARK_MINIMAL_BUILD_DIR)/; fi && \
	if [ -f coremark.dump ]; then cp coremark.dump $(COREMARK_MINIMAL_BUILD_DIR)/; fi && \
	riscv32-unknown-elf-objcopy -O binary $(COREMARK_MINIMAL_BUILD_DIR)/coremark $(COREMARK_MINIMAL_MEM)
	@echo -e "$(GREEN)[COREMARK-MINIMAL] $(SUCCESS) Built: $(COREMARK_MINIMAL_EXE)$(RESET)"

# ============================================================
# 3. Run on Spike
# ============================================================

coremark_minimal_spike: coremark_minimal_build
	@echo -e "$(YELLOW)[COREMARK-MINIMAL] Running on Spike...$(RESET)"
	@mkdir -p $(COREMARK_MINIMAL_LOG_DIR)
	@echo -e "$(CYAN)[INFO]$(RESET) Spike ISA: $(SPIKE_ISA)"
	@echo -e "$(CYAN)[INFO]$(RESET) Binary: $(COREMARK_MINIMAL_EXE)"
	@$(SPIKE_BIN) --isa=$(SPIKE_ISA) --log-commits --log=$(COREMARK_SPIKE_COMMITS) \
		$(COREMARK_MINIMAL_EXE) 2>&1 | tee $(COREMARK_SPIKE_OUTPUT) || true
	@echo -e "$(GREEN)[COREMARK-MINIMAL] $(SUCCESS) Spike execution complete$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Spike output: $(COREMARK_SPIKE_OUTPUT)"
	@echo -e "$(CYAN)[INFO]$(RESET) Spike commits: $(COREMARK_SPIKE_COMMITS)"

# ============================================================
# 4. Run on Ceres-V
# ============================================================

coremark_minimal_ceres: coremark_minimal_build
	@echo -e "$(YELLOW)[COREMARK-MINIMAL] Running on Ceres-V...$(RESET)"
	@# Copy minimal binary to Ceres-V test directory
	@mkdir -p $(BUILD_DIR)/tests/coremark
	@cp -f $(COREMARK_MINIMAL_MEM) $(BUILD_DIR)/tests/coremark/coremark.mem
	@cp -f $(COREMARK_MINIMAL_DUMP) $(BUILD_DIR)/tests/coremark/coremark.dump
	@echo -e "$(CYAN)[INFO]$(RESET) Reverilating with minimal binary..."
	@$(MAKE) --no-print-directory verilate
	@echo -e "$(CYAN)[INFO]$(RESET) Running Ceres-V simulation..."
	@$(MAKE) --no-print-directory run_coremark MAX_CYCLES=$(MAX_CYCLES) COREMARK_ITERATIONS=$(COREMARK_ITERATIONS)
	@echo -e "$(GREEN)[COREMARK-MINIMAL] $(SUCCESS) Ceres-V execution complete$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Ceres-V commits: $(COREMARK_CERES_COMMITS)"

# ============================================================
# 5. Compare Logs
# ============================================================

coremark_minimal_compare: coremark_minimal_spike coremark_minimal_ceres
	@echo -e "$(YELLOW)[COREMARK-MINIMAL] Comparing commit logs...$(RESET)"
	@mkdir -p $(COREMARK_MINIMAL_COMPARE_DIR)
	@# Run comparison script
	@echo -e "$(CYAN)[INFO]$(RESET) Running compare_coremark_commits.py..."
	@python3 $(COMPARE_MINIMAL_SCRIPT) \
		--ceres $(COREMARK_CERES_COMMITS) \
		--spike $(COREMARK_SPIKE_COMMITS) \
		--ceres-dump $(COREMARK_MINIMAL_DUMP) \
		--spike-dump $(COREMARK_MINIMAL_DUMP) \
		--output $(COREMARK_MINIMAL_DIFF_LOG) \
		2>&1 | tee $(COREMARK_MINIMAL_COMPARE_REPORT); \
	COMPARE_EXIT=$$?; \
	if [ $$COMPARE_EXIT -eq 0 ]; then \
		echo -e "$(GREEN)✓ Commit logs match!$(RESET)"; \
	else \
		echo -e "$(YELLOW)[WARNING]$(RESET) Commit logs differ"; \
	fi
	@# Generate summary report
	@echo "" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo "════════════════════════════════════════════════════════════" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo "  CoreMark Minimal Comparison Complete" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo "════════════════════════════════════════════════════════════" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo "" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo "Results:" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo "  - Spike output:      $(COREMARK_SPIKE_OUTPUT)" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo "  - Spike commits:     $(COREMARK_SPIKE_COMMITS)" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo "  - Ceres-V commits:   $(COREMARK_CERES_COMMITS)" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo "  - Comparison report: $(COREMARK_MINIMAL_COMPARE_REPORT)" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo "  - Diff log:          $(COREMARK_MINIMAL_DIFF_LOG)" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo "" | tee -a $(COREMARK_MINIMAL_COMPARE_REPORT)

# ============================================================
# 6. Short Aliases
# ============================================================

cm_minimal: coremark_minimal_compare

cm_minimal_compare: coremark_minimal_compare

cm_minimal_quick:
	@$(MAKE) --no-print-directory coremark_minimal_compare COREMARK_ITERATIONS=1 MAX_CYCLES=100000

# ============================================================
# 7. Help
# ============================================================

coremark_minimal_help:
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)  CoreMark Minimal Comparison System$(RESET)"
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Targets:$(RESET)"
	@echo -e "  coremark_minimal_setup     - Setup minimal port"
	@echo -e "  coremark_minimal_build     - Build minimal CoreMark"
	@echo -e "  coremark_minimal_spike     - Run on Spike"
	@echo -e "  coremark_minimal_ceres     - Run on Ceres-V"
	@echo -e "  coremark_minimal_compare   - Run both and compare"
	@echo ""
	@echo -e "$(YELLOW)Short Aliases:$(RESET)"
	@echo -e "  cm_minimal                 - Full comparison (alias)"
	@echo -e "  cm_minimal_quick           - Quick comparison (1 iteration)"
	@echo ""
	@echo -e "$(YELLOW)Configuration:$(RESET)"
	@echo -e "  COREMARK_ITERATIONS        - Number of iterations (default: 10)"
	@echo -e "  MAX_CYCLES                 - Max simulation cycles (default: 500000)"
	@echo ""
	@echo -e "$(YELLOW)Output Locations:$(RESET)"
	@echo -e "  Binary:            $(COREMARK_MINIMAL_EXE)"
	@echo -e "  Spike output:      $(COREMARK_SPIKE_OUTPUT)"
	@echo -e "  Spike commits:     $(COREMARK_SPIKE_COMMITS)"
	@echo -e "  Ceres-V commits:   $(COREMARK_CERES_COMMITS)"
	@echo -e "  Comparison report: $(COREMARK_MINIMAL_COMPARE_REPORT)"
	@echo ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make cm_minimal_quick              # Quick comparison test"
	@echo -e "  make cm_minimal COREMARK_ITERATIONS=10"
	@echo ""
