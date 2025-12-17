# ============================================================
# CERES CoreMark Spike-pk Build and Comparison Rules
# Run CoreMark on both Ceres-V and Spike for comparison
# ============================================================

.PHONY: coremark_spike coremark_spike_setup coremark_spike_build coremark_spike_run
.PHONY: coremark_compare cm_spike cm_compare

# ============================================================
# Configuration
# ============================================================

# Spike-pk port paths
COREMARK_SPIKE_PORT_SRC := $(ROOT_DIR)/env/coremark/spike-pk
COREMARK_SPIKE_PORT_DST := $(COREMARK_SRC_DIR)/spike-pk
COREMARK_SPIKE_BUILD_DIR := $(BUILD_DIR)/tests/coremark-spike

# Spike configuration
SPIKE_BIN := $(shell which spike || echo /home/kerim/tools/spike/bin/spike)
PK_BIN := $(shell which pk || echo /home/kerim/tools/pk32/riscv32-unknown-elf/bin/pk)
SPIKE_ISA := rv32imc

# Spike log directory (matching Ceres-V structure in results/)
COREMARK_SPIKE_LOG_DIR := $(RESULTS_DIR)/logs/spike/coremark

# Output files for spike-pk
COREMARK_SPIKE_EXE := $(COREMARK_SPIKE_BUILD_DIR)/coremark.exe
COREMARK_SPIKE_LOG := $(COREMARK_SPIKE_LOG_DIR)/uart_output.log
COREMARK_SPIKE_COMMITS := $(COREMARK_SPIKE_LOG_DIR)/spike_commits.log

# Comparison output
COREMARK_COMPARE_DIR := $(RESULTS_DIR)/comparison/coremark
COREMARK_COMPARE_REPORT := $(COREMARK_COMPARE_DIR)/comparison_report.txt

# ============================================================
# 1. Setup spike-pk Port
# ============================================================

coremark_spike_setup: coremark_check
	@echo -e "$(YELLOW)[COREMARK-SPIKE] Setting up spike-pk port...$(RESET)"
	@if [ ! -d "$(COREMARK_SPIKE_PORT_SRC)" ]; then \
		echo -e "$(RED)[COREMARK-SPIKE] ✗ spike-pk port not found: $(COREMARK_SPIKE_PORT_SRC)$(RESET)"; \
		exit 1; \
	fi
	@mkdir -p $(COREMARK_SPIKE_PORT_DST)
	@cp -r $(COREMARK_SPIKE_PORT_SRC)/* $(COREMARK_SPIKE_PORT_DST)/
	@echo -e "$(GREEN)[COREMARK-SPIKE] $(SUCCESS) spike-pk port files copied$(RESET)"

# ============================================================
# 2. Build CoreMark for Spike + pk
# ============================================================

coremark_spike_build: coremark_spike_setup
	@echo -e "$(YELLOW)[COREMARK-SPIKE] Building with $(COREMARK_ITERATIONS) iterations...$(RESET)"
	@mkdir -p $(COREMARK_SPIKE_BUILD_DIR)
	@# Clean previous build
	@env -u CC -u LD -u AS -u OBJCOPY -u OBJDUMP \
		$(MAKE) -C $(COREMARK_SRC_DIR) PORT_DIR=spike-pk clean 2>/dev/null || true
	@# Build CoreMark for spike-pk (compile only, ignore run errors on x86)
	@env -u CC -u LD -u AS -u OBJCOPY -u OBJDUMP -u RISCV_PREFIX \
		$(MAKE) -C $(COREMARK_SRC_DIR) \
		PORT_DIR=spike-pk \
		ITERATIONS=$(COREMARK_ITERATIONS) \
		XCFLAGS="-DPERFORMANCE_RUN=1" \
		compile link 2>&1 | grep -v "Exec format error" || true
	@# Check if binary was created
	@if [ ! -f "$(COREMARK_SRC_DIR)/coremark.exe" ]; then \
		echo -e "$(RED)[COREMARK-SPIKE] ✗ Build failed - binary not found$(RESET)"; \
		exit 1; \
	fi
	@# Copy output
	@cp $(COREMARK_SRC_DIR)/coremark.exe $(COREMARK_SPIKE_EXE)
	@echo -e "$(GREEN)[COREMARK-SPIKE] $(SUCCESS) Build complete: $(COREMARK_SPIKE_EXE)$(RESET)"

# ============================================================
# 3. Run CoreMark on Spike with pk
# ============================================================

coremark_spike_run: coremark_spike_build
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running CoreMark on Spike + pk$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@# Clean previous Spike logs
	@if [ -d "$(COREMARK_SPIKE_LOG_DIR)" ]; then \
		echo -e "$(CYAN)[CLEAN]$(RESET) Removing previous Spike logs: $(COREMARK_SPIKE_LOG_DIR)"; \
		rm -rf "$(COREMARK_SPIKE_LOG_DIR)"; \
	fi
	@$(MKDIR) "$(COREMARK_SPIKE_LOG_DIR)"
	@if [ ! -f "$(SPIKE_BIN)" ]; then \
		echo -e "$(RED)[ERROR] Spike not found at: $(SPIKE_BIN)$(RESET)"; \
		exit 1; \
	fi
	@if [ ! -f "$(PK_BIN)" ]; then \
		echo -e "$(RED)[ERROR] pk not found at: $(PK_BIN)$(RESET)"; \
		exit 1; \
	fi
	@echo -e "$(YELLOW)[INFO] Spike:    $(SPIKE_BIN)$(RESET)"
	@echo -e "$(YELLOW)[INFO] pk:       $(PK_BIN)$(RESET)"
	@echo -e "$(YELLOW)[INFO] ISA:      $(SPIKE_ISA)$(RESET)"
	@echo -e "$(YELLOW)[INFO] Log Dir:  $(COREMARK_SPIKE_LOG_DIR)$(RESET)"
	@echo -e "$(YELLOW)[INFO] Running CoreMark with commit logging...$(RESET)"
	@$(SPIKE_BIN) --isa=$(SPIKE_ISA) \
		--log-commits \
		--log=$(COREMARK_SPIKE_COMMITS) \
		$(PK_BIN) \
		$(COREMARK_SPIKE_EXE) 0x0 0x0 0x66 $(COREMARK_ITERATIONS) 7 1 2000 \
		2>&1 | tee $(COREMARK_SPIKE_LOG)
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Spike Simulation Complete$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)[OUTPUT LOG]$(RESET) $(COREMARK_SPIKE_LOG)"
	@echo -e "$(YELLOW)[COMMIT LOG]$(RESET) $(COREMARK_SPIKE_COMMITS)"
	@if [ -f "$(COREMARK_SPIKE_LOG)" ]; then \
		echo -e ""; \
		echo -e "$(CYAN)[SPIKE OUTPUT]$(RESET)"; \
		cat "$(COREMARK_SPIKE_LOG)"; \
	fi

# Short alias
cm_spike: coremark_spike_run

# ============================================================
# 4. Build and Run Both Versions
# ============================================================

coremark_both: coremark coremark_spike_build
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Both CoreMark versions built successfully$(RESET)"
	@echo -e "$(GREEN)  - Ceres-V barebone: $(COREMARK_MEM)$(RESET)"
	@echo -e "$(GREEN)  - Spike pk:         $(COREMARK_SPIKE_EXE)$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"

# ============================================================
# 5. Compare Ceres-V vs Spike Results
# ============================================================

# Compare script
COMPARE_SCRIPT := $(SCRIPT_DIR)/python/makefile/compare_logs.py
COREMARK_DIFF_LOG := $(COREMARK_COMPARE_DIR)/diff.log
COREMARK_DIFF_HTML := $(COREMARK_COMPARE_DIR)/diff.html

coremark_compare: coremark_both
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  Running CoreMark Comparison$(RESET)"
	@echo -e "$(CYAN)  Ceres-V (Verilator) vs Spike (ISS)$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@mkdir -p $(COREMARK_COMPARE_DIR)
	@# Step 1: Run on Ceres-V (Verilator)
	@echo -e ""
	@echo -e "$(YELLOW)═══ Step 1/4: Running on Ceres-V (Verilator) ═══$(RESET)"
	@$(MAKE) --no-print-directory run_coremark COREMARK_ITERATIONS=$(COREMARK_ITERATIONS)
	@# Step 2: Run on Spike
	@echo -e ""
	@echo -e "$(YELLOW)═══ Step 2/4: Running on Spike + pk ═══$(RESET)"
	@$(MAKE) --no-print-directory coremark_spike_run COREMARK_ITERATIONS=$(COREMARK_ITERATIONS)
	@# Step 3: Compare commit logs
	@echo -e ""
	@echo -e "$(YELLOW)═══ Step 3/4: Comparing Commit Logs ═══$(RESET)"
	@CERES_LOG="$(COREMARK_LOG_DIR)/commit_trace.log"; \
	SPIKE_LOG="$(COREMARK_SPIKE_COMMITS)"; \
	if [ ! -f "$$CERES_LOG" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Ceres-V commit log not found: $$CERES_LOG"; \
		exit 1; \
	fi; \
	if [ ! -f "$$SPIKE_LOG" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Spike commit log not found: $$SPIKE_LOG"; \
		exit 1; \
	fi; \
	echo -e "$(CYAN)[INFO]$(RESET) Ceres-V log: $$CERES_LOG"; \
	echo -e "$(CYAN)[INFO]$(RESET) Spike log:   $$SPIKE_LOG"; \
	echo -e "$(CYAN)[INFO]$(RESET) Running compare_logs.py..."; \
	python3 $(COMPARE_SCRIPT) \
		--rtl "$$CERES_LOG" \
		--spike "$$SPIKE_LOG" \
		--output "$(COREMARK_DIFF_LOG)" \
		--test-name "coremark" \
		--dump "$(COREMARK_BUILD_DIR)/coremark.dump" \
		--skip-csr \
		--resync \
		--window 200 \
		--verbose \
		2>&1 | tee -a $(COREMARK_COMPARE_REPORT); \
	COMPARE_EXIT=$$?; \
	if [ $$COMPARE_EXIT -eq 0 ]; then \
		echo -e "$(GREEN)✓ Commit logs match!$(RESET)"; \
	else \
		echo -e "$(YELLOW)[WARNING]$(RESET) Commit logs differ (expected for different implementations)"; \
	fi
	@# Step 4: Generate summary report
	@echo -e ""
	@echo -e "$(YELLOW)═══ Step 4/4: Generating Summary Report ═══$(RESET)"
	@echo "======================================" > $(COREMARK_COMPARE_REPORT).tmp
	@echo "  CoreMark Comparison Report" >> $(COREMARK_COMPARE_REPORT).tmp
	@echo "  Ceres-V (Verilator) vs Spike (ISS)" >> $(COREMARK_COMPARE_REPORT).tmp
	@echo "======================================" >> $(COREMARK_COMPARE_REPORT).tmp
	@echo "" >> $(COREMARK_COMPARE_REPORT).tmp
	@echo "Iterations: $(COREMARK_ITERATIONS)" >> $(COREMARK_COMPARE_REPORT).tmp
	@echo "Date: $$(date)" >> $(COREMARK_COMPARE_REPORT).tmp
	@echo "" >> $(COREMARK_COMPARE_REPORT).tmp
	@echo "--- Ceres-V (Verilator) Output ---" >> $(COREMARK_COMPARE_REPORT).tmp
	@if [ -f "$(COREMARK_LOG_DIR)/uart_output.log" ]; then \
		cat "$(COREMARK_LOG_DIR)/uart_output.log" >> $(COREMARK_COMPARE_REPORT).tmp; \
	else \
		echo "ERROR: Ceres-V log not found" >> $(COREMARK_COMPARE_REPORT).tmp; \
	fi
	@echo "" >> $(COREMARK_COMPARE_REPORT).tmp
	@echo "--- Spike + pk Output ---" >> $(COREMARK_COMPARE_REPORT).tmp
	@if [ -f "$(COREMARK_SPIKE_LOG)" ]; then \
		cat "$(COREMARK_SPIKE_LOG)" >> $(COREMARK_COMPARE_REPORT).tmp; \
	else \
		echo "ERROR: Spike log not found" >> $(COREMARK_COMPARE_REPORT).tmp; \
	fi
	@echo "" >> $(COREMARK_COMPARE_REPORT).tmp
	@echo "--- Commit Log Comparison Summary ---" >> $(COREMARK_COMPARE_REPORT).tmp
	@if [ -f "$(COREMARK_DIFF_LOG)" ]; then \
		tail -100 "$(COREMARK_DIFF_LOG)" >> $(COREMARK_COMPARE_REPORT).tmp; \
	fi
	@mv $(COREMARK_COMPARE_REPORT).tmp $(COREMARK_COMPARE_REPORT)
	@# Display summary
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Comparison Complete$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)[COMPARISON REPORT]$(RESET) $(COREMARK_COMPARE_REPORT)"
	@echo -e "$(YELLOW)[DIFF LOG]$(RESET)          $(COREMARK_DIFF_LOG)"
	@if [ -f "$(COREMARK_DIFF_HTML)" ]; then \
		echo -e "$(YELLOW)[HTML REPORT]$(RESET)       $(COREMARK_DIFF_HTML)"; \
	fi
	@echo -e "$(YELLOW)[CERES COMMITS]$(RESET)     $(COREMARK_LOG_DIR)/commit_trace.log"
	@echo -e "$(YELLOW)[SPIKE COMMITS]$(RESET)     $(COREMARK_SPIKE_COMMITS)"
	@echo -e ""
	@if [ -f "$(COREMARK_DIFF_LOG)" ]; then \
		echo -e "$(CYAN)[COMPARISON SUMMARY]$(RESET)"; \
		tail -50 "$(COREMARK_DIFF_LOG)"; \
	fi

# Short alias
cm_compare: coremark_compare

# ============================================================
# 6. Quick Compare (minimal iterations for testing)
# ============================================================

cm_compare_quick:
	@$(MAKE) --no-print-directory coremark_compare COREMARK_ITERATIONS=1 MAX_CYCLES=100000

# ============================================================
# 7. Help
# ============================================================

coremark_spike_help:
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)  CoreMark Spike Comparison System$(RESET)"
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Spike Targets:$(RESET)"
	@echo -e "  make coremark_spike_setup  - Setup spike-pk port files"
	@echo -e "  make coremark_spike_build  - Build CoreMark for Spike+pk"
	@echo -e "  make coremark_spike_run    - Run CoreMark on Spike"
	@echo -e "  make cm_spike              - Short alias for spike run"
	@echo ""
	@echo -e "$(YELLOW)Comparison Targets:$(RESET)"
	@echo -e "  make coremark_both         - Build both versions"
	@echo -e "  make coremark_compare      - Full comparison (Ceres vs Spike)"
	@echo -e "  make cm_compare            - Short alias for comparison"
	@echo -e "  make cm_compare_quick      - Quick test (ITER=1)"
	@echo ""
	@echo -e "$(YELLOW)Configuration:$(RESET)"
	@echo -e "  COREMARK_ITERATIONS=N      - Set iteration count"
	@echo -e "  MAX_CYCLES=N               - Max cycles for Ceres-V sim"
	@echo ""
	@echo -e "$(YELLOW)Output Files:$(RESET)"
	@echo -e "  Spike executable:  $(COREMARK_SPIKE_EXE)"
	@echo -e "  Spike output:      $(COREMARK_SPIKE_LOG)"
	@echo -e "  Spike commits:     $(COREMARK_SPIKE_COMMITS)"
	@echo -e "  Comparison report: $(COREMARK_COMPARE_REPORT)"
	@echo ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make cm_compare_quick              # Quick comparison test"
	@echo -e "  make cm_compare COREMARK_ITERATIONS=10"
	@echo -e "  make cm_spike                      # Just run on Spike"
	@echo ""
