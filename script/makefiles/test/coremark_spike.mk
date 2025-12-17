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

# Output files for spike-pk
COREMARK_SPIKE_EXE := $(COREMARK_SPIKE_BUILD_DIR)/coremark.exe
COREMARK_SPIKE_LOG := $(COREMARK_SPIKE_BUILD_DIR)/coremark_spike.log
COREMARK_SPIKE_COMMITS := $(COREMARK_SPIKE_BUILD_DIR)/spike_commits.log

# Comparison output
COREMARK_COMPARE_DIR := $(BUILD_DIR)/tests/coremark-compare
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
	@if [ ! -f "$(SPIKE_BIN)" ]; then \
		echo -e "$(RED)[ERROR] Spike not found at: $(SPIKE_BIN)$(RESET)"; \
		exit 1; \
	fi
	@if [ ! -f "$(PK_BIN)" ]; then \
		echo -e "$(RED)[ERROR] pk not found at: $(PK_BIN)$(RESET)"; \
		exit 1; \
	fi
	@echo -e "$(YELLOW)[INFO] Spike: $(SPIKE_BIN)$(RESET)"
	@echo -e "$(YELLOW)[INFO] pk:    $(PK_BIN)$(RESET)"
	@echo -e "$(YELLOW)[INFO] ISA:   $(SPIKE_ISA)$(RESET)"
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

coremark_compare: coremark_both
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  Running CoreMark Comparison$(RESET)"
	@echo -e "$(CYAN)  Ceres-V (Verilator) vs Spike (ISS)$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@mkdir -p $(COREMARK_COMPARE_DIR)
	@# Step 1: Run on Ceres-V (Verilator)
	@echo -e ""
	@echo -e "$(YELLOW)═══ Step 1/3: Running on Ceres-V (Verilator) ═══$(RESET)"
	@$(MAKE) --no-print-directory run_coremark COREMARK_ITERATIONS=$(COREMARK_ITERATIONS)
	@# Step 2: Run on Spike
	@echo -e ""
	@echo -e "$(YELLOW)═══ Step 2/3: Running on Spike + pk ═══$(RESET)"
	@$(MAKE) --no-print-directory coremark_spike_run COREMARK_ITERATIONS=$(COREMARK_ITERATIONS)
	@# Step 3: Generate comparison
	@echo -e ""
	@echo -e "$(YELLOW)═══ Step 3/3: Generating Comparison Report ═══$(RESET)"
	@echo -e "$(CYAN)[COMPARE] Creating comparison report...$(RESET)"
	@echo "======================================" > $(COREMARK_COMPARE_REPORT)
	@echo "  CoreMark Comparison Report" >> $(COREMARK_COMPARE_REPORT)
	@echo "  Ceres-V (Verilator) vs Spike (ISS)" >> $(COREMARK_COMPARE_REPORT)
	@echo "======================================" >> $(COREMARK_COMPARE_REPORT)
	@echo "" >> $(COREMARK_COMPARE_REPORT)
	@echo "Iterations: $(COREMARK_ITERATIONS)" >> $(COREMARK_COMPARE_REPORT)
	@echo "Date: $$(date)" >> $(COREMARK_COMPARE_REPORT)
	@echo "" >> $(COREMARK_COMPARE_REPORT)
	@echo "--- Ceres-V (Verilator) Output ---" >> $(COREMARK_COMPARE_REPORT)
	@if [ -f "$(COREMARK_LOG_DIR)/uart_output.log" ]; then \
		cat "$(COREMARK_LOG_DIR)/uart_output.log" >> $(COREMARK_COMPARE_REPORT); \
	else \
		echo "ERROR: Ceres-V log not found" >> $(COREMARK_COMPARE_REPORT); \
	fi
	@echo "" >> $(COREMARK_COMPARE_REPORT)
	@echo "--- Spike + pk Output ---" >> $(COREMARK_COMPARE_REPORT)
	@if [ -f "$(COREMARK_SPIKE_LOG)" ]; then \
		cat "$(COREMARK_SPIKE_LOG)" >> $(COREMARK_COMPARE_REPORT); \
	else \
		echo "ERROR: Spike log not found" >> $(COREMARK_COMPARE_REPORT); \
	fi
	@echo "" >> $(COREMARK_COMPARE_REPORT)
	@echo "--- Commit Logs ---" >> $(COREMARK_COMPARE_REPORT)
	@echo "Ceres-V commits: $(COREMARK_LOG_DIR)/ceres_commits.log" >> $(COREMARK_COMPARE_REPORT)
	@echo "Spike commits:   $(COREMARK_SPIKE_COMMITS)" >> $(COREMARK_COMPARE_REPORT)
	@echo "" >> $(COREMARK_COMPARE_REPORT)
	@# Display report
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Comparison Complete$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@cat $(COREMARK_COMPARE_REPORT)
	@echo -e ""
	@echo -e "$(YELLOW)[REPORT]$(RESET) Full report saved to: $(COREMARK_COMPARE_REPORT)"
	@echo -e "$(YELLOW)[CERES COMMITS]$(RESET) $(COREMARK_LOG_DIR)/ceres_commits.log"
	@echo -e "$(YELLOW)[SPIKE COMMITS]$(RESET) $(COREMARK_SPIKE_COMMITS)"
	@echo -e ""
	@echo -e "$(CYAN)Use your Python comparison script to analyze commit logs:$(RESET)"
	@echo -e "  python3 your_compare_script.py \\"
	@echo -e "    $(COREMARK_LOG_DIR)/ceres_commits.log \\"
	@echo -e "    $(COREMARK_SPIKE_COMMITS)"

# Short alias
cm_compare: coremark_compare

# ============================================================
# 6. Quick Compare (minimal iterations for testing)
# ============================================================

cm_compare_quick:
	@$(MAKE) --no-print-directory coremark_compare COREMARK_ITERATIONS=1 MAX_CYCLES=10000000

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
