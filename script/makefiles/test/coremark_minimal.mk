# ============================================================
# CERES CoreMark Minimal Port - Build and Comparison
# Minimal CoreMark port without UART, using CSR-based timing
# ============================================================

.PHONY: coremark_minimal_build coremark_minimal_spike coremark_minimal_ceres coremark_minimal_compare
.PHONY: cm_minimal cm_minimal_quick

# ============================================================
# Configuration
# ============================================================

# Minimal port source
COREMARK_MINIMAL_PORT_SRC := $(ROOT_DIR)/env/coremark/minimal
COREMARK_MINIMAL_PORT_DST := $(COREMARK_SRC_DIR)/minimal

# Build directories (following run_test.mk pattern)
COREMARK_MINIMAL_ROOT := $(BUILD_DIR)/tests/coremark-minimal
COREMARK_MINIMAL_ELF_DIR := $(COREMARK_MINIMAL_ROOT)/elf
COREMARK_MINIMAL_MEM_DIR := $(COREMARK_MINIMAL_ROOT)/mem
COREMARK_MINIMAL_DUMP_DIR := $(COREMARK_MINIMAL_ROOT)/dump

# Binary files
COREMARK_MINIMAL_ELF := $(COREMARK_MINIMAL_ELF_DIR)/coremark.elf
COREMARK_MINIMAL_MEM := $(COREMARK_MINIMAL_MEM_DIR)/coremark.mem
COREMARK_MINIMAL_DUMP := $(COREMARK_MINIMAL_DUMP_DIR)/coremark.dump

# Spike configuration
SPIKE_BIN := $(shell which spike || echo /home/kerim/tools/spike/bin/spike)
SPIKE_ISA := rv32imc_zicsr

# Log directories
COREMARK_MINIMAL_LOG_DIR := $(RESULTS_DIR)/logs/minimal
COREMARK_SPIKE_OUTPUT := $(COREMARK_MINIMAL_LOG_DIR)/spike_output.log
COREMARK_SPIKE_COMMITS := $(COREMARK_MINIMAL_LOG_DIR)/spike_commits.log

# Ceres-V logs (will be in verilator/coremark-minimal/ since TEST_NAME=coremark-minimal)
COREMARK_CERES_LOG_DIR := $(RESULTS_DIR)/logs/verilator/coremark-minimal
COREMARK_CERES_COMMITS := $(COREMARK_CERES_LOG_DIR)/commit_trace.log

# Comparison output
COREMARK_MINIMAL_COMPARE_DIR := $(RESULTS_DIR)/comparison/minimal
COREMARK_MINIMAL_COMPARE_REPORT := $(COREMARK_MINIMAL_COMPARE_DIR)/comparison.log
COREMARK_MINIMAL_DIFF_LOG := $(COREMARK_MINIMAL_COMPARE_DIR)/commit_diff.log

# Comparison script (use compare_logs.py like run_test.mk does)
COMPARE_SCRIPT := $(ROOT_DIR)/script/python/makefile/compare_logs.py

# ============================================================
# 1. Build Minimal CoreMark
# ============================================================

coremark_minimal_build: coremark_check
	@echo -e "$(YELLOW)[COREMARK-MINIMAL] Building minimal CoreMark...$(RESET)"
	@# Setup port
	@if [ ! -d "$(COREMARK_MINIMAL_PORT_SRC)" ]; then \
		echo -e "$(RED)ERROR: Minimal port not found: $(COREMARK_MINIMAL_PORT_SRC)$(RESET)"; \
		exit 1; \
	fi
	@mkdir -p $(COREMARK_MINIMAL_PORT_DST)
	@cp -r $(COREMARK_MINIMAL_PORT_SRC)/* $(COREMARK_MINIMAL_PORT_DST)/
	@echo -e "$(CYAN)[INFO]$(RESET) Minimal port files copied"

	@# Create build directories
	@mkdir -p $(COREMARK_MINIMAL_ELF_DIR) $(COREMARK_MINIMAL_MEM_DIR) $(COREMARK_MINIMAL_DUMP_DIR)

	@# Build
	@cd $(COREMARK_SRC_DIR) && \
	$(MAKE) PORT_DIR=minimal clean && \
	$(MAKE) PORT_DIR=minimal ITERATIONS=$(COREMARK_ITERATIONS) XCFLAGS="-DPERFORMANCE_RUN=1"

	@# Copy outputs
	@cp $(COREMARK_SRC_DIR)/coremark $(COREMARK_MINIMAL_ELF)
	@if [ -f $(COREMARK_SRC_DIR)/coremark.dump ]; then \
		cp $(COREMARK_SRC_DIR)/coremark.dump $(COREMARK_MINIMAL_DUMP); \
	fi
	@# Create binary file
	@riscv32-unknown-elf-objcopy -O binary $(COREMARK_MINIMAL_ELF) $(COREMARK_MINIMAL_ROOT)/coremark.bin
	@# Create mem file using elf_to_mem.py (same parameters as coremark.mk)
	@python3 $(ROOT_DIR)/script/python/elf_to_mem.py \
		--in $(COREMARK_MINIMAL_ROOT)/coremark.bin \
		--out $(COREMARK_MINIMAL_MEM) \
		--addr 0x80000000 \
		--block-bytes 4 \
		--word-size 4 \
		--word-endian little \
		--word-order high-to-low

	@echo -e "$(GREEN)✓ Built minimal CoreMark$(RESET)"
	@echo -e "  ELF:  $(COREMARK_MINIMAL_ELF)"
	@echo -e "  MEM:  $(COREMARK_MINIMAL_MEM)"
	@echo -e "  DUMP: $(COREMARK_MINIMAL_DUMP)"

# ============================================================
# 2. Run on Spike
# ============================================================

coremark_minimal_spike: coremark_minimal_build
	@echo -e "$(YELLOW)[COREMARK-MINIMAL] Running on Spike...$(RESET)"
	@mkdir -p $(COREMARK_MINIMAL_LOG_DIR)
	@timeout 60 $(SPIKE_BIN) --isa=$(SPIKE_ISA) \
		--log-commits --log=$(COREMARK_SPIKE_COMMITS) \
		$(COREMARK_MINIMAL_ELF) \
		2>&1 | tee $(COREMARK_SPIKE_OUTPUT) || true
	@echo -e "$(GREEN)✓ Spike execution complete$(RESET)"
	@wc -l $(COREMARK_SPIKE_COMMITS) | awk '{print "  Commits: " $$1}'

# ============================================================
# 3. Run on Ceres-V (using run_test.mk pattern with plusargs)
# ============================================================

coremark_minimal_ceres: coremark_minimal_build
	@echo -e "$(YELLOW)[COREMARK-MINIMAL] Running on Ceres-V...$(RESET)"
	@# Copy to custom test directory for test runner
	@mkdir -p $(BUILD_DIR)/tests/custom/elf $(BUILD_DIR)/tests/custom/mem $(BUILD_DIR)/tests/custom/dump
	@cp -f $(COREMARK_MINIMAL_ELF) $(BUILD_DIR)/tests/custom/elf/coremark-minimal.elf
	@cp -f $(COREMARK_MINIMAL_MEM) $(BUILD_DIR)/tests/custom/mem/coremark-minimal.mem
	@cp -f $(COREMARK_MINIMAL_DUMP) $(BUILD_DIR)/tests/custom/dump/coremark-minimal.dump
	@# Run with test runner
	@$(MAKE) --no-print-directory run \
		TEST_NAME=coremark-minimal \
		TEST_TYPE=custom \
		MAX_CYCLES=$(MAX_CYCLES) \
		USE_PYTHON=1
	@echo -e "$(GREEN)✓ Ceres-V execution complete$(RESET)"
	@if [ -f $(COREMARK_CERES_COMMITS) ]; then \
		wc -l $(COREMARK_CERES_COMMITS) | awk '{print "  Commits: " $$1}'; \
	else \
		echo -e "$(YELLOW)  Warning: Commit log not found at $(COREMARK_CERES_COMMITS)$(RESET)"; \
	fi

# ============================================================
# 4. Compare Logs (using compare_logs.py like run_test.mk)
# ============================================================

coremark_minimal_compare: coremark_minimal_spike coremark_minimal_ceres
	@echo -e "$(YELLOW)[COREMARK-MINIMAL] Comparing commit logs...$(RESET)"
	@mkdir -p $(COREMARK_MINIMAL_COMPARE_DIR)
	@if [ ! -f $(COREMARK_CERES_COMMITS) ]; then \
		echo -e "$(RED)ERROR: Ceres-V commit log not found$(RESET)"; \
		exit 1; \
	fi
	@if [ ! -f $(COREMARK_SPIKE_COMMITS) ]; then \
		echo -e "$(RED)ERROR: Spike commit log not found$(RESET)"; \
		exit 1; \
	fi
	@python3 $(COMPARE_SCRIPT) \
		--rtl $(COREMARK_CERES_COMMITS) \
		--spike $(COREMARK_SPIKE_COMMITS) \
		--output $(COREMARK_MINIMAL_DIFF_LOG) \
		--test-name coremark-minimal \
		--dump $(COREMARK_MINIMAL_DUMP) \
		--skip-csr \
		2>&1 | tee $(COREMARK_MINIMAL_COMPARE_REPORT)
	@echo ""
	@echo -e "$(CYAN)════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)  CoreMark Minimal Comparison Complete$(RESET)"
	@echo -e "$(CYAN)════════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo "Results:"
	@echo "  Spike output:      $(COREMARK_SPIKE_OUTPUT)"
	@echo "  Spike commits:     $(COREMARK_SPIKE_COMMITS)"
	@echo "  Ceres-V commits:   $(COREMARK_CERES_COMMITS)"
	@echo "  Comparison report: $(COREMARK_MINIMAL_COMPARE_REPORT)"
	@echo "  Diff log:          $(COREMARK_MINIMAL_DIFF_LOG)"
	@echo ""

# ============================================================
# 5. Shortcuts
# ============================================================

cm_minimal: coremark_minimal_compare

cm_minimal_quick:
	@$(MAKE) --no-print-directory coremark_minimal_compare \
		COREMARK_ITERATIONS=1 MAX_CYCLES=100000

# ============================================================
# 6. Help
# ============================================================

coremark_minimal_help:
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)  CoreMark Minimal Comparison System$(RESET)"
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Targets:$(RESET)"
	@echo "  coremark_minimal_build     - Build minimal CoreMark"
	@echo "  coremark_minimal_spike     - Run on Spike"
	@echo "  coremark_minimal_ceres     - Run on Ceres-V"
	@echo "  coremark_minimal_compare   - Run both and compare"
	@echo ""
	@echo -e "$(YELLOW)Shortcuts:$(RESET)"
	@echo "  cm_minimal                 - Full comparison"
	@echo "  cm_minimal_quick           - Quick test (1 iteration, 100k cycles)"
	@echo ""
	@echo -e "$(YELLOW)Configuration:$(RESET)"
	@echo "  COREMARK_ITERATIONS        - Number of iterations (default: 10)"
	@echo "  MAX_CYCLES                 - Max simulation cycles (default: 500000)"
	@echo ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo "  make cm_minimal_quick"
	@echo "  make cm_minimal COREMARK_ITERATIONS=10 MAX_CYCLES=1000000"
	@echo ""
