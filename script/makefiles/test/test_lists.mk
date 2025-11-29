# ============================================================
# CERES RISC-V — Test List Shortcuts
# ============================================================
# Kısa isimlerle test listeleri çalıştırma
#
# Usage:
#   make isa          - Run all ISA tests
#   make csr          - Run CSR tests
#   make bench        - Run benchmarks (NO_ADDR=1)
#   make all_tests    - Run all tests
# ============================================================

# -----------------------------------------
# Test List Paths
# -----------------------------------------
TEST_LIST_DIR := $(SIM_DIR)/test

# Test list files
FLIST_ISA       := $(TEST_LIST_DIR)/riscv_test_list.flist
FLIST_CSR       := $(TEST_LIST_DIR)/machine_csr_test.flist
FLIST_BENCH     := $(TEST_LIST_DIR)/riscv_benchmark.flist
FLIST_ALL       := $(TEST_LIST_DIR)/all_tests.flist
FLIST_EXCEPTION := $(TEST_LIST_DIR)/exception_test.flist
FLIST_ARCH      := $(TEST_LIST_DIR)/arch_test.flist

# -----------------------------------------
# ISA Tests (riscv-tests)
# -----------------------------------------
.PHONY: isa isa-tests

isa isa-tests:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running RISC-V ISA Tests$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_ISA) \
		TEST_TYPE=isa \
		SIM=$(SIM) \
		MAX_CYCLES=$(MAX_CYCLES)

# -----------------------------------------
# CSR Tests (machine mode CSR)
# -----------------------------------------
.PHONY: csr csr-tests

csr csr-tests:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running Machine CSR Tests$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_CSR) \
		TEST_TYPE=isa \
		SIM=$(SIM) \
		MAX_CYCLES=$(MAX_CYCLES)

# -----------------------------------------
# Benchmarks (NO_ADDR=1)
# -----------------------------------------
.PHONY: bench benchmarks

bench benchmarks:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running RISC-V Benchmarks$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_bench_flist \
		FLIST=$(FLIST_BENCH) \
		SIM=$(SIM) \
		MAX_CYCLES=$(or $(MAX_CYCLES),1000000)

# -----------------------------------------
# All Tests
# -----------------------------------------
.PHONY: all_tests

all_tests:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running ALL Tests$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_ALL) \
		TEST_TYPE=isa \
		SIM=$(SIM) \
		MAX_CYCLES=$(MAX_CYCLES)

# -----------------------------------------
# Exception Tests
# -----------------------------------------
.PHONY: exc exception-tests

exc exception-tests:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running Exception Tests$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_EXCEPTION) \
		TEST_TYPE=isa \
		SIM=$(SIM) \
		MAX_CYCLES=$(MAX_CYCLES)

# -----------------------------------------
# Architecture Tests (riscv-arch-test)
# -----------------------------------------
.PHONY: arch arch-tests

arch arch-tests:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running RISC-V Architecture Tests$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@if [ ! -f "$(FLIST_ARCH)" ]; then \
		echo -e "$(YELLOW)[INFO] Generating arch test list...$(RESET)"; \
		$(MAKE) --no-print-directory arch_gen_flist; \
	fi
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_ARCH) \
		TEST_TYPE=arch \
		SIM=$(SIM) \
		MAX_CYCLES=$(MAX_CYCLES)

# Generate arch test flist from built tests
.PHONY: arch_gen_flist
arch_gen_flist:
	@echo -e "$(YELLOW)[GEN] Generating arch_test.flist...$(RESET)"
	@mkdir -p $(TEST_LIST_DIR)
	@echo "# RISC-V Architecture Tests" > $(FLIST_ARCH)
	@echo "# Auto-generated from build/tests/riscv-arch-test/elf" >> $(FLIST_ARCH)
	@if [ -d "$(BUILD_DIR)/tests/riscv-arch-test/elf" ]; then \
		for elf in $(BUILD_DIR)/tests/riscv-arch-test/elf/*.elf; do \
			if [ -f "$$elf" ]; then \
				basename $$elf .elf >> $(FLIST_ARCH); \
			fi; \
		done; \
		echo -e "$(GREEN)[OK] Generated $(FLIST_ARCH)$(RESET)"; \
	else \
		echo -e "$(RED)[ERROR] No arch tests found. Run 'make arch_auto' first.$(RESET)"; \
	fi

# Quick arch test: make ta T=I-add-01
.PHONY: ta
ta:
ifndef T
	$(error Usage: make ta T=<arch_test_name> (e.g., I-add-01))
endif
	@$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=$(T) \
		TEST_TYPE=arch \
		SIM=verilator

# -----------------------------------------
# Benchmark List Runner (NO_ADDR=1)
# -----------------------------------------
.PHONY: run_bench_flist

run_bench_flist:
	@if [ ! -f "$(FLIST)" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Test list file not found: $(FLIST)"; \
		exit 1; \
	fi
	@$(MKDIR) "$(LOG_DIR)"
	@# Clean all logs for this simulator if CLEAN_LOGS=1
	@if [ "$(CLEAN_LOGS)" = "1" ]; then \
		echo -e "$(CYAN)[CLEAN]$(RESET) Removing all previous logs: $(RESULTS_DIR)/logs/$(SIM)/"; \
		rm -rf "$(RESULTS_DIR)/logs/$(SIM)/"*; \
	fi
	@echo -n "" > $(PASS_LIST_FILE)
	@echo -n "" > $(FAIL_LIST_FILE)
	@echo -e "$(GREEN)Running benchmarks from list file:$(RESET) $(FLIST)"
	@echo -e "$(CYAN)Output directory:$(RESET) $(RESULTS_DIR)/logs/$(SIM)/"
	@PASS=0; FAIL=0; TOTAL=0; \
	while IFS= read -r test || [ -n "$${test}" ]; do \
		test="$${test%% }"; test="$${test## }"; \
		if echo "$${test}" | grep -E '^\s*#' >/dev/null || [ -z "$${test}" ]; then continue; fi; \
		TOTAL=$$(( $${TOTAL} + 1 )); \
		TEST_LOG_DIR="$(RESULTS_DIR)/logs/$(SIM)/$${test}"; \
		if [ -d "$${TEST_LOG_DIR}" ]; then \
			rm -rf "$${TEST_LOG_DIR}"; \
		fi; \
		mkdir -p "$${TEST_LOG_DIR}"; \
		echo -e ""; \
		echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		echo -e "$(CYAN)[BENCH] Test $${TOTAL}: $${test}$(RESET)"; \
		echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		if $(MAKE) --no-print-directory run_verilator \
			TEST_NAME=$${test} \
			TEST_TYPE=bench \
			NO_ADDR=1 \
			MAX_CYCLES=$(MAX_CYCLES) \
			VERILATOR_LOG_DIR=$${TEST_LOG_DIR} > "$${TEST_LOG_DIR}/summary.log" 2>&1; then \
			PASS=$$(( $${PASS} + 1 )); \
			echo "$${test}" >> "$(PASS_LIST_FILE)"; \
			echo -e "$(GREEN)✓ $${test} PASSED$(RESET)"; \
		else \
			TEST_EXIT=$$?; \
			FAIL=$$(( $${FAIL} + 1 )); \
			echo "$${test}" >> "$(FAIL_LIST_FILE)"; \
			echo -e "$(RED)✗ $${test} FAILED (exit code: $${TEST_EXIT})$(RESET)"; \
			echo -e "$(YELLOW)  ↳ Summary log: $${TEST_LOG_DIR}/summary.log$(RESET)"; \
		fi; \
	done < "$(FLIST)"; \
	echo -e ""; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN) Benchmark Summary$(RESET)"; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN)✅ Passed: $${PASS}$(RESET)"; \
	echo -e "$(RED)❌ Failed: $${FAIL}$(RESET)"; \
	echo -e "$(CYAN)📊 Total:  $${TOTAL}$(RESET)"; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	if [ $${FAIL} -gt 0 ]; then \
		echo -e "$(RED)⚠️  $${FAIL} benchmark(s) failed$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)🎉 All benchmarks passed!$(RESET)"; \
	fi

# -----------------------------------------
# Quick Single Test Shortcuts
# -----------------------------------------
.PHONY: t tb

# Quick ISA test: make t T=rv32ui-p-add
t:
ifndef T
	$(error Usage: make t T=<test_name>)
endif
	@$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=$(T) \
		TEST_TYPE=isa \
		SIM=verilator

# Quick benchmark test: make tb T=dhrystone
tb:
ifndef T
	$(error Usage: make tb T=<benchmark_name>)
endif
	@$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=$(T) \
		TEST_TYPE=bench \
		NO_ADDR=1 \
		MAX_CYCLES=$(or $(MAX_CYCLES),1000000) \
		SIM=verilator

# -----------------------------------------
# Help
# -----------------------------------------
.PHONY: help_lists

help_lists:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)            CERES RISC-V — Test List Shortcuts                $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Test List Commands:$(RESET)"
	@echo -e "  $(GREEN)make isa$(RESET)         – Run all ISA tests (rv32ui, rv32um, rv32uc)"
	@echo -e "  $(GREEN)make csr$(RESET)         – Run machine CSR tests (rv32mi)"
	@echo -e "  $(GREEN)make bench$(RESET)       – Run benchmarks (dhrystone, etc.) [NO_ADDR=1]"
	@echo -e "  $(GREEN)make arch$(RESET)        – Run architecture tests (riscv-arch-test)"
	@echo -e "  $(GREEN)make all_tests$(RESET)   – Run ALL tests"
	@echo -e "  $(GREEN)make exc$(RESET)         – Run exception tests"
	@echo -e ""
	@echo -e "$(YELLOW)CoreMark Commands:$(RESET)"
	@echo -e "  $(GREEN)make cm$(RESET)          – Build and run CoreMark"
	@echo -e "  $(GREEN)make cm_run$(RESET)      – Quick CoreMark run (skip rebuild if exists)"
	@echo -e "  $(GREEN)make coremark$(RESET)    – Build CoreMark only"
	@echo -e "  $(GREEN)make coremark_help$(RESET)– Show detailed CoreMark help"
	@echo -e ""
	@echo -e "$(YELLOW)Quick Single Test:$(RESET)"
	@echo -e "  $(GREEN)make t T=rv32ui-p-add$(RESET)     – Quick ISA test"
	@echo -e "  $(GREEN)make tb T=dhrystone$(RESET)       – Quick benchmark [NO_ADDR=1]"
	@echo -e "  $(GREEN)make ta T=I-add-01$(RESET)        – Quick arch test"
	@echo -e ""
	@echo -e "$(YELLOW)Options:$(RESET)"
	@echo -e "  SIM=verilator|modelsim  – Simulator (default: verilator)"
	@echo -e "  MAX_CYCLES=<n>          – Max cycles (default: 100000)"
	@echo -e "  FAST_SIM=1              – Disable all logging for speed"
	@echo -e "  CLEAN_LOGS=1            – Clear all logs before batch run"
	@echo -e ""
	@echo -e "$(YELLOW)Architecture Test Pipeline:$(RESET)"
	@echo -e "  $(GREEN)make arch_auto$(RESET)   – Full pipeline: Clone → Build → Import"
	@echo -e "  $(GREEN)make arch_list$(RESET)   – List available arch test extensions"
	@echo -e "  $(GREEN)make arch_help$(RESET)   – Show detailed arch test help"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make isa SIM=verilator"
	@echo -e "  make bench MAX_CYCLES=5000000"
	@echo -e "  make bench CLEAN_LOGS=1          # Clear old logs first"
	@echo -e "  make t T=rv32ui-p-add"
	@echo -e "  make tb T=median MAX_CYCLES=500000"
	@echo -e "  make ta T=I-add-01"
	@echo -e "  make t T=rv32ui-p-add FAST_SIM=1  # Fast simulation without logs"
	@echo -e "  make cm                           # Run CoreMark"
	@echo -e "  make cm MAX_CYCLES=10000000       # CoreMark with more cycles"
	@echo -e ""
