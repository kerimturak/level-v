# ============================================================
# CERES RISC-V Test Runner
# ============================================================
# Usage:
#   make run T=rv32ui-p-add         # Auto-detects TEST_TYPE=isa
#   make run T=C-ADDI-01            # Auto-detects TEST_TYPE=arch
#   make run T=median               # Auto-detects TEST_TYPE=bench
#   make run T=I-ADD-01             # Auto-detects TEST_TYPE=imperas
#   make run TEST_NAME=xxx TEST_TYPE=yyy  # Manual override
#
# Python Mode (recommended):
#   make run T=rv32ui-p-add USE_PYTHON=1
#   CERES_DEBUG=1 make run T=rv32ui-p-add USE_PYTHON=1  # With debug log
# ============================================================

# Python Test Runner
TEST_RUNNER_SCRIPT := $(SCRIPT_DIR)/python/makefile/test_runner.py
USE_PYTHON ?= 1

# Allow short form variable `T` to specify the test name (e.g. `make run T=rv32ui-p-add`).
# Prefer `T` if provided; otherwise fall back to any pre-existing `TEST_NAME`.
TEST_NAME := $(if $(T),$(T),$(TEST_NAME))

# Recompute per-test paths now that TEST_NAME is finalized so CLI `T=` works
TEST_LOG_DIR := $(RESULTS_DIR)/logs/$(SIM)/$(TEST_NAME)
RTL_LOG_DIR  := $(TEST_LOG_DIR)
RTL_LOG      := $(TEST_LOG_DIR)/rtl_sim.log
SPIKE_LOG    := $(TEST_LOG_DIR)/spike.log
DIFF_LOG     := $(TEST_LOG_DIR)/diff.log
REPORT_FILE  := $(TEST_LOG_DIR)/test_report.txt

# -----------------------------------------
# File-based TEST_TYPE Auto-detection
# -----------------------------------------
# If TEST_TYPE was auto-detected (not user-specified), verify by checking
# if the test file actually exists in the expected directory.
# This provides a fallback if pattern matching fails.

define DETECT_TEST_TYPE_FROM_FILES
$(if $(wildcard $(BUILD_DIR)/tests/riscv-tests/elf/$(TEST_NAME)),isa,\
$(if $(wildcard $(BUILD_DIR)/tests/riscv-tests/elf/$(TEST_NAME).elf),isa,\
$(if $(wildcard $(BUILD_DIR)/tests/riscv-arch-test/elf/$(TEST_NAME).elf),arch,\
$(if $(wildcard $(BUILD_DIR)/tests/imperas/elf/$(TEST_NAME).elf),imperas,\
$(if $(wildcard $(BUILD_DIR)/tests/riscv-benchmarks/elf/$(TEST_NAME)),bench,\
$(if $(wildcard $(BUILD_DIR)/tests/dhrystone/$(TEST_NAME).elf),dhrystone,\
$(if $(wildcard $(BUILD_DIR)/tests/embench/elf/$(TEST_NAME).elf),embench,\
$(if $(wildcard $(BUILD_DIR)/tests/torture/elf/$(TEST_NAME).elf),torture,\
$(if $(wildcard $(BUILD_DIR)/tests/custom/$(TEST_NAME).elf),custom,\
$(TEST_TYPE))))))))))
endef

# Apply file-based detection as a verification/fallback
TEST_TYPE := $(strip $(call DETECT_TEST_TYPE_FROM_FILES))

# -----------------------------------------
# Test Type Based Paths
# -----------------------------------------
ifeq ($(TEST_TYPE),bench)
    TEST_ROOT := $(BUILD_DIR)/tests/riscv-benchmarks
else ifeq ($(TEST_TYPE),isa)
    TEST_ROOT := $(BUILD_DIR)/tests/riscv-tests
else ifeq ($(TEST_TYPE),arch)
    TEST_ROOT := $(BUILD_DIR)/tests/riscv-arch-test
else ifeq ($(TEST_TYPE),imperas)
    TEST_ROOT := $(BUILD_DIR)/tests/imperas
else ifeq ($(TEST_TYPE),dhrystone)
    TEST_ROOT := $(BUILD_DIR)/tests/dhrystone
else ifeq ($(TEST_TYPE),embench)
    TEST_ROOT := $(BUILD_DIR)/tests/embench
else ifeq ($(TEST_TYPE),torture)
    TEST_ROOT := $(BUILD_DIR)/tests/torture
else ifeq ($(TEST_TYPE),riscv-dv)
    TEST_ROOT := $(BUILD_DIR)/tests/riscv-dv
else ifeq ($(TEST_TYPE),custom)
    TEST_ROOT := $(BUILD_DIR)/tests/custom
else ifneq ($(MEM_DIR),)
    # If MEM_DIR is provided, skip TEST_TYPE validation (custom paths)
    TEST_ROOT := $(dir $(MEM_DIR))
else
    $(error Invalid TEST_TYPE="$(TEST_TYPE)". Use: isa, bench, arch, imperas, dhrystone, embench, torture, riscv-dv, or custom)
endif

# Derived paths from TEST_ROOT (can be overridden)
ELF_DIR  ?= $(TEST_ROOT)/elf
MEM_DIR  ?= $(TEST_ROOT)/mem
HEX_DIR  ?= $(TEST_ROOT)/hex
DUMP_DIR ?= $(TEST_ROOT)/dump
ADDR_DIR ?= $(TEST_ROOT)/pass_fail_addr

# ELF file extension (arch, imperas, dhrystone, embench, torture, riscv-dv, custom use .elf)
ifeq ($(TEST_TYPE),arch)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),imperas)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),dhrystone)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),embench)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),torture)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),riscv-dv)
    ELF_EXT := .elf
else ifeq ($(TEST_TYPE),custom)
    ELF_EXT := .elf
else
    ELF_EXT :=
endif
ELF_FILE := $(ELF_DIR)/$(TEST_NAME)$(ELF_EXT)

# -----------------------------------------
# Exception Address Override
# -----------------------------------------
EXCEPTION_ADDR_FILE := $(SIM_DIR)/test/exception_test.flist

define GET_EXCEPTION_ADDR
$(shell awk '$$1=="$(1)" {print $$2" " $$3}' $(EXCEPTION_ADDR_FILE) 2>/dev/null)
endef

# =========================================
# Targets
# =========================================

.PHONY: run run_python run_make test_prepare run_rtl run_spike compare_logs test_report clean_test list_tests help_test run_flist


# ============================================================
# Main Pipeline
# ============================================================
ifeq ($(USE_PYTHON),1)
run: run_python
else
run: run_make
endif

run_make: test_prepare run_rtl run_spike compare_logs test_report

# Python-based test runner (USE_PYTHON=1)
run_python:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  CERES RISC-V Test Runner (Python Mode)$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@python3 $(TEST_RUNNER_SCRIPT) \
		--test-name "$(TEST_NAME)" \
		--test-type "$(TEST_TYPE)" \
		--simulator "$(SIM)" \
		--build-dir "$(BUILD_DIR)" \
		--sim-dir "$(SIM_DIR)" \
		--results-dir "$(RESULTS_DIR)" \
		--test-log-dir "$(TEST_LOG_DIR)" \
		--max-cycles $(MAX_CYCLES) \
		$(if $(filter 1,$(LOG_COMMIT)),--log-commit,) \
		$(if $(filter 1,$(LOG_BP)),--log-bp,) \
		$(if $(filter 1,$(KONATA_TRACER)),--konata-tracer,) \
		$(if $(filter 1,$(TRACE)),--trace,) \
		$(if $(filter 1,$(CFG_SPIKE)),--enable-spike,--no-spike) \
		$(if $(filter 1,$(CFG_COMPARE)),--enable-compare,--no-compare) \
		$(if $(SKIP_CSR),--skip-csr,) \
		$(if $(RESYNC),--resync --resync-window $(or $(RESYNC_WINDOW),8),)
	@echo -e "$(GREEN)$(SUCCESS) Python test runner completed$(RESET)"

# ============================================================
# 1 Prepare Test Environment
# ============================================================
test_prepare:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  CERES RISC-V Test Runner$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Test Name   : $(TEST_NAME)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Simulator   : $(SIM)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Max Cycles  : $(MAX_CYCLES)"
	@echo -e "$(YELLOW)[INFO]$(RESET) Test Log Dir: $(TEST_LOG_DIR)"
	@echo -e "$(YELLOW)[INFO]$(RESET) RTL Log Dir : $(RTL_LOG_DIR)"
	@echo -e "$(YELLOW)[INFO]$(RESET) ELF File     : $(ELF_FILE)"
	@echo -e "$(YELLOW)[INFO]$(RESET) MEM File     : $(MEM_DIR)/$(TEST_NAME).mem"
	@echo -e "$(YELLOW)[INFO]$(RESET) HEX File     : $(HEX_DIR)/$(TEST_NAME).hex"
	@echo -e "$(YELLOW)[INFO]$(RESET) DUMP File    : $(DUMP_DIR)/$(TEST_NAME).dump"
	@echo -e "$(YELLOW)[INFO]$(RESET) ADDR File    : $(ADDR_DIR)/$(TEST_NAME)_addr.txt"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@# Clean previous test logs to avoid stale data
	@if [ -d "$(RTL_LOG_DIR)" ]; then \
		echo -e "$(CYAN)[CLEAN]$(RESET) Removing previous logs: $(RTL_LOG_DIR)"; \
		rm -rf "$(RTL_LOG_DIR)"; \
	fi
	@$(MKDIR) "$(TEST_LOG_DIR)" "$(TEST_WORK_DIR)"
	@echo "=== CERES Test Report ==="        >  $(REPORT_FILE)
	@echo "Test: $(TEST_NAME)"              >> $(REPORT_FILE)
	@echo "Date: $$(date)"                  >> $(REPORT_FILE)
	@echo "Simulator: $(SIM)"               >> $(REPORT_FILE)
	@echo ""                                >> $(REPORT_FILE)

# ============================================================
# 2 Run RTL Simulation
# ============================================================
run_rtl:
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Step 1/3: Running RTL Simulation$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
ifeq ($(SIM),verilator)
	@echo -e "$(CYAN)[DEBUG]$(RESET) Calling Verilator with VERILATOR_LOG_DIR=$(RTL_LOG_DIR)"
	@$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=$(TEST_NAME) MAX_CYCLES=$(MAX_CYCLES) \
		VERILATOR_LOG_DIR=$(RTL_LOG_DIR) \
		MEM_FILE=$(MEM_DIR)/$(TEST_NAME).mem \
		ADDR_FILE=$(ADDR_DIR)/$(TEST_NAME)_addr.txt \
		2>&1 | tee $(RTL_LOG); \
	RTL_EXIT=$$?; \
	echo "RTL_EXIT_CODE=$$RTL_EXIT" >> $(REPORT_FILE); \
	if [ $$RTL_EXIT -ne 0 ]; then \
		echo -e "$(RED)[ERROR]$(RESET) RTL simulation failed with exit code $$RTL_EXIT"; \
		exit $$RTL_EXIT; \
	fi
else ifeq ($(SIM),icarus)
	@echo -e "$(RED)⚠ WARNING: Icarus Verilog does NOT support CERES RTL$(RESET)"
	@echo -e "$(RED)  CERES uses SystemVerilog 2012 features not supported by Icarus:$(RESET)"
	@echo -e "$(RED)  - 'inside' operator, 'automatic' variables, struct parameters$(RESET)"
	@echo -e "$(YELLOW)  Please use: make run SIM=verilator or make run SIM=modelsim$(RESET)"
	@exit 1
else ifeq ($(SIM),modelsim)
	@$(MAKE) --no-print-directory simulate TEST_NAME=$(TEST_NAME) GUI=0 \
		2>&1 | tee $(RTL_LOG); \
	RTL_EXIT=$$?; \
	echo "RTL_EXIT_CODE=$$RTL_EXIT" >> $(REPORT_FILE); \
	if [ $$RTL_EXIT -ne 0 ]; then \
		echo -e "$(RED)[ERROR]$(RESET) RTL simulation failed with exit code $$RTL_EXIT"; \
		exit $$RTL_EXIT; \
	fi
else
	@echo -e "$(RED)$(ERROR) Unknown simulator: $(SIM)$(RESET)"
	@echo -e "   Valid options: verilator, icarus, modelsim"
	@exit 1
endif
	@echo -e "$(GREEN)$(SUCCESS) RTL simulation complete$(RESET)"

# ============================================================
# 3 Run Spike Golden Reference
# ============================================================
run_spike:
ifeq ($(CFG_SPIKE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)  Step 2/3: Spike comparison disabled (benchmark mode)$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
else
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Step 2/3: Running Spike Golden Model$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MKDIR) "$(dir $(SPIKE_LOG))"

	@EXC_ADDRS="$(call GET_EXCEPTION_ADDR,$(TEST_NAME))"; \
	if [ -n "$$EXC_ADDRS" ]; then \
		echo -e "$(YELLOW)[INFO]$(RESET) Exception override for $(TEST_NAME): $$EXC_ADDRS"; \
		set -- $$EXC_ADDRS; \
		PASS_ADDR="$$1"; \
		FAIL_ADDR="$$2"; \
	else \
		ADDR_FILE="$(ADDR_DIR)/$(TEST_NAME)_addr.txt"; \
		if [ ! -f "$$ADDR_FILE" ]; then \
			echo -e "$(RED)[ERROR]$(RESET) Address file not found: $$ADDR_FILE"; \
			exit 1; \
		fi; \
		read PASS_ADDR FAIL_ADDR < "$$ADDR_FILE"; \
	fi; \
	echo -e "$(GREEN)$(SUCCESS) Using PASS address: $$PASS_ADDR$(RESET)"; \
	DEBUG_CMD="$(BUILD_DIR)/test_work/$(TEST_NAME)_spike.cmd"; \
	echo -e "until pc 0 $$PASS_ADDR\nquit" > "$$DEBUG_CMD"; \
	echo -e "$(CYAN)[DEBUG]$(RESET) Spike args: $(SPIKE_ARGS)"; \
	$(SPIKE) -d $(SPIKE_ARGS) \
		--debug-cmd="$$DEBUG_CMD" \
		$(ELF_FILE) \
		2>&1 | tee $(SPIKE_LOG); \
	SPIKE_EXIT=$$?; \
	echo "SPIKE_EXIT_CODE=$$SPIKE_EXIT" >> $(REPORT_FILE); \
	if [ $$SPIKE_EXIT -ne 0 ]; then \
		echo -e "$(YELLOW)[WARNING]$(RESET) Spike exited with code $$SPIKE_EXIT (may be normal)"; \
	fi; \
	echo -e "$(GREEN)$(SUCCESS) Spike execution complete$(RESET)"
endif

# ============================================================
# 4 Compare Logs
# ============================================================
compare_logs:
ifeq ($(CFG_COMPARE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)  Step 3/3: Log comparison disabled (benchmark mode)$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo "COMPARE_STATUS=SKIPPED" >> $(REPORT_FILE)
else ifeq ($(CFG_SPIKE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)  Step 3/3: Log comparison skipped (no Spike run)$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo "COMPARE_STATUS=SKIPPED" >> $(REPORT_FILE)
else
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Step 3/3: Comparing RTL vs Spike$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@RTL_LOG_PATH="$(RTL_LOG_DIR)/commit_trace.log"; \
	echo -e "$(CYAN)[DEBUG]$(RESET) RTL log: $$RTL_LOG_PATH"; \
	echo -e "$(CYAN)[DEBUG]$(RESET) Spike log: $(SPIKE_LOG)"; \
	if [ ! -f "$$RTL_LOG_PATH" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) RTL log not found"; \
		echo "COMPARE_STATUS=RTL_LOG_MISSING" >> $(REPORT_FILE); \
		exit 1; \
	fi; \
	if [ ! -f "$(SPIKE_LOG)" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Spike log not found"; \
		echo "COMPARE_STATUS=SPIKE_LOG_MISSING" >> $(REPORT_FILE); \
		exit 1; \
	fi; \
	EXTRA_ARGS=""; \
	[ -f "$(DUMP_DIR)/$(TEST_NAME).dump" ] && EXTRA_ARGS="$$EXTRA_ARGS --dump $(DUMP_DIR)/$(TEST_NAME).dump"; \
	[ -f "$(ADDR_DIR)/$(TEST_NAME)_addr.txt" ] && EXTRA_ARGS="$$EXTRA_ARGS --addr $(ADDR_DIR)/$(TEST_NAME)_addr.txt"; \
	$(MKDIR) "$(dir $(DIFF_LOG))"; \
	python3 $(SCRIPT_DIR)/python/makefile/compare_logs.py \
		--rtl "$$RTL_LOG_PATH" \
		--spike "$(SPIKE_LOG)" \
		--output "$(DIFF_LOG)" \
		--test-name "$(TEST_NAME)" \
		$$EXTRA_ARGS \
		$(if $(SKIP_CSR),--skip-csr,) \
		$(if $(RESYNC),--resync --window $(or $(RESYNC_WINDOW),8),) \
		2>&1 | tee -a $(REPORT_FILE); \
	COMPARE_EXIT=$$?; \
	if [ $$COMPARE_EXIT -eq 0 ]; then \
		echo "COMPARE_STATUS=MATCH" >> $(REPORT_FILE); \
		echo -e "$(GREEN)$(SUCCESS) Logs match!$(RESET)"; \
	else \
		echo "COMPARE_STATUS=MISMATCH" >> $(REPORT_FILE); \
		echo -e "$(RED)✗ Logs differ$(RESET)"; \
		exit $$COMPARE_EXIT; \
	fi
endif


# ============================================================
# 5 Generate Final Test Report
# ============================================================
test_report:
ifeq ($(CFG_COMPARE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Benchmark Run Complete$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo "BENCHMARK_STATUS=COMPLETE" >> $(REPORT_FILE)
	@echo -e "$(GREEN)$(SUCCESS) RTL simulation finished$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Check UART log for benchmark output"
else ifeq ($(CFG_SPIKE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Benchmark Run Complete$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo "BENCHMARK_STATUS=COMPLETE" >> $(REPORT_FILE)
	@echo -e "$(GREEN)$(SUCCESS) RTL simulation finished$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Check UART log for benchmark output"
else
	@if grep -q "PASS" $(REPORT_FILE); then \
		echo -e "$(GREEN)TEST PASSED$(RESET)"; \
		exit 0; \
	elif grep -q "FAIL" $(REPORT_FILE); then \
		echo -e "$(RED)TEST FAILED$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(YELLOW)TEST STATUS UNKNOWN$(RESET)"; \
		exit 1; \
	fi
endif
# ============================================================
# 6 Batch Test Execution from File
# ============================================================
run_flist:
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
	@echo -e "$(GREEN)Running tests from list file:$(RESET) $(FLIST)"
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
		echo -e "$(CYAN)[FLIST] Test $${TOTAL}: $${test}$(RESET)"; \
		echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		echo -e "$(CYAN)[INFO]$(RESET) Log directory: $$TEST_LOG_DIR"; \
		echo -e "$(CYAN)[INFO]$(RESET) ELF  : $(ELF_DIR)/$${test}"; \
		echo -e "$(CYAN)[INFO]$(RESET) MEM  : $(MEM_DIR)/$${test}.mem"; \
		echo -e "$(CYAN)[INFO]$(RESET) HEX  : $(HEX_DIR)/$${test}.hex"; \
		echo -e "$(CYAN)[INFO]$(RESET) DUMP : $(DUMP_DIR)/$${test}.dump"; \
		echo -e "$(CYAN)[INFO]$(RESET) ADDR : $(ADDR_DIR)/$${test}_addr.txt"; \
		if $(MAKE) --no-print-directory run \
			TEST_NAME=$${test} \
			SIM=$(SIM) \
			MAX_CYCLES=$(MAX_CYCLES) \
			SKIP_CSR=$(SKIP_CSR) \
			RESYNC=$(RESYNC) \
			RESYNC_WINDOW=$(RESYNC_WINDOW) \
			TEST_LOG_DIR=$${TEST_LOG_DIR} \
			RTL_LOG_DIR=$${TEST_LOG_DIR} > "$${TEST_LOG_DIR}/summary.log" 2>&1; then \
			PASS=$$(( $${PASS} + 1 )); \
			echo "$${test}" >> "$(PASS_LIST_FILE)"; \
			echo -e "$(GREEN)$(SUCCESS) $${test} PASSED$(RESET)"; \
		else \
			TEST_EXIT=$$?; \
			FAIL=$$(( $${FAIL} + 1 )); \
			echo "$${test}" >> "$(FAIL_LIST_FILE)"; \
			echo -e "$(RED)✗ $${test} FAILED (exit code: $${TEST_EXIT})$(RESET)"; \
			echo -e "$(YELLOW)  ↳ Summary log: $${TEST_LOG_DIR}/summary.log$(RESET)"; \
			echo -e "$(YELLOW)  ↳ HTML report: $${TEST_LOG_DIR}/diff.html$(RESET)"; \
			if [ -f "$${TEST_LOG_DIR}/test_report.txt" ]; then \
				echo -e "$(CYAN)[DEBUG]$(RESET) Report file preview:"; \
				head -20 "$${TEST_LOG_DIR}/test_report.txt"; \
			fi; \
		fi; \
	done < "$(FLIST)"; \
	echo -e ""; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN) File-Based Batch Summary$(RESET)"; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN)✅ Passed: $${PASS}$(RESET)"; \
	echo -e "$(RED)$(ERROR) Failed: $${FAIL}$(RESET)"; \
	echo -e "$(CYAN)📊 Total:  $${TOTAL}$(RESET)"; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN)Passed tests:$(RESET) $(PASS_LIST_FILE)"; \
	echo -e "$(RED)Failed tests:$(RESET) $(FAIL_LIST_FILE)"; \
	if [ $${FAIL} -gt 0 ]; then \
		echo -e "$(RED)$(WARN)  $${FAIL} test(s) failed$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)🎉 All tests passed!$(RESET)"; \
	fi


# ============================================================
# 7 Generate HTML Test Dashboard
# ============================================================
# Usage:
#   make html                    # Generate dashboard for verilator results
#   make html SIM=modelsim       # Generate dashboard for modelsim results
#   make html DASHBOARD_TITLE="My Tests"  # Custom title
# ============================================================
DASHBOARD_OUTPUT ?= $(RESULTS_DIR)/logs/dashboard.html
DASHBOARD_TITLE  ?= CERES Test Dashboard
DASHBOARD_SCRIPT := $(SCRIPT_DIR)/python/makefile/generate_test_dashboard.py

.PHONY: html dashboard open_dashboard

html: dashboard

dashboard:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Generating HTML Test Dashboard$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Results Dir : $(RESULTS_DIR)"
	@echo -e "$(CYAN)[INFO]$(RESET) Simulator   : $(SIM)"
	@echo -e "$(CYAN)[INFO]$(RESET) Output      : $(DASHBOARD_OUTPUT)"
	@python3 $(DASHBOARD_SCRIPT) \
		--results-dir "$(RESULTS_DIR)" \
		--simulator "$(SIM)" \
		--output "$(DASHBOARD_OUTPUT)" \
		--title "$(DASHBOARD_TITLE)"
	@echo -e "$(GREEN)$(SUCCESS) Dashboard generated successfully$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Open with: xdg-open $(DASHBOARD_OUTPUT)"

open_dashboard: dashboard
	@xdg-open "$(DASHBOARD_OUTPUT)" 2>/dev/null || open "$(DASHBOARD_OUTPUT)" 2>/dev/null || echo "Please open $(DASHBOARD_OUTPUT) in a browser"
