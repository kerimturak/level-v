# ============================================================
# CERES RISC-V Test Runner (Debug + Fixed)
# ============================================================

# ============================================================
# Test Type: isa / bench (manual selection)
# ============================================================
# Usage:
#   make run TEST_NAME=median TEST_TYPE=bench
#   make run TEST_NAME=rv32ui-p-add TEST_TYPE=isa

ifeq ($(TEST_TYPE),bench)
    TEST_ROOT := $(BUILD_DIR)/tests/riscv-benchmarks
else ifeq ($(TEST_TYPE),isa)
    TEST_ROOT := $(BUILD_DIR)/tests/riscv-tests
else
    $(error Invalid TEST_TYPE="$(TEST_TYPE)". Use: isa or bench)
endif

# Paths for ELF/MEM/HEX/DUMP/ADDR
ELF_DIR  := $(TEST_ROOT)/elf
MEM_DIR  := $(TEST_ROOT)/mem
HEX_DIR  := $(TEST_ROOT)/hex
DUMP_DIR := $(TEST_ROOT)/dump
ADDR_DIR := $(TEST_ROOT)/pass_fail_addr


.PHONY: run test_prepare run_rtl run_spike compare_logs test_report clean_test list_tests help_test run_flist

# ============================================================
#  Exception Test Address Override
# ============================================================

EXCEPTION_ADDR_FILE := /home/kerim/level-v/sim/test/exception_test.flist

define GET_EXCEPTION_ADDR
$(shell awk '$$1=="$(1)" {print $$2" " $$3}' $(EXCEPTION_ADDR_FILE) 2>/dev/null)
endef


# ============================================================
# Main Pipeline
# ============================================================
run: test_prepare run_rtl run_spike compare_logs test_report

# ============================================================
# 1️⃣ Prepare Test Environment
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
	@echo -e "$(YELLOW)[INFO]$(RESET) ELF File     : $(ELF_DIR)/$(TEST_NAME)"
	@echo -e "$(YELLOW)[INFO]$(RESET) MEM File     : $(MEM_DIR)/$(TEST_NAME).mem"
	@echo -e "$(YELLOW)[INFO]$(RESET) HEX File     : $(HEX_DIR)/$(TEST_NAME).hex"
	@echo -e "$(YELLOW)[INFO]$(RESET) DUMP File    : $(DUMP_DIR)/$(TEST_NAME).dump"
	@echo -e "$(YELLOW)[INFO]$(RESET) ADDR File    : $(ADDR_DIR)/$(TEST_NAME)_addr.txt"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MKDIR) "$(TEST_LOG_DIR)" "$(TEST_WORK_DIR)"
	@echo "=== CERES Test Report ==="        >  $(REPORT_FILE)
	@echo "Test: $(TEST_NAME)"              >> $(REPORT_FILE)
	@echo "Date: $$(date)"                  >> $(REPORT_FILE)
	@echo "Simulator: $(SIM)"               >> $(REPORT_FILE)
	@echo ""                                >> $(REPORT_FILE)

# ============================================================
# 2️⃣ Run RTL Simulation
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
		2>&1 | tee $(RTL_LOG); \
	RTL_EXIT=$$?; \
	echo "RTL_EXIT_CODE=$$RTL_EXIT" >> $(REPORT_FILE); \
	if [ $$RTL_EXIT -ne 0 ]; then \
		echo -e "$(RED)[ERROR]$(RESET) RTL simulation failed with exit code $$RTL_EXIT"; \
		exit $$RTL_EXIT; \
	fi
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
	@echo -e "$(RED)❌ Unknown simulator: $(SIM)$(RESET)"
	@echo -e "   Valid options: verilator, modelsim"
	@exit 1
endif
	@echo -e "$(GREEN)✓ RTL simulation complete$(RESET)"

# ============================================================
# 3️⃣ Run Spike Golden Reference
# ============================================================
run_spike:
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
	echo -e "$(GREEN)✓ Using PASS address: $$PASS_ADDR$(RESET)"; \
	DEBUG_CMD="$(BUILD_DIR)/test_work/$(TEST_NAME)_spike.cmd"; \
	echo -e "until pc 0 $$PASS_ADDR\nquit" > "$$DEBUG_CMD"; \
	$(SPIKE) -d --isa=RV32IMC --pc=0x80000000 --log-commits \
		--debug-cmd="$$DEBUG_CMD" \
		$(ELF_DIR)/$(TEST_NAME) \
		2>&1 | tee $(SPIKE_LOG); \
	SPIKE_EXIT=$$?; \
	echo "SPIKE_EXIT_CODE=$$SPIKE_EXIT" >> $(REPORT_FILE); \
	if [ $$SPIKE_EXIT -ne 0 ]; then \
		echo -e "$(YELLOW)[WARNING]$(RESET) Spike exited with code $$SPIKE_EXIT (may be normal)"; \
	fi; \
	echo -e "$(GREEN)✓ Spike execution complete$(RESET)"

# ============================================================
# 4️⃣ Compare Logs
# ============================================================
compare_logs:
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Step 3/3: Comparing RTL vs Spike$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"

	@if [ "$(SIM)" = "verilator" ]; then \
		RTL_LOG_PATH="$(RTL_LOG_DIR)/commit_trace.log"; \
	elif [ "$(SIM)" = "modelsim" ]; then \
		RTL_LOG_PATH="$(RTL_LOG_DIR)/commit_trace.log"; \
	else \
		echo -e "$(RED)[ERROR]$(RESET) Unknown SIM=$(SIM)"; exit 1; \
	fi; \
	echo -e "$(CYAN)[DEBUG]$(RESET) RTL log path: $$RTL_LOG_PATH"; \
	echo -e "$(CYAN)[DEBUG]$(RESET) Spike log path: $(SPIKE_LOG)"; \
	echo -e "$(CYAN)[DEBUG]$(RESET) Diff output: $(DIFF_LOG)"; \
	if [ ! -f "$$RTL_LOG_PATH" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) RTL log not found at $$RTL_LOG_PATH"; \
		echo "COMPARE_STATUS=RTL_LOG_MISSING" >> $(REPORT_FILE); \
		exit 1; \
	fi; \
	if [ ! -f "$(SPIKE_LOG)" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Spike log not found at $(SPIKE_LOG)"; \
		echo "COMPARE_STATUS=SPIKE_LOG_MISSING" >> $(REPORT_FILE); \
		exit 1; \
	fi; \
	DUMP_FILE="$(DUMP_DIR)/$(TEST_NAME).dump"; \
	ADDR_FILE="$(ADDR_DIR)/$(TEST_NAME)_addr.txt"; \
	EXTRA_ARGS=""; \
	if [ -f "$$DUMP_FILE" ]; then \
		echo -e "$(GREEN)✓$(RESET) Found disassembly: $$DUMP_FILE"; \
		EXTRA_ARGS="$$EXTRA_ARGS --dump $$DUMP_FILE"; \
	else \
		echo -e "$(YELLOW)[INFO]$(RESET) No disassembly file found (optional)"; \
	fi; \
	if [ -f "$$ADDR_FILE" ]; then \
		echo -e "$(GREEN)✓$(RESET) Found address file: $$ADDR_FILE"; \
		EXTRA_ARGS="$$EXTRA_ARGS --addr $$ADDR_FILE"; \
	else \
		echo -e "$(YELLOW)[INFO]$(RESET) No address file found (optional)"; \
	fi; \
	echo -e "$(YELLOW)[INFO]$(RESET) Comparing RTL vs Spike..."; \
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
		echo -e "$(GREEN)✓ Logs match!$(RESET)"; \
	else \
		echo "COMPARE_STATUS=MISMATCH" >> $(REPORT_FILE); \
		echo "COMPARE_EXIT_CODE=$$COMPARE_EXIT" >> $(REPORT_FILE); \
		echo -e "$(RED)✗ Logs differ (exit code: $$COMPARE_EXIT)$(RESET)"; \
		exit $$COMPARE_EXIT; \
	fi


# ============================================================
# 5️⃣ Generate Final Test Report
# ============================================================
test_report:
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
# ============================================================
# 6️⃣ Batch Test Execution from File
# ============================================================
run_flist:
	@if [ ! -f "$(FLIST)" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Test list file not found: $(FLIST)"; \
		exit 1; \
	fi
	@$(MKDIR) "$(LOG_DIR)"
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
			echo -e "$(GREEN)✓ $${test} PASSED$(RESET)"; \
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
	echo -e "$(RED)❌ Failed: $${FAIL}$(RESET)"; \
	echo -e "$(CYAN)📊 Total:  $${TOTAL}$(RESET)"; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN)Passed tests:$(RESET) $(PASS_LIST_FILE)"; \
	echo -e "$(RED)Failed tests:$(RESET) $(FAIL_LIST_FILE)"; \
	if [ $${FAIL} -gt 0 ]; then \
		echo -e "$(RED)⚠️  $${FAIL} test(s) failed$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)🎉 All tests passed!$(RESET)"; \
	fi
