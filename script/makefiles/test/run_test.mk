# ============================================================
# CERES RISC-V Test Runner
# ============================================================
# Usage:
#   make run T=rv32ui-p-add         # Auto-detects TEST_TYPE=isa
#   make run T=C-ADDI-01            # Auto-detects TEST_TYPE=arch
#   make run T=median               # Auto-detects TEST_TYPE=bench
#   make run T=I-ADD-01             # Auto-detects TEST_TYPE=imperas
#   make run TEST_NAME=xxx TEST_TYPE=yyy  # Manual override
# ============================================================


# Test tipi ve dosya/dizin mapping'i artık test_types.mk'den otomatik geliyor.
# Sadece test_types.mk'yi include etmek yeterli.

# -----------------------------------------
# Test Type Based Paths
# -----------------------------------------
# NOT: TEST_ROOT, ELF_DIR, MEM_DIR, HEX_DIR, DUMP_DIR, ADDR_DIR, ELF_EXT
# değişkenleri artık config/test_types.mk'de merkezi olarak tanımlanıyor.
# Yeni bir test tipi eklemek için sadece test_types.mk'deki tabloya satır ekleyin.
#
# Burada sadece ELF_FILE'ı tanımlıyoruz (backward compat için):
ELF_FILE ?= $(ELF_DIR)/$(TEST_NAME)$(ELF_EXT)

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

.PHONY: run test_prepare run_rtl run_spike compare_logs test_report clean_test list_tests help_test run_flist


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
	@echo -e "$(RED)❌ Unknown simulator: $(SIM)$(RESET)"
	@echo -e "   Valid options: verilator, icarus, modelsim"
	@exit 1
endif
	@echo -e "$(GREEN)✓ RTL simulation complete$(RESET)"

# ============================================================
# 3️⃣ Run Spike Golden Reference
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
	echo -e "$(GREEN)✓ Using PASS address: $$PASS_ADDR$(RESET)"; \
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
	echo -e "$(GREEN)✓ Spike execution complete$(RESET)"
endif

# ============================================================
# 4️⃣ Compare Logs
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
		echo -e "$(GREEN)✓ Logs match!$(RESET)"; \
	else \
		echo "COMPARE_STATUS=MISMATCH" >> $(REPORT_FILE); \
		echo -e "$(RED)✗ Logs differ$(RESET)"; \
		exit $$COMPARE_EXIT; \
	fi
endif


# ============================================================
# 5️⃣ Generate Final Test Report
# ============================================================
test_report:
ifeq ($(CFG_COMPARE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Benchmark Run Complete$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo "BENCHMARK_STATUS=COMPLETE" >> $(REPORT_FILE)
	@echo -e "$(GREEN)✓ RTL simulation finished$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Check UART log for benchmark output"
else ifeq ($(CFG_SPIKE),0)
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Benchmark Run Complete$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo "BENCHMARK_STATUS=COMPLETE" >> $(REPORT_FILE)
	@echo -e "$(GREEN)✓ RTL simulation finished$(RESET)"
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
# 6️⃣ Batch Test Execution from File
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


# ============================================================
# 7️⃣ Generate HTML Test Dashboard
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
	@echo -e "$(GREEN)✓ Dashboard generated successfully$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Open with: xdg-open $(DASHBOARD_OUTPUT)"

open_dashboard: dashboard
	@xdg-open "$(DASHBOARD_OUTPUT)" 2>/dev/null || open "$(DASHBOARD_OUTPUT)" 2>/dev/null || echo "Please open $(DASHBOARD_OUTPUT) in a browser"
