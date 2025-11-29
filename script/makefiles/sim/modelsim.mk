# =========================================
# CERES RISC-V — ModelSim / Questa Simulation
# =========================================

# -----------------------------------------
# ModelSim Paths
# -----------------------------------------
MODELSIM_LOG_DIR := $(LOG_DIR)/modelsim/$(TEST_NAME)

# -----------------------------------------
# Compilation Options
# -----------------------------------------
VLOG_OPTS := -sv -mfcu +acc=npr +incdir+$(INC_DIRS) \
             -work $(WORK_DIR) -svinputport=relaxed \
             -suppress vlog-2583 -suppress vlog-2275

# -----------------------------------------
# Simulation Flags
# -----------------------------------------
VSIM_FLAGS_BASE := -t ns -voptargs=+acc=npr +notimingchecks \
             +define+TRACER_EN=1 +test_name=$(TEST_NAME) \
             +sim=modelsim +define+KONATA_TRACE $(SV_DEFINES) \
             +simulator=modelsim

DO_FILE    ?= $(SIM_DIR)/do/questa.do
VSIM_LOG   := $(LOG_DIR)/vsim_$(shell date +%Y%m%d_%H%M%S).log

# =========================================
# Targets
# =========================================

.PHONY: $(WORK_DIR) compile resolve_mem simulate clean_modelsim modelsim_help

# ============================================================
# Library Creation
# ============================================================
$(WORK_DIR):
	@echo -e "$(YELLOW)[CREATING WORK LIBRARY]$(RESET)"
	@$(MKDIR) "$(MODELSIM_LOG_DIR)"
	$(VLIB) $(WORK_DIR)

# ============================================================
# Compilation
# ============================================================
compile: $(WORK_DIR)
	@echo -e "$(YELLOW)[COMPILING RTL SOURCES]$(RESET)"
	@$(MKDIR) "$(MODELSIM_LOG_DIR)"
	@($(VLOG) $(VLOG_OPTS) \
		$(SV_SOURCES) $(TB_FILE) 2>&1 | tee "$(MODELSIM_LOG_DIR)/compile.log"); \
	EXIT_CODE=$$?; \
	if [ $$EXIT_CODE -ne 0 ]; then \
		echo -e "$(RED)❌ Compilation failed.$(RESET)"; exit $$EXIT_CODE; \
	elif grep -i "Error" $(MODELSIM_LOG_DIR)/compile.log | grep -v "Errors: 0" >/dev/null; then \
		echo -e "$(RED)❌ Errors found in log.$(RESET)"; exit 1; \
	else \
		echo -e "$(GREEN)Compilation successful.$(RESET)"; \
	fi

# ============================================================
# Resolve Memory File (TEST_NAME -> absolute path)
# ============================================================
resolve_mem:
	@if [ -z "$(TEST_NAME)" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) TEST_NAME not provided (use TEST_NAME=<name>)."; \
		exit 1; \
	fi; \
	MATCH=""; \
	for dir in $(MEM_DIRS); do \
		if [ -f "$$dir/$(TEST_NAME).mem" ]; then MATCH="$$dir/$(TEST_NAME).mem"; break; fi; \
		if [ -f "$$dir/$(TEST_NAME).hex" ]; then MATCH="$$dir/$(TEST_NAME).hex"; break; fi; \
	done; \
	if [ -z "$$MATCH" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Could not find $(TEST_NAME).mem in: $(MEM_DIRS)"; \
		exit 1; \
	fi; \
	ABS="$$(cd $$(dirname $$MATCH) && pwd)/$$(basename $$MATCH)"; \
	MEM_TMP="$(BUILD_DIR)/.mem_path_$(TEST_NAME).tmp"; \
	echo -e "MEM_FILE=$$ABS" > "$$MEM_TMP"; \
	echo -e "$(GREEN)[OK]$(RESET) Found memory file:"; echo -e "       → $$ABS"


# ============================================================
# Simulation
# ============================================================
simulate: compile
	@# Clean previous logs for this test
	@if [ -d "$(MODELSIM_LOG_DIR)" ]; then \
		echo -e "$(CYAN)[CLEAN]$(RESET) Removing previous logs: $(MODELSIM_LOG_DIR)"; \
		rm -rf "$(MODELSIM_LOG_DIR)"; \
	fi
	@if [ -z "$(MEM_FILE)" ]; then \
		echo -e "$(YELLOW)[INFO]$(RESET) Resolving MEM_FILE from TEST_NAME='$(TEST_NAME)'..."; \
		$(MAKE) --no-print-directory resolve_mem TEST_NAME=$(TEST_NAME); \
		MEM_FILE=$$(grep MEM_FILE "$(BUILD_DIR)/.mem_path_$(TEST_NAME).tmp" | cut -d'=' -f2); \
	else \
		if echo -e "$(MEM_FILE)" | grep -q '/'; then \
			MF_DIR=$$(dirname "$(MEM_FILE)"); MF_BASE=$$(basename "$(MEM_FILE)"); \
			MEM_FILE="$$(cd $$MF_DIR && pwd)/$$MF_BASE"; \
		else \
			MATCH=""; \
			for dir in $(MEM_DIRS); do \
				if [ -f "$$dir/$(MEM_FILE)" ]; then MATCH="$$dir/$(MEM_FILE)"; break; fi; \
			done; \
			if [ -z "$$MATCH" ]; then echo -e "$(RED)[ERROR]$(RESET) MEM_FILE not found"; exit 1; fi; \
			MEM_FILE=$$(cd $$(dirname $$MATCH) && pwd)/$$(basename $$MATCH); \
		fi; \
	fi; \
	rm -f "$(BUILD_DIR)/.mem_path_$(TEST_NAME).tmp" || true; \
	ADDR_FILE="$(BUILD_DIR)/tests/riscv-tests/pass_fail_addr/$(TEST_NAME)_addr.txt"; \
	if [ -f "$$ADDR_FILE" ]; then \
		echo -e "$(GREEN)[INFO]$(RESET) Using +addr_file => $$ADDR_FILE"; \
		VSIM_FLAGS="$(VSIM_FLAGS_BASE) +addr_file=$$ADDR_FILE"; \
	else \
		echo -e "$(YELLOW)[WARN]$(RESET) No addr_file found, skipping."; \
		VSIM_FLAGS="$(VSIM_FLAGS_BASE)"; \
	fi; \
	echo -e "$(YELLOW)[INFO]$(RESET) Using INIT_FILE:"; echo -e "       → $$MEM_FILE"; \
	@$(MKDIR) "$(MODELSIM_LOG_DIR)"; \
	TRACE_ARG="+trace_file=$(MODELSIM_LOG_DIR)/commit_trace.log"; \
	LOG_ARG="+log_path=$(MODELSIM_LOG_DIR)/ceres.log"; \
	DUMP_ARG="+DUMP_FILE=$(MODELSIM_LOG_DIR)/waveform.wlf"; \
	if [ "$(GUI)" = "1" ]; then \
		echo -e "$(YELLOW)[RUN]$(RESET) GUI Mode"; \
		$(VSIM) build/work.$(TB_LEVEL) -do $(DO_FILE) $$VSIM_FLAGS $$TRACE_ARG $$LOG_ARG $$DUMP_ARG \
			+INIT_FILE="$$MEM_FILE" +UVM_TESTNAME=$(TEST_NAME); \
	else \
		echo -e "$(YELLOW)[RUN]$(RESET) Batch Mode"; \
		( $(VSIM) -c build/work.$(TB_LEVEL) \
			-do "run $(SIM_TIME); quit" $$VSIM_FLAGS $$TRACE_ARG $$LOG_ARG $$DUMP_ARG \
			+INIT_FILE="$$MEM_FILE" +UVM_TESTNAME=$(TEST_NAME) \
			2>&1 | tee "$(MODELSIM_LOG_DIR)/modelsim_run.log" ); \
		VSIM_EXIT=$$?; \
		printf '{"test":"%s","mem_file":"%s","exit_code":%s,"log_dir":"%s"}\n' "$(TEST_NAME)" "$$MEM_FILE" "$$VSIM_EXIT" "$(MODELSIM_LOG_DIR)" > "$(MODELSIM_LOG_DIR)/summary.json"; \
	fi; \
	echo -e "$(GREEN)Logs saved under: $(MODELSIM_LOG_DIR)$(RESET)"


# ============================================================
# Clean
# ============================================================
clean_modelsim:
	@echo -e "$(RED)[CLEANING MODELSIM FILES]$(RESET)"
	@$(RM) "$(WORK_DIR)" "transcript" "vsim.wlf" "modelsim.ini" || true
	@$(RM) "$(LOG_DIR)/rtl/modelsim" || true
	@echo -e "$(GREEN)ModelSim clean complete.$(RESET)"

# ============================================================
# Help
# ============================================================
modelsim_help:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)        CERES RISC-V — ModelSim / Questa Simulation            $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Main Targets:$(RESET)"
	@echo -e "  $(GREEN)compile        $(RESET)– Compile all RTL + Testbench sources"
	@echo -e "  $(GREEN)simulate       $(RESET)– Run simulation (auto memory resolve)"
	@echo -e "  $(GREEN)clean_modelsim $(RESET)– Clean ModelSim/Questa build artifacts"
	@echo -e ""
	@echo -e "$(YELLOW)Parameters:$(RESET)"
	@echo -e "  TEST_NAME=<name>   – Select test to run"
	@echo -e "  GUI=1         – Launch ModelSim GUI"
	@echo -e "  SIM_TIME=<t>  – Simulation time (default: $(SIM_TIME))"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make compile"
	@echo -e "  make simulate TEST_NAME=rv32ui-p-add GUI=1"
	@echo -e "  make simulate TEST_NAME=rv32uc-p-rvc SIM_TIME=50000ns"
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"