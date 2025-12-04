# =========================================
# CERES RISC-V — ModelSim / Questa Simulation
# =========================================
# NOT: LOG/SIM/TRACE kontrolleri sim/common.mk'de merkezi olarak yönetiliyor.
#      common.mk ana makefile tarafından include edilir.

# -----------------------------------------
# Configuration Loading (from JSON)
# -----------------------------------------
MODELSIM_CONFIG_SCRIPT := $(ROOT_DIR)/script/shell/parse_modelsim_config.sh
MODELSIM_CONFIG_FILE   := $(ROOT_DIR)/script/config/modelsim.json

# Load config if available and no explicit overrides
ifneq ($(wildcard $(MODELSIM_CONFIG_SCRIPT)),)
  ifneq ($(wildcard $(MODELSIM_CONFIG_FILE)),)
    # Check if jq is available
    JQ_EXISTS := $(shell command -v jq 2>/dev/null)
    ifdef JQ_EXISTS
      # Load profile if specified
      ifdef MODELSIM_PROFILE
        MODELSIM_CONFIG_ARGS := --profile $(MODELSIM_PROFILE)
      endif
      
      # Include generated config (only if not already set)
      -include $(BUILD_DIR)/.modelsim_config.mk
      
      # Generate config makefile
      $(BUILD_DIR)/.modelsim_config.mk: $(MODELSIM_CONFIG_FILE) $(wildcard $(ROOT_DIR)/script/config/modelsim.local.json)
		@mkdir -p $(BUILD_DIR)
		@$(MODELSIM_CONFIG_SCRIPT) --make $(MODELSIM_CONFIG_ARGS) > $@ 2>/dev/null || true
    endif
  endif
endif

# -----------------------------------------
# ModelSim Paths
# -----------------------------------------
MODELSIM_LOG_DIR := $(LOG_DIR)/modelsim/$(TEST_NAME)

# -----------------------------------------
# Default Values (can be overridden by JSON config)
# -----------------------------------------
MODELSIM_TIME_RES       ?= ns
MODELSIM_VOPTARGS       ?= +acc=npr
MODELSIM_SV_MODE        ?= -sv
MODELSIM_MFCU           ?= -mfcu
MODELSIM_SVINPUTPORT    ?= relaxed
MODELSIM_LINT_ENABLED   ?= 1
MODELSIM_LINT_MODE      ?= default
MODELSIM_PEDANTIC       ?=
MODELSIM_ACC            ?= npr
MODELSIM_FSMDEBUG       ?=
MODELSIM_CLASSDEBUG     ?=
MODELSIM_ASSERTDEBUG    ?=
MODELSIM_COVERAGE       ?=
MODELSIM_SV_COMPAT      ?= -sv12compat
MODELSIM_TIMESCALE      ?= 1ns/1ps
MODELSIM_NOTIMINGCHECKS ?= +notimingchecks
MODELSIM_NOSPECIFY      ?=
MODELSIM_DELAY_MODE     ?=
MODELSIM_SUPPRESS       ?= -suppress vlog-2583 -suppress vlog-2275
MODELSIM_NOWARN         ?=
MODELSIM_SOURCE         ?= -source
MODELSIM_MULTICORE      ?=
MODELSIM_QUIET          ?=

# -----------------------------------------
# Compilation Options
# -----------------------------------------
VLOG_BASE_OPTS := $(MODELSIM_SV_MODE) $(MODELSIM_MFCU) \
                  +acc=$(MODELSIM_ACC) +incdir+$(INC_DIRS) \
                  -work $(WORK_DIR) -svinputport=$(MODELSIM_SVINPUTPORT) \
                  $(MODELSIM_SUPPRESS) $(MODELSIM_NOWARN)

ifdef MODELSIM_SV_COMPAT
  VLOG_BASE_OPTS += $(MODELSIM_SV_COMPAT)
endif

# Timescale
VLOG_BASE_OPTS += -timescale "$(MODELSIM_TIMESCALE)"

# Coverage options
ifneq ($(MODELSIM_COVERAGE),)
  VLOG_BASE_OPTS += $(MODELSIM_COVERAGE)
endif

# Multicore options
ifneq ($(MODELSIM_MULTICORE),)
  VLOG_BASE_OPTS += $(MODELSIM_MULTICORE)
endif

# Standard compile opts (for backward compatibility)
VLOG_OPTS := $(VLOG_BASE_OPTS)

# -----------------------------------------
# Lint Options
# -----------------------------------------
# Lint mode configurations
ifeq ($(MODELSIM_LINT_MODE),full)
  VLOG_LINT_OPTS := -lint=full $(MODELSIM_PEDANTIC)
else ifeq ($(MODELSIM_LINT_MODE),fast)
  VLOG_LINT_OPTS := -lint=fast
else
  VLOG_LINT_OPTS := -lint
endif

# Full lint compile options
VLOG_LINT_FULL_OPTS := $(MODELSIM_SV_MODE) $(MODELSIM_MFCU) \
                       +incdir+$(INC_DIRS) -work $(WORK_DIR) \
                       -svinputport=$(MODELSIM_SVINPUTPORT) \
                       $(VLOG_LINT_OPTS) \
                       $(MODELSIM_SV_COMPAT) $(MODELSIM_SOURCE) \
                       $(MODELSIM_SUPPRESS) \
                       -timescale "$(MODELSIM_TIMESCALE)"

# -----------------------------------------
# Simulation Flags
# -----------------------------------------
VSIM_FLAGS_BASE := -t $(MODELSIM_TIME_RES) -voptargs=$(MODELSIM_VOPTARGS) \
                   $(MODELSIM_NOTIMINGCHECKS) $(MODELSIM_NOSPECIFY) \
                   $(MODELSIM_DELAY_MODE) \
                   +define+COMMIT_TRACER=1 +test_name=$(TEST_NAME) \
                   +sim=modelsim +define+KONATA_TRACE $(SV_DEFINES) \
                   +simulator=modelsim $(MODELSIM_QUIET)

# Debug flags for simulation
ifneq ($(MODELSIM_FSMDEBUG),)
  VSIM_FLAGS_BASE += $(MODELSIM_FSMDEBUG)
endif

ifneq ($(MODELSIM_CLASSDEBUG),)
  VSIM_FLAGS_BASE += $(MODELSIM_CLASSDEBUG)
endif

ifneq ($(MODELSIM_ASSERTDEBUG),)
  VSIM_FLAGS_BASE += $(MODELSIM_ASSERTDEBUG)
endif

# Coverage in simulation
ifneq ($(MODELSIM_COVERAGE),)
  VSIM_FLAGS_BASE += -coverage
endif

DO_FILE    ?= $(SIM_DIR)/do/questa.do
VSIM_LOG   := $(LOG_DIR)/vsim_$(shell date +%Y%m%d_%H%M%S).log

# =========================================
# Targets
# =========================================

.PHONY: $(WORK_DIR) compile compile_lint lint_modelsim lint_report_modelsim \
        resolve_mem simulate clean_modelsim modelsim_help modelsim_config_summary

# ============================================================
# Library Creation
# ============================================================
$(WORK_DIR):
	@echo -e "$(YELLOW)[CREATING WORK LIBRARY]$(RESET)"
	@$(MKDIR) "$(MODELSIM_LOG_DIR)"
	$(VLIB) $(WORK_DIR)

# ============================================================
# Standard Compilation
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
# Lint Compilation (with lint checks enabled)
# ============================================================
compile_lint: $(WORK_DIR)
	@echo -e "$(YELLOW)[COMPILING RTL WITH LINT CHECKS]$(RESET)"
	@$(MKDIR) "$(MODELSIM_LOG_DIR)"
	@($(VLOG) $(VLOG_LINT_FULL_OPTS) \
		$(SV_SOURCES) 2>&1 | tee "$(MODELSIM_LOG_DIR)/lint_compile.log"); \
	EXIT_CODE=$$?; \
	echo -e "$(CYAN)════════════════════════════════════════$(RESET)"; \
	echo -e "$(CYAN)  Lint Compilation Summary$(RESET)"; \
	echo -e "$(CYAN)════════════════════════════════════════$(RESET)"; \
	ERR=$$(grep -c "^\\*\\* Error" "$(MODELSIM_LOG_DIR)/lint_compile.log" 2>/dev/null) || ERR=0; \
	WARN=$$(grep -c "^\\*\\* Warning" "$(MODELSIM_LOG_DIR)/lint_compile.log" 2>/dev/null) || WARN=0; \
	NOTE=$$(grep -c "^\\*\\* Note" "$(MODELSIM_LOG_DIR)/lint_compile.log" 2>/dev/null) || NOTE=0; \
	if [ "$$ERR" != "0" ]; then \
		echo -e "  $(RED)Errors:   $$ERR$(RESET)"; \
	else \
		echo -e "  $(GREEN)Errors:   0$(RESET)"; \
	fi; \
	if [ "$$WARN" != "0" ]; then \
		echo -e "  $(YELLOW)Warnings: $$WARN$(RESET)"; \
	else \
		echo -e "  $(GREEN)Warnings: 0$(RESET)"; \
	fi; \
	if [ "$$NOTE" != "0" ]; then \
		echo -e "  $(CYAN)Notes:    $$NOTE$(RESET)"; \
	fi; \
	echo -e "$(CYAN)════════════════════════════════════════$(RESET)"; \
	echo -e "$(GREEN)Log saved: $(MODELSIM_LOG_DIR)/lint_compile.log$(RESET)"

# ============================================================
# Lint — Full lint analysis with detailed report
# Output: results/lint/modelsim/
# ============================================================
MODELSIM_LINT_DIR := $(LINT_DIR)/modelsim

lint_modelsim: $(WORK_DIR)
	@echo -e "$(YELLOW)[MODELSIM LINT ANALYSIS]$(RESET)"
	@$(MKDIR) "$(MODELSIM_LINT_DIR)"
	@echo -e "$(CYAN)[INFO]$(RESET) Lint Mode: $(MODELSIM_LINT_MODE)"
	@echo -e "$(CYAN)[INFO]$(RESET) Output: $(MODELSIM_LINT_DIR)/"
	@($(VLOG) $(VLOG_LINT_FULL_OPTS) \
		$(SV_SOURCES) 2>&1 | tee "$(MODELSIM_LINT_DIR)/lint.log"); \
	echo ""; \
	echo -e "$(CYAN)════════════════════════════════════════$(RESET)"; \
	echo -e "$(CYAN)        ModelSim Lint Summary$(RESET)"; \
	echo -e "$(CYAN)════════════════════════════════════════$(RESET)"; \
	ERR=$$(grep -c "^\\*\\* Error" "$(MODELSIM_LINT_DIR)/lint.log" 2>/dev/null) || ERR=0; \
	WARN=$$(grep -c "^\\*\\* Warning" "$(MODELSIM_LINT_DIR)/lint.log" 2>/dev/null) || WARN=0; \
	NOTE=$$(grep -c "^\\*\\* Note" "$(MODELSIM_LINT_DIR)/lint.log" 2>/dev/null) || NOTE=0; \
	if [ "$$ERR" != "0" ]; then \
		echo -e "  $(RED)Errors:   $$ERR$(RESET)"; \
	else \
		echo -e "  $(GREEN)Errors:   0$(RESET)"; \
	fi; \
	if [ "$$WARN" != "0" ]; then \
		echo -e "  $(YELLOW)Warnings: $$WARN$(RESET)"; \
	else \
		echo -e "  $(GREEN)Warnings: 0$(RESET)"; \
	fi; \
	if [ "$$NOTE" != "0" ]; then \
		echo -e "  $(CYAN)Notes:    $$NOTE$(RESET)"; \
	fi; \
	echo -e "$(CYAN)════════════════════════════════════════$(RESET)"; \
	echo -e "  Log: $(MODELSIM_LINT_DIR)/lint.log"; \
	echo -e "$(CYAN)════════════════════════════════════════$(RESET)"

# ============================================================
# Lint Report — Categorized lint findings
# ============================================================
lint_report_modelsim:
	@if [ ! -f "$(MODELSIM_LINT_DIR)/lint.log" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) No lint log found. Run 'make lint_modelsim' first."; \
		exit 1; \
	fi
	@echo -e "$(CYAN)════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)        ModelSim Lint Detailed Report$(RESET)"
	@echo -e "$(CYAN)════════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(RED)═══ ERRORS ═══$(RESET)"
	@grep "^\\*\\* Error" "$(MODELSIM_LINT_DIR)/lint.log" 2>/dev/null || echo "  None"
	@echo ""
	@echo -e "$(YELLOW)═══ WARNINGS (by category) ═══$(RESET)"
	@echo -e "$(YELLOW)--- Width Issues ---$(RESET)"
	@grep -i "width" "$(MODELSIM_LINT_DIR)/lint.log" 2>/dev/null | head -20 || echo "  None"
	@echo ""
	@echo -e "$(YELLOW)--- Unconnected/Unused ---$(RESET)"
	@grep -iE "unconnected|unused|undriven" "$(MODELSIM_LINT_DIR)/lint.log" 2>/dev/null | head -20 || echo "  None"
	@echo ""
	@echo -e "$(YELLOW)--- Timing Issues ---$(RESET)"
	@grep -iE "timing|delay|latch" "$(MODELSIM_LINT_DIR)/lint.log" 2>/dev/null | head -20 || echo "  None"
	@echo ""
	@echo -e "$(YELLOW)--- Case/Default ---$(RESET)"
	@grep -iE "case|default" "$(MODELSIM_LINT_DIR)/lint.log" 2>/dev/null | head -20 || echo "  None"
	@echo ""
	@echo -e "$(CYAN)═══ NOTES ═══$(RESET)"
	@grep "^\\*\\* Note" "$(MODELSIM_LINT_DIR)/lint.log" 2>/dev/null | head -10 || echo "  None"
	@echo ""
	@echo -e "$(CYAN)════════════════════════════════════════════════════════════$(RESET)"

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
# Configuration Summary
# ============================================================
modelsim_config_summary:
	@echo -e "$(CYAN)════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)        ModelSim Configuration Summary$(RESET)"
	@echo -e "$(CYAN)════════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Compile Options:$(RESET)"
	@echo -e "  SV Mode:       $(MODELSIM_SV_MODE)"
	@echo -e "  MFCU:          $(MODELSIM_MFCU)"
	@echo -e "  SV Input Port: $(MODELSIM_SVINPUTPORT)"
	@echo -e "  Opt Level:     $(MODELSIM_OPT_LEVEL)"
	@echo -e "  Incremental:   $(MODELSIM_INCREMENTAL)"
	@echo ""
	@echo -e "$(YELLOW)Lint Options:$(RESET)"
	@echo -e "  Enabled:       $(MODELSIM_LINT_ENABLED)"
	@echo -e "  Mode:          $(MODELSIM_LINT_MODE)"
	@echo -e "  Pedantic:      $(if $(MODELSIM_PEDANTIC),Yes,No)"
	@echo ""
	@echo -e "$(YELLOW)Debug Options:$(RESET)"
	@echo -e "  Access:        $(MODELSIM_ACC)"
	@echo -e "  FSM Debug:     $(if $(MODELSIM_FSMDEBUG),Yes,No)"
	@echo -e "  Assert Debug:  $(if $(MODELSIM_ASSERTDEBUG),Yes,No)"
	@echo -e "  Line Info:     $(if $(MODELSIM_LINEINFO),Yes,No)"
	@echo ""
	@echo -e "$(YELLOW)Coverage:$(RESET)"
	@echo -e "  Options:       $(if $(MODELSIM_COVERAGE),$(MODELSIM_COVERAGE),Disabled)"
	@echo ""
	@echo -e "$(YELLOW)Simulation:$(RESET)"
	@echo -e "  Time Res:      $(MODELSIM_TIME_RES)"
	@echo -e "  Sim Time:      $(SIM_TIME)"
	@echo -e "  Timing Checks: $(if $(MODELSIM_NOTIMINGCHECKS),Disabled,Enabled)"
	@echo ""
	@echo -e "$(YELLOW)Message Handling:$(RESET)"
	@echo -e "  Suppress:      $(MODELSIM_SUPPRESS)"
	@echo ""
	@echo -e "$(CYAN)════════════════════════════════════════════════════════════$(RESET)"

# ============================================================
# Clean
# ============================================================
clean_modelsim:
	@echo -e "$(RED)[CLEANING MODELSIM FILES]$(RESET)"
	@$(RM) "$(WORK_DIR)" "transcript" "vsim.wlf" "modelsim.ini" || true
	@$(RM) "$(LOG_DIR)/rtl/modelsim" || true
	@$(RM) "$(BUILD_DIR)/.modelsim_config.mk" || true
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
	@echo -e "  $(GREEN)compile              $(RESET)– Compile all RTL + Testbench sources"
	@echo -e "  $(GREEN)compile_lint         $(RESET)– Compile with lint checks enabled"
	@echo -e "  $(GREEN)lint_modelsim        $(RESET)– Full lint analysis"
	@echo -e "  $(GREEN)lint_report_modelsim $(RESET)– Categorized lint report"
	@echo -e "  $(GREEN)simulate             $(RESET)– Run simulation (auto memory resolve)"
	@echo -e "  $(GREEN)clean_modelsim       $(RESET)– Clean ModelSim/Questa build artifacts"
	@echo -e "  $(GREEN)modelsim_config_summary $(RESET)– Show current configuration"
	@echo -e ""
	@echo -e "$(YELLOW)Configuration:$(RESET)"
	@echo -e "  Configuration is loaded from: script/config/modelsim.json"
	@echo -e "  Local overrides:              script/config/modelsim.local.json"
	@echo -e ""
	@echo -e "$(YELLOW)Profiles:$(RESET)"
	@echo -e "  $(GREEN)MODELSIM_PROFILE=fast      $(RESET)– Maximum speed, minimal checking"
	@echo -e "  $(GREEN)MODELSIM_PROFILE=debug     $(RESET)– Full debugging features"
	@echo -e "  $(GREEN)MODELSIM_PROFILE=lint_only $(RESET)– Lint checking only"
	@echo -e "  $(GREEN)MODELSIM_PROFILE=coverage  $(RESET)– Coverage collection mode"
	@echo -e "  $(GREEN)MODELSIM_PROFILE=gls       $(RESET)– Gate-level simulation"
	@echo -e ""
	@echo -e "$(YELLOW)Lint Modes:$(RESET)"
	@echo -e "  $(GREEN)MODELSIM_LINT_MODE=default $(RESET)– Standard lint checks"
	@echo -e "  $(GREEN)MODELSIM_LINT_MODE=fast    $(RESET)– Quick lint scan"
	@echo -e "  $(GREEN)MODELSIM_LINT_MODE=full    $(RESET)– Comprehensive lint analysis"
	@echo -e ""
	@echo -e "$(YELLOW)Parameters:$(RESET)"
	@echo -e "  TEST_NAME=<name>             – Select test to run"
	@echo -e "  GUI=1                        – Launch ModelSim GUI"
	@echo -e "  SIM_TIME=<t>                 – Simulation time (default: $(SIM_TIME))"
	@echo -e "  MODELSIM_LINT_MODE=<mode>    – Lint mode: default, fast, full"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make compile"
	@echo -e "  make lint_modelsim MODELSIM_LINT_MODE=full"
	@echo -e "  make simulate TEST_NAME=rv32ui-p-add GUI=1"
	@echo -e "  make simulate TEST_NAME=rv32uc-p-rvc SIM_TIME=50000ns"
	@echo -e "  make compile MODELSIM_PROFILE=debug"
	@echo -e "  make lint_modelsim MODELSIM_PROFILE=lint_only"
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"