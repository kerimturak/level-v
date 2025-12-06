# =========================================
# CERES RISC-V — Verilator Simulation
# Optimized for Verilator 5.x + Python Runner
# =========================================

# -----------------------------------------
# Configuration (Python-based)
# -----------------------------------------
# JSON config is now handled by Python runner
# See: script/python/makefile/verilator_config.py
VERILATOR_CONFIG_FILE := $(ROOT_DIR)/script/config/verilator.json

# -----------------------------------------
# Verilator Paths
# -----------------------------------------
# Use provided VERILATOR_LOG_DIR or default to LOG_DIR/verilator/TEST_NAME
VERILATOR_LOG_DIR  ?= $(LOG_DIR)/verilator/$(TEST_NAME)
VERILATOR_INCLUDES := $(addprefix -I, $(INC_DIRS))

# Waiver file for suppressing known UNOPTFLAT warnings
VERILATOR_WAIVER   := $(RTL_DIR)/verilator.vlt

# -----------------------------------------
# Threading Configuration
# -----------------------------------------
# Auto-detect CPU cores if not specified
# Can be overridden by JSON config (CFG_BUILD_THREADS, CFG_SIM_THREADS)
VERILATOR_THREADS  ?= $(or $(CFG_BUILD_THREADS),$(shell nproc 2>/dev/null || echo 4))
BUILD_JOBS         ?= $(VERILATOR_THREADS)
SIM_THREADS        ?= $(or $(CFG_SIM_THREADS),1)

# -----------------------------------------
# Verilator Defines (New naming convention)
# -----------------------------------------

# ===========================================
# LOG CONTROLS (LOG_XXX=1 to enable)
# ===========================================

# Commit trace (Spike-compatible) - LOG_COMMIT=1
ifeq ($(LOG_COMMIT),1)
  SV_DEFINES += +define+LOG_COMMIT
endif

# Pipeline trace (KONATA format) - LOG_PIPELINE=1
ifeq ($(LOG_PIPELINE),1)
  SV_DEFINES += +define+LOG_PIPELINE
endif

# RAM init messages - LOG_RAM=1
ifeq ($(LOG_RAM),1)
  SV_DEFINES += +define+LOG_RAM
endif

# UART file logging - LOG_UART=1
ifeq ($(LOG_UART),1)
  SV_DEFINES += +define+LOG_UART
endif

# Branch Predictor stats - LOG_BP=1
ifeq ($(LOG_BP),1)
  SV_DEFINES += +define+LOG_BP
endif

# Verbose BP logging - LOG_BP_VERBOSE=1
ifeq ($(LOG_BP_VERBOSE),1)
  SV_DEFINES += +define+LOG_BP +define+LOG_BP_VERBOSE
endif

# ===========================================
# TRACE CONTROLS
# ===========================================

# KONATA pipeline visualizer - KONATA_TRACER=1
ifeq ($(KONATA_TRACER),1)
  SV_DEFINES += +define+KONATA_TRACER
endif

# ===========================================
# SIMULATION CONTROLS
# ===========================================

# Fast simulation mode - SIM_FAST=1
ifeq ($(SIM_FAST),1)
  SV_DEFINES += +define+SIM_FAST
  TRACE_FLAGS :=
  TRACE_DEFINE :=
endif

# UART monitoring + auto-stop - SIM_UART_MONITOR=1
ifeq ($(SIM_UART_MONITOR),1)
  SV_DEFINES += +define+SIM_UART_MONITOR
endif

# Coverage collection - SIM_COVERAGE=1
ifeq ($(SIM_COVERAGE),1)
  COVERAGE_FLAGS := --coverage --coverage-line --coverage-toggle
  SV_DEFINES += +define+SIM_COVERAGE
else
  COVERAGE_FLAGS :=
endif

# ===========================================
# BACKWARD COMPATIBILITY (old names)
# ===========================================

# BP_LOG -> LOG_BP
ifeq ($(BP_LOG),1)
  SV_DEFINES += +define+LOG_BP
endif

# BP_VERBOSE -> LOG_BP_VERBOSE  
ifeq ($(BP_VERBOSE),1)
  SV_DEFINES += +define+LOG_BP +define+LOG_BP_VERBOSE
endif

# FAST_SIM -> SIM_FAST
ifeq ($(FAST_SIM),1)
  SV_DEFINES += +define+SIM_FAST
  TRACE_FLAGS :=
  TRACE_DEFINE :=
endif

# MINIMAL_SOC -> Minimal peripherals for faster simulation
# Only CPU + RAM + UART + Timer + CLINT active
ifeq ($(MINIMAL_SOC),1)
  SV_DEFINES += +define+MINIMAL_SOC
endif

# COVERAGE -> SIM_COVERAGE
ifeq ($(COVERAGE),1)
  COVERAGE_FLAGS := --coverage --coverage-line --coverage-toggle
  SV_DEFINES += +define+SIM_COVERAGE
endif

# Auto-enable for benchmark tests
ifeq ($(TEST_TYPE),bench)
  SV_DEFINES += +define+SIM_UART_MONITOR
endif

# ===========================================
# OTHER FLAGS
# ===========================================

# VPI support - VPI=1
ifeq ($(VPI),1)
  VPI_FLAGS := --vpi
else
  VPI_FLAGS :=
endif

# Hierarchical build - HIERARCHICAL=1
ifeq ($(HIERARCHICAL),1)
  HIER_FLAGS := --hierarchical
else
  HIER_FLAGS :=
endif

# Setup trace flags if not in fast mode
ifndef TRACE_FLAGS
  TRACE_FLAGS := --trace-fst --trace-structs --trace-params
  TRACE_DEFINE := +define+VM_TRACE_FST
endif

VERILATOR_DEFINE = $(TRACE_DEFINE) $(SV_DEFINES)

# Trace depth control
TRACE_DEPTH ?= 99
ifneq ($(TRACE_FLAGS),)
  TRACE_FLAGS += --trace-depth $(TRACE_DEPTH)
endif

# Multi-threaded FST writing
ifeq ($(TRACE_THREADS),1)
  TRACE_FLAGS += --trace-threads 2
endif

# -----------------------------------------
# Compiler Flags (based on MODE)
# -----------------------------------------
ifeq ($(MODE),debug)
    OPT_LEVEL     := -O0
    CFLAGS_DEBUG  := -g -DDEBUG
    # Debug mode specific verilator flags
    VERILATOR_DEBUG_FLAGS := --debug-check
else ifeq ($(MODE),profile)
    OPT_LEVEL     := -O2
    CFLAGS_DEBUG  := -pg -g
    # Profile mode for gprof/perf
    VERILATOR_DEBUG_FLAGS := --prof-cfuncs --prof-exec
else
    OPT_LEVEL     := -O3
    CFLAGS_DEBUG  :=
    VERILATOR_DEBUG_FLAGS :=
endif

# -----------------------------------------
# Advanced Optimization Flags
# -----------------------------------------
# Output splitting for faster compilation of large designs
OUTPUT_SPLIT       ?= 20000
OUTPUT_SPLIT_CFUNC ?= 5000

# Loop unrolling limits
UNROLL_COUNT       ?= 64
UNROLL_STMTS       ?= 30000

# X-state handling
X_ASSIGN           ?= fast
X_INITIAL          ?= 0

# Use x-initial-edge to better match event-driven simulators
X_INITIAL_EDGE     ?= 1

# -----------------------------------------
# Multi-threading Support
# -----------------------------------------
# THREADS=N enables multi-threaded simulation (N = number of threads)
# Default: 0 (single-threaded for determinism)
THREADS            ?= 0
ifneq ($(THREADS),0)
  THREAD_FLAGS     := --threads $(THREADS) --threads-dpi all
  THREAD_CFLAGS    := -pthread
  THREAD_LDFLAGS   := -lpthread -latomic
else
  THREAD_FLAGS     :=
  THREAD_CFLAGS    :=
  THREAD_LDFLAGS   :=
endif

# -----------------------------------------
# Warning Suppressions (organized by category)
# -----------------------------------------
# Critical warnings that should never be suppressed
# --Wno-fatal allows build to continue despite warnings

# Width-related warnings
NO_WARN_WIDTH = \
    --Wno-WIDTH \
    --Wno-WIDTHEXPAND \
    --Wno-WIDTHTRUNC \
    --Wno-WIDTHCONCAT

# Unused signal warnings
NO_WARN_UNUSED = \
    --Wno-UNDRIVEN \
    --Wno-UNUSED \
    --Wno-UNUSEDPARAM \
    --Wno-UNUSEDSIGNAL

# Style and naming warnings
NO_WARN_STYLE = \
    --Wno-style \
    --Wno-DECLFILENAME \
    --Wno-GENUNNAMED \
    --Wno-VARHIDDEN \
    --Wno-SYMRSVDWORD \
    --Wno-IMPORTSTAR

# Timing and synthesis warnings
NO_WARN_TIMING = \
    --Wno-ASSIGNDLY \
    --Wno-INITIALDLY \
    --Wno-BLKANDNBLK \
    --Wno-BLKLOOPINIT \
    --Wno-TIMESCALEMOD

# Structural warnings
NO_WARN_STRUCT = \
    --Wno-PINCONNECTEMPTY \
    --Wno-MODDUP \
    --Wno-IMPLICIT \
    --Wno-LATCH

# Optimization warnings
NO_WARN_OPT = \
    --Wno-UNOPTFLAT \
    --Wno-UNOPTTHREADS \
    --Wno-ALWCOMBORDER

# Case/enum warnings
NO_WARN_CASE = \
    --Wno-CASEINCOMPLETE \
    --Wno-ENUMVALUE

# Combined warning suppressions for simulation
NO_WARNING = \
    --Wno-fatal \
    --Wno-lint \
    $(NO_WARN_WIDTH) \
    $(NO_WARN_UNUSED) \
    $(NO_WARN_STYLE) \
    $(NO_WARN_TIMING) \
    $(NO_WARN_STRUCT) \
    $(NO_WARN_OPT) \
    $(NO_WARN_CASE)

# Lint-specific - minimal suppressions for maximum feedback
# Only suppress warnings that are truly not useful for lint
NO_WARNING_LINT = \
    --Wno-DECLFILENAME \
    --Wno-IMPORTSTAR

# -----------------------------------------
# Build Flags
# -----------------------------------------
# Lint flags: -Wall enables all warnings, no suppressions for real issues
LINT_FLAGS  = --lint-only -Wall -I$(INC_DIRS) --top-module $(RTL_LEVEL)
RUN_BIN     := $(OBJ_DIR)/V$(RTL_LEVEL)

# Common verilator flags
# --converge-limit: Allows more iterations for combinational loops
# --x-initial-edge: Triggers initial blocks on the edge for better compatibility
VERILATOR_COMMON_FLAGS = \
    --top-module $(RTL_LEVEL) \
    $(VERILATOR_INCLUDES) \
    --timing \
    --x-assign $(X_ASSIGN) \
    --x-initial $(X_INITIAL) \
    $(if $(filter 1,$(X_INITIAL_EDGE)),--x-initial-edge,) \
    --converge-limit 100 \
    --error-limit 100 \
    $(if $(wildcard $(VERILATOR_WAIVER)),$(VERILATOR_WAIVER),) \
    $(THREAD_FLAGS) \
    --Mdir $(OBJ_DIR)

# Build-specific flags
VERILATOR_BUILD_FLAGS = \
    --cc \
    --exe $(CPP_TB_FILE) \
    --build \
    -j $(BUILD_JOBS) \
    --output-split $(OUTPUT_SPLIT) \
    --output-split-cfuncs $(OUTPUT_SPLIT_CFUNC) \
    --unroll-count $(UNROLL_COUNT) \
    --unroll-stmts $(UNROLL_STMTS) \
    $(TRACE_FLAGS) \
    $(COVERAGE_FLAGS) \
    $(VPI_FLAGS) \
    $(HIER_FLAGS) \
    $(VERILATOR_DEBUG_FLAGS) \
    --CFLAGS "$(OPT_LEVEL) $(CFLAGS_DEBUG) $(THREAD_CFLAGS) -std=c++17 -Wall -Wextra -Wno-unused-parameter" \
    --LDFLAGS "-lm $(THREAD_LDFLAGS)"

# =========================================
# Targets
# =========================================

.PHONY: dirs lint lint-report verilate verilate-fast run_verilator wave clean_verilator verilator_help stats

dirs:
	@$(MKDIR) -p "$(BUILD_DIR)" "$(OBJ_DIR)" "$(LOG_DIR)"

# ============================================================
# Lint — Full lint check with all warnings enabled
# ============================================================
# Log output: $(LINT_DIR)/verilator/lint.log
# Waiver output: $(LINT_DIR)/verilator/lint_waiver.vlt
VERILATOR_LINT_DIR := $(LINT_DIR)/verilator

lint: dirs
	@printf "$(GREEN)[VERILATOR LINT]$(RESET)\n"
	@mkdir -p "$(VERILATOR_LINT_DIR)"
	@printf "$(CYAN)[INFO]$(RESET) Output: $(VERILATOR_LINT_DIR)/\n"
	-@$(VERILATOR) \
		$(LINT_FLAGS) $(VERILATOR_INCLUDES) \
		$(SV_SOURCES) \
		--timing \
		--Wno-fatal \
		--bbox-unsup \
		--report-unoptflat \
		--Mdir "$(OBJ_DIR)" \
		--waiver-output "$(VERILATOR_LINT_DIR)/lint_waiver.vlt" \
		2>&1 | tee "$(VERILATOR_LINT_DIR)/lint.log"
	@echo ""
	@printf "$(CYAN)════════════════════════════════════════$(RESET)\n"
	@printf "$(CYAN)  Lint Summary$(RESET)\n"
	@printf "$(CYAN)════════════════════════════════════════$(RESET)\n"
	@ERR=$$(grep -c "%Error" "$(VERILATOR_LINT_DIR)/lint.log" 2>/dev/null) || ERR=0; \
		if [ "$$ERR" != "0" ] && [ -n "$$ERR" ]; then \
			printf "  $(RED)Errors:   $$ERR$(RESET)\n"; \
		else \
			printf "  $(GREEN)Errors:   0$(RESET)\n"; \
		fi
	@WARN=$$(grep -c "%Warning" "$(VERILATOR_LINT_DIR)/lint.log" 2>/dev/null) || WARN=0; \
		if [ "$$WARN" != "0" ] && [ -n "$$WARN" ]; then \
			printf "  $(YELLOW)Warnings: $$WARN$(RESET)\n"; \
		else \
			printf "  $(GREEN)Warnings: 0$(RESET)\n"; \
		fi
	@printf "$(CYAN)════════════════════════════════════════$(RESET)\n"
	@printf "  Log:    $(VERILATOR_LINT_DIR)/lint.log\n"
	@printf "  Waiver: $(VERILATOR_LINT_DIR)/lint_waiver.vlt\n"
	@printf "$(CYAN)════════════════════════════════════════$(RESET)\n"

# Lint with detailed report and statistics
lint-report: dirs
	@printf "$(GREEN)[VERILATOR LINT REPORT]$(RESET)\n"
	@mkdir -p "$(VERILATOR_LINT_DIR)"
	@printf "$(CYAN)[INFO]$(RESET) Log: $(VERILATOR_LINT_DIR)/lint_report.log\n"
	-@$(VERILATOR) \
		$(LINT_FLAGS) $(VERILATOR_INCLUDES) \
		$(SV_SOURCES) \
		--timing \
		--Wno-fatal \
		--stats \
		--stats-vars \
		--report-unoptflat \
		--Mdir "$(OBJ_DIR)" \
		--bbox-unsup \
		2>&1 | tee "$(VERILATOR_LINT_DIR)/lint_report.log"
	@echo ""
	@printf "$(GREEN)[DONE]$(RESET) Report: $(VERILATOR_LINT_DIR)/lint_report.log\n"

# Lint specific category
lint-width: dirs
	@printf "$(GREEN)[LINT: WIDTH WARNINGS]$(RESET)\n"
	@mkdir -p "$(VERILATOR_LINT_DIR)"
	-@$(VERILATOR) --lint-only -Wall -Wno-fatal \
		$(VERILATOR_INCLUDES) $(SV_SOURCES) \
		--timing --bbox-unsup --Mdir "$(OBJ_DIR)" \
		--top-module $(RTL_LEVEL) 2>&1 | tee "$(VERILATOR_LINT_DIR)/lint_width.log" | grep -E "WIDTH|width" || echo "No width issues found"

lint-unused: dirs
	@printf "$(GREEN)[LINT: UNUSED SIGNALS]$(RESET)\n"
	@mkdir -p "$(VERILATOR_LINT_DIR)"
	-@$(VERILATOR) --lint-only -Wall -Wno-fatal \
		$(VERILATOR_INCLUDES) $(SV_SOURCES) \
		--timing --bbox-unsup --Mdir "$(OBJ_DIR)" \
		--top-module $(RTL_LEVEL) 2>&1 | tee "$(VERILATOR_LINT_DIR)/lint_unused.log" | grep -E "UNUSED|UNDRIVEN" || echo "No unused signals found"

lint-loops: dirs
	@printf "$(GREEN)[LINT: COMBINATIONAL LOOPS]$(RESET)\n"
	@mkdir -p "$(VERILATOR_LINT_DIR)"
	-@$(VERILATOR) --lint-only -Wall -Wno-fatal \
		$(VERILATOR_INCLUDES) $(SV_SOURCES) \
		--timing --bbox-unsup --report-unoptflat --Mdir "$(OBJ_DIR)" \
		--top-module $(RTL_LEVEL) 2>&1 | tee "$(VERILATOR_LINT_DIR)/lint_loops.log" | grep -E "UNOPTFLAT|loop|circular" || printf "$(GREEN)No combinational loops found$(RESET)\n"
	@if ls $(OBJ_DIR)/*_unoptflat.dot 1>/dev/null 2>&1; then \
		printf "$(CYAN)[INFO]$(RESET) Loop diagrams available in $(OBJ_DIR)/*.dot\n"; \
		printf "$(CYAN)[TIP]$(RESET)  Run 'make lint-loops-view' to generate PDF\n"; \
	fi

# View combinational loop diagrams as PDF
lint-loops-view: lint-loops
	@printf "$(GREEN)[GENERATING LOOP DIAGRAMS]$(RESET)\n"
	@mkdir -p "$(VERILATOR_LINT_DIR)/loops"
	@if ! command -v dot &>/dev/null; then \
		printf "$(RED)[ERROR]$(RESET) Graphviz not installed. Run: sudo apt install graphviz\n"; \
		exit 1; \
	fi
	@for dotfile in $(OBJ_DIR)/*_unoptflat.dot; do \
		if [ -f "$$dotfile" ]; then \
			name=$$(basename "$$dotfile" .dot); \
			printf "  $(CYAN)→$(RESET) Converting $$name.dot to PDF...\n"; \
			dot -Tpdf -o "$(VERILATOR_LINT_DIR)/loops/$$name.pdf" "$$dotfile"; \
			dot -Tsvg -o "$(VERILATOR_LINT_DIR)/loops/$$name.svg" "$$dotfile"; \
		fi; \
	done
	@if ls $(VERILATOR_LINT_DIR)/loops/*.pdf 1>/dev/null 2>&1; then \
		printf "$(GREEN)[DONE]$(RESET) Diagrams saved to: $(VERILATOR_LINT_DIR)/loops/\n"; \
		printf "$(CYAN)[INFO]$(RESET) Opening first diagram...\n"; \
		xdg-open "$$(ls $(VERILATOR_LINT_DIR)/loops/*.pdf | head -1)" 2>/dev/null || \
		printf "$(YELLOW)[TIP]$(RESET) Open manually: $(VERILATOR_LINT_DIR)/loops/\n"; \
	else \
		printf "$(GREEN)[INFO]$(RESET) No loop diagrams to display (no UNOPTFLAT warnings)\n"; \
	fi

# ============================================================
# Verilate — Build C++ Model (Standard)
# ============================================================
verilate: dirs
	@printf "$(GREEN)[VERILATING RTL SOURCES — $(MODE) mode, $(VERILATOR_THREADS) threads]$(RESET)\n"
	$(VERILATOR) \
		$(SV_SOURCES) $(LOGGER_SRC) \
		$(VERILATOR_COMMON_FLAGS) \
		$(VERILATOR_BUILD_FLAGS) \
		$(NO_WARNING) \
		$(VERILATOR_DEFINE)
	@printf "$(GREEN)[SUCCESS]$(RESET) Built: $(RUN_BIN)\n"

# Fast verilate - skip if binary is up-to-date
verilate-fast: dirs
	@if [ -x "$(RUN_BIN)" ] && [ "$(RUN_BIN)" -nt "$(word 1,$(SV_SOURCES))" ]; then \
		printf "$(YELLOW)[SKIP]$(RESET) Binary up-to-date: $(RUN_BIN)\n"; \
	else \
		printf "$(GREEN)[VERILATING RTL SOURCES — FAST MODE]$(RESET)\n"; \
		$(VERILATOR) \
			$(SV_SOURCES) $(LOGGER_SRC) \
			$(VERILATOR_COMMON_FLAGS) \
			$(VERILATOR_BUILD_FLAGS) \
			$(NO_WARNING) \
			$(VERILATOR_DEFINE); \
		printf "$(GREEN)[SUCCESS]$(RESET) Built: $(RUN_BIN)\n"; \
	fi

# Rebuild only C++ without re-verilating (for testbench changes)
rebuild-cpp: dirs
	@printf "$(GREEN)[REBUILDING C++ ONLY]$(RESET)\n"
	$(VERILATOR) \
		$(SV_SOURCES) $(LOGGER_SRC) \
		$(VERILATOR_COMMON_FLAGS) \
		$(VERILATOR_BUILD_FLAGS) \
		$(NO_WARNING) \
		$(VERILATOR_DEFINE) \
		--no-verilate
	@printf "$(GREEN)[SUCCESS]$(RESET) Rebuilt: $(RUN_BIN)\n"

# ============================================================
# Run Simulation
# ============================================================
# Coverage data directory
COVERAGE_DATA_DIR := $(LOG_DIR)/verilator/coverage_data

# Python runner
VERILATOR_RUNNER := $(ROOT_DIR)/script/python/makefile/verilator_runner.py
VERILATOR_CONFIG := $(ROOT_DIR)/script/config/verilator.json

# Memory search directories
VERILATOR_MEM_DIRS := $(BUILD_DIR)/tests/riscv-tests/mem \
                      $(BUILD_DIR)/tests/riscv-arch-test/mem \
                      $(BUILD_DIR)/tests/imperas/mem \
                      $(BUILD_DIR)/tests/bench/mem

# Runner arguments
VERILATOR_RUNNER_ARGS := \
    --test $(TEST_NAME) \
    --bin-path $(RUN_BIN) \
    --log-dir $(VERILATOR_LOG_DIR) \
    --mem-dirs "$(VERILATOR_MEM_DIRS)" \
    --build-dir $(BUILD_DIR)/tests

# Optional arguments
ifdef VERILATOR_PROFILE
    VERILATOR_RUNNER_ARGS += --profile $(VERILATOR_PROFILE)
endif

ifdef MAX_CYCLES
    VERILATOR_RUNNER_ARGS += --max-cycles $(MAX_CYCLES)
endif

ifdef MEM_FILE
    VERILATOR_RUNNER_ARGS += --mem-file $(MEM_FILE)
endif

ifeq ($(TRACE),0)
    VERILATOR_RUNNER_ARGS += --no-trace
endif

ifeq ($(COVERAGE),1)
    VERILATOR_RUNNER_ARGS += --coverage --coverage-file $(COVERAGE_DATA_DIR)/$(TEST_NAME).dat
endif

ifeq ($(FAST),1)
    VERILATOR_RUNNER_ARGS += --fast
endif

ifeq ($(NO_COLOR),1)
    VERILATOR_RUNNER_ARGS += --no-color
endif

# Main run target using Python runner
run_verilator: verilate
	@$(PYTHON) $(VERILATOR_RUNNER) $(VERILATOR_RUNNER_ARGS)

# Quick run - use verilate-fast
run_verilator_quick: verilate-fast
	@$(PYTHON) $(VERILATOR_RUNNER) $(VERILATOR_RUNNER_ARGS)

# Dry-run to see command
run_verilator_dry:
	@$(PYTHON) $(VERILATOR_RUNNER) $(VERILATOR_RUNNER_ARGS) --dry-run

# Show current config
verilator_show_config:
	@$(PYTHON) $(VERILATOR_RUNNER) $(VERILATOR_RUNNER_ARGS) --show-config

# Validate config
verilator_validate_config:
	@$(PYTHON) $(ROOT_DIR)/script/python/makefile/verilator_config.py --validate

# ============================================================
# Waveform Viewer
# ============================================================
wave:
	@echo -e "$(YELLOW)[INFO]$(RESET) Opening GTKWave..."
	@if [ -f "$(VERILATOR_LOG_DIR)/waveform.fst" ]; then \
		gtkwave "$(VERILATOR_LOG_DIR)/waveform.fst" & \
	else \
		echo -e "$(RED)[ERROR]$(RESET) No waveform file found at $(VERILATOR_LOG_DIR)/waveform.fst"; \
		echo -e "$(YELLOW)[TIP]$(RESET) Run simulation first with: make run_verilator TEST_NAME=<test>"; \
	fi

# ============================================================
# Statistics and Profiling
# ============================================================
stats: dirs
	@printf "$(GREEN)[GENERATING VERILATOR STATISTICS]$(RESET)\n"
	@mkdir -p "$(LOG_DIR)/verilator"
	$(VERILATOR) \
		--lint-only \
		$(SV_SOURCES) \
		$(VERILATOR_INCLUDES) \
		--top-module $(RTL_LEVEL) \
		--timing \
		--stats \
		--stats-vars \
		$(NO_WARNING) \
		--bbox-unsup \
		2>&1 | tee "$(LOG_DIR)/verilator/stats.log"
	@if [ -f "$(OBJ_DIR)/V$(RTL_LEVEL)__stats.txt" ]; then \
		cp "$(OBJ_DIR)/V$(RTL_LEVEL)__stats.txt" "$(LOG_DIR)/verilator/"; \
	fi
	@printf "$(GREEN)[DONE]$(RESET) Statistics saved to $(LOG_DIR)/verilator/\n"

# ============================================================
# Coverage Analysis
# ============================================================
# Build and run tests with coverage, then generate reports
# Usage:
#   make coverage          - Full coverage run (isa + arch tests)
#   make coverage-quick    - Quick coverage (ISA tests only)
#   make coverage-report   - Generate report from existing data
#   make coverage-html     - Generate HTML coverage report
# ============================================================

.PHONY: coverage coverage-quick coverage-report coverage-html coverage-clean

# Quick coverage with ISA tests only
coverage-quick:
	@echo -e "$(CYAN)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║           CERES RISC-V — Quick Coverage Run                 ║$(RESET)"
	@echo -e "$(CYAN)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo -e "$(YELLOW)[1/3] Building with coverage enabled...$(RESET)"
	@$(MAKE) --no-print-directory clean_verilator
	@$(MAKE) --no-print-directory verilate COVERAGE=1
	@echo -e "$(YELLOW)[2/3] Running ISA tests...$(RESET)"
	@$(MAKE) --no-print-directory isa COVERAGE=1
	@echo -e "$(YELLOW)[3/3] Generating coverage report...$(RESET)"
	@$(MAKE) --no-print-directory coverage-html
	@echo -e "$(GREEN)$(SUCCESS) Coverage complete! Open results/coverage/index.html$(RESET)"

# Full coverage with all compliance tests
coverage:
	@echo -e "$(CYAN)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║           CERES RISC-V — Full Coverage Analysis             ║$(RESET)"
	@echo -e "$(CYAN)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo -e "$(YELLOW)[1/4] Building with coverage enabled...$(RESET)"
	@$(MAKE) --no-print-directory clean_verilator
	@$(MAKE) --no-print-directory verilate COVERAGE=1
	@echo -e "$(YELLOW)[2/4] Running ISA tests...$(RESET)"
	@$(MAKE) --no-print-directory isa COVERAGE=1
	@echo -e "$(YELLOW)[3/4] Running Architecture tests...$(RESET)"
	@$(MAKE) --no-print-directory arch COVERAGE=1
	@echo -e "$(YELLOW)[4/4] Generating coverage report...$(RESET)"
	@$(MAKE) --no-print-directory coverage-html
	@echo -e "$(GREEN)$(SUCCESS) Coverage complete! Open results/coverage/index.html$(RESET)"

# Generate text-based coverage report
coverage-report:
	@if [ -f "$(LOG_DIR)/verilator/coverage.dat" ]; then \
		mkdir -p "$(LOG_DIR)/verilator/coverage_annotated"; \
		verilator_coverage --annotate "$(LOG_DIR)/verilator/coverage_annotated" \
			"$(LOG_DIR)/verilator/coverage.dat"; \
		echo -e "$(GREEN)[OK]$(RESET) Coverage annotations: $(LOG_DIR)/verilator/coverage_annotated/"; \
	else \
		echo -e "$(RED)[ERROR]$(RESET) No coverage data. Run: make coverage"; \
	fi

# Generate HTML coverage report
COVERAGE_HTML_DIR := $(RESULTS_DIR)/coverage

coverage-html:
	@mkdir -p $(COVERAGE_HTML_DIR)
	@# First, merge all individual coverage files
	@if [ -d "$(COVERAGE_DATA_DIR)" ] && [ -n "$$(ls -A $(COVERAGE_DATA_DIR)/*.dat 2>/dev/null)" ]; then \
		echo -e "$(YELLOW)[COV] Merging coverage data files...$(RESET)"; \
		verilator_coverage --write "$(LOG_DIR)/verilator/coverage.dat" \
			$(COVERAGE_DATA_DIR)/*.dat 2>/dev/null; \
		COV_COUNT=$$(ls -1 $(COVERAGE_DATA_DIR)/*.dat 2>/dev/null | wc -l); \
		echo -e "$(GREEN)[OK]$(RESET) Merged $$COV_COUNT coverage files"; \
	fi
	@if [ -f "$(LOG_DIR)/verilator/coverage.dat" ]; then \
		echo -e "$(YELLOW)[COV] Generating HTML coverage report...$(RESET)"; \
		verilator_coverage --annotate-all --annotate-min 1 \
			--write-info "$(COVERAGE_HTML_DIR)/coverage.info" \
			"$(LOG_DIR)/verilator/coverage.dat" 2>/dev/null || true; \
		if command -v genhtml >/dev/null 2>&1; then \
			genhtml "$(COVERAGE_HTML_DIR)/coverage.info" \
				--output-directory "$(COVERAGE_HTML_DIR)" \
				--title "CERES RISC-V Coverage" \
				--legend --highlight 2>/dev/null; \
			echo -e "$(GREEN)[OK]$(RESET) HTML report: $(COVERAGE_HTML_DIR)/index.html"; \
		else \
			echo -e "$(YELLOW)[INFO]$(RESET) Install lcov for HTML reports: sudo apt install lcov"; \
			verilator_coverage --annotate "$(COVERAGE_HTML_DIR)/annotated" \
				"$(LOG_DIR)/verilator/coverage.dat"; \
			echo -e "$(GREEN)[OK]$(RESET) Text annotations: $(COVERAGE_HTML_DIR)/annotated/"; \
		fi; \
		echo -e "$(CYAN)[COV] Coverage Summary:$(RESET)"; \
		verilator_coverage --rank "$(LOG_DIR)/verilator/coverage.dat" 2>/dev/null | head -30 || true; \
	else \
		echo -e "$(RED)[ERROR]$(RESET) No coverage data found."; \
		echo -e "$(YELLOW)[HINT]$(RESET) Run: make coverage-quick"; \
	fi

# Clean coverage data
coverage-clean:
	@echo -e "$(RED)[CLEAN]$(RESET) Removing coverage data..."
	@$(RM) "$(LOG_DIR)/verilator/coverage.dat"
	@$(RM) "$(LOG_DIR)/verilator/coverage_annotated"
	@$(RM) "$(COVERAGE_DATA_DIR)"
	@$(RM) "$(COVERAGE_HTML_DIR)"
	@echo -e "$(GREEN)[OK]$(RESET) Coverage data cleaned"

# ============================================================
# Clean
# ============================================================
clean_verilator:
	@echo -e "$(RED)[CLEANING VERILATOR]$(RESET)"
	@$(RM) "$(OBJ_DIR)"
	@$(RM) "$(LOG_DIR)/verilator"
	@echo -e "$(GREEN)Clean complete.$(RESET)"

# Deep clean - also remove dependency files
clean_verilator_deep: clean_verilator
	@echo -e "$(RED)[DEEP CLEANING]$(RESET)"
	@find "$(BUILD_DIR)" -name "*.d" -delete 2>/dev/null || true
	@find "$(BUILD_DIR)" -name "*.o" -delete 2>/dev/null || true

# ============================================================
# Help
# ============================================================
verilator_help:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)            CERES RISC-V — Verilator Simulation               $(RESET)"
	@echo -e "$(GREEN)              Verilator 5.x + Python Runner                   $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Lint Targets:$(RESET)"
	@echo -e "  $(GREEN)lint              $(RESET)– Full lint with all warnings"
	@echo -e "  $(GREEN)lint-report       $(RESET)– Lint with statistics"
	@echo -e "  $(GREEN)lint-width        $(RESET)– Check width mismatches only"
	@echo -e "  $(GREEN)lint-unused       $(RESET)– Check unused/undriven signals only"
	@echo -e "  $(GREEN)lint-loops        $(RESET)– Check combinational loops only"
	@echo -e "  $(GREEN)lint-loops-view   $(RESET)– Generate loop diagrams (PDF/SVG)"
	@echo -e ""
	@echo -e "$(YELLOW)Build Targets:$(RESET)"
	@echo -e "  $(GREEN)verilate          $(RESET)– Build C++ simulation model"
	@echo -e "  $(GREEN)verilate-fast     $(RESET)– Build only if sources changed"
	@echo -e "  $(GREEN)rebuild-cpp       $(RESET)– Rebuild C++ without re-verilating"
	@echo -e "  $(GREEN)stats             $(RESET)– Generate design statistics"
	@echo -e ""
	@echo -e "$(YELLOW)Run Targets:$(RESET)"
	@echo -e "  $(GREEN)run_verilator       $(RESET)– Build and run simulation (Python runner)"
	@echo -e "  $(GREEN)run_verilator_quick $(RESET)– Quick run (skip rebuild if up-to-date)"
	@echo -e "  $(GREEN)run_verilator_dry   $(RESET)– Show command without running"
	@echo -e "  $(GREEN)wave                $(RESET)– Open GTKWave waveform viewer"
	@echo -e ""
	@echo -e "$(YELLOW)Config Targets:$(RESET)"
	@echo -e "  $(GREEN)verilator_show_config    $(RESET)– Show current JSON config"
	@echo -e "  $(GREEN)verilator_validate_config$(RESET)– Validate JSON config"
	@echo -e ""
	@echo -e "$(YELLOW)Coverage Targets:$(RESET)"
	@echo -e "  $(GREEN)coverage          $(RESET)– Full coverage run"
	@echo -e "  $(GREEN)coverage-quick    $(RESET)– Quick coverage (ISA only)"
	@echo -e "  $(GREEN)coverage-html     $(RESET)– Generate HTML report"
	@echo -e ""
	@echo -e "$(YELLOW)Clean Targets:$(RESET)"
	@echo -e "  $(GREEN)clean_verilator   $(RESET)– Clean build files"
	@echo -e "  $(GREEN)clean_verilator_deep$(RESET)– Deep clean including .d/.o files"
	@echo -e ""
	@echo -e "$(YELLOW)Configuration:$(RESET)"
	@echo -e "  $(CYAN)Config file$(RESET): script/config/verilator.json"
	@echo -e "  $(CYAN)Local override$(RESET): script/config/verilator.local.json"
	@echo -e ""
	@echo -e "$(YELLOW)CLI Parameters (override JSON):$(RESET)"
	@echo -e "  $(CYAN)VERILATOR_PROFILE$(RESET)=<name>  – Use profile (fast/debug/coverage/benchmark)"
	@echo -e "  $(CYAN)TEST_NAME$(RESET)=<name>         – Test to run"
	@echo -e "  $(CYAN)MAX_CYCLES$(RESET)=<n>           – Max cycles (default: from JSON)"
	@echo -e "  $(CYAN)FAST$(RESET)=1                   – Fast mode (no trace)"
	@echo -e "  $(CYAN)COVERAGE$(RESET)=1               – Enable coverage"
	@echo -e "  $(CYAN)TRACE$(RESET)=0                  – Disable trace"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make run_verilator TEST_NAME=rv32ui-p-add"
	@echo -e "  make run_verilator TEST_NAME=coremark VERILATOR_PROFILE=benchmark"
	@echo -e "  make run_verilator TEST_NAME=dhrystone FAST=1 MAX_CYCLES=1000000"
	@echo -e ""
	@echo -e "  $(CYAN)VPI$(RESET)=1                  – Enable VPI support"
	@echo -e "  $(CYAN)HIERARCHICAL$(RESET)=1         – Enable hierarchical build"
	@echo -e "  $(CYAN)TRACE_DEPTH$(RESET)=<n>        – Signal trace depth (default: 99)"
	@echo -e "  $(CYAN)TRACE_THREADS$(RESET)=1        – Multi-threaded FST writing"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make run_verilator TEST_NAME=rv32ui-p-add"
	@echo -e "  make run_verilator TEST_NAME=rv32ui-p-add PROFILE=debug"
	@echo -e "  make bench PROFILE=fast                        # Fast benchmark"
	@echo -e "  make isa PROFILE=coverage                      # With coverage"
	@echo -e "  make verilate PROFILE=benchmark BP_LOG=1       # Profile + override"
	@echo -e ""

# ============================================================
# Configuration Management (Python-based)
# ============================================================
.PHONY: config-show config-profiles config-edit

config-show: verilator_show_config

config-profiles:
	@$(PYTHON) $(ROOT_DIR)/script/python/makefile/verilator_config.py --help | grep -A20 "Profiller:"

config-edit:
	@echo -e "$(CYAN)[INFO]$(RESET) Edit config: $(VERILATOR_CONFIG_FILE)"
	@echo -e "$(CYAN)[INFO]$(RESET) For local overrides, create: $(ROOT_DIR)/script/config/verilator.local.json"
	@$${EDITOR:-nano} "$(VERILATOR_CONFIG_FILE)"
