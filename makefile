# ==================================================
# CERES RISC-V Makefile (Top-Level Controller)
# ==================================================
.DEFAULT_GOAL := help

SHELL := /bin/bash

# Configuration
include script/makefiles/config/config.mk
include script/makefiles/config/profiles.mk

# Simulation Tools
include script/makefiles/sim/modelsim.mk
include script/makefiles/sim/verilator.mk
include script/makefiles/sim/icarus.mk
include script/makefiles/sim/spike.mk

# Test Rules
include script/makefiles/test/run_test.mk
include script/makefiles/test/isa_import.mk
include script/makefiles/test/arch_test.mk
include script/makefiles/test/imperas_test.mk
include script/makefiles/test/coremark.mk
include script/makefiles/test/test_lists.mk
include script/makefiles/custom_test.mk

# Extended Test Suites
include script/makefiles/test/embench.mk
include script/makefiles/test/dhrystone.mk
include script/makefiles/test/torture.mk
include script/makefiles/test/riscv_dv.mk
include script/makefiles/test/riscv_formal.mk

# Synthesis Tools
include script/makefiles/synth/yosys.mk

# Utility Tools
include script/makefiles/tools/clean.mk
include script/makefiles/tools/konata.mk
include script/makefiles/tools/surfer.mk

# Linting Tools
include script/makefiles/lint/lint.mk

.PHONY: all compile simulate simulate_gui lint verilate run_verilator yosys_check clean help

all: simulate_gui

help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)                    CERES RISC-V Makefile Help$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)▶ Simulation Targets:$(RESET)"
	@echo -e "  compile         Compile RTL with ModelSim"
	@echo -e "  simulate        Run batch simulation"
	@echo -e "  simulate_gui    Run GUI simulation with waveforms"
	@echo -e "  verilate        Build Verilator model"
	@echo -e "  run_verilator   Run Verilator simulation"
	@echo -e "  iverilog        Compile with Icarus Verilog"
	@echo -e "  run_icarus      Run Icarus simulation"
	@echo -e ""
	@echo -e "$(CYAN)▶ Test Commands:$(RESET)"
	@echo -e "  run             Run single test with RTL+Spike comparison"
	@echo -e "  run_batch       Run multiple tests from list"
	@echo -e "  quick_test      Run RTL only (skip Spike)"
	@echo -e "  list_tests      List available tests"
	@echo -e ""
	@echo -e "$(CYAN)▶ Test Suites:$(RESET)"
	@echo -e "  isa             Run all ISA tests (riscv-tests)"
	@echo -e "  arch            Run architecture tests (riscv-arch-test)"
	@echo -e "  csr             Run CSR tests"
	@echo -e "  bench           Run benchmarks"
	@echo -e "  imperas         Run Imperas tests"
	@echo -e "  all_tests       Run ALL tests"
	@echo -e ""
	@echo -e "$(CYAN)▶ Quick Test Shortcuts:$(RESET)"
	@echo -e "  t T=<name>      Quick single ISA test    (e.g., make t T=rv32ui-p-add)"
	@echo -e "  tb T=<name>     Quick single benchmark   (e.g., make tb T=dhrystone)"
	@echo -e "  ti T=<name>     Quick single Imperas test"
	@echo -e ""
	@echo -e "$(CYAN)▶ CoreMark:$(RESET)"
	@echo -e "  cm              Build and run CoreMark"
	@echo -e "  cm_run          Quick CoreMark run (skip rebuild)"
	@echo -e "  coremark        Build CoreMark only"
	@echo -e "  coremark_help   Show CoreMark help"
	@echo -e ""
	@echo -e "$(CYAN)▶ Extended Test Suites:$(RESET)"
	@echo -e "  embench         Build Embench-IoT benchmarks"
	@echo -e "  embench_run     Run Embench benchmarks"
	@echo -e "  dhrystone       Build Dhrystone benchmark"
	@echo -e "  dhrystone_run   Run Dhrystone benchmark"
	@echo -e "  torture         Generate & build torture tests"
	@echo -e "  torture_run     Run torture tests"
	@echo -e "  riscv_dv        Build RISCV-DV generated tests"
	@echo -e "  riscv_dv_run    Run RISCV-DV tests"
	@echo -e "  formal          Run formal verification"
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)                    Logging & Trace Defines$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(GREEN)▶ Log Controls (enable with LOG_XXX=1):$(RESET)"
	@echo -e "  LOG_COMMIT=1    Enable Spike-compatible commit trace"
	@echo -e "  LOG_PIPELINE=1  Enable Konata pipeline trace file"
	@echo -e "  LOG_RAM=1       Enable RAM initialization messages"
	@echo -e "  LOG_UART=1      Enable UART TX file logging"
	@echo -e "  LOG_BP=1        Enable branch predictor statistics"
	@echo -e "  LOG_BP_VERBOSE=1 Enable per-branch verbose logging"
	@echo -e ""
	@echo -e "$(GREEN)▶ Trace Controls:$(RESET)"
	@echo -e "  KONATA_TRACER=1  Enable Konata pipeline visualizer"
	@echo -e ""
	@echo -e "$(GREEN)▶ Simulation Controls:$(RESET)"
	@echo -e "  SIM_FAST=1      Fast mode (all logs disabled)"
	@echo -e "  SIM_UART_MONITOR=1  UART monitoring + auto-stop (benchmarks)"
	@echo -e "  SIM_COVERAGE=1  Enable coverage collection"
	@echo -e ""
	@echo -e "$(CYAN)▶ Examples:$(RESET)"
	@echo -e "  make run T=rv32ui-p-add LOG_COMMIT=1 LOG_PIPELINE=1"
	@echo -e "  make cm SIM_FAST=1 LOG_BP=1 SIM_UART_MONITOR=1"
	@echo -e "  make isa LOG_COMMIT=1"
	@echo -e ""
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(YELLOW)                    Configuration$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(GREEN)▶ JSON Test Configs (script/config/tests/):$(RESET)"
	@echo -e "  list-configs    List available test configurations"
	@echo -e "  show-config     Show current config values"
	@echo -e "  TEST_CONFIG=X   Use specific config (isa,bench,arch,coremark...)"
	@echo -e ""
	@echo -e "$(GREEN)▶ Build Modes:$(RESET)"
	@echo -e "  MODE=debug      Full tracing, assertions ON (default)"
	@echo -e "  MODE=release    Optimized build, minimal logging"
	@echo -e "  MODE=test       RISC-V test mode with assertions"
	@echo -e ""
	@echo -e "$(GREEN)▶ Other Options:$(RESET)"
	@echo -e "  MAX_CYCLES=N    Set max simulation cycles"
	@echo -e "  CLEAN_LOGS=1    Clear logs before batch run"
	@echo -e "  TRACE=1         Enable waveform tracing"
	@echo -e ""
	@echo -e "$(CYAN)▶ Utilities:$(RESET)"
	@echo -e "  lint            Run Verilator lint check"
	@echo -e "  yosys_check     Run Yosys structural checks"
	@echo -e "  clean           Clean all build directories"
	@echo -e "  gtkwave         Open waveform with GTKWave"
	@echo -e "  surfer          Open waveform with Surfer"
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""