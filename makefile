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
include script/makefiles/sim/spike.mk

# Test Rules
include script/makefiles/test/run_test.mk
include script/makefiles/test/isa_import.mk
include script/makefiles/test/arch_test.mk
include script/makefiles/test/coremark.mk
include script/makefiles/test/test_lists.mk

# Synthesis Tools
include script/makefiles/synth/yosys.mk

# Utility Tools
include script/makefiles/tools/clean.mk
include script/makefiles/tools/konata.mk

.PHONY: all compile simulate simulate_gui lint verilate run_verilator yosys_check clean help

all: simulate_gui

help:
	@echo -e ""
	@echo -e "$(GREEN)Available targets:$(RESET)"
	@echo -e "  compile         - Compile RTL with ModelSim"
	@echo -e "  simulate        - Run batch simulation"
	@echo -e "  simulate_gui    - Run GUI simulation"
	@echo -e "  lint            - Run Verilator lint & loop check"
	@echo -e "  verilate        - Build Verilator model"
	@echo -e "  run_verilator   - Run Verilator simulation"
	@echo -e "  run             - Run test with RTL+Spike comparison"
	@echo -e "  run_batch       - Run multiple tests"
	@echo -e "  quick_test      - Run RTL only (no Spike)"
	@echo -e "  list_tests      - List available tests"
	@echo -e "  yosys_check     - Run Yosys structural checks"
	@echo -e "  clean           - Clean all build directories"
	@echo -e ""
	@echo -e "$(GREEN)Test List Shortcuts:$(RESET)"
	@echo -e "  isa             - Run all ISA tests"
	@echo -e "  csr             - Run CSR tests"
	@echo -e "  bench           - Run benchmarks (NO_ADDR=1)"
	@echo -e "  all_tests       - Run ALL tests"
	@echo -e "  t T=<name>      - Quick single ISA test"
	@echo -e "  tb T=<name>     - Quick single benchmark (NO_ADDR=1)"
	@echo -e ""
	@echo -e "$(GREEN)CoreMark & Benchmark Shortcuts:$(RESET)"
	@echo -e "  cm              - Build and run CoreMark"
	@echo -e "  cm_run          - Quick CoreMark run (skip rebuild)"
	@echo -e "  coremark        - Build CoreMark only"
	@echo -e "  coremark_help   - Show CoreMark help"
	@echo -e ""
	@echo -e "$(YELLOW)Build Profiles:$(RESET)"
	@echo -e "  MODE=debug      - Default, full tracing, assertions ON"
	@echo -e "  MODE=release    - Optimized, minimal logging"
	@echo -e "  MODE=test       - RISC-V tests & assertions"
	@echo -e ""
	@echo -e "$(YELLOW)Log Management:$(RESET)"
	@echo -e "  CLEAN_LOGS=1    - Clear all logs before batch run"
	@echo -e ""
	@echo -e "$(GREEN)Test Examples:$(RESET)"
	@echo -e "  make run TEST_NAME=rv32ui-p-add SIM=verilator"
	@echo -e "  make run_batch SIM=verilator"
	@echo -e "  make t T=rv32ui-p-add"
	@echo -e "  make tb T=dhrystone MAX_CYCLES=1000000"
	@echo -e "  make isa"
	@echo -e "  make bench"
	@echo -e "  make bench CLEAN_LOGS=1  # Clear old logs first"
	@echo -e "  make cm                   # Run CoreMark"
	@echo -e "  make help_lists  # Show detailed list commands"
	@echo -e "  make help_test   # Show detailed test commands"
	@echo -e ""
	@echo -e "$(GREEN)Simulation Examples:$(RESET)"
	@echo -e "  make simulate_gui MODE=debug"
	@echo -e "  make verilate MODE=release"
	@echo -e "  make yosys_check MODE=test"
	@echo -e ""