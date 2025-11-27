# ==================================================
# CERES RISC-V Makefile (Top-Level Controller)
# ==================================================
.DEFAULT_GOAL := help

SHELL := /bin/bash

include script/makefiles/config.mk
include script/makefiles/profiles.mk
include script/makefiles/rules_modelsim.mk
include script/makefiles/rules_verilator.mk
include script/makefiles/rules_yosys.mk
include script/makefiles/rules_spike.mk
include script/makefiles/rules_run_test.mk     # ← YENİ
include script/makefiles/rules_clean.mk
include script/makefiles/rules_isa_import.mk
include script/makefiles/rules_arch_test.mk
include script/makefiles/rules_konata.mk
include script/makefiles/rules_coremark.mk

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
	@echo -e "  run             - Run test with RTL+Spike comparison"  # ← YENİ
	@echo -e "  run_batch       - Run multiple tests"                  # ← YENİ
	@echo -e "  quick_test      - Run RTL only (no Spike)"            # ← YENİ
	@echo -e "  list_tests      - List available tests"                # ← YENİ
	@echo -e "  yosys_check     - Run Yosys structural checks"
	@echo -e "  clean           - Clean all build directories"
	@echo -e ""
	@echo -e "$(YELLOW)Build Profiles:$(RESET)"
	@echo -e "  MODE=debug      - Default, full tracing, assertions ON"
	@echo -e "  MODE=release    - Optimized, minimal logging"
	@echo -e "  MODE=test       - RISC-V tests & assertions"
	@echo -e ""
	@echo -e "$(GREEN)Test Examples:$(RESET)"
	@echo -e "  make run TEST_NAME=rv32ui-p-add SIM=verilator"
	@echo -e "  make run_batch SIM=verilator"
	@echo -e "  make help_test  # Show detailed test commands"
	@echo -e ""
	@echo -e "$(GREEN)Simulation Examples:$(RESET)"
	@echo -e "  make simulate_gui MODE=debug"
	@echo -e "  make verilate MODE=release"
	@echo -e "  make yosys_check MODE=test"
	@echo -e ""