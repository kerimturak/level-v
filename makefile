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
include script/makefiles/test/coremark_spike.mk
include script/makefiles/test/coremark_minimal.mk
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
include script/makefiles/synth/openlane.mk

# Utility Tools
include script/makefiles/tools/clean.mk
include script/makefiles/tools/konata.mk
include script/makefiles/tools/surfer.mk
include script/makefiles/tools/help.mk

# Linting Tools
include script/makefiles/lint/lint.mk

.PHONY: all compile simulate simulate_gui lint verilate run_verilator yosys_check clean

all: simulate_gui

# Help target'ı artık tools/help.mk'den geliyor