# =========================================
# CERES RISC-V — Toolchain Configuration
# =========================================

# -----------------------------------------
# Architecture
# -----------------------------------------
XLEN          := 32

# -----------------------------------------
# RISC-V GCC Toolchain
# -----------------------------------------
RISCV_PREFIX   ?= riscv32-unknown-elf
RISCV_MARCH    := rv32imc_zicsr_zifencei_zfinx
RISCV_ABI      := ilp32
RISCV_TARGET   ?= $(HOME)/riscv/target

RISCV_GCC      ?= $(RISCV_PREFIX)-gcc
RISCV_OBJDUMP  ?= $(RISCV_PREFIX)-objdump
RISCV_AR       ?= $(RISCV_PREFIX)-ar
RISCV_OBJCOPY  ?= $(RISCV_PREFIX)-objcopy

# -----------------------------------------
# Spike Simulator
# -----------------------------------------
SPIKE          ?= $(HOME)/tools/spike/bin/spike
SPIKE_ISA      ?= rv32imc_zicntr
SPIKE_PC       ?= 0x80000000
SPIKE_PRIV     ?= m
SPIKE_FLAGS    := --isa=$(SPIKE_ISA) --pc=$(SPIKE_PC) --priv=$(SPIKE_PRIV) --log-commits

# -----------------------------------------
# EDA Tools
# -----------------------------------------
VLIB           := vlib
VLOG           := vlog
VSIM           := vsim
VERILATOR      ?= $(shell command -v verilator 2>/dev/null || echo verilator)
YOSYS          := yosys

# -----------------------------------------
# Python
# -----------------------------------------
PYTHON         ?= python3

# -----------------------------------------
# Build Jobs
# -----------------------------------------
MAKE_JOBS      ?= $(shell nproc)

# -----------------------------------------
# Environment Export
# -----------------------------------------
export XLEN
export RISCV_PREFIX
export PATH
