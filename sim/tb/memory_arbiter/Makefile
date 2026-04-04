SHELL := /bin/bash
.SHELLFLAGS := -e -u -o pipefail -c

ROOT_DIR := $(shell cd ../../.. && pwd)
RTL_DIR := $(ROOT_DIR)/rtl
INC_DIR := $(RTL_DIR)/include
GEN_DIR := $(ROOT_DIR)/build/gen
GEN_PY := $(ROOT_DIR)/script/python/gen_level_param_profile.py
PROFILE_SVH := $(GEN_DIR)/level_param_profile.svh
TB_DIR := $(ROOT_DIR)/sim/tb/memory_arbiter
BUILD_DIR := $(ROOT_DIR)/build/tb_memory_arbiter
OBJ_DIR := $(BUILD_DIR)/obj_dir
RESULTS_DIR := $(ROOT_DIR)/results/tb_memory_arbiter

TB_SV := $(TB_DIR)/tb_memory_arbiter.sv
TB_CPP := $(TB_DIR)/tb_main.cpp

RTL_SOURCES := \
	$(RTL_DIR)/pkg/level_param.sv \
	$(RTL_DIR)/core/mmu/memory_arbiter.sv

VERILATOR := verilator
VERILATOR_FLAGS := \
	--cc \
	--exe \
	--build \
	-j 4 \
	--top-module tb_memory_arbiter \
	-I$(INC_DIR) \
	-I$(GEN_DIR) \
	--timing \
	--trace-fst \
	--Mdir $(OBJ_DIR) \
	-CFLAGS "-std=c++17 -O2" \
	-LDFLAGS "-lm"

BIN := $(OBJ_DIR)/Vtb_memory_arbiter

.PHONY: all build run clean dirs

all: run

dirs:
	@mkdir -p $(BUILD_DIR) $(OBJ_DIR) $(RESULTS_DIR) $(GEN_DIR)

$(PROFILE_SVH): $(GEN_PY) $(wildcard $(ROOT_DIR)/rtl/cfg/*.cfg)
	@mkdir -p $(GEN_DIR)
	@python3 $(GEN_PY) full_soc --out $(PROFILE_SVH)

build: dirs $(PROFILE_SVH)
	@echo "[BUILD] Building memory_arbiter self-check..."
	@$(VERILATOR) $(VERILATOR_FLAGS) $(RTL_SOURCES) $(TB_SV) $(TB_CPP)
	@echo "[BUILD] Done: $(BIN)"

run: build
	@echo "[RUN] Running memory_arbiter self-check..."
	@cd $(RESULTS_DIR) && $(BIN) 2>&1 | tee simulation.log || true

clean:
	@rm -rf $(BUILD_DIR) $(RESULTS_DIR)
