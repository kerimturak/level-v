# ============================================================
# MLPerf Tiny — Level-V stub harness (CoreMark-like workflow, separate rules)
# ============================================================
# Uses official API from subrepo/mlperf-tiny/benchmark; inference is a stub.
#   make mlperf_tiny_init     # ensure mlcommons/tiny clone (from tinyml_submodules.mk)
#   make mlperf_tiny          # link + .mem
#   make run_mlperf_tiny      # Verilator (like run_coremark, no CoreMark coupling)
# ============================================================

.PHONY: mlperf_tiny mlperf_tiny_check mlperf_tiny_gen_linker mlperf_tiny_build
.PHONY: mlperf_tiny_clean mlperf_tiny_help run_mlperf_tiny

MLPERF_TINY_REPO_DIR := $(SUBREPO_DIR)/mlperf-tiny
MLPERF_TINY_BENCH    := $(MLPERF_TINY_REPO_DIR)/benchmark
MLPERF_TINY_PORT     := $(ROOT_DIR)/env/mlperf-tiny/levelv
MLPERF_TINY_BUILD    := $(BUILD_DIR)/tests/mlperf_tiny

MLPERF_TINY_LINKER_GEN := $(SCRIPT_DIR)/python/gen_linker.py
MLPERF_TINY_MEMORY_MAP := $(MLPERF_TINY_PORT)/memory_map.yaml
MLPERF_TINY_LINK_LD    := $(MLPERF_TINY_PORT)/link.ld
MLPERF_TINY_MEM_HDR   := $(MLPERF_TINY_PORT)/memory_map.h

MLPERF_TINY_ELF  := $(MLPERF_TINY_BUILD)/mlperf_tiny.elf
MLPERF_TINY_BIN  := $(MLPERF_TINY_BUILD)/mlperf_tiny.bin
MLPERF_TINY_MEM  := $(MLPERF_TINY_BUILD)/mlperf_tiny.mem
MLPERF_TINY_DUMP := $(MLPERF_TINY_BUILD)/mlperf_tiny.dump

ELF_TO_MEM := $(SCRIPT_DIR)/python/elf_to_mem.py

# Deferred: RISCV_PREFIX is defined later in the root makefile.
MLPERF_TINY_CXX     = $(RISCV_PREFIX)-g++
MLPERF_TINY_OBJCOPY = $(RISCV_PREFIX)-objcopy
MLPERF_TINY_OBJDUMP = $(RISCV_PREFIX)-objdump

MLPERF_TINY_INCLUDES := \
	-I$(MLPERF_TINY_BENCH) \
	-I$(ROOT_DIR)/env/common \
	$(LEVELV_CPU_CLK_CPPFLAGS)

MLPERF_TINY_CXXFLAGS := -std=c++17 -Os \
	-fno-exceptions -fno-rtti -fno-threadsafe-statics \
	-ffunction-sections -fdata-sections -fomit-frame-pointer \
	-march=rv32imc_zicsr -mabi=ilp32 -mcmodel=medany \
	-include $(MLPERF_TINY_PORT)/th_model_version_force.h \
	$(MLPERF_TINY_INCLUDES)

MLPERF_TINY_LDFLAGS  := -nostartfiles \
	-T$(MLPERF_TINY_LINK_LD) \
	-Wl,--gc-sections \
	-march=rv32imc_zicsr -mabi=ilp32 \
	-mno-relax \
	--specs=nano.specs

MLPERF_TINY_SRC_INTERNAL := $(MLPERF_TINY_BENCH)/api/internally_implemented.cpp
MLPERF_TINY_SRC_PORT := \
	$(MLPERF_TINY_PORT)/crt0.S \
	$(MLPERF_TINY_PORT)/levelv_mlp_printf.cpp \
	$(MLPERF_TINY_PORT)/submitter_implemented.cpp \
	$(MLPERF_TINY_PORT)/main.cpp

MLPERF_TINY_OBJ_DIR := $(MLPERF_TINY_BUILD)/obj
MLPERF_TINY_OBJS := \
	$(MLPERF_TINY_OBJ_DIR)/crt0.o \
	$(MLPERF_TINY_OBJ_DIR)/internally_implemented.o \
	$(MLPERF_TINY_OBJ_DIR)/levelv_mlp_printf.o \
	$(MLPERF_TINY_OBJ_DIR)/submitter_implemented.o \
	$(MLPERF_TINY_OBJ_DIR)/main.o

mlperf_tiny: mlperf_tiny_check mlperf_tiny_gen_linker mlperf_tiny_build
	@echo -e "$(GREEN)[MLPERF_TINY] $(SUCCESS) Build complete$(RESET)"
	@echo -e "  ELF: $(MLPERF_TINY_ELF)"
	@echo -e "  MEM: $(MLPERF_TINY_MEM)"

mlperf_tiny_check:
	@if [ ! -f "$(MLPERF_TINY_SRC_INTERNAL)" ]; then \
		echo -e "$(RED)[MLPERF_TINY] Missing $(MLPERF_TINY_SRC_INTERNAL)$(RESET)"; \
		echo -e "$(YELLOW)Run: make mlperf_tiny_init$(RESET)"; \
		exit 1; \
	fi

mlperf_tiny_gen_linker: mlperf_tiny_check
	@$(MKDIR) "$(MLPERF_TINY_BUILD)" "$(MLPERF_TINY_OBJ_DIR)"
	@if [ ! -f "$(MLPERF_TINY_MEMORY_MAP)" ]; then \
		echo -e "$(RED)[MLPERF_TINY] Missing $(MLPERF_TINY_MEMORY_MAP)$(RESET)"; \
		exit 1; \
	fi
	@echo -e "$(YELLOW)[MLPERF_TINY] Generating linker script...$(RESET)"
	@$(PYTHON) $(MLPERF_TINY_LINKER_GEN) \
		"$(MLPERF_TINY_MEMORY_MAP)" "$(MLPERF_TINY_LINK_LD)" \
		--header "$(MLPERF_TINY_MEM_HDR)" --verbose

$(MLPERF_TINY_OBJ_DIR)/crt0.o: $(MLPERF_TINY_PORT)/crt0.S
	$(MLPERF_TINY_CXX) $(MLPERF_TINY_CXXFLAGS) -x assembler-with-cpp -c $< -o $@

$(MLPERF_TINY_OBJ_DIR)/internally_implemented.o: $(MLPERF_TINY_SRC_INTERNAL)
	$(MLPERF_TINY_CXX) $(MLPERF_TINY_CXXFLAGS) -c $< -o $@

$(MLPERF_TINY_OBJ_DIR)/levelv_mlp_printf.o: $(MLPERF_TINY_PORT)/levelv_mlp_printf.cpp
	$(MLPERF_TINY_CXX) $(MLPERF_TINY_CXXFLAGS) -c $< -o $@

$(MLPERF_TINY_OBJ_DIR)/submitter_implemented.o: $(MLPERF_TINY_PORT)/submitter_implemented.cpp
	$(MLPERF_TINY_CXX) $(MLPERF_TINY_CXXFLAGS) -c $< -o $@

$(MLPERF_TINY_OBJ_DIR)/main.o: $(MLPERF_TINY_PORT)/main.cpp
	$(MLPERF_TINY_CXX) $(MLPERF_TINY_CXXFLAGS) -c $< -o $@

mlperf_tiny_build: mlperf_tiny_gen_linker $(MLPERF_TINY_OBJS)
	@echo -e "$(YELLOW)[MLPERF_TINY] Linking...$(RESET)"
	$(MLPERF_TINY_CXX) $(MLPERF_TINY_CXXFLAGS) -o $(MLPERF_TINY_ELF) $(MLPERF_TINY_OBJS) $(MLPERF_TINY_LDFLAGS) -lc -lstdc++ -lm -lgcc
	$(MLPERF_TINY_OBJCOPY) -O binary $(MLPERF_TINY_ELF) $(MLPERF_TINY_BIN)
	$(MLPERF_TINY_OBJDUMP) -d $(MLPERF_TINY_ELF) > $(MLPERF_TINY_DUMP)
	@$(PYTHON) $(ELF_TO_MEM) \
		--in $(MLPERF_TINY_BIN) \
		--out $(MLPERF_TINY_MEM) \
		--addr 0x80000000 \
		--block-bytes 4 \
		--word-size 4 \
		--word-endian little \
		--word-order high-to-low

MLPERF_TINY_LOG_DIR := $(RESULTS_DIR)/logs/$(SIM)/mlperf_tiny

run_mlperf_tiny: mlperf_tiny
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  MLPerf Tiny (stub) — Verilator$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@if [ -d "$(MLPERF_TINY_LOG_DIR)" ]; then \
		rm -rf "$(MLPERF_TINY_LOG_DIR)"; \
	fi
	@$(MKDIR) "$(MLPERF_TINY_LOG_DIR)"
	@set -e; \
	if [ "$(origin MAX_CYCLES)" = "command line" ]; then \
	  MT_MAX="$(MAX_CYCLES)"; \
	else \
	  MT_MAX=5000000; \
	fi; \
	$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=mlperf_tiny \
		TEST_CONFIG=mlperf_tiny \
		MEM_FILE=$(MLPERF_TINY_MEM) \
		NO_ADDR=1 \
		MAX_CYCLES=$$MT_MAX \
		VERILATOR_LOG_DIR=$(MLPERF_TINY_LOG_DIR)
	@echo -e "$(GREEN)  Done$(RESET)"

mlperf_tiny_clean:
	rm -rf "$(MLPERF_TINY_BUILD)"

mlperf_tiny_help:
	@echo -e "$(GREEN)MLPerf Tiny (Level-V stub harness)$(RESET)"
	@echo -e "  make mlperf_tiny_init   # get subrepo (see tinyml_submodules.mk)"
	@echo -e "  make mlperf_tiny        # build ELF + mlperf_tiny.mem"
	@echo -e "  make run_mlperf_tiny    # Verilator (TEST_CONFIG=mlperf_tiny)"
	@echo -e "  make mlperf_tiny_clean"
	@echo ""
	@echo "Outputs under $(MLPERF_TINY_BUILD)/"
