# ============================================================
# Embench-IoT Benchmark Suite for Ceres-V
# ============================================================
# Modern embedded benchmark suite from embench.org
# https://github.com/embench/embench-iot

.PHONY: embench embench_clone embench_setup embench_build embench_run embench_clean embench_help
.PHONY: embench_list embench_report

# ============================================================
# Configuration
# ============================================================

# Repository URL
EMBENCH_REPO_URL   := https://github.com/embench/embench-iot.git
EMBENCH_ROOT       := $(SUBREPO_DIR)/embench-iot

# Paths
EMBENCH_ENV_SRC    := $(ENV_DIR)/embench
EMBENCH_BUILD_DIR  := $(BUILD_DIR)/tests/embench
EMBENCH_LOG_DIR    := $(RESULTS_DIR)/logs/$(SIM)/embench

# Output directories
EMBENCH_ELF_DIR    := $(EMBENCH_BUILD_DIR)/elf
EMBENCH_HEX_DIR    := $(EMBENCH_BUILD_DIR)/hex
EMBENCH_MEM_DIR    := $(EMBENCH_BUILD_DIR)/mem
EMBENCH_DUMP_DIR   := $(EMBENCH_BUILD_DIR)/dump

# Compiler settings
EMBENCH_CC         := $(RISCV_PREFIX)-gcc
EMBENCH_OBJCOPY    := $(RISCV_PREFIX)-objcopy
EMBENCH_OBJDUMP    := $(RISCV_PREFIX)-objdump
EMBENCH_SIZE       := $(RISCV_PREFIX)-size

# Architecture flags
EMBENCH_MARCH      := rv32imc_zicsr
EMBENCH_MABI       := ilp32

# Compiler flags
EMBENCH_CFLAGS     := -march=$(EMBENCH_MARCH) -mabi=$(EMBENCH_MABI) \
                      -O2 -ffunction-sections -fdata-sections \
                      -static -nostdlib -nostartfiles \
                      -DCPU_MHZ=50

# Linker flags (include libgcc for soft-float support)
EMBENCH_LDSCRIPT   := $(EMBENCH_ENV_SRC)/link.ld
EMBENCH_LDFLAGS    := -T$(EMBENCH_LDSCRIPT) -Wl,--gc-sections -lgcc

# Python scripts
ELF_TO_MEM         := $(SCRIPT_DIR)/python/elf_to_mem.py

# ============================================================
# Embench Benchmark Configuration
# ============================================================
# All available benchmarks:
#   aha-mont64, crc32, cubic, edn, huffbench, matmult-int, md5sum,
#   minver, nbody, nettle-aes, nettle-sha256, nsichneu, picojpeg,
#   primecount, qrduino, sglib-combined, slre, st, statemate,
#   tarfind, ud, wikisort
#
# Notes:
#   - wikisort: excluded (bool typedef conflict with stdbool.h)
#
# Floating-point benchmarks (require soft-float via -lgcc or FPU):
#   cubic, minver, nbody, st, ud
#   Uncomment below if your CPU supports floating-point
#
# EMBENCH_FP_BENCHMARKS := cubic minver nbody st ud
#
# Integer-only benchmarks (16 total - works on RV32IMC without FPU):
EMBENCH_BENCHMARKS := aha-mont64 crc32 edn huffbench matmult-int \
                      md5sum nettle-aes nettle-sha256 nsichneu picojpeg \
                      primecount qrduino sglib-combined slre statemate tarfind
#
# Full benchmark list (uncomment if FPU available):
# EMBENCH_BENCHMARKS := aha-mont64 crc32 cubic edn huffbench matmult-int \
#                       md5sum minver nbody nettle-aes nettle-sha256 \
#                       nsichneu picojpeg primecount qrduino \
#                       sglib-combined slre st statemate tarfind ud

# ============================================================
# Main Targets
# ============================================================

embench: embench_clone embench_setup embench_build
	@echo -e "$(GREEN)[EMBENCH] $(SUCCESS) Build complete$(RESET)"
	@echo -e "$(GREEN)[EMBENCH] Built benchmarks:$(RESET)"
	@ls -1 $(EMBENCH_ELF_DIR)/*.elf 2>/dev/null | wc -l | xargs -I{} echo -e "  {} benchmarks ready"

# ============================================================
# Clone Repository
# ============================================================

embench_clone:
	@echo -e "$(YELLOW)[EMBENCH] Checking embench-iot repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(EMBENCH_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(EMBENCH_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone --depth=1 $(EMBENCH_REPO_URL); \
		echo -e "$(GREEN)[OK] embench-iot cloned.$(RESET)"; \
	else \
		echo -e "$(GREEN)[SKIP] embench-iot already exists.$(RESET)"; \
	fi

# ============================================================
# Setup Environment
# ============================================================

embench_setup: embench_clone
	@echo -e "$(YELLOW)[EMBENCH] Setting up Ceres-V environment...$(RESET)"
	@mkdir -p $(EMBENCH_ENV_SRC)
	@mkdir -p $(EMBENCH_ELF_DIR) $(EMBENCH_HEX_DIR) $(EMBENCH_MEM_DIR) $(EMBENCH_DUMP_DIR)
	@# Create environment files if not exists
	@if [ ! -f "$(EMBENCH_LDSCRIPT)" ]; then \
		$(MAKE) --no-print-directory _embench_gen_env; \
	fi
	@echo -e "$(GREEN)[OK] Environment ready.$(RESET)"

# Generate environment files
_embench_gen_env:
	@echo -e "$(YELLOW)[EMBENCH] Generating environment files...$(RESET)"
	@# Linker script will be created separately
	@# Startup file will be created separately

# ============================================================
# Build Benchmarks
# ============================================================

embench_build: embench_setup
	@echo -e "$(YELLOW)[EMBENCH] Building benchmarks...$(RESET)"
	@PASS=0; FAIL=0; \
	for bench in $(EMBENCH_BENCHMARKS); do \
		if $(MAKE) --no-print-directory _embench_build_one BENCH=$$bench; then \
			PASS=$$((PASS + 1)); \
		else \
			FAIL=$$((FAIL + 1)); \
		fi; \
	done; \
	echo -e "$(GREEN)[EMBENCH] Build complete: $$PASS passed, $$FAIL failed$(RESET)"

# Build single benchmark
# Embench structure: src/<bench>/*.c + support/main.c + support/board.c + support/beebsc.c
_embench_build_one:
	@SRC_DIR="$(EMBENCH_ROOT)/src/$(BENCH)"; \
	SUPPORT_DIR="$(EMBENCH_ROOT)/support"; \
	if [ ! -d "$$SRC_DIR" ]; then \
		echo -e "  $(RED)✗ $(BENCH): source not found$(RESET)"; \
		exit 1; \
	fi; \
	echo -e "  $(YELLOW)→ Building: $(BENCH)$(RESET)"; \
	BENCH_SRCS="$$(find $$SRC_DIR -name '*.c')"; \
	SUPPORT_SRCS="$$SUPPORT_DIR/main.c $$SUPPORT_DIR/beebsc.c $$SUPPORT_DIR/board.c"; \
	INCS="-I$$SRC_DIR -I$$SUPPORT_DIR -I$(EMBENCH_ENV_SRC) -DHAVE_BOARDSUPPORT_H"; \
	$(EMBENCH_CC) $(EMBENCH_CFLAGS) $$INCS $(EMBENCH_LDFLAGS) \
		-o $(EMBENCH_ELF_DIR)/$(BENCH).elf \
		$(EMBENCH_ENV_SRC)/crt0.S $$BENCH_SRCS $$SUPPORT_SRCS $(EMBENCH_ENV_SRC)/syscalls.c 2>&1 && \
	$(EMBENCH_OBJDUMP) -d $(EMBENCH_ELF_DIR)/$(BENCH).elf > $(EMBENCH_DUMP_DIR)/$(BENCH).dump && \
	$(EMBENCH_OBJCOPY) -O binary $(EMBENCH_ELF_DIR)/$(BENCH).elf $(EMBENCH_HEX_DIR)/$(BENCH).bin && \
	python3 $(ELF_TO_MEM) --in $(EMBENCH_HEX_DIR)/$(BENCH).bin --out $(EMBENCH_MEM_DIR)/$(BENCH).mem \
		--addr 0x80000000 --block-bytes 4 --word-size 4 --word-endian little --word-order high-to-low && \
	echo -e "  $(GREEN)$(SUCCESS) $(BENCH)$(RESET)"

# ============================================================
# Run Benchmarks
# ============================================================

embench_run: embench_build embench_verilate
	@echo -e "$(YELLOW)[EMBENCH] Running benchmarks...$(RESET)"
	@mkdir -p $(EMBENCH_LOG_DIR)
	@PASS=0; FAIL=0; TOTAL=0; \
	for bench in $(EMBENCH_BENCHMARKS); do \
		if [ -f "$(EMBENCH_MEM_DIR)/$$bench.mem" ]; then \
			TOTAL=$$((TOTAL + 1)); \
			echo -e "  $(YELLOW)→ Running: $$bench$(RESET)"; \
			if $(MAKE) --no-print-directory run \
				TEST_TYPE=embench \
				TEST_NAME=$$bench \
				MEM_DIR="$(EMBENCH_MEM_DIR)" \
				ELF_DIR="$(EMBENCH_ELF_DIR)" \
				DUMP_DIR="$(EMBENCH_DUMP_DIR)" \
				HEX_DIR="$(EMBENCH_HEX_DIR)" \
				TEST_LOG_DIR="$(EMBENCH_LOG_DIR)/$$bench" \
				RTL_LOG_DIR="$(EMBENCH_LOG_DIR)/$$bench" 2>&1; then \
				PASS=$$((PASS + 1)); \
				echo -e "  $(GREEN)$(SUCCESS) $$bench PASSED$(RESET)"; \
			else \
				FAIL=$$((FAIL + 1)); \
				echo -e "  $(RED)✗ $$bench FAILED$(RESET)"; \
			fi; \
		fi; \
	done; \
	echo ""; \
	echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"; \
	echo -e "$(CYAN)  EMBENCH RESULTS: $$PASS/$$TOTAL passed, $$FAIL failed$(RESET)"; \
	echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"; \
	if [ $$FAIL -gt 0 ]; then \
		echo -e "$(RED)[EMBENCH] ✗ Some benchmarks failed$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)[EMBENCH] $(SUCCESS) All benchmarks passed$(RESET)"; \
	fi

# ============================================================
# List and Report
# ============================================================

embench_list:
	@echo -e "$(CYAN)[EMBENCH] Available benchmarks:$(RESET)"
	@for bench in $(EMBENCH_BENCHMARKS); do \
		echo -e "  - $$bench"; \
	done

embench_report:
	@echo -e "$(CYAN)[EMBENCH] Size Report:$(RESET)"
	@if [ -d "$(EMBENCH_ELF_DIR)" ]; then \
		for elf in $(EMBENCH_ELF_DIR)/*.elf; do \
			if [ -f "$$elf" ]; then \
				name=$$(basename $$elf .elf); \
				size=$$($(EMBENCH_SIZE) $$elf | tail -1 | awk '{print $$1+$$2}'); \
				printf "  %-20s %8s bytes\n" "$$name" "$$size"; \
			fi; \
		done; \
	else \
		echo -e "  $(YELLOW)No builds found. Run 'make embench_build' first.$(RESET)"; \
	fi

# ============================================================
# Simulation with run_flist
# ============================================================

# Generate flist for run_flist compatibility
embench_flist: embench_build
	@echo -e "$(YELLOW)[EMBENCH] Generating test file list...$(RESET)"
	@> $(SIM_DIR)/test/embench.flist.tmp
	@for bench in $(EMBENCH_BENCHMARKS); do \
		if [ -f "$(EMBENCH_MEM_DIR)/$$bench.mem" ]; then \
			echo "$$bench" >> $(SIM_DIR)/test/embench.flist.tmp; \
		fi; \
	done
	@mv $(SIM_DIR)/test/embench.flist.tmp $(SIM_DIR)/test/embench.flist
	@count=$$(wc -l < $(SIM_DIR)/test/embench.flist); \
	echo -e "$(GREEN)[OK] Generated embench.flist with $$count benchmarks$(RESET)"

# Ensure verilator is built with config from JSON
embench_verilate:
	@echo -e "$(YELLOW)[EMBENCH] Building Verilator with embench config...$(RESET)"
	@$(MAKE) --no-print-directory verilate TEST_TYPE=embench

# Run all embench tests using run_flist
embench_run_all: embench_flist embench_verilate
	@echo -e "$(YELLOW)[EMBENCH] Running all benchmarks via run_flist...$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		TEST_TYPE=embench \
		FLIST="$(SIM_DIR)/test/embench.flist" \
		MEM_DIR="$(EMBENCH_MEM_DIR)" \
		ELF_DIR="$(EMBENCH_ELF_DIR)" \
		DUMP_DIR="$(EMBENCH_DUMP_DIR)" \
		HEX_DIR="$(EMBENCH_HEX_DIR)" \
		TEST_LOG_DIR="$(EMBENCH_LOG_DIR)" \
		RTL_LOG_DIR="$(EMBENCH_LOG_DIR)"

# Run single embench benchmark
embench_run_one: embench_verilate
	@if [ -z "$(BENCH)" ]; then \
		echo -e "$(RED)[ERROR] Specify benchmark: make embench_run_one BENCH=crc32$(RESET)"; \
		exit 1; \
	fi
	@if [ ! -f "$(EMBENCH_MEM_DIR)/$(BENCH).mem" ]; then \
		echo -e "$(RED)[ERROR] Benchmark not found: $(BENCH)$(RESET)"; \
		exit 1; \
	fi
	@echo -e "$(YELLOW)[EMBENCH] Running: $(BENCH)$(RESET)"
	@$(MAKE) --no-print-directory run \
		TEST_TYPE=embench \
		TEST_NAME=$(BENCH) \
		MEM_DIR="$(EMBENCH_MEM_DIR)" \
		ELF_DIR="$(EMBENCH_ELF_DIR)" \
		DUMP_DIR="$(EMBENCH_DUMP_DIR)" \
		HEX_DIR="$(EMBENCH_HEX_DIR)" \
		TEST_LOG_DIR="$(EMBENCH_LOG_DIR)/$(BENCH)" \
		RTL_LOG_DIR="$(EMBENCH_LOG_DIR)/$(BENCH)"

# ============================================================
# Clean
# ============================================================

embench_clean:
	@echo -e "$(YELLOW)[EMBENCH] Cleaning build files...$(RESET)"
	@rm -rf $(EMBENCH_BUILD_DIR)
	@echo -e "$(GREEN)[OK] Clean complete.$(RESET)"

# ============================================================
# Help
# ============================================================

embench_help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)        Embench-IoT Benchmark Suite$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Build:$(RESET)"
	@echo -e "  make embench              Build all benchmarks"
	@echo -e "  make embench_clean        Clean build files"
	@echo -e ""
	@echo -e "$(CYAN)Simulation:$(RESET)"
	@echo -e "  make embench_run          Build and run all benchmarks"
	@echo -e "  make embench_run_all      Run all benchmarks (via run_flist)"
	@echo -e "  make embench_run_one BENCH=<name>  Run single benchmark"
	@echo -e ""
	@echo -e "$(CYAN)Info:$(RESET)"
	@echo -e "  make embench_list         List available benchmarks"
	@echo -e "  make embench_report       Show code size report"
	@echo -e "  make embench_flist        Generate test file list"
	@echo -e ""
	@echo -e "$(CYAN)Config Files:$(RESET)"
	@echo -e "  sim/test/embench.flist           Test list"
	@echo -e "  script/config/tests/embench.json Simulation config"
	@echo -e ""
	@echo -e "$(CYAN)Integer Benchmarks (16):$(RESET)"
	@echo -e "  aha-mont64, crc32, edn, huffbench, matmult-int, md5sum"
	@echo -e "  nettle-aes, nettle-sha256, nsichneu, picojpeg, primecount"
	@echo -e "  qrduino, sglib-combined, slre, statemate, tarfind"
	@echo -e ""
	@echo -e "$(CYAN)FP Benchmarks (requires FPU - commented out):$(RESET)"
	@echo -e "  cubic, minver, nbody, st, ud"
	@echo -e ""
