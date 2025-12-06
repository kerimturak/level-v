# ============================================================
# Dhrystone Benchmark for Ceres-V
# ============================================================
# Classic MIPS benchmark, useful for comparing CPU performance
# https://github.com/riscv-software-src/riscv-tests (benchmarks)

.PHONY: dhrystone dhrystone_clone dhrystone_setup dhrystone_build dhrystone_run dhrystone_clean dhrystone_help

# ============================================================
# Configuration
# ============================================================

# Use the riscv-tests benchmarks or standalone
DHRYSTONE_STANDALONE := 1

# Paths
DHRYSTONE_ENV_SRC    := $(ENV_DIR)/dhrystone
DHRYSTONE_BUILD_DIR  := $(BUILD_DIR)/tests/dhrystone
DHRYSTONE_LOG_DIR    := $(RESULTS_DIR)/logs/$(SIM)/dhrystone

# Output
DHRYSTONE_ELF        := $(DHRYSTONE_BUILD_DIR)/dhrystone.elf
DHRYSTONE_HEX        := $(DHRYSTONE_BUILD_DIR)/dhrystone.bin
DHRYSTONE_MEM        := $(DHRYSTONE_BUILD_DIR)/dhrystone.mem
DHRYSTONE_DUMP       := $(DHRYSTONE_BUILD_DIR)/dhrystone.dump

# Compiler settings
DHRY_CC              := $(RISCV_PREFIX)-gcc
DHRY_OBJCOPY         := $(RISCV_PREFIX)-objcopy
DHRY_OBJDUMP         := $(RISCV_PREFIX)-objdump
DHRY_SIZE            := $(RISCV_PREFIX)-size

# Architecture flags
DHRY_MARCH           := rv32imc_zicsr
DHRY_MABI            := ilp32

# Compiler flags (optimize for performance, avoid inline to keep structure)
DHRY_CFLAGS          := -march=$(DHRY_MARCH) -mabi=$(DHRY_MABI) \
                        -O3 -fno-inline -funroll-loops \
                        -static -nostdlib -nostartfiles \
                        -DTIME -DDHRY_ITERS=100000 \
                        -DCPU_MHZ=50

# Linker
DHRY_LDSCRIPT        := $(DHRYSTONE_ENV_SRC)/link.ld
DHRY_LDFLAGS         := -T$(DHRY_LDSCRIPT) -Wl,--gc-sections

# Python scripts
ELF_TO_MEM           := $(SCRIPT_DIR)/python/elf_to_mem.py

# ============================================================
# Main Targets
# ============================================================

dhrystone: dhrystone_setup dhrystone_build
	@echo -e "$(GREEN)[DHRYSTONE] $(SUCCESS) Build complete$(RESET)"

# ============================================================
# Setup Environment
# ============================================================

dhrystone_setup:
	@echo -e "$(YELLOW)[DHRYSTONE] Setting up environment...$(RESET)"
	@mkdir -p $(DHRYSTONE_BUILD_DIR)
	@mkdir -p $(DHRYSTONE_ENV_SRC)
	@if [ ! -f "$(DHRY_LDSCRIPT)" ]; then \
		echo -e "$(YELLOW)[DHRYSTONE] Environment files need to be created$(RESET)"; \
	fi
	@echo -e "$(GREEN)[OK] Setup complete$(RESET)"

# ============================================================
# Build
# ============================================================

dhrystone_build: dhrystone_setup
	@echo -e "$(YELLOW)[DHRYSTONE] Building benchmark...$(RESET)"
	@# Compile all source files
	$(DHRY_CC) $(DHRY_CFLAGS) $(DHRY_LDFLAGS) \
		-I$(DHRYSTONE_ENV_SRC) \
		$(DHRYSTONE_ENV_SRC)/crt0.S \
		$(DHRYSTONE_ENV_SRC)/syscalls.c \
		$(DHRYSTONE_ENV_SRC)/dhry_1.c \
		$(DHRYSTONE_ENV_SRC)/dhry_2.c \
		-o $(DHRYSTONE_ELF)
	@# Generate outputs
	$(DHRY_OBJDUMP) -d $(DHRYSTONE_ELF) > $(DHRYSTONE_DUMP)
	$(DHRY_OBJCOPY) -O binary $(DHRYSTONE_ELF) $(DHRYSTONE_HEX)
	@python3 $(ELF_TO_MEM) --in $(DHRYSTONE_HEX) --out $(DHRYSTONE_MEM) \
		--addr 0x80000000 --block-bytes 4 --word-size 4 --word-endian little --word-order high-to-low
	@# Show size
	$(DHRY_SIZE) $(DHRYSTONE_ELF)
	@echo -e "$(GREEN)[OK] Dhrystone built: $(DHRYSTONE_MEM)$(RESET)"

# ============================================================
# Run
# ============================================================

# Ensure verilator is built with config from JSON
dhrystone_verilate:
	@echo -e "$(YELLOW)[DHRYSTONE] Building Verilator with dhrystone config...$(RESET)"
	@$(MAKE) --no-print-directory verilate TEST_TYPE=dhrystone

dhrystone_run: dhrystone_build dhrystone_verilate
	@echo -e "$(YELLOW)[DHRYSTONE] Running benchmark...$(RESET)"
	@mkdir -p $(DHRYSTONE_LOG_DIR)
	$(MAKE) --no-print-directory run \
		TEST_TYPE=dhrystone \
		TEST_NAME=dhrystone \
		MEM_DIR="$(DHRYSTONE_BUILD_DIR)" \
		ELF_DIR="$(DHRYSTONE_BUILD_DIR)" \
		DUMP_DIR="$(DHRYSTONE_BUILD_DIR)" \
		HEX_DIR="$(DHRYSTONE_BUILD_DIR)" \
		TEST_LOG_DIR="$(DHRYSTONE_LOG_DIR)" \
		RTL_LOG_DIR="$(DHRYSTONE_LOG_DIR)"

# Generate flist for run_flist compatibility
dhrystone_flist: dhrystone_build
	@echo -e "$(YELLOW)[DHRYSTONE] Generating test file list...$(RESET)"
	@echo "dhrystone" > $(SIM_DIR)/test/dhrystone.flist
	@echo -e "$(GREEN)[OK] Generated dhrystone.flist$(RESET)"

# Run via run_flist (for batch processing)
dhrystone_run_all: dhrystone_flist dhrystone_verilate
	@echo -e "$(YELLOW)[DHRYSTONE] Running via run_flist...$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		TEST_TYPE=dhrystone \
		FLIST="$(SIM_DIR)/test/dhrystone.flist" \
		MEM_DIR="$(DHRYSTONE_BUILD_DIR)" \
		ELF_DIR="$(DHRYSTONE_BUILD_DIR)" \
		DUMP_DIR="$(DHRYSTONE_BUILD_DIR)" \
		HEX_DIR="$(DHRYSTONE_BUILD_DIR)" \
		TEST_LOG_DIR="$(DHRYSTONE_LOG_DIR)" \
		RTL_LOG_DIR="$(DHRYSTONE_LOG_DIR)"

# ============================================================
# Clean
# ============================================================

dhrystone_clean:
	@echo -e "$(YELLOW)[DHRYSTONE] Cleaning...$(RESET)"
	@rm -rf $(DHRYSTONE_BUILD_DIR)
	@echo -e "$(GREEN)[OK] Clean complete$(RESET)"

# ============================================================
# Help
# ============================================================

dhrystone_help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)           Dhrystone Benchmark$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Build:$(RESET)"
	@echo -e "  make dhrystone        Build Dhrystone benchmark"
	@echo -e "  make dhrystone_clean  Clean build files"
	@echo -e ""
	@echo -e "$(CYAN)Simulation:$(RESET)"
	@echo -e "  make dhrystone_run      Build and run benchmark"
	@echo -e "  make dhrystone_run_all  Run via run_flist"
	@echo -e ""
	@echo -e "$(CYAN)Config Files:$(RESET)"
	@echo -e "  sim/test/dhrystone.flist            Test list"
	@echo -e "  script/config/tests/dhrystone.json  Simulation config"
	@echo -e ""
	@echo -e "$(CYAN)Configuration:$(RESET)"
	@echo -e "  DHRY_ITERS   Number of iterations (default: 100000)"
	@echo -e "  CPU_MHZ      CPU frequency for DMIPS calculation"
	@echo -e ""
	@echo -e "$(CYAN)Results:$(RESET)"
	@echo -e "  DMIPS/MHz = (Dhrystones/second) / 1757 / MHz"
	@echo -e ""
