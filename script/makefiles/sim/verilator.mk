# =========================================
# CERES RISC-V — Verilator Simulation
# =========================================

# -----------------------------------------
# Verilator Paths
# -----------------------------------------
VERILATOR_LOG_DIR  := $(LOG_DIR)/verilator/$(TEST_NAME)
VERILATOR_INCLUDES := $(addprefix -I, $(INC_DIRS))

# -----------------------------------------
# Verilator Defines
# -----------------------------------------
ifeq ($(TEST_TYPE),bench)
  SV_DEFINES += +define+CERES_UART_TX_MONITOR
endif

# Branch Predictor Logger - aktivasyon: BP_LOG=1
ifeq ($(BP_LOG),1)
  SV_DEFINES += +define+BP_LOGGER_EN
endif

# Verbose BP Logger - aktivasyon: BP_VERBOSE=1
ifeq ($(BP_VERBOSE),1)
  SV_DEFINES += +define+BP_LOGGER_EN +define+BP_VERBOSE_LOG
endif

# Fast simulation mode - disable all loggers for speed
ifeq ($(FAST_SIM),1)
  SV_DEFINES += +define+FAST_SIM
  SV_DEFINES += +define+NO_COMMIT_TRACE
  SV_DEFINES += +define+NO_PIPELINE_LOG
  SV_DEFINES += +define+NO_RAM_LOG
  SV_DEFINES += +define+NO_UART_LOG
  VERILATOR_DEFINE = $(SV_DEFINES)
else
  VERILATOR_DEFINE = +define+KONATA_TRACE +define+VM_TRACE_FST $(SV_DEFINES)
endif

# -----------------------------------------
# Compiler Flags (based on MODE)
# -----------------------------------------
ifeq ($(MODE),debug)
    OPT_LEVEL     := -O0
    CFLAGS_DEBUG  := -g
else
    OPT_LEVEL     := -O2
    CFLAGS_DEBUG  :=
endif

# -----------------------------------------
# Warning Suppressions (simplified)
# -----------------------------------------
# --Wno-fatal allows build to continue despite warnings
# --Wno-lint disables most lint warnings
# Additional specific suppressions for common cases
NO_WARNING = \
    --Wno-UNOPTFLAT \
    --Wno-CASEINCOMPLETE \
    --Wno-fatal \
    --Wno-lint \
    --Wno-style \
	--Wno-WIDTH \
    --Wno-UNOPTFLAT \
    --Wno-WIDTHEXPAND \
    --Wno-WIDTHTRUNC \
    --Wno-WIDTHCONCAT \
    --Wno-UNDRIVEN \
    --Wno-UNUSED \
    --Wno-UNUSEDPARAM \
    --Wno-UNUSEDSIGNAL \
    --Wno-LATCH \
    --Wno-IMPLICIT \
    --Wno-MODDUP \
    --Wno-PINCONNECTEMPTY \
    --Wno-DECLFILENAME \
    --Wno-GENUNNAMED \
    --Wno-ASSIGNDLY \
    --Wno-ALWCOMBORDER \
    --Wno-ENUMVALUE \
    --Wno-INITIALDLY \
    --Wno-BLKANDNBLK \
    --Wno-UNOPTTHREADS \
    --Wno-SYMRSVDWORD \
    --Wno-TIMESCALEMOD \
    --Wno-IMPORTSTAR \
    --Wno-IMPORTSTAR \
    --Wno-VARHIDDEN

# Lint-specific (fewer suppressions for better feedback)
NO_WARNING_LINT = \
    --Wno-DECLFILENAME \
    --Wno-PINCONNECTEMPTY \
    --Wno-GENUNNAMED \
    --Wno-IMPORTSTAR \
    --Wno-WIDTHEXPAND \
    --Wno-VARHIDDEN \
    --Wno-WIDTHEXPAND \
    --Wno-UNUSEDSIGNAL \
    --Wno-UNUSEDPARAM \
    --Wno-UNDRIVEN \
    --Wno-UNOPTFLAT \
    --Wno-ALWCOMBORDER

# -----------------------------------------
# Build Flags
# -----------------------------------------
LINT_FLAGS  = --lint-only -Wall $(NO_WARNING_LINT) -I$(INC_DIRS) --top-module $(RTL_LEVEL)
RUN_BIN     := $(OBJ_DIR)/V$(RTL_LEVEL)

# =========================================
# Targets
# =========================================

.PHONY: dirs lint verilate run_verilator wave clean_verilator verilator_help

dirs:
	@$(MKDIR) -p "$(BUILD_DIR)" "$(OBJ_DIR)" "$(LOG_DIR)" "$(VERILATOR_LOG_DIR)"

# ============================================================
# Lint (includes loop detection)
# ============================================================
lint: dirs
	@printf "$(GREEN)[VERILATOR LINT — $(MODE)]$(RESET)\n"
	@mkdir -p "$(LOG_DIR)/verilator"
	@$(VERILATOR) \
		$(LINT_FLAGS) $(VERILATOR_INCLUDES) \
		$(SV_SOURCES) $(CPP_TB_FILE) \
		--timing \
		--error-limit 100 \
		--bbox-unsup \
		2>&1 | tee "$(LOG_DIR)/verilator/lint.log"
	@if grep -qi "loop\|UNOPTFLAT" "$(LOG_DIR)/verilator/lint.log"; then \
		printf "$(RED)[WARNING] Potential combinational loops detected.$(RESET)\n"; \
	else \
		printf "$(GREEN)No combinational loops found.$(RESET)\n"; \
	fi

# ============================================================
# Verilate — Build C++ Model
# ============================================================
verilate: dirs
	@printf "$(GREEN)[VERILATING RTL SOURCES]$(RESET)\n"
	$(VERILATOR) \
		--cc $(SV_SOURCES) $(LOGGER_SRC) \
		--exe $(CPP_TB_FILE) \
		--top-module $(RTL_LEVEL) \
		$(VERILATOR_INCLUDES) \
		$(NO_WARNING) \
		--trace-fst \
		$(VERILATOR_DEFINE) \
		--build -j 0 \
		--timing \
		--Mdir $(OBJ_DIR) \
		--CFLAGS "$(OPT_LEVEL) $(CFLAGS_DEBUG) -std=c++17 -Wall -Wextra" \
		--LDFLAGS "-lm -lpthread"
	@printf "$(GREEN)[SUCCESS]$(RESET) Built: $(OBJ_DIR)/V$(RTL_LEVEL)\n"

# ============================================================
# Run Simulation
# ============================================================
run_verilator: verilate
	@echo -e "$(GREEN)[RUNNING VERILATOR SIMULATION]$(RESET)"
	@# Clean previous logs for this test
	@if [ -d "$(VERILATOR_LOG_DIR)" ]; then \
		echo -e "$(CYAN)[CLEAN]$(RESET) Removing previous logs: $(VERILATOR_LOG_DIR)"; \
		rm -rf "$(VERILATOR_LOG_DIR)"; \
	fi
	@mkdir -p "$(VERILATOR_LOG_DIR)"
	@VERILATOR_LOG_DIR="$(VERILATOR_LOG_DIR)" \
		TEST_NAME="$(TEST_NAME)" \
		MAX_CYCLES="$(MAX_CYCLES)" \
		MEM_FILE="$(MEM_FILE)" \
		NO_ADDR="$(NO_ADDR)" \
		"$(ROOT_DIR)/script/shell/run_verilator.sh"

# ============================================================
# Waveform Viewer
# ============================================================
wave:
	@echo -e "$(YELLOW)[INFO]$(RESET) Opening GTKWave..."
	@if [ -f "$(VERILATOR_LOG_DIR)/waveform.fst" ]; then \
		gtkwave "$(VERILATOR_LOG_DIR)/waveform.fst" & \
	else \
		echo -e "$(RED)[ERROR]$(RESET) No waveform file found!"; \
	fi

# ============================================================
# Clean
# ============================================================
clean_verilator:
	@echo -e "$(RED)[CLEANING VERILATOR]$(RESET)"
	@$(RM) "$(OBJ_DIR)"
	@$(RM) "$(LOG_DIR)/verilator"
	@echo -e "$(GREEN)Clean complete.$(RESET)"

# ============================================================
# Help
# ============================================================
verilator_help:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)            CERES RISC-V — Verilator Simulation               $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Targets:$(RESET)"
	@echo -e "  $(GREEN)lint           $(RESET)– Run lint & loop checks"
	@echo -e "  $(GREEN)verilate       $(RESET)– Build C++ simulation model"
	@echo -e "  $(GREEN)run_verilator  $(RESET)– Run simulation"
	@echo -e "  $(GREEN)wave           $(RESET)– Open GTKWave"
	@echo -e "  $(GREEN)clean_verilator$(RESET)– Clean build files"
	@echo -e ""
	@echo -e "$(YELLOW)Parameters:$(RESET)"
	@echo -e "  TEST_NAME=<name>  – Test to run"
	@echo -e "  MAX_CYCLES=<n>    – Max cycles (default: $(MAX_CYCLES))"
	@echo -e "  BP_LOG=1          – Enable branch predictor statistics logger"
	@echo -e "  BP_VERBOSE=1      – Enable verbose BP logger (logs every misprediction)"
	@echo -e ""
	@echo -e "$(YELLOW)Example:$(RESET)"
	@echo -e "  make run_verilator TEST_NAME=rv32ui-p-add"
	@echo -e "  make isa BP_LOG=1                          # ISA tests with BP stats"
	@echo -e "  make bench BP_LOG=1                        # Benchmarks with BP stats"
	@echo -e ""
