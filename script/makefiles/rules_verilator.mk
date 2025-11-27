# Eğer run_flist LOG_DIR olarak test-specific dizini veriyorsa,
# tekrar rtl/verilator eklememek için kontrol yapıyoruz.

dirs:
	@$(MKDIR) -p "$(BUILD_DIR)" "$(OBJ_DIR)" "$(LOG_DIR)" "$(VERILATOR_LOG_DIR)"

.PHONY: dirs lint verilate run_verilator wave verilator_static clean_verilator verilator_help

# ============================================================
# 1️⃣ Lint
# ============================================================
lint: dirs
	@printf "$(GREEN)[VERILATOR LINT — $(MODE)]$(RESET)\n"
	@mkdir -p $(VERILATOR_LOG_DIR)
	@$(VERILATOR) \
		$(LINT_FLAGS) $(VERILATOR_INCLUDES) \
		$(SV_SOURCES) $(CPP_TB_FILE) \
		--timing \
		--error-limit 100 \
		--bbox-unsup \
		2>&1 | sed -r "s/\x1B\[[0-9;]*m//g" | sed "s/[\xE2\x80\x8B]//g" | tee $(LOG_DIR)/verilator/verilator_lint.log

	@if grep -qi "loop" $(LOG_DIR)/verilator/verilator_lint.log; then \
		printf "$(RED)[WARNING] Potential combinational loops detected.$(RESET)\n"; \
	else \
		printf "$(GREEN)No combinational loops found.$(RESET)\n"; \
	fi

# ============================================================
# 2️⃣ Verilate — Build C++ Model
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
	@printf "$(GREEN)[SUCCESS]$(RESET) Verilated C++ model built successfully at $(OBJ_DIR)/V$(RTL_LEVEL)\n"

# ============================================================
# 3️⃣ Run Simulation - FIXED VERSION
# ============================================================
run_verilator: verilate
	@echo -e "$(GREEN)[RUNNING VERILATOR SIMULATION]$(RESET)"; \
	{ \
		mkdir -p "$(VERILATOR_LOG_DIR)"; \
		VERILATOR_LOG_DIR="$(VERILATOR_LOG_DIR)" TEST_NAME="$(TEST_NAME)" MAX_CYCLES="$(MAX_CYCLES)" MEM_FILE="$(MEM_FILE)" "$(ROOT_DIR)/script/run_verilator.sh"; \
	}

# ============================================================
# 4️⃣ Waveform Open
# ============================================================
wave:
	@echo -e "$(YELLOW)[INFO]$(RESET) Opening GTKWave..."
	@if [ -f "$(VERILATOR_LOG_DIR)/waveform.fst" ]; then \
		gtkwave "$(VERILATOR_LOG_DIR)/waveform.fst" & \
	elif [ -f "$(LOG_DIR)/rtl/waveform.vcd" ]; then \
		gtkwave "$(LOG_DIR)/rtl/waveform.vcd" & \
	else \
		echo -e "$(RED)[ERROR]$(RESET) No waveform file found!"; \
	fi

# ============================================================
# 5️⃣ Static Checks
# ============================================================
verilator_static: dirs
	@echo -e "$(GREEN)[STATIC CHECKS — unused/multidriven/loops]$(RESET)"
	@mkdir -p "$(VERILATOR_LOG_DIR)"
	$(VERILATOR) --lint-only -Wall -Wno-fatal -Wno-UNOPTFLAT --error-limit 0 --timing \
		$(VERILATOR_INCLUDES) --top-module $(RTL_LEVEL) $(SV_SOURCES) $(CPP_TB_FILE) | tee $(VERILATOR_LOG_DIR)/verilator_static.log
	@grep -e "UNOPTFLAT|UNUSED|MULTIDRIVEN|loop" $(VERILATOR_LOG_DIR)/verilator_static.log || echo -e "$(GREEN) No structural issues found.$(RESET)"

# ============================================================
# 6️⃣ Clean
# ============================================================
clean_verilator:
	@echo -e "$(RED)[CLEANING VERILATOR BUILD FILES]$(RESET)"
	@$(RM) -rf $(OBJ_DIR) $(VERILATOR_LOG_DIR) $(LOG_DIR)/verilator_*.log $(LOG_DIR)/rtl/verilator
	@echo -e "$(GREEN) Clean complete.$(RESET)"

# ============================================================
# 7️⃣ Help
# ============================================================
verilator_help:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)            CERES RISC-V — Verilator Simulation               $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Main Targets:$(RESET)"
	@echo -e "  $(GREEN)lint              $(RESET)– Run Verilator lint & loop checks"
	@echo -e "  $(GREEN)verilate          $(RESET)– Generate and build C++ simulation model"
	@echo -e "  $(GREEN)run_verilator     $(RESET)– Execute simulation (+INIT_FILE resolved automatically)"
	@echo -e "  $(GREEN)wave              $(RESET)– Open GTKWave with latest waveform"
	@echo -e "  $(GREEN)clean_verilator   $(RESET)– Clean Verilator build artifacts"
	@echo -e ""
	@echo -e "$(YELLOW)Parameters:$(RESET)"
	@echo -e "  TEST_NAME=<name>     – Select RISC-V test (auto-locates .mem/.hex)"
	@echo -e "  MAX_CYCLES=<n>  – Max simulation cycles (default: $(MAX_CYCLES))"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make run_verilator TEST_NAME=rv32ui-p-add MAX_CYCLES=50000"
	@echo -e "  make wave"
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN) Logs now saved under results/logs/rtl/verilator/<TEST_NAME>/ $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"