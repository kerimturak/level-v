# ============================================================
# RISC-V Formal Verification Framework for Ceres-V
# ============================================================
# Formal verification using SymbiYosys and RISC-V Formal
# https://github.com/YosysHQ/riscv-formal

.PHONY: formal formal_clone formal_setup formal_run formal_clean formal_help
.PHONY: formal_check formal_cover formal_prove formal_bmc formal_report

# ============================================================
# Configuration
# ============================================================

# Repository
FORMAL_REPO_URL     := https://github.com/YosysHQ/riscv-formal.git
FORMAL_ROOT         := $(SUBREPO_DIR)/riscv-formal

# Paths
FORMAL_ENV_SRC      := $(ENV_DIR)/riscv-formal
FORMAL_BUILD_DIR    := $(BUILD_DIR)/formal
FORMAL_WORK_DIR     := $(FORMAL_BUILD_DIR)/work
FORMAL_LOG_DIR      := $(RESULTS_DIR)/logs/formal

# Tool paths (adjust for your system)
YOSYS               ?= yosys
SBY                 ?= sby
BOOLECTOR           ?= boolector
Z3                  ?= z3

# RTL source
RTL_DIR             := $(ROOT_DIR)/rtl
CORE_DIR            := $(RTL_DIR)/core
PKG_DIR             := $(RTL_DIR)/pkg
INCLUDE_DIR         := $(RTL_DIR)/include

# RISC-V Formal configuration
FORMAL_ISA          ?= rv32imc
FORMAL_DEPTH        ?= 20
FORMAL_MODE         ?= bmc
FORMAL_ENGINE       ?= z3

# Checks to run
FORMAL_CHECKS       := insn_check reg_check pc_check liveness

# ============================================================
# Main Targets
# ============================================================

formal: formal_setup formal_run
	@echo -e "$(GREEN)[FORMAL] ✓ Formal verification complete$(RESET)"

# ============================================================
# Clone Repository
# ============================================================

formal_clone:
	@echo -e "$(YELLOW)[FORMAL] Checking riscv-formal repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(FORMAL_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(FORMAL_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone --depth=1 $(FORMAL_REPO_URL); \
		echo -e "$(GREEN)[OK] riscv-formal cloned.$(RESET)"; \
	else \
		echo -e "$(GREEN)[SKIP] riscv-formal already exists.$(RESET)"; \
	fi

# ============================================================
# Setup Environment
# ============================================================

formal_setup: formal_clone
	@echo -e "$(YELLOW)[FORMAL] Setting up environment...$(RESET)"
	@mkdir -p $(FORMAL_ENV_SRC)
	@mkdir -p $(FORMAL_WORK_DIR) $(FORMAL_LOG_DIR)
	@# Check required tools
	@echo -e "$(YELLOW)[FORMAL] Checking required tools...$(RESET)"
	@if ! which $(YOSYS) > /dev/null 2>&1; then \
		echo -e "$(RED)[ERROR] yosys not found$(RESET)"; \
		echo -e "  Install: $(CYAN)apt install yosys$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)  ✓ yosys found$(RESET)"; \
	fi
	@if ! which $(SBY) > /dev/null 2>&1; then \
		echo -e "$(RED)[ERROR] sby (SymbiYosys) not found$(RESET)"; \
		echo -e "  Install:"; \
		echo -e "    $(CYAN)git clone https://github.com/YosysHQ/sby.git$(RESET)"; \
		echo -e "    $(CYAN)cd sby && pip install .$(RESET)"; \
		echo -e "  Or via package manager:"; \
		echo -e "    $(CYAN)pip install sby$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)  ✓ sby found$(RESET)"; \
	fi
	@if ! which $(BOOLECTOR) > /dev/null 2>&1 && ! which $(Z3) > /dev/null 2>&1; then \
		echo -e "$(YELLOW)[WARN] No SMT solver found (boolector or z3)$(RESET)"; \
		echo -e "  Install: $(CYAN)apt install z3$(RESET) or $(CYAN)apt install boolector$(RESET)"; \
	else \
		echo -e "$(GREEN)  ✓ SMT solver found$(RESET)"; \
	fi
	@# Check if wrapper exists
	@if [ ! -f "$(FORMAL_ENV_SRC)/rvfi_wrapper.sv" ]; then \
		echo -e "$(YELLOW)[WARN] RVFI wrapper not found. Generate with CPU integration.$(RESET)"; \
	fi
	@echo -e "$(GREEN)[OK] Setup complete$(RESET)"

# ============================================================
# Generate SymbiYosys Script
# ============================================================

formal_gen_sby:
	@echo -e "$(YELLOW)[FORMAL] Generating SymbiYosys config...$(RESET)"
	@echo "[options]" > $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "mode $(FORMAL_MODE)" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "depth $(FORMAL_DEPTH)" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "[engines]" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "smtbmc $(FORMAL_ENGINE)" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "[script]" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "read_verilog -sv $(FORMAL_ENV_SRC)/rvfi_wrapper.sv" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "prep -top rvfi_wrapper" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "[files]" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "$(FORMAL_ENV_SRC)/rvfi_wrapper.sv" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo -e "$(GREEN)[OK] SBY config generated$(RESET)"

# ============================================================
# Run Formal Verification
# ============================================================

formal_run: formal_setup formal_gen_sby
	@echo -e "$(YELLOW)[FORMAL] Running formal verification...$(RESET)"
	@echo -e "  Mode: $(FORMAL_MODE)"
	@echo -e "  Depth: $(FORMAL_DEPTH)"
	@echo -e "  Engine: $(FORMAL_ENGINE)"
	@if [ -f "$(FORMAL_ENV_SRC)/rvfi_wrapper.sv" ]; then \
		cd $(FORMAL_WORK_DIR) && $(SBY) -f ceres_formal.sby 2>&1 | tee $(FORMAL_LOG_DIR)/formal.log; \
		if [ $${PIPESTATUS[0]} -ne 0 ]; then \
			echo -e "$(RED)[FAIL] Formal verification failed$(RESET)"; \
			exit 1; \
		fi; \
	else \
		echo -e "$(RED)[ERROR] RVFI wrapper not found$(RESET)"; \
		echo -e "$(YELLOW)Create $(FORMAL_ENV_SRC)/rvfi_wrapper.sv first$(RESET)"; \
		exit 1; \
	fi
	@echo -e "$(GREEN)[OK] Formal run complete$(RESET)"

# ============================================================
# Specific Formal Checks
# ============================================================

formal_bmc: FORMAL_MODE=bmc
formal_bmc: formal_run
	@echo -e "$(GREEN)[FORMAL] BMC complete$(RESET)"

formal_prove: FORMAL_MODE=prove
formal_prove: formal_run
	@echo -e "$(GREEN)[FORMAL] Prove complete$(RESET)"

formal_cover: FORMAL_MODE=cover
formal_cover: formal_run
	@echo -e "$(GREEN)[FORMAL] Cover complete$(RESET)"

# ============================================================
# Report
# ============================================================

formal_report:
	@echo -e "$(CYAN)[FORMAL] Verification Report$(RESET)"
	@echo -e "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
	@if [ -f "$(FORMAL_LOG_DIR)/formal.log" ]; then \
		grep -E "(PASS|FAIL|ERROR|TIMEOUT)" $(FORMAL_LOG_DIR)/formal.log || true; \
	else \
		echo -e "$(YELLOW)No logs found. Run 'make formal' first.$(RESET)"; \
	fi
	@echo -e "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# ============================================================
# Clean
# ============================================================

formal_clean:
	@echo -e "$(YELLOW)[FORMAL] Cleaning...$(RESET)"
	@rm -rf $(FORMAL_BUILD_DIR)
	@echo -e "$(GREEN)[OK] Clean complete$(RESET)"

# ============================================================
# Help
# ============================================================

formal_help:
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)     RISC-V Formal Verification Framework$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Usage:$(RESET)"
	@echo -e "  make formal              Run formal verification"
	@echo -e "  make formal_bmc          Run bounded model checking"
	@echo -e "  make formal_prove        Run inductive proof"
	@echo -e "  make formal_cover        Run coverage analysis"
	@echo -e "  make formal_report       Show verification report"
	@echo -e "  make formal_clean        Clean build files"
	@echo -e ""
	@echo -e "$(CYAN)Configuration:$(RESET)"
	@echo -e "  FORMAL_DEPTH=N           BMC depth (default: 20)"
	@echo -e "  FORMAL_MODE=mode         bmc|prove|cover"
	@echo -e "  FORMAL_ENGINE=solver     boolector|z3|yices"
	@echo -e ""
	@echo -e "$(CYAN)Prerequisites:$(RESET)"
	@echo -e "  - Yosys:       apt install yosys"
	@echo -e "  - SymbiYosys:  pip3 install sby"
	@echo -e "  - Boolector:   apt install boolector"
	@echo -e ""
	@echo -e "$(CYAN)Note:$(RESET)"
	@echo -e "  Full formal verification requires adding RVFI interface"
	@echo -e "  to the CPU. See docs/EXTENDED_TEST_SUITES.md for details."
	@echo -e ""
