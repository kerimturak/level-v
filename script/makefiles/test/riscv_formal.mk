# ============================================================
# RISC-V Formal Verification Framework for Ceres-V
# ============================================================
# Formal verification using SymbiYosys and RISC-V Formal
# https://github.com/YosysHQ/riscv-formal

.PHONY: formal formal_clone formal_setup formal_run formal_clean formal_help
.PHONY: formal_check formal_cover formal_prove formal_bmc formal_report
.PHONY: formal_quick formal_standard formal_thorough formal_coverage formal_config formal_gen_sby

# ============================================================
# JSON Configuration
# ============================================================

FORMAL_CONFIG       := $(CONFIG_DIR)/tests/formal.json

# Helper to read JSON values
define read_formal_json
$(shell $(PYTHON) -c "import json; f=open('$(FORMAL_CONFIG)'); d=json.load(f); print($(1))" 2>/dev/null)
endef

# ============================================================
# Configuration from JSON
# ============================================================

# Repository
FORMAL_REPO_URL     := https://github.com/YosysHQ/riscv-formal.git
FORMAL_ROOT         := $(SUBREPO_DIR)/riscv-formal

# Paths from JSON (with defaults)
FORMAL_ENV_SRC      := $(ROOT_DIR)/$(or $(call read_formal_json,d.get('paths',{}).get('env_dir','')),env/riscv-formal)
FORMAL_BUILD_DIR    := $(ROOT_DIR)/$(or $(call read_formal_json,d.get('paths',{}).get('build_dir','')),build/formal)
FORMAL_WORK_DIR     := $(ROOT_DIR)/$(or $(call read_formal_json,d.get('paths',{}).get('work_dir','')),build/formal/work)
FORMAL_LOG_DIR      := $(ROOT_DIR)/$(or $(call read_formal_json,d.get('paths',{}).get('log_dir','')),results/logs/formal)

# Tool paths from JSON (with defaults)
YOSYS               ?= $(or $(call read_formal_json,d.get('tools',{}).get('yosys',{}).get('command','')),yosys)
SBY                 ?= $(or $(call read_formal_json,d.get('tools',{}).get('sby',{}).get('command','')),sby)
FORMAL_SOLVER_CMD   ?= $(or $(call read_formal_json,d.get('tools',{}).get('solver',{}).get('command','')),z3)

# RTL source
RTL_DIR             := $(ROOT_DIR)/rtl
CORE_DIR            := $(RTL_DIR)/core
PKG_DIR             := $(RTL_DIR)/pkg
INCLUDE_DIR         := $(RTL_DIR)/include

# RISC-V Formal configuration from JSON (with defaults)
FORMAL_MODE         ?= $(or $(call read_formal_json,d.get('verification',{}).get('mode','')),bmc)
FORMAL_DEPTH        ?= $(or $(call read_formal_json,d.get('verification',{}).get('depth','')),20)
FORMAL_ENGINE       ?= $(or $(call read_formal_json,d.get('verification',{}).get('engine','')),smtbmc)
FORMAL_SOLVER       ?= $(or $(call read_formal_json,d.get('verification',{}).get('solver','')),z3)
FORMAL_TIMEOUT      ?= $(or $(call read_formal_json,d.get('verification',{}).get('timeout','')),3600)

# ISA configuration from JSON
FORMAL_ISA_BASE     := $(or $(call read_formal_json,d.get('isa',{}).get('base','')),rv32i)
FORMAL_ISA_M        := $(call read_formal_json,d.get('isa',{}).get('extensions',{}).get('M',False))
FORMAL_ISA_C        := $(call read_formal_json,d.get('isa',{}).get('extensions',{}).get('C',False))

# CPU configuration from JSON
FORMAL_WRAPPER      := $(or $(call read_formal_json,d.get('cpu',{}).get('wrapper','')),rvfi_wrapper)
FORMAL_WRAPPER_FILE := $(ROOT_DIR)/$(or $(call read_formal_json,d.get('cpu',{}).get('wrapper_file','')),env/riscv-formal/rvfi_wrapper.sv)
FORMAL_CHANNELS     := $(or $(call read_formal_json,d.get('cpu',{}).get('channels','')),1)
FORMAL_XLEN         := $(or $(call read_formal_json,d.get('cpu',{}).get('xlen','')),32)

# Build ISA string
FORMAL_ISA          := $(FORMAL_ISA_BASE)
ifeq ($(FORMAL_ISA_M),True)
FORMAL_ISA          := $(FORMAL_ISA)m
endif
ifeq ($(FORMAL_ISA_C),True)
FORMAL_ISA          := $(FORMAL_ISA)c
endif

# Checks to run (from JSON)
FORMAL_CHECK_INSN   := $(call read_formal_json,d.get('checks',{}).get('instruction',{}).get('enabled',True))
FORMAL_CHECK_REG    := $(call read_formal_json,d.get('checks',{}).get('register',{}).get('enabled',True))
FORMAL_CHECK_PC_FWD := $(call read_formal_json,d.get('checks',{}).get('pc_forward',{}).get('enabled',True))
FORMAL_CHECK_PC_BWD := $(call read_formal_json,d.get('checks',{}).get('pc_backward',{}).get('enabled',True))
FORMAL_CHECK_MEM    := $(call read_formal_json,d.get('checks',{}).get('memory',{}).get('enabled',True))
FORMAL_CHECK_LIVE   := $(call read_formal_json,d.get('checks',{}).get('liveness',{}).get('enabled',False))
FORMAL_CHECK_UNIQUE := $(call read_formal_json,d.get('checks',{}).get('unique',{}).get('enabled',False))
FORMAL_CHECK_HANG   := $(call read_formal_json,d.get('checks',{}).get('hang',{}).get('enabled',True))
FORMAL_CHECK_COVER  := $(call read_formal_json,d.get('checks',{}).get('cover',{}).get('enabled',False))

# ============================================================
# Main Targets
# ============================================================

formal: formal_setup formal_run
	@echo -e "$(GREEN)[FORMAL] $(SUCCESS) Formal verification complete$(RESET)"

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
		echo -e "$(GREEN)  $(SUCCESS) yosys found$(RESET)"; \
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
		echo -e "$(GREEN)  $(SUCCESS) sby found$(RESET)"; \
	fi
	@if ! which $(FORMAL_SOLVER_CMD) > /dev/null 2>&1; then \
		echo -e "$(YELLOW)[WARN] SMT solver $(FORMAL_SOLVER_CMD) not found$(RESET)"; \
		echo -e "  Install: $(CYAN)apt install z3$(RESET) or $(CYAN)apt install boolector$(RESET)"; \
	else \
		echo -e "$(GREEN)  $(SUCCESS) SMT solver $(FORMAL_SOLVER_CMD) found$(RESET)"; \
	fi
	@# Check if wrapper exists
	@if [ ! -f "$(FORMAL_WRAPPER_FILE)" ]; then \
		echo -e "$(YELLOW)[WARN] RVFI wrapper not found at $(FORMAL_WRAPPER_FILE)$(RESET)"; \
		echo -e "$(YELLOW)       Generate with CPU integration.$(RESET)"; \
	else \
		echo -e "$(GREEN)  $(SUCCESS) RVFI wrapper found$(RESET)"; \
	fi
	@echo -e "$(GREEN)[OK] Setup complete$(RESET)"

# ============================================================
# Show Configuration
# ============================================================

formal_config:
	@echo -e "$(CYAN)[FORMAL] Current Configuration$(RESET)"
	@echo -e "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
	@echo -e "  Config file:    $(FORMAL_CONFIG)"
	@echo -e "  Mode:           $(FORMAL_MODE)"
	@echo -e "  Depth:          $(FORMAL_DEPTH)"
	@echo -e "  Engine:         $(FORMAL_ENGINE)"
	@echo -e "  Solver:         $(FORMAL_SOLVER)"
	@echo -e "  Timeout:        $(FORMAL_TIMEOUT)s"
	@echo -e "  ISA:            $(FORMAL_ISA)"
	@echo -e "  XLEN:           $(FORMAL_XLEN)"
	@echo -e "  Wrapper:        $(FORMAL_WRAPPER)"
	@echo -e "  Wrapper File:   $(FORMAL_WRAPPER_FILE)"
	@echo -e "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
	@echo -e "  Checks enabled:"
	@echo -e "    Instruction:  $(FORMAL_CHECK_INSN)"
	@echo -e "    Register:     $(FORMAL_CHECK_REG)"
	@echo -e "    PC Forward:   $(FORMAL_CHECK_PC_FWD)"
	@echo -e "    PC Backward:  $(FORMAL_CHECK_PC_BWD)"
	@echo -e "    Memory:       $(FORMAL_CHECK_MEM)"
	@echo -e "    Liveness:     $(FORMAL_CHECK_LIVE)"
	@echo -e "    Unique:       $(FORMAL_CHECK_UNIQUE)"
	@echo -e "    Hang:         $(FORMAL_CHECK_HANG)"
	@echo -e "    Cover:        $(FORMAL_CHECK_COVER)"
	@echo -e "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# ============================================================
# Generate SymbiYosys Script
# ============================================================

# Note: Full CPU verification requires Yosys-compatible RTL.
# Current Ceres-V uses advanced SystemVerilog features.
# For now, only wrapper module is verified.

formal_gen_sby:
	@echo -e "$(YELLOW)[FORMAL] Generating SymbiYosys config...$(RESET)"
	@echo "[options]" > $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "mode $(FORMAL_MODE)" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "depth $(FORMAL_DEPTH)" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "timeout $(FORMAL_TIMEOUT)" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "[engines]" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "$(FORMAL_ENGINE) $(FORMAL_SOLVER)" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "[script]" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "read_verilog -sv -DFORMAL $(FORMAL_WRAPPER_FILE)" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "prep -top $(FORMAL_WRAPPER)" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "[files]" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo "$(FORMAL_WRAPPER_FILE)" >> $(FORMAL_WORK_DIR)/ceres_formal.sby
	@echo -e "$(GREEN)[OK] SBY config generated at $(FORMAL_WORK_DIR)/ceres_formal.sby$(RESET)"

# ============================================================
# Run Formal Verification
# ============================================================

formal_run: formal_setup formal_gen_sby
	@echo -e "$(YELLOW)[FORMAL] Running formal verification...$(RESET)"
	@echo -e "  Mode:    $(FORMAL_MODE)"
	@echo -e "  Depth:   $(FORMAL_DEPTH)"
	@echo -e "  Engine:  $(FORMAL_ENGINE)"
	@echo -e "  Solver:  $(FORMAL_SOLVER)"
	@echo -e "  Timeout: $(FORMAL_TIMEOUT)s"
	@if [ -f "$(FORMAL_WRAPPER_FILE)" ]; then \
		cd $(FORMAL_WORK_DIR) && $(SBY) -f ceres_formal.sby 2>&1 | tee $(FORMAL_LOG_DIR)/formal.log; \
		if [ $${PIPESTATUS[0]} -ne 0 ]; then \
			echo -e "$(RED)[FAIL] Formal verification failed$(RESET)"; \
			exit 1; \
		fi; \
	else \
		echo -e "$(RED)[ERROR] RVFI wrapper not found$(RESET)"; \
		echo -e "$(YELLOW)Create $(FORMAL_WRAPPER_FILE) first$(RESET)"; \
		exit 1; \
	fi
	@echo -e "$(GREEN)[OK] Formal run complete$(RESET)"

# ============================================================
# Preset Targets (from JSON)
# ============================================================

formal_quick:
	@echo -e "$(CYAN)[FORMAL] Running quick preset...$(RESET)"
	$(MAKE) formal_run FORMAL_MODE=bmc FORMAL_DEPTH=10

formal_standard:
	@echo -e "$(CYAN)[FORMAL] Running standard preset...$(RESET)"
	$(MAKE) formal_run FORMAL_MODE=bmc FORMAL_DEPTH=20

formal_thorough:
	@echo -e "$(CYAN)[FORMAL] Running thorough preset...$(RESET)"
	$(MAKE) formal_run FORMAL_MODE=prove FORMAL_DEPTH=30

formal_coverage:
	@echo -e "$(CYAN)[FORMAL] Running coverage preset...$(RESET)"
	$(MAKE) formal_run FORMAL_MODE=cover FORMAL_DEPTH=50

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
	@echo -e "$(CYAN)Configuration:$(RESET)"
	@echo -e "  Config file: $(FORMAL_CONFIG)"
	@echo -e ""
	@echo -e "$(CYAN)Main Commands:$(RESET)"
	@echo -e "  make formal              Run formal verification"
	@echo -e "  make formal_config       Show current configuration"
	@echo -e "  make formal_report       Show verification report"
	@echo -e "  make formal_clean        Clean build files"
	@echo -e ""
	@echo -e "$(CYAN)Modes:$(RESET)"
	@echo -e "  make formal_bmc          Bounded Model Checking"
	@echo -e "  make formal_prove        Inductive Proof"
	@echo -e "  make formal_cover        Coverage Analysis"
	@echo -e ""
	@echo -e "$(CYAN)Presets (from JSON):$(RESET)"
	@echo -e "  make formal_quick        Quick test (depth=10, bmc)"
	@echo -e "  make formal_standard     Standard (depth=20, bmc)"
	@echo -e "  make formal_thorough     Thorough (depth=30, prove)"
	@echo -e "  make formal_coverage     Coverage (depth=50, cover)"
	@echo -e ""
	@echo -e "$(CYAN)Override Options:$(RESET)"
	@echo -e "  FORMAL_DEPTH=N           Set BMC depth"
	@echo -e "  FORMAL_MODE=mode         bmc|prove|cover|live"
	@echo -e "  FORMAL_ENGINE=engine     smtbmc|btor|abc"
	@echo -e "  FORMAL_SOLVER=solver     z3|boolector|yices|bitwuzla"
	@echo -e "  FORMAL_TIMEOUT=N         Timeout in seconds"
	@echo -e ""
	@echo -e "$(CYAN)Examples:$(RESET)"
	@echo -e "  make formal FORMAL_DEPTH=30"
	@echo -e "  make formal_prove FORMAL_SOLVER=boolector"
	@echo -e "  make formal_quick FORMAL_TIMEOUT=600"
	@echo -e ""
	@echo -e "$(CYAN)Prerequisites:$(RESET)"
	@echo -e "  - Yosys:       apt install yosys"
	@echo -e "  - SymbiYosys:  pip3 install sby"
	@echo -e "  - SMT Solver:  apt install z3 (or boolector)"
	@echo -e ""
	@echo -e "$(CYAN)Note:$(RESET)"
	@echo -e "  Edit $(FORMAL_CONFIG) to change defaults."
	@echo -e "  Full verification requires RVFI interface in CPU."
	@echo -e ""
