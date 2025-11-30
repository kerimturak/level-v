# =========================================
# CERES RISC-V — Linting Tools
# svlint, Slang, Verilator lint
# =========================================
# Usage:
#   make svlint                - Run svlint on RTL
#   make slang_lint            - Run Slang linter
#   make lint_all              - Run all linters
#   make lint_install          - Install lint tools
# =========================================

# -----------------------------------------
# Tool Paths
# -----------------------------------------
SVLINT         ?= svlint
SLANG          ?= slang

# -----------------------------------------
# Lint Output Directories (LINT_DIR from paths.mk)
# Each tool gets its own subdirectory:
#   results/lint/svlint/    - svlint style checker
#   results/lint/slang/     - Slang compiler lint
#   results/lint/verilator/ - Verilator static analysis
# -----------------------------------------
SVLINT_OUT_DIR   := $(LINT_DIR)/svlint
SLANG_OUT_DIR    := $(LINT_DIR)/slang

# -----------------------------------------
# Source Files for Linting
# -----------------------------------------
LINT_SOURCES   := $(SV_SOURCES)
LINT_INCLUDES  := $(addprefix -I, $(INC_DIRS))

# -----------------------------------------
# svlint Configuration
# -----------------------------------------
SVLINT_CONFIG  := $(ROOT_DIR)/.svlint.toml

# Create default config if not exists
$(SVLINT_CONFIG):
	@echo -e "$(CYAN)[svlint]$(RESET) Creating default configuration..."
	@echo '[option]' > $@
	@echo 'exclude_paths = ["subrepo/", "build/"]' >> $@
	@echo '' >> $@
	@echo '[rules]' >> $@
	@echo '# Naming conventions' >> $@
	@echo 'prefix_module = false' >> $@
	@echo 'prefix_interface = false' >> $@
	@echo '' >> $@
	@echo '# Style rules' >> $@
	@echo 'style_keyword_0or1space = true' >> $@
	@echo 'style_keyword_1space = true' >> $@
	@echo '' >> $@
	@echo '# Relaxed rules for generated code' >> $@
	@echo 'generate_keyword_forbidden = false' >> $@

# -----------------------------------------
# Targets
# -----------------------------------------
.PHONY: svlint slang_lint lint_all lint_install lint_clean lint_help

# Check if svlint is installed
check_svlint:
	@command -v $(SVLINT) >/dev/null 2>&1 || { \
		echo -e "$(RED)❌ svlint not found$(RESET)"; \
		echo -e "$(YELLOW)Install with:$(RESET)"; \
		echo -e "  cargo install svlint"; \
		echo -e "  # or download from: https://github.com/dalance/svlint/releases"; \
		exit 1; \
	}

# Check if Slang/pyslang is installed
check_slang:
	@python3 -c "import pyslang" 2>/dev/null || { \
		echo -e "$(RED)❌ pyslang not found$(RESET)"; \
		echo -e "$(YELLOW)Install with:$(RESET)"; \
		echo -e "  pip install pyslang"; \
		exit 1; \
	}

# Run svlint
svlint: check_svlint $(SVLINT_CONFIG)
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  svlint - SystemVerilog Style Linter$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MKDIR) $(SVLINT_OUT_DIR)
	@echo -e "$(CYAN)[INFO]$(RESET) Config: $(SVLINT_CONFIG)"
	@echo -e "$(CYAN)[INFO]$(RESET) Output: $(SVLINT_OUT_DIR)/"
	@echo -e "$(CYAN)[INFO]$(RESET) Files: $(words $(LINT_SOURCES)) source files"
	@echo -e ""
	@$(SVLINT) --config $(SVLINT_CONFIG) $(LINT_INCLUDES) $(LINT_SOURCES) 2>&1 | tee $(SVLINT_OUT_DIR)/svlint.log; \
	EXIT_CODE=$${PIPESTATUS[0]}; \
	if [ $$EXIT_CODE -eq 0 ]; then \
		echo -e ""; \
		echo -e "$(GREEN)✓ svlint passed - no issues found$(RESET)"; \
	else \
		echo -e ""; \
		echo -e "$(YELLOW)⚠ svlint found issues$(RESET)"; \
		echo -e "$(CYAN)[LOG]$(RESET) $(SVLINT_OUT_DIR)/svlint.log"; \
	fi

# Run Slang linter (via pyslang)
slang_lint: check_slang
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Slang - SystemVerilog Compiler & Linter$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MKDIR) $(SLANG_OUT_DIR)
	@echo -e "$(CYAN)[INFO]$(RESET) Output: $(SLANG_OUT_DIR)/"
	@echo -e "$(CYAN)[INFO]$(RESET) Files: $(words $(LINT_SOURCES)) source files"
	@echo -e "$(CYAN)[INFO]$(RESET) Using pyslang v$$(python3 -c 'import pyslang; print(pyslang.__version__)')"
	@echo -e ""
	@python3 $(ROOT_DIR)/script/python/slang_lint.py \
		$(addprefix -I , $(INC_DIRS)) \
		$(LINT_SOURCES) 2>&1 | tee $(SLANG_OUT_DIR)/slang.log; \
	EXIT_CODE=$${PIPESTATUS[0]}; \
	if [ $$EXIT_CODE -eq 0 ]; then \
		echo -e ""; \
		echo -e "$(GREEN)✓ Slang lint passed$(RESET)"; \
	else \
		echo -e ""; \
		echo -e "$(YELLOW)⚠ Slang found issues$(RESET)"; \
		echo -e "$(CYAN)[LOG]$(RESET) $(SLANG_OUT_DIR)/slang.log"; \
	fi

# Run Slang with more detailed output (via pyslang)
slang_check: check_slang
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Slang - Full Compilation Check$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MKDIR) $(SLANG_OUT_DIR)
	@echo -e "$(CYAN)[INFO]$(RESET) Output: $(SLANG_OUT_DIR)/"
	@echo -e "$(CYAN)[INFO]$(RESET) Using pyslang for full check"
	@python3 $(ROOT_DIR)/script/python/slang_lint.py \
		--top ceres_wrapper \
		-v \
		$(addprefix -I , $(INC_DIRS)) \
		$(LINT_SOURCES) 2>&1 | tee $(SLANG_OUT_DIR)/slang_full.log
	@echo -e "$(CYAN)[LOG]$(RESET) $(SLANG_OUT_DIR)/slang_full.log"

# Run all linters
lint_all: 
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running All Linters$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)[INFO]$(RESET) Output directory: $(LINT_DIR)/"
	@echo -e ""
	@$(MAKE) --no-print-directory svlint || true
	@echo -e ""
	@$(MAKE) --no-print-directory slang_lint || true
	@echo -e ""
	@$(MAKE) --no-print-directory lint || true
	@echo -e ""
	@$(MAKE) --no-print-directory lint_modelsim || true
	@echo -e ""
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Lint Summary$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)Output Structure:$(RESET)"
	@echo -e "  $(LINT_DIR)/"
	@echo -e "  ├── svlint/      - Style & naming checks"
	@echo -e "  ├── slang/       - Semantic analysis"
	@echo -e "  ├── verilator/   - Static analysis & loops"
	@echo -e "  └── modelsim/    - ModelSim lint checks"
	@echo -e ""
	@find $(LINT_DIR) -name "*.log" -type f 2>/dev/null | while read f; do echo "  $$f"; done || true

# Install lint tools (Linux)
lint_install:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Installing Lint Tools$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)[1/2]$(RESET) Installing svlint..."
	@cd /tmp && \
	rm -rf svlint-install && mkdir -p svlint-install && cd svlint-install && \
	curl -sLO https://github.com/dalance/svlint/releases/download/v0.9.5/svlint-v0.9.5-x86_64-lnx.zip && \
	unzip -o svlint-v0.9.5-x86_64-lnx.zip && \
	sudo cp bin/svlint /usr/local/bin/ && \
	cd /tmp && rm -rf svlint-install
	@echo -e ""
	@echo -e "$(CYAN)[2/2]$(RESET) Installing pyslang (Slang Python bindings)..."
	@pip install --quiet pyslang
	@echo -e ""
	@echo -e "$(GREEN)✓ Installation complete$(RESET)"
	@echo -e ""
	@echo -e "Versions installed:"
	@svlint --version 2>/dev/null || echo "  svlint: not found"
	@python3 -c "import pyslang; print('  pyslang:', pyslang.__version__)" 2>/dev/null || echo "  pyslang: not found"

# Clean lint outputs
lint_clean:
	@echo -e "$(CYAN)[CLEAN]$(RESET) Removing lint outputs..."
	@rm -rf $(LINT_DIR)
	@echo -e "$(GREEN)✓ Clean complete$(RESET)"

# Help
lint_help:
	@echo -e ""
	@echo -e "$(GREEN)Linting Tools$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Available Linters:$(RESET)"
	@echo -e "  make svlint              - Run svlint (style & naming)"
	@echo -e "  make slang_lint          - Run Slang (parsing & semantics)"
	@echo -e "  make slang_check         - Run Slang full check"
	@echo -e "  make lint                - Run Verilator lint (static analysis)"
	@echo -e "  make lint-report         - Verilator lint with stats"
	@echo -e "  make lint-loops          - Check combinational loops"
	@echo -e "  make lint_modelsim       - Run ModelSim lint"
	@echo -e "  make lint_report_modelsim- ModelSim lint categorized report"
	@echo -e "  make lint_all            - Run all linters"
	@echo -e ""
	@echo -e "$(CYAN)Setup:$(RESET)"
	@echo -e "  make lint_install        - Install svlint & Slang"
	@echo -e "  make lint_clean          - Clean lint outputs"
	@echo -e ""
	@echo -e "$(CYAN)Tool Descriptions:$(RESET)"
	@echo -e "  $(GREEN)svlint$(RESET)     - Fast SV linter, style/naming rules"
	@echo -e "               https://github.com/dalance/svlint"
	@echo -e ""
	@echo -e "  $(GREEN)Slang$(RESET)      - Full SV compiler, best parsing"
	@echo -e "               https://github.com/MikePopoloski/slang"
	@echo -e ""
	@echo -e "  $(GREEN)Verilator$(RESET)  - Static analysis, loop detection"
	@echo -e "               https://verilator.org"
	@echo -e ""
	@echo -e "  $(GREEN)ModelSim$(RESET)   - Commercial simulator lint checks"
	@echo -e "               https://eda.sw.siemens.com/modelsim"
	@echo -e ""
	@echo -e "$(CYAN)Output Structure:$(RESET)"
	@echo -e "  results/lint/"
	@echo -e "  ├── svlint/      - svlint logs"
	@echo -e "  ├── slang/       - Slang logs"
	@echo -e "  ├── verilator/   - Verilator logs & diagrams"
	@echo -e "  └── modelsim/    - ModelSim lint logs"
	@echo -e ""
