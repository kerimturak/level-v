# =========================================
# CERES RISC-V — Surfer Waveform Viewer
# Modern waveform viewer (Rust-based)
# =========================================
# Usage:
#   make surfer                - Open waveform with Surfer
#   make surfer_install        - Install Surfer
# =========================================
# Surfer: https://surfer-project.org/
# - Fast rendering (GPU accelerated)
# - Supports VCD, FST, GHW formats
# - Modern UI with signal search
# =========================================

# -----------------------------------------
# Configuration
# -----------------------------------------
SURFER         ?= surfer

# Default waveform files
SURFER_VCD     ?= $(BUILD_DIR)/verilator/waveform.vcd
SURFER_FST     ?= $(BUILD_DIR)/verilator/waveform.fst

# -----------------------------------------
# Targets
# -----------------------------------------
.PHONY: surfer surfer_install surfer_help

# Check if Surfer is installed
check_surfer:
	@command -v $(SURFER) >/dev/null 2>&1 || { \
		echo -e "$(RED)❌ Surfer not found$(RESET)"; \
		echo -e "$(YELLOW)Install with:$(RESET)"; \
		echo -e "  cargo install --git https://gitlab.com/surfer-project/surfer surfer"; \
		echo -e "  # Or download from: https://surfer-project.org/"; \
		exit 1; \
	}

# Open waveform with Surfer
surfer: check_surfer
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Surfer Waveform Viewer$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@if [ -f "$(SURFER_FST)" ]; then \
		echo -e "$(CYAN)[INFO]$(RESET) Opening FST: $(SURFER_FST)"; \
		$(SURFER) $(SURFER_FST) &; \
	elif [ -f "$(SURFER_VCD)" ]; then \
		echo -e "$(CYAN)[INFO]$(RESET) Opening VCD: $(SURFER_VCD)"; \
		$(SURFER) $(SURFER_VCD) &; \
	else \
		echo -e "$(RED)❌ No waveform file found$(RESET)"; \
		echo -e "$(YELLOW)Run simulation first with TRACE=1:$(RESET)"; \
		echo -e "  make run_verilator TEST_NAME=rv32ui-p-add TRACE=1"; \
		exit 1; \
	fi

# Open specific waveform file
surfer_file: check_surfer
ifndef WAVE_FILE
	@echo -e "$(RED)❌ WAVE_FILE not specified$(RESET)"
	@echo -e "$(YELLOW)Usage: make surfer_file WAVE_FILE=path/to/file.vcd$(RESET)"
	@exit 1
endif
	@echo -e "$(CYAN)[INFO]$(RESET) Opening: $(WAVE_FILE)"
	@$(SURFER) $(WAVE_FILE) &

# Install Surfer
surfer_install:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Installing Surfer$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@if command -v cargo >/dev/null 2>&1; then \
		echo -e "$(CYAN)[INFO]$(RESET) Installing via cargo..."; \
		cargo install --git https://gitlab.com/surfer-project/surfer surfer; \
	else \
		echo -e "$(RED)❌ Cargo not found$(RESET)"; \
		echo -e "$(YELLOW)Install Rust first: https://rustup.rs/$(RESET)"; \
		echo -e ""; \
		echo -e "$(YELLOW)Alternative: Download AppImage from:$(RESET)"; \
		echo -e "  https://surfer-project.org/"; \
		exit 1; \
	fi
	@echo -e ""
	@echo -e "$(GREEN)✓ Surfer installed$(RESET)"
	@surfer --version 2>/dev/null || true

# Compare with GTKWave
wave_compare:
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Waveform Viewers Comparison$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)GTKWave$(RESET) (Traditional)"
	@echo -e "  ✓ Mature, well-documented"
	@echo -e "  ✓ TCL scripting support"
	@echo -e "  ✗ Older UI, slower with large files"
	@echo -e "  Command: make gtkwave"
	@echo -e ""
	@echo -e "$(CYAN)Surfer$(RESET) (Modern)"
	@echo -e "  ✓ GPU accelerated, very fast"
	@echo -e "  ✓ Modern UI, signal search"
	@echo -e "  ✓ VCD/FST/GHW support"
	@echo -e "  ✗ Newer, less documentation"
	@echo -e "  Command: make surfer"
	@echo -e ""

# Help
surfer_help:
	@echo -e ""
	@echo -e "$(GREEN)Surfer Waveform Viewer$(RESET)"
	@echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)Commands:$(RESET)"
	@echo -e "  make surfer              - Open default waveform"
	@echo -e "  make surfer_file WAVE_FILE=path  - Open specific file"
	@echo -e "  make surfer_install      - Install Surfer"
	@echo -e "  make wave_compare        - Compare GTKWave vs Surfer"
	@echo -e ""
	@echo -e "$(CYAN)Supported Formats:$(RESET)"
	@echo -e "  VCD  - Value Change Dump (standard)"
	@echo -e "  FST  - Fast Signal Trace (compressed)"
	@echo -e "  GHW  - GHDL Waveform"
	@echo -e ""
	@echo -e "$(CYAN)Website:$(RESET)"
	@echo -e "  https://surfer-project.org/"
	@echo -e ""
