# ============================================================
# TinyML / MLPerf Tiny — subrepos + Level-V env hooks
# ============================================================
# Repos (official):
#   - https://github.com/mlcommons/tiny          — MLPerf Tiny rules & reference
#   - https://github.com/tensorflow/tflite-micro — embedded inference runtime
#
# MLPerf Tiny stub on Verilator: make mlperf_tiny_init && make run_mlperf_tiny
# (separate from CoreMark). CoreMark: make run_coremark
# ============================================================

.PHONY: tinyml_help tinyml_status tinyml_submodules_init mlperf_tiny_init tflite_micro_init

MLPERF_TINY_DIR      := $(SUBREPO_DIR)/mlperf-tiny
TFLITE_MICRO_DIR     := $(SUBREPO_DIR)/tflite-micro
MLPERF_TINY_URL      := https://github.com/mlcommons/tiny.git
TFLITE_MICRO_URL     := https://github.com/tensorflow/tflite-micro.git

MLPERF_TINY_ENV      := $(ENV_DIR)/mlperf-tiny/levelv
TFLITE_MICRO_ENV     := $(ENV_DIR)/tflite-micro/levelv

# ---------------------------------------------------------------------------
# Initialize both subrepos (prefer git submodule; else shallow clone)
# ---------------------------------------------------------------------------
tinyml_submodules_init: mlperf_tiny_init tflite_micro_init
	@echo -e "$(GREEN)[TINYML] $(SUCCESS) Submodule / clone step done$(RESET)"
	@echo -e "$(CYAN)Next:$(RESET) read $(ENV_DIR)/mlperf-tiny/README.md and env/tflite-micro/README.md"

mlperf_tiny_init:
	@echo -e "$(YELLOW)[TINYML] MLPerf Tiny → $(MLPERF_TINY_DIR)$(RESET)"
	@if [ -f "$(ROOT_DIR)/.gitmodules" ] && grep -q 'subrepo/mlperf-tiny' "$(ROOT_DIR)/.gitmodules" 2>/dev/null; then \
		git -C "$(ROOT_DIR)" submodule update --init --recursive -- "$(MLPERF_TINY_DIR)" || true; \
	fi
	@if [ -f "$(MLPERF_TINY_DIR)/README.md" ] || [ -f "$(MLPERF_TINY_DIR)/LICENSE.md" ]; then \
		echo -e "$(GREEN)[TINYML] mlperf-tiny present$(RESET)"; \
	else \
		echo -e "$(YELLOW)[TINYML] Cloning $(MLPERF_TINY_URL) ...$(RESET)"; \
		mkdir -p "$(SUBREPO_DIR)"; \
		git clone --depth=1 "$(MLPERF_TINY_URL)" "$(MLPERF_TINY_DIR)"; \
	fi

tflite_micro_init:
	@echo -e "$(YELLOW)[TINYML] TensorFlow Lite Micro → $(TFLITE_MICRO_DIR)$(RESET)"
	@if [ -f "$(ROOT_DIR)/.gitmodules" ] && grep -q 'subrepo/tflite-micro' "$(ROOT_DIR)/.gitmodules" 2>/dev/null; then \
		git -C "$(ROOT_DIR)" submodule update --init --recursive -- "$(TFLITE_MICRO_DIR)" || true; \
	fi
	@if [ -d "$(TFLITE_MICRO_DIR)/tensorflow/lite/micro" ]; then \
		echo -e "$(GREEN)[TINYML] tflite-micro present$(RESET)"; \
	else \
		echo -e "$(YELLOW)[TINYML] Cloning $(TFLITE_MICRO_URL) ...$(RESET)"; \
		mkdir -p "$(SUBREPO_DIR)"; \
		git clone --depth=1 "$(TFLITE_MICRO_URL)" "$(TFLITE_MICRO_DIR)"; \
	fi

tinyml_status:
	@echo -e "$(CYAN)MLPerf Tiny:$(RESET)  $(MLPERF_TINY_DIR)"
	@ls -la "$(MLPERF_TINY_DIR)" 2>/dev/null | head -3 || echo "  (missing — make tinyml_submodules_init)"
	@echo -e "$(CYAN)TFLM:$(RESET)         $(TFLITE_MICRO_DIR)"
	@ls -la "$(TFLITE_MICRO_DIR)/tensorflow/lite/micro" 2>/dev/null | head -3 || echo "  (missing — make tinyml_submodules_init)"
	@echo -e "$(CYAN)Level-V env:$(RESET)  $(MLPERF_TINY_ENV)  $(TFLITE_MICRO_ENV)"

tinyml_help:
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)  TinyML / MLPerf Tiny — Level-V subrepos$(RESET)"
	@echo -e "$(GREEN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Subrepos (under subrepo/):$(RESET)"
	@echo -e "  make tinyml_submodules_init   Clone or git submodule update"
	@echo -e "  make tinyml_status            Show paths + quick ls"
	@echo -e "  make mlperf_tiny_init         MLPerf Tiny only"
	@echo -e "  make tflite_micro_init        TFLite Micro only"
	@echo ""
	@echo -e "$(YELLOW)CoreMark (CPU benchmark):$(RESET)"
	@echo -e "  make coremark                 Build CoreMark for Level-V"
	@echo -e "  make run_coremark             Verilator sim + UART output"
	@echo -e "  make coremark_help            All CoreMark options"
	@echo ""
	@echo -e "$(YELLOW)MLPerf Tiny (stub harness — own makefile, not CoreMark):$(RESET)"
	@echo -e "  make mlperf_tiny              Build API stub + mlperf_tiny.mem"
	@echo -e "  make run_mlperf_tiny          Verilator (like run_coremark)"
	@echo -e "  make mlperf_tiny_help         Target list"
	@echo ""
	@echo -e "$(YELLOW)Level-V memory / UART templates for future TinyML port:$(RESET)"
	@echo -e "  $(MLPERF_TINY_ENV)/memory_map.yaml"
	@echo -e "  $(TFLITE_MICRO_ENV)/memory_map.yaml"
	@echo -e "  (edit RAM length for model arena; match rtl/pkg/level_param.sv BRAM)"
	@echo ""
	@echo -e "$(YELLOW)Note:$(RESET) Full reference models use TFLM + Mbed; this repo adds a small stub for sim smoke."
	@echo ""
