# ============================================================
# CERES RISC-V ISA & Benchmark Tests — Auto Clone & Build Pipeline
# Submodule Version
# ============================================================

.PHONY: isa_auto isa_clone isa_configure isa_my_configure isa_build isa_import \
        isa_clean isa_check isa_reset isa_help \
        bench_auto bench_build bench_import

# ============================================================
# 1️⃣ ISA PIPELINE
# ============================================================

isa_auto: isa_clone isa_configure isa_my_configure isa_build isa_import

isa_clone:
	@echo -e "$(YELLOW)[CHECK] riscv-tests source availability...$(RESET)"

	@bash -c '\
		ISA_ROOT="$(ISA_ROOT)"; \
		SUBDIR="$(SUBREPO_DIR)"; \
		URL="$(ISA_REPO_URL)"; \
		\
		# Submodule path .gitmodules içinde tanımlı mı? \
		if grep -q "path = $${ISA_ROOT}" .gitmodules 2>/dev/null; then \
			echo -e "$(YELLOW)[SUBMODULE] riscv-tests found in .gitmodules$(RESET)"; \
			\
			echo -e "$(YELLOW)[INIT+UPDATE] git submodule update --init --recursive$(RESET)"; \
			git submodule update --init --recursive -- "$${ISA_ROOT}"; \
			\
			echo -e "$(GREEN)[OK] Submodule ready (with nested submodules).$(RESET)"; \
			exit 0; \
		fi; \
		\
		# Submodule tanımı yok — fallback clone \
		echo -e "$(RED)[WARN] Submodule NOT defined. Falling back to git clone.$(RESET)"; \
		mkdir -p "$${SUBDIR}"; \
		\
		if [ ! -d "$${ISA_ROOT}" ] || [ -z "$$(ls -A "$${ISA_ROOT}" 2>/dev/null)" ]; then \
			echo -e "$(YELLOW)[CLONE] git clone --recursive $${URL} → $${ISA_ROOT}$(RESET)"; \
			cd "$${SUBDIR}" && git clone --recursive "$${URL}"; \
			echo -e "$(GREEN)[DONE] Repository cloned (recursive).$(RESET)"; \
		else \
			echo -e "$(GREEN)[SKIP] Repo folder already exists.$(RESET)"; \
		fi; \
	'

isa_configure:
	@echo -e "$(YELLOW)[BUILD] Configuring riscv-tests for RV$(XLEN)...$(RESET)"
	@cd $(ISA_ROOT) && \
		if [ ! -f configure ]; then \
			echo -e "$(YELLOW)[STEP] Running autoconf...$(RESET)"; \
			autoconf; \
		fi; \
		if [ ! -f Makefile ]; then \
			echo -e "$(YELLOW)[STEP] Running ./configure...$(RESET)"; \
			./configure --prefix=$(RISCV_TARGET) \
						--host=$(RISCV_PREFIX) \
						--target=$(RISCV_PREFIX) \
						--with-xlen=$(XLEN); \
		fi

isa_my_configure:
	@echo -e "$(YELLOW)[CERES ENV] Linking Ceres environment → riscv-tests/env$(RESET)"
	@CERES_ENV_SRC="$(ROOT_DIR)/env/riscv-test/ceres"; \
	CERES_ENV_DST="$(ISA_ROOT)/env"; \
	if [ ! -d "$$CERES_ENV_SRC" ]; then \
		echo -e "$(RED)[ERROR] Missing environment at: $$CERES_ENV_SRC$(RESET)"; \
		exit 1; \
	fi; \
	mkdir -p $$CERES_ENV_DST/ceres; \
	cp -r $$CERES_ENV_SRC/* $$CERES_ENV_DST/ceres/; \
	rm -rf $$CERES_ENV_DST/p; \
	ln -sfn ceres $$CERES_ENV_DST/p; \
	echo -e "$(GREEN)[DONE] Ceres test env active.$(RESET)"

isa_build:
	@echo -e "$(YELLOW)[STEP] make isa$(RESET)"
	@$(MAKE) -C $(ISA_ROOT) -j$(MAKE_JOBS) isa || { echo -e "$(RED)ISA build failed$(RESET)"; exit 1; }
	@echo -e "$(GREEN)ISA build complete.$(RESET)"

isa_import:
	@echo -e "$(YELLOW)[IMPORT] Importing ISA tests via pipeline$(RESET)"
	@$(PYTHON) $(PIPELINE_PY) --isa-dir $(ISA_SRC_DIR) --ceres-root $(ROOT_DIR)
	@echo -e "$(GREEN)ISA import complete.$(RESET)"

# ============================================================
# 2️⃣ BENCHMARK PIPELINE
# ============================================================

bench_auto: isa_clone bench_build bench_import

bench_build:
	@echo -e "$(YELLOW)[STEP] make benchmarks$(RESET)"
	@$(MAKE) -C $(ISA_ROOT) -j$(MAKE_JOBS) benchmarks || { echo -e "$(RED)Benchmarks failed$(RESET)"; exit 1; }
	@echo -e "$(GREEN)Benchmarks build complete.$(RESET)"

bench_import:
	@echo -e "$(YELLOW)[IMPORT] Importing Benchmarks via pipeline$(RESET)"
	@$(PYTHON) $(PIPELINE_PY) --bench-dir $(ISA_ROOT)/benchmarks --ceres-root $(ROOT_DIR)
	@echo -e "$(GREEN)Benchmark import complete.$(RESET)"

# ============================================================
# 3️⃣ HELPERS
# ============================================================

isa_clean:
	@echo -e "$(RED)[CLEAN] Removing ISA outputs$(RESET)"
	@rm -rf $(ISA_OUT_DIR)

isa_check:
	@echo -e "$(GREEN)[CHECK] Listing ISA ELF & DUMP$(RESET)"
	@ls -lh $(ISA_SRC_DIR) | grep -E "riscv|dump" || echo "No files."

isa_reset:
	@echo -e "$(RED)[RESET] Removing submodule: $(ISA_ROOT)$(RESET)"
	@rm -rf $(ISA_ROOT)

isa_help:
	@echo -e "$(GREEN)CERES RISC-V ISA Test Management$(RESET)"
	@echo -e "  isa_auto     – Full ISA pipeline"
	@echo -e "  bench_auto   – Full Benchmark pipeline"
	@echo -e "  isa_build    – make isa"
	@echo -e "  bench_build  – make benchmarks"
	@echo -e "  isa_import   – Import ISA ELF → HEX → MEM → ADDR"
	@echo -e "  bench_import – Import Benchmark tests"
