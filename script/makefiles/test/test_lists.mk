# ============================================================
# CERES RISC-V — Test List Shortcuts
# ============================================================
# Kısa isimlerle test listeleri çalıştırma
#
# Usage:
#   make isa          - Run all ISA tests
#   make csr          - Run CSR tests
#   make bench        - Run benchmarks (NO_ADDR=1)
#   make all_tests    - Run all tests
#   make regression   - Full regression (isa + arch + imperas + csr)
#   make quick        - Quick smoke test (~5 min)
#   make full         - Full test suite (~30 min)
#   make nightly      - Nightly build (full + CoreMark + benchmarks)
# ============================================================

# -----------------------------------------
# Regression Results Directory
# -----------------------------------------
REGRESSION_DIR     := $(RESULTS_DIR)/regression
REGRESSION_REPORT  := $(REGRESSION_DIR)/report_$(shell date +%Y%m%d_%H%M%S).txt
REGRESSION_SUMMARY := $(REGRESSION_DIR)/latest_summary.txt

# -----------------------------------------
# Test List Paths
# -----------------------------------------
TEST_LIST_DIR := $(SIM_DIR)/test

# Test list files
FLIST_ISA       := $(TEST_LIST_DIR)/riscv_test_list.flist
FLIST_CSR       := $(TEST_LIST_DIR)/machine_csr_test.flist
FLIST_BENCH     := $(TEST_LIST_DIR)/riscv_benchmark.flist
FLIST_ALL       := $(TEST_LIST_DIR)/all_tests.flist
FLIST_EXCEPTION := $(TEST_LIST_DIR)/exception_test.flist
FLIST_ARCH      := $(TEST_LIST_DIR)/arch_test.flist
FLIST_BRANCH    := $(TEST_LIST_DIR)/branch_test.flist

# -----------------------------------------
# ISA Tests (riscv-tests)
# -----------------------------------------
.PHONY: isa isa-tests

# ISA test cycle limit (override with ISA_MAX_CYCLES=N)
ISA_MAX_CYCLES ?= 10000

isa isa-tests:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running RISC-V ISA Tests$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_ISA) \
		TEST_TYPE=isa \
		SIM=$(SIM) \
		MAX_CYCLES=$(ISA_MAX_CYCLES)

# -----------------------------------------
# Branch Predictor Tests (branch/jump instructions)
# -----------------------------------------
.PHONY: branch bp-tests branch-all branch-isa branch-imperas branch-arch

# Branch test cycle limit (override with BRANCH_MAX_CYCLES=N)
BRANCH_MAX_CYCLES ?= 100000

# Branch test patterns
BRANCH_PATTERNS := beq bne blt bge bltu bgeu jal jalr cbeqz cbnez cjal cjalr

branch bp-tests:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running Branch Predictor Tests (ISA only)$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_BRANCH) \
		TEST_TYPE=isa \
		SIM=$(SIM) \
		MAX_CYCLES=$(BRANCH_MAX_CYCLES) \
		CONFIG=branch_test

# Run ALL branch tests from all directories (ISA + Imperas + Arch)
branch-all:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running ALL Branch Tests (ISA + Imperas + Arch)$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory branch-isa
	@$(MAKE) --no-print-directory branch-imperas
	@$(MAKE) --no-print-directory branch-arch

# ISA branch tests
branch-isa:
	@echo -e "$(CYAN)[ISA] Running ISA branch tests...$(RESET)"
	@PASS=0; FAIL=0; \
	for test in rv32ui-p-beq rv32ui-p-bne rv32ui-p-blt rv32ui-p-bge \
	            rv32ui-p-bltu rv32ui-p-bgeu rv32ui-p-jal rv32ui-p-jalr; do \
		if $(MAKE) --no-print-directory t T=$$test CONFIG=branch_test > /dev/null 2>&1; then \
			echo -e "$(GREEN)[PASS]$(RESET) $$test"; \
			PASS=$$((PASS+1)); \
		else \
			echo -e "$(RED)[FAIL]$(RESET) $$test"; \
			FAIL=$$((FAIL+1)); \
		fi; \
	done; \
	echo -e "$(CYAN)[ISA] Results: $$PASS passed, $$FAIL failed$(RESET)"

# Imperas branch tests
branch-imperas:
	@echo -e "$(CYAN)[IMPERAS] Running Imperas branch tests...$(RESET)"
	@PASS=0; FAIL=0; \
	for test in I-BEQ-01 I-BNE-01 I-BLT-01 I-BGE-01 I-BLTU-01 I-BGEU-01 I-JAL-01 I-JALR-01; do \
		if $(MAKE) --no-print-directory ti T=$$test CONFIG=branch_test > /dev/null 2>&1; then \
			echo -e "$(GREEN)[PASS]$(RESET) $$test"; \
			PASS=$$((PASS+1)); \
		else \
			echo -e "$(RED)[FAIL]$(RESET) $$test"; \
			FAIL=$$((FAIL+1)); \
		fi; \
	done; \
	echo -e "$(CYAN)[IMPERAS] Results: $$PASS passed, $$FAIL failed$(RESET)"

# Arch branch tests
branch-arch:
	@echo -e "$(CYAN)[ARCH] Running Arch branch tests...$(RESET)"
	@PASS=0; FAIL=0; \
	for test in I-beq-01 I-bne-01 I-blt-01 I-bge-01 I-bltu-01 I-bgeu-01 I-jal-01 I-jalr-01 \
	            C-cbeqz-01 C-cbnez-01 C-cjal-01 C-cjalr-01; do \
		if $(MAKE) --no-print-directory ta T=$$test CONFIG=branch_test > /dev/null 2>&1; then \
			echo -e "$(GREEN)[PASS]$(RESET) $$test"; \
			PASS=$$((PASS+1)); \
		else \
			echo -e "$(RED)[FAIL]$(RESET) $$test"; \
			FAIL=$$((FAIL+1)); \
		fi; \
	done; \
	echo -e "$(CYAN)[ARCH] Results: $$PASS passed, $$FAIL failed$(RESET)"

# -----------------------------------------
# CSR Tests (machine mode CSR)
# -----------------------------------------
.PHONY: csr csr-tests

# CSR test cycle limit (override with CSR_MAX_CYCLES=N)
CSR_MAX_CYCLES ?= 10000

csr csr-tests:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running Machine CSR Tests$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_CSR) \
		TEST_TYPE=isa \
		SIM=$(SIM) \
		MAX_CYCLES=$(CSR_MAX_CYCLES)

# -----------------------------------------
# Benchmarks (NO_ADDR=1)
# -----------------------------------------
.PHONY: bench benchmarks

# Benchmark cycle limit (override with BENCH_MAX_CYCLES=N)
BENCH_MAX_CYCLES ?= 1000000

bench benchmarks:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running RISC-V Benchmarks$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_bench_flist \
		FLIST=$(FLIST_BENCH) \
		SIM=$(SIM) \
		MAX_CYCLES=$(BENCH_MAX_CYCLES)

# -----------------------------------------
# All Tests
# -----------------------------------------
.PHONY: all_tests

all_tests:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running ALL Tests$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_ALL) \
		TEST_TYPE=isa \
		SIM=$(SIM) \
		MAX_CYCLES=$(ISA_MAX_CYCLES)

# -----------------------------------------
# Exception Tests
# -----------------------------------------
.PHONY: exc exception-tests

# Exception test cycle limit (override with EXC_MAX_CYCLES=N)
EXC_MAX_CYCLES ?= 10000

exc exception-tests:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running Exception Tests$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_EXCEPTION) \
		TEST_TYPE=isa \
		SIM=$(SIM) \
		MAX_CYCLES=$(EXC_MAX_CYCLES)

# -----------------------------------------
# Architecture Tests (riscv-arch-test)
# -----------------------------------------
.PHONY: arch arch-tests

# Arch test cycle limit (override with ARCH_MAX_CYCLES=N)
ARCH_MAX_CYCLES ?= 100000

arch arch-tests:
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(GREEN)  Running RISC-V Architecture Tests$(RESET)"
	@echo -e "$(GREEN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@if [ ! -f "$(FLIST_ARCH)" ]; then \
		echo -e "$(YELLOW)[INFO] Generating arch test list...$(RESET)"; \
		$(MAKE) --no-print-directory arch_gen_flist; \
	fi
	@$(MAKE) --no-print-directory run_flist \
		FLIST=$(FLIST_ARCH) \
		TEST_TYPE=arch \
		SIM=$(SIM) \
		MAX_CYCLES=$(ARCH_MAX_CYCLES)

# Generate arch test flist from built tests
.PHONY: arch_gen_flist
arch_gen_flist:
	@echo -e "$(YELLOW)[GEN] Generating arch_test.flist...$(RESET)"
	@mkdir -p $(TEST_LIST_DIR)
	@echo "# RISC-V Architecture Tests" > $(FLIST_ARCH)
	@echo "# Auto-generated from build/tests/riscv-arch-test/elf" >> $(FLIST_ARCH)
	@if [ -d "$(BUILD_DIR)/tests/riscv-arch-test/elf" ]; then \
		for elf in $(BUILD_DIR)/tests/riscv-arch-test/elf/*.elf; do \
			if [ -f "$$elf" ]; then \
				basename $$elf .elf >> $(FLIST_ARCH); \
			fi; \
		done; \
		echo -e "$(GREEN)[OK] Generated $(FLIST_ARCH)$(RESET)"; \
	else \
		echo -e "$(RED)[ERROR] No arch tests found. Run 'make arch_auto' first.$(RESET)"; \
	fi

# Quick arch test: make ta T=I-add-01
.PHONY: ta
ta:
ifndef T
	$(error Usage: make ta T=<arch_test_name> (e.g., I-add-01))
endif
	@$(MAKE) --no-print-directory run \
		TEST_NAME=$(T) \
		TEST_TYPE=arch \
		MEM_DIR="$(BUILD_DIR)/tests/riscv-arch-test/mem" \
		ELF_DIR="$(BUILD_DIR)/tests/riscv-arch-test/elf" \
		DUMP_DIR="$(BUILD_DIR)/tests/riscv-arch-test/dump" \
		ADDR_DIR="$(BUILD_DIR)/tests/riscv-arch-test/pass_fail_addr" \
		TEST_LOG_DIR="$(RESULTS_DIR)/logs/verilator/arch/$(T)" \
		RTL_LOG_DIR="$(RESULTS_DIR)/logs/verilator/arch/$(T)" \
		SIM=verilator

# -----------------------------------------
# Universal Test Shortcut with Auto-Detection
# -----------------------------------------
# make test T=<test_name>   - Auto-detects test type and runs with Spike comparison
# 
# Detection patterns:
#   rv32*-p-*, rv64*-p-*  → ISA tests
#   *-01, *-02, etc.      → Arch tests
#   I-*, M-*, A-*, C-*    → Could be Imperas or Arch (file-based detection)
#   median, dhrystone     → Benchmarks
#
.PHONY: test
test:
ifndef T
	$(error Usage: make test T=<test_name>  (auto-detects type))
endif
	@echo -e "$(CYAN)[AUTO-DETECT]$(RESET) Searching for test: $(T)"
	@# File-based detection with priority: arch > imperas > isa > bench
	@if [ -f "$(BUILD_DIR)/tests/riscv-arch-test/elf/$(T).elf" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: arch (riscv-arch-test)"; \
		$(MAKE) --no-print-directory run TEST_NAME=$(T) TEST_TYPE=arch; \
	elif [ -f "$(BUILD_DIR)/tests/imperas/elf/$(T).elf" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: imperas"; \
		$(MAKE) --no-print-directory run TEST_NAME=$(T) TEST_TYPE=imperas; \
	elif [ -f "$(BUILD_DIR)/tests/riscv-tests/elf/$(T)" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: isa (riscv-tests)"; \
		$(MAKE) --no-print-directory run TEST_NAME=$(T) TEST_TYPE=isa; \
	elif [ -f "$(BUILD_DIR)/tests/riscv-benchmarks/elf/$(T)" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: bench (riscv-benchmarks)"; \
		$(MAKE) --no-print-directory run TEST_NAME=$(T) TEST_TYPE=bench NO_ADDR=1; \
	else \
		echo -e "$(RED)[ERROR]$(RESET) Test '$(T)' not found in any test directory."; \
		echo -e "$(YELLOW)Searched in:$(RESET)"; \
		echo -e "  - $(BUILD_DIR)/tests/riscv-arch-test/elf/$(T).elf"; \
		echo -e "  - $(BUILD_DIR)/tests/imperas/elf/$(T).elf"; \
		echo -e "  - $(BUILD_DIR)/tests/riscv-tests/elf/$(T)"; \
		echo -e "  - $(BUILD_DIR)/tests/riscv-benchmarks/elf/$(T)"; \
		echo -e "$(YELLOW)Available tests:$(RESET)"; \
		echo -e "  make list_tests    - List all ISA tests"; \
		echo -e "  make list_arch     - List all arch tests"; \
		echo -e "  make list_imperas  - List all Imperas tests"; \
		exit 1; \
	fi

# Quick version (Verilator only, no Spike comparison)
.PHONY: qt
qt:
ifndef T
	$(error Usage: make qt T=<test_name>  (quick test, auto-detects type))
endif
	@echo -e "$(CYAN)[AUTO-DETECT]$(RESET) Quick test: $(T)"
	@if [ -f "$(BUILD_DIR)/tests/riscv-arch-test/elf/$(T).elf" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: arch"; \
		$(MAKE) --no-print-directory run_verilator TEST_NAME=$(T) TEST_TYPE=arch; \
	elif [ -f "$(BUILD_DIR)/tests/imperas/elf/$(T).elf" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: imperas"; \
		$(MAKE) --no-print-directory run_verilator TEST_NAME=$(T) TEST_TYPE=imperas; \
	elif [ -f "$(BUILD_DIR)/tests/riscv-tests/elf/$(T)" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: isa"; \
		$(MAKE) --no-print-directory run_verilator TEST_NAME=$(T) TEST_TYPE=isa; \
	elif [ -f "$(BUILD_DIR)/tests/riscv-benchmarks/elf/$(T)" ]; then \
		echo -e "$(GREEN)[DETECTED]$(RESET) Type: bench"; \
		$(MAKE) --no-print-directory run_verilator TEST_NAME=$(T) TEST_TYPE=bench NO_ADDR=1; \
	else \
		echo -e "$(RED)[ERROR]$(RESET) Test '$(T)' not found."; \
		exit 1; \
	fi

# ============================================================
# REGRESSION TEST SUITES
# ============================================================
# Farklı test coverage seviyeleri için komutlar
# ============================================================

# -----------------------------------------
# Quick Smoke Test (~5 min)
# -----------------------------------------
# Kritik testlerin hızlı kontrolü
.PHONY: quick smoke

quick smoke:
	@echo -e ""
	@echo -e "$(CYAN)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║           CERES RISC-V — Quick Smoke Test                   ║$(RESET)"
	@echo -e "$(CYAN)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo -e ""
	@mkdir -p $(REGRESSION_DIR)
	@START_TIME=$$(date +%s); \
	TOTAL_PASS=0; TOTAL_FAIL=0; \
	echo -e "$(YELLOW)[1/2] Running ISA tests...$(RESET)"; \
	if $(MAKE) --no-print-directory isa CLEAN_LOGS=1 2>&1 | tee $(REGRESSION_DIR)/quick_isa.log | tail -5; then \
		ISA_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/quick_isa.log 2>/dev/null || echo 0); \
		ISA_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/quick_isa.log 2>/dev/null || echo 0); \
	else \
		ISA_PASS=0; ISA_FAIL=1; \
	fi; \
	echo -e "$(YELLOW)[2/2] Running CSR tests...$(RESET)"; \
	if $(MAKE) --no-print-directory csr 2>&1 | tee $(REGRESSION_DIR)/quick_csr.log | tail -5; then \
		CSR_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/quick_csr.log 2>/dev/null || echo 0); \
		CSR_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/quick_csr.log 2>/dev/null || echo 0); \
	else \
		CSR_PASS=0; CSR_FAIL=1; \
	fi; \
	END_TIME=$$(date +%s); \
	DURATION=$$((END_TIME - START_TIME)); \
	echo -e ""; \
	echo -e "$(GREEN)╔══════════════════════════════════════════════════════════════╗$(RESET)"; \
	echo -e "$(GREEN)║                    Quick Test Summary                        ║$(RESET)"; \
	echo -e "$(GREEN)╠══════════════════════════════════════════════════════════════╣$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  ISA Tests:  $$ISA_PASS passed, $$ISA_FAIL failed                       $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  CSR Tests:  $$CSR_PASS passed, $$CSR_FAIL failed                       $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)╠══════════════════════════════════════════════════════════════╣$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  Duration: $${DURATION}s                                              $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)╚══════════════════════════════════════════════════════════════╝$(RESET)"; \
	if [ $$ISA_FAIL -gt 0 ] || [ $$CSR_FAIL -gt 0 ]; then exit 1; fi

# -----------------------------------------
# Full Test Suite (~30 min)
# -----------------------------------------
# ISA + Arch + Imperas + CSR
.PHONY: full regression

full regression:
	@echo -e ""
	@echo -e "$(CYAN)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║           CERES RISC-V — Full Regression Suite              ║$(RESET)"
	@echo -e "$(CYAN)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo -e ""
	@mkdir -p $(REGRESSION_DIR)
	@REPORT=$(REGRESSION_DIR)/report_$$(date +%Y%m%d_%H%M%S).txt; \
	echo "CERES RISC-V Regression Report" > $$REPORT; \
	echo "Date: $$(date)" >> $$REPORT; \
	echo "============================================" >> $$REPORT; \
	START_TIME=$$(date +%s); \
	ISA_PASS=0; ISA_FAIL=0; \
	ARCH_PASS=0; ARCH_FAIL=0; \
	IMP_PASS=0; IMP_FAIL=0; \
	CSR_PASS=0; CSR_FAIL=0; \
	echo -e "$(YELLOW)[1/4] Running ISA tests...$(RESET)"; \
	if $(MAKE) --no-print-directory isa CLEAN_LOGS=1 2>&1 | tee $(REGRESSION_DIR)/reg_isa.log; then \
		ISA_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/reg_isa.log 2>/dev/null || echo 0); \
		ISA_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/reg_isa.log 2>/dev/null || echo 0); \
	fi; \
	echo "ISA: $$ISA_PASS passed, $$ISA_FAIL failed" >> $$REPORT; \
	echo -e "$(YELLOW)[2/4] Running Architecture tests...$(RESET)"; \
	if $(MAKE) --no-print-directory arch 2>&1 | tee $(REGRESSION_DIR)/reg_arch.log; then \
		ARCH_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/reg_arch.log 2>/dev/null || echo 0); \
		ARCH_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/reg_arch.log 2>/dev/null || echo 0); \
	fi; \
	echo "ARCH: $$ARCH_PASS passed, $$ARCH_FAIL failed" >> $$REPORT; \
	echo -e "$(YELLOW)[3/4] Running Imperas tests...$(RESET)"; \
	if $(MAKE) --no-print-directory imperas 2>&1 | tee $(REGRESSION_DIR)/reg_imperas.log; then \
		IMP_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/reg_imperas.log 2>/dev/null || echo 0); \
		IMP_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/reg_imperas.log 2>/dev/null || echo 0); \
	fi; \
	echo "IMPERAS: $$IMP_PASS passed, $$IMP_FAIL failed" >> $$REPORT; \
	echo -e "$(YELLOW)[4/4] Running CSR tests...$(RESET)"; \
	if $(MAKE) --no-print-directory csr 2>&1 | tee $(REGRESSION_DIR)/reg_csr.log; then \
		CSR_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/reg_csr.log 2>/dev/null || echo 0); \
		CSR_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/reg_csr.log 2>/dev/null || echo 0); \
	fi; \
	echo "CSR: $$CSR_PASS passed, $$CSR_FAIL failed" >> $$REPORT; \
	END_TIME=$$(date +%s); \
	DURATION=$$((END_TIME - START_TIME)); \
	TOTAL_PASS=$$((ISA_PASS + ARCH_PASS + IMP_PASS + CSR_PASS)); \
	TOTAL_FAIL=$$((ISA_FAIL + ARCH_FAIL + IMP_FAIL + CSR_FAIL)); \
	echo "============================================" >> $$REPORT; \
	echo "TOTAL: $$TOTAL_PASS passed, $$TOTAL_FAIL failed" >> $$REPORT; \
	echo "Duration: $${DURATION}s" >> $$REPORT; \
	cp $$REPORT $(REGRESSION_SUMMARY); \
	echo -e ""; \
	echo -e "$(GREEN)╔══════════════════════════════════════════════════════════════╗$(RESET)"; \
	echo -e "$(GREEN)║                 Full Regression Summary                      ║$(RESET)"; \
	echo -e "$(GREEN)╠══════════════════════════════════════════════════════════════╣$(RESET)"; \
	printf "$(GREEN)║$(RESET)  %-12s  %3d passed, %3d failed                      $(GREEN)║$(RESET)\n" "ISA:" $$ISA_PASS $$ISA_FAIL; \
	printf "$(GREEN)║$(RESET)  %-12s  %3d passed, %3d failed                      $(GREEN)║$(RESET)\n" "ARCH:" $$ARCH_PASS $$ARCH_FAIL; \
	printf "$(GREEN)║$(RESET)  %-12s  %3d passed, %3d failed                      $(GREEN)║$(RESET)\n" "IMPERAS:" $$IMP_PASS $$IMP_FAIL; \
	printf "$(GREEN)║$(RESET)  %-12s  %3d passed, %3d failed                      $(GREEN)║$(RESET)\n" "CSR:" $$CSR_PASS $$CSR_FAIL; \
	echo -e "$(GREEN)╠══════════════════════════════════════════════════════════════╣$(RESET)"; \
	printf "$(GREEN)║$(RESET)  %-12s  %3d passed, %3d failed                      $(GREEN)║$(RESET)\n" "TOTAL:" $$TOTAL_PASS $$TOTAL_FAIL; \
	echo -e "$(GREEN)║$(RESET)  Duration: $${DURATION}s                                             $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  Report: $$REPORT  $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)╚══════════════════════════════════════════════════════════════╝$(RESET)"; \
	if [ $$TOTAL_FAIL -gt 0 ]; then \
		echo -e "$(RED)$(WARN)  $$TOTAL_FAIL test(s) failed!$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)🎉 All tests passed!$(RESET)"; \
	fi

# -----------------------------------------
# Nightly Build (Full + Benchmarks + CoreMark)
# -----------------------------------------
.PHONY: nightly

nightly:
	@echo -e ""
	@echo -e "$(CYAN)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║           CERES RISC-V — Nightly Build Suite                ║$(RESET)"
	@echo -e "$(CYAN)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo -e ""
	@mkdir -p $(REGRESSION_DIR)
	@REPORT=$(REGRESSION_DIR)/nightly_$$(date +%Y%m%d_%H%M%S).txt; \
	START_TIME=$$(date +%s); \
	echo "CERES RISC-V Nightly Build Report" > $$REPORT; \
	echo "Date: $$(date)" >> $$REPORT; \
	echo "============================================" >> $$REPORT; \
	echo -e "$(YELLOW)[1/3] Running full regression...$(RESET)"; \
	$(MAKE) --no-print-directory full 2>&1 | tee -a $$REPORT || true; \
	echo -e "$(YELLOW)[2/3] Running benchmarks...$(RESET)"; \
	$(MAKE) --no-print-directory bench 2>&1 | tee $(REGRESSION_DIR)/nightly_bench.log || true; \
	BENCH_PASS=$$(grep -c "PASSED" $(REGRESSION_DIR)/nightly_bench.log 2>/dev/null || echo 0); \
	BENCH_FAIL=$$(grep -c "FAILED" $(REGRESSION_DIR)/nightly_bench.log 2>/dev/null || echo 0); \
	echo "BENCH: $$BENCH_PASS passed, $$BENCH_FAIL failed" >> $$REPORT; \
	echo -e "$(YELLOW)[3/3] Running CoreMark...$(RESET)"; \
	$(MAKE) --no-print-directory cm MAX_CYCLES=10000000 2>&1 | tee $(REGRESSION_DIR)/nightly_coremark.log || true; \
	if grep -q "CoreMark" $(REGRESSION_DIR)/nightly_coremark.log 2>/dev/null; then \
		COREMARK_SCORE=$$(grep -oP "CoreMark.*?:\s*\K[\d.]+" $(REGRESSION_DIR)/nightly_coremark.log 2>/dev/null || echo "N/A"); \
		echo "CoreMark Score: $$COREMARK_SCORE" >> $$REPORT; \
	fi; \
	END_TIME=$$(date +%s); \
	DURATION=$$((END_TIME - START_TIME)); \
	echo "============================================" >> $$REPORT; \
	echo "Total Duration: $${DURATION}s" >> $$REPORT; \
	echo -e ""; \
	echo -e "$(GREEN)╔══════════════════════════════════════════════════════════════╗$(RESET)"; \
	echo -e "$(GREEN)║                  Nightly Build Complete                      ║$(RESET)"; \
	echo -e "$(GREEN)╠══════════════════════════════════════════════════════════════╣$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  Duration: $${DURATION}s                                             $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)║$(RESET)  Report: $$REPORT  $(GREEN)║$(RESET)"; \
	echo -e "$(GREEN)╚══════════════════════════════════════════════════════════════╝$(RESET)"

# -----------------------------------------
# Benchmark List Runner (NO_ADDR=1)
# -----------------------------------------
.PHONY: run_bench_flist

run_bench_flist:
	@if [ ! -f "$(FLIST)" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Test list file not found: $(FLIST)"; \
		exit 1; \
	fi
	@$(MKDIR) "$(LOG_DIR)"
	@# Clean all logs for this simulator if CLEAN_LOGS=1
	@if [ "$(CLEAN_LOGS)" = "1" ]; then \
		echo -e "$(CYAN)[CLEAN]$(RESET) Removing all previous logs: $(RESULTS_DIR)/logs/$(SIM)/"; \
		rm -rf "$(RESULTS_DIR)/logs/$(SIM)/"*; \
	fi
	@echo -n "" > $(PASS_LIST_FILE)
	@echo -n "" > $(FAIL_LIST_FILE)
	@echo -e "$(GREEN)Running benchmarks from list file:$(RESET) $(FLIST)"
	@echo -e "$(CYAN)Output directory:$(RESET) $(RESULTS_DIR)/logs/$(SIM)/"
	@PASS=0; FAIL=0; TOTAL=0; \
	while IFS= read -r test || [ -n "$${test}" ]; do \
		test="$${test%% }"; test="$${test## }"; \
		if echo "$${test}" | grep -E '^\s*#' >/dev/null || [ -z "$${test}" ]; then continue; fi; \
		TOTAL=$$(( $${TOTAL} + 1 )); \
		TEST_LOG_DIR="$(RESULTS_DIR)/logs/$(SIM)/$${test}"; \
		if [ -d "$${TEST_LOG_DIR}" ]; then \
			rm -rf "$${TEST_LOG_DIR}"; \
		fi; \
		mkdir -p "$${TEST_LOG_DIR}"; \
		echo -e ""; \
		echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		echo -e "$(CYAN)[BENCH] Test $${TOTAL}: $${test}$(RESET)"; \
		echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
		if $(MAKE) --no-print-directory run_verilator \
			TEST_NAME=$${test} \
			TEST_TYPE=bench \
			NO_ADDR=1 \
			MAX_CYCLES=$(MAX_CYCLES) \
			VERILATOR_LOG_DIR=$${TEST_LOG_DIR} > "$${TEST_LOG_DIR}/summary.log" 2>&1; then \
			PASS=$$(( $${PASS} + 1 )); \
			echo "$${test}" >> "$(PASS_LIST_FILE)"; \
			echo -e "$(GREEN)$(SUCCESS) $${test} PASSED$(RESET)"; \
		else \
			TEST_EXIT=$$?; \
			FAIL=$$(( $${FAIL} + 1 )); \
			echo "$${test}" >> "$(FAIL_LIST_FILE)"; \
			echo -e "$(RED)✗ $${test} FAILED (exit code: $${TEST_EXIT})$(RESET)"; \
			echo -e "$(YELLOW)  ↳ Summary log: $${TEST_LOG_DIR}/summary.log$(RESET)"; \
		fi; \
	done < "$(FLIST)"; \
	echo -e ""; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN) Benchmark Summary$(RESET)"; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	echo -e "$(GREEN)✅ Passed: $${PASS}$(RESET)"; \
	echo -e "$(RED)$(ERROR) Failed: $${FAIL}$(RESET)"; \
	echo -e "$(CYAN)📊 Total:  $${TOTAL}$(RESET)"; \
	echo -e "$(YELLOW)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"; \
	if [ $${FAIL} -gt 0 ]; then \
		echo -e "$(RED)$(WARN)  $${FAIL} benchmark(s) failed$(RESET)"; \
		exit 1; \
	else \
		echo -e "$(GREEN)🎉 All benchmarks passed!$(RESET)"; \
	fi

# -----------------------------------------
# Quick Single Test Shortcuts
# -----------------------------------------
.PHONY: t tb

# Quick ISA test: make t T=rv32ui-p-add
t:
ifndef T
	$(error Usage: make t T=<test_name>)
endif
	@$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=$(T) \
		TEST_TYPE=isa \
		SIM=verilator

# Quick benchmark test: make tb T=dhrystone
tb:
ifndef T
	$(error Usage: make tb T=<benchmark_name>)
endif
	@$(MAKE) --no-print-directory run_verilator \
		TEST_NAME=$(T) \
		TEST_TYPE=bench \
		NO_ADDR=1 \
		MAX_CYCLES=$(or $(MAX_CYCLES),1000000) \
		SIM=verilator

# -----------------------------------------
# Help
# -----------------------------------------
.PHONY: help_lists

help_lists:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)            CERES RISC-V — Test Automation                    $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  REGRESSION SUITES$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make quick$(RESET)        – Quick smoke test (~5 min) [ISA + CSR]"
	@echo -e "  $(GREEN)make full$(RESET)         – Full regression (~30 min) [ISA + Arch + Imperas + CSR]"
	@echo -e "  $(GREEN)make regression$(RESET)   – Alias for 'make full'"
	@echo -e "  $(GREEN)make nightly$(RESET)      – Nightly build (full + benchmarks + CoreMark)"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  INDIVIDUAL TEST SUITES$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make isa$(RESET)          – Run ISA tests (rv32ui, rv32um, rv32uc)"
	@echo -e "  $(GREEN)make csr$(RESET)          – Run machine CSR tests (rv32mi)"
	@echo -e "  $(GREEN)make arch$(RESET)         – Run architecture tests (I: 38, M: 8, C: 27)"
	@echo -e "  $(GREEN)make imperas$(RESET)      – Run Imperas tests (45 tests)"
	@echo -e "  $(GREEN)make bench$(RESET)        – Run benchmarks [NO_ADDR=1]"
	@echo -e "  $(GREEN)make exc$(RESET)          – Run exception tests"
	@echo -e "  $(GREEN)make branch$(RESET)       – Run branch predictor tests (30 tests, LOG_BP=1)"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  COREMARK$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make cm$(RESET)           – Build and run CoreMark"
	@echo -e "  $(GREEN)make cm_run$(RESET)       – Quick run (skip rebuild)"
	@echo -e "  $(GREEN)make coremark_help$(RESET)– Detailed CoreMark help"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  QUICK SINGLE TEST$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make t T=rv32ui-p-add$(RESET)   – Quick ISA test"
	@echo -e "  $(GREEN)make ta T=I-add-01$(RESET)      – Quick arch test"
	@echo -e "  $(GREEN)make ti T=I-ADD-01$(RESET)      – Quick Imperas test"
	@echo -e "  $(GREEN)make tb T=dhrystone$(RESET)     – Quick benchmark [NO_ADDR=1]"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  COVERAGE$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make coverage$(RESET)      – Full coverage (ISA + Arch tests)"
	@echo -e "  $(GREEN)make coverage-quick$(RESET)– Quick coverage (ISA only)"
	@echo -e "  $(GREEN)make coverage-html$(RESET) – Generate HTML report"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  TEST PIPELINES$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  $(GREEN)make arch_auto$(RESET)     – Arch: Clone → Build → Import"
	@echo -e "  $(GREEN)make imperas_auto$(RESET)  – Imperas: Clone → Build → Import"
	@echo -e ""
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  OPTIONS$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  SIM=verilator|modelsim   – Simulator (default: verilator)"
	@echo -e "  CLEAN_LOGS=1             – Clear logs before batch run"
	@echo -e "  FAST_SIM=1               – Disable logging for speed"
	@echo -e "  COVERAGE=1               – Enable coverage collection"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make quick                        # Quick smoke test"
	@echo -e "  make full CLEAN_LOGS=1            # Full regression, clean logs first"
	@echo -e "  make coverage                     # Full coverage analysis"
	@echo -e "  make t T=rv32ui-p-add FAST_SIM=1  # Single fast test"
	@echo -e ""
