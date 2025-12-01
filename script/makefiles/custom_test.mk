# ============================================================================
# Custom Test Support - Makefile Integration
# ============================================================================
# Include this in your main makefile to support custom test building
# Usage: make custom_test TEST=my_test
#        make custom_help
# ============================================================================

# -----------------------------------------
# Custom Test Variables
# -----------------------------------------
CUSTOM_TEST_DIR    := $(SIM_DIR)/test/custom
CUSTOM_BUILD_DIR   := $(BUILD_DIR)/tests/custom
CUSTOM_SCRIPT      := $(SCRIPT_DIR)/shell/build_custom_test.sh
CUSTOM_CONFIG      := $(SCRIPT_DIR)/config/tests/custom.json

# Load configuration if it exists
ifdef CUSTOM_CONFIG
  ifeq ($(wildcard $(CUSTOM_CONFIG)),$(CUSTOM_CONFIG))
    CUSTOM_MAX_CYCLES := $(shell grep -oP '"max_cycles":\s*\K[0-9]+' $(CUSTOM_CONFIG) 2>/dev/null || echo "100000")
  else
    CUSTOM_MAX_CYCLES := 100000
  endif
else
  CUSTOM_MAX_CYCLES := 100000
endif

# Allow override from command line
MAX_CYCLES ?= $(CUSTOM_MAX_CYCLES)

# Coverage data directory
COVERAGE_DATA_DIR := $(RESULTS_DIR)/logs/verilator/coverage_data

# Dynamically discover custom tests
CUSTOM_TESTS := $(patsubst $(CUSTOM_TEST_DIR)/%.c,%,$(wildcard $(CUSTOM_TEST_DIR)/*.c))


.PHONY: custom_help custom_test custom_build custom_run custom_clean custom_list custom_config

# Help
custom_help:
	@echo -e "$(CYAN)╔════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(CYAN)║$(RESET)  Custom UART Test Support$(RESET)"
	@echo -e "$(CYAN)╚════════════════════════════════════════════════════════════╝$(RESET)"
	@echo ""
	@echo -e "$(GREEN)Available Commands:$(RESET)"
	@echo -e "  $(YELLOW)make custom_list$(RESET)          - List available custom tests"
	@echo -e "  $(YELLOW)make custom_test TEST=<name>$(RESET) - Build and run custom test"
	@echo -e "  $(YELLOW)make custom_build TEST=<name>$(RESET) - Build custom test"
	@echo -e "  $(YELLOW)make custom_run TEST=<name>$(RESET) - Run custom test simulation"
	@echo -e "  $(YELLOW)make custom_clean TEST=<name>$(RESET) - Clean custom test artifacts"
	@echo -e "  $(YELLOW)make custom_config$(RESET)        - Show custom test configuration"
	@echo ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make custom_test TEST=uart_hello_test"
	@echo -e "  make custom_build TEST=my_test"
	@echo -e "  make custom_run TEST=my_test MAX_CYCLES=200000"
	@echo -e "  make custom_clean TEST=my_test"
	@echo ""
	@echo -e "$(YELLOW)Location:$(RESET)"
	@echo -e "  Source:  $(CUSTOM_TEST_DIR)/"
	@echo -e "  Build:   $(CUSTOM_BUILD_DIR)/"
	@echo ""

# List available tests
custom_list:
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)Available Custom Tests:$(RESET)"
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@if [ -z "$(CUSTOM_TESTS)" ]; then \
		echo -e "  $(YELLOW)No custom tests found in $(CUSTOM_TEST_DIR)$(RESET)"; \
	else \
		echo "$(CUSTOM_TESTS)" | tr ' ' '\n' | nl | awk '{printf "  %2d. %-30s\n", $$1, $$2}'; \
	fi
	@echo ""
	@echo -e "$(YELLOW)Usage:$(RESET)"
	@echo -e "  make custom_test TEST=<name>   - Build and run a test"
	@echo -e "  make custom_build TEST=<name>  - Build only"
	@echo -e "  make custom_run TEST=<name>    - Run only"
	@echo ""

# Build custom test
custom_build:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_build TEST=<test_name>"
	@echo -e "        Example: make custom_build TEST=uart_hello_test"
	@exit 1
endif
	@mkdir -p $(CUSTOM_BUILD_DIR)
	@echo -e "$(YELLOW)[BUILD]$(RESET) Compiling $(TEST)..."
	@if [ ! -f "$(CUSTOM_TEST_DIR)/$(TEST).c" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Test not found: $(CUSTOM_TEST_DIR)/$(TEST).c"; \
		exit 1; \
	fi
	@bash $(CUSTOM_SCRIPT) "$(TEST)" -n

# Run simulation
custom_run:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_run TEST=<test_name>"
	@exit 1
endif
	@echo -e "$(YELLOW)[RUN]$(RESET) Running $(TEST) simulation..."
	@if [ ! -f "$(CUSTOM_BUILD_DIR)/$(TEST).mem" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Memory file not found. Run 'make custom_build TEST=$(TEST)' first."; \
		exit 1; \
	fi
	@cd $(ROOT_DIR) && $(MAKE) run_verilator MEM_FILE="$(CUSTOM_BUILD_DIR)/$(TEST).mem" TEST_NAME="$(TEST)" MAX_CYCLES=$(MAX_CYCLES) LOG_UART=1 SIM_UART_MONITOR=1 COVERAGE_FILE="$(COVERAGE_DATA_DIR)/$(TEST).dat" 2>&1 | tee "$(CUSTOM_BUILD_DIR)/sim.log"
	@UART_LOG="$(LOG_DIR)/verilator/$(TEST)/uart_output.log"; \
	if [ -f "$$UART_LOG" ]; then \
		cp "$$UART_LOG" "$(CUSTOM_BUILD_DIR)/$(TEST)_uart.log"; \
		echo ""; \
		echo -e "$(CYAN)╔════════════════════════════════════════════╗$(RESET)"; \
		echo -e "$(CYAN)║$(RESET)  UART Output:                              $(CYAN)║$(RESET)"; \
		echo -e "$(CYAN)╚════════════════════════════════════════════╝$(RESET)"; \
		cat "$$UART_LOG"; \
	fi

# Build and Run (avoid double build)
custom_test:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_test TEST=<test_name>"
	@exit 1
endif
	@$(MAKE) custom_build TEST=$(TEST)
	@$(MAKE) custom_run TEST=$(TEST) MAX_CYCLES=$(MAX_CYCLES)

# Clean
custom_clean:
ifndef TEST
	@echo -e "$(YELLOW)[CLEAN]$(RESET) Removing all custom test artifacts..."
	@rm -rf $(CUSTOM_BUILD_DIR)/*
	@echo -e "$(GREEN)[OK]$(RESET) Cleaned"
else
	@echo -e "$(YELLOW)[CLEAN]$(RESET) Removing $(TEST) artifacts..."
	@rm -f $(CUSTOM_BUILD_DIR)/$(TEST).*
	@echo -e "$(GREEN)[OK]$(RESET) Cleaned $(TEST)"
endif
	@echo ""

# ============================================================================
# Utility Targets
# ============================================================================

.PHONY: custom_disass custom_size custom_hex

# Show disassembly
custom_disass:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_disass TEST=<test_name>"
	@exit 1
endif
	@if [ ! -f "$(CUSTOM_BUILD_DIR)/$(TEST).elf" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) ELF file not found"; \
		exit 1; \
	fi
	@riscv32-unknown-elf-objdump -d "$(CUSTOM_BUILD_DIR)/$(TEST).elf" | less

# Show size
custom_size:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_size TEST=<test_name>"
	@exit 1
endif
	@if [ ! -f "$(CUSTOM_BUILD_DIR)/$(TEST).elf" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) ELF file not found"; \
		exit 1; \
	fi
	@riscv32-unknown-elf-size "$(CUSTOM_BUILD_DIR)/$(TEST).elf"

# Show hex dump
custom_hex:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_hex TEST=<test_name>"
	@exit 1
endif
	@if [ ! -f "$(CUSTOM_BUILD_DIR)/$(TEST).elf" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) ELF file not found"; \
		exit 1; \
	fi
	@riscv32-unknown-elf-objdump -x "$(CUSTOM_BUILD_DIR)/$(TEST).elf" | head -40

# Print info
custom_info:
ifndef TEST
	@echo -e "$(RED)[ERROR]$(RESET) Usage: make custom_info TEST=<test_name>"
	@exit 1
endif
	@mkdir -p $(CUSTOM_BUILD_DIR)
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)Custom Test Info: $(TEST)$(RESET)"
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Paths:$(RESET)"
	@echo "  Source:     $(CUSTOM_TEST_DIR)/$(TEST).c"
	@echo "  ELF:        $(CUSTOM_BUILD_DIR)/$(TEST).elf"
	@echo "  Binary:     $(CUSTOM_BUILD_DIR)/$(TEST).bin"
	@echo "  Memory:     $(CUSTOM_BUILD_DIR)/$(TEST).mem"
	@echo "  Disass:     $(CUSTOM_BUILD_DIR)/$(TEST).disass"
	@echo ""
	@echo -e "$(YELLOW)Build Status:$(RESET)"
	@if [ -f "$(CUSTOM_BUILD_DIR)/$(TEST).elf" ]; then \
		echo -e "  ELF:        $(GREEN)✓ Built$(RESET)"; \
		riscv32-unknown-elf-size "$(CUSTOM_BUILD_DIR)/$(TEST).elf" | tail -1 | \
			awk '{printf "  Size:       %s text + %s data + %s bss\n", $$1, $$2, $$3}'; \
	else \
		echo -e "  ELF:        $(RED)✗ Not built$(RESET)"; \
	fi
	@if [ -f "$(CUSTOM_BUILD_DIR)/$(TEST).mem" ]; then \
		echo -e "  Memory:     $(GREEN)✓ Generated$(RESET)"; \
	else \
		echo -e "  Memory:     $(RED)✗ Not generated$(RESET)"; \
	fi
	@echo ""

# Show configuration
custom_config:
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)Custom Test Configuration$(RESET)"
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo ""
	@echo -e "$(YELLOW)Config File:$(RESET)"
	@echo "  $(CUSTOM_CONFIG)"
	@echo ""
	@echo -e "$(YELLOW)Simulation Settings:$(RESET)"
	@echo "  Max Cycles:    $(CUSTOM_MAX_CYCLES)"
	@echo "  Timeout:       30 seconds"
	@echo ""
	@echo -e "$(YELLOW)Directories:$(RESET)"
	@echo "  Source:        $(CUSTOM_TEST_DIR)/"
	@echo "  Build:         $(CUSTOM_BUILD_DIR)/"
	@echo ""
	@echo -e "$(YELLOW)Configuration Details:$(RESET)"
	@if [ -f "$(CUSTOM_CONFIG)" ]; then \
		echo "  UART Logging:  Enabled"; \
		echo "  Spike Compare: Disabled"; \
		echo "  Format:        JSON"; \
		echo "  Schema:        $(SCRIPT_DIR)/config/tests/tests.schema.json"; \
	else \
		echo "  Config file not found"; \
	fi
	@echo ""

# ============================================================================
# Batch Operations
# ============================================================================

.PHONY: custom_run_all custom_build_all

# Build all custom tests
custom_build_all:
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)Building All Custom Tests$(RESET)"
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@if [ -z "$(CUSTOM_TESTS)" ]; then \
		echo -e "  $(YELLOW)No custom tests found$(RESET)"; \
	else \
		for test in $(CUSTOM_TESTS); do \
			echo -e "$(CYAN)[BUILD]$(RESET) $$test"; \
			$(MAKE) --no-print-directory custom_build TEST=$$test || exit 1; \
		done; \
	fi
	@echo -e "$(GREEN)[OK]$(RESET) All tests built"

# Run all custom tests from FLIST
custom_run_all:
	@if [ ! -f "$(SIM_DIR)/test/custom_tests.flist" ]; then \
		echo -e "$(RED)[ERROR]$(RESET) Test list not found: $(SIM_DIR)/test/custom_tests.flist"; \
		exit 1; \
	fi
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(CYAN)Running Custom Tests from FLIST$(RESET)"
	@echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"
	@TOTAL=0; PASSED=0; FAILED=0; \
	while IFS= read -r test; do \
		[ -z "$$test" ] && continue; \
		TOTAL=$$((TOTAL + 1)); \
		echo -e ""; \
		echo -e "$(CYAN)[TEST $$TOTAL]$(RESET) Running $$test..."; \
		if [ ! -f "$(CUSTOM_BUILD_DIR)/$$test.mem" ]; then \
			echo -e "$(YELLOW)[BUILD]$(RESET) Building $$test..."; \
			$(MAKE) --no-print-directory custom_build TEST=$$test || { FAILED=$$((FAILED + 1)); continue; }; \
		fi; \
		if $(MAKE) --no-print-directory custom_run TEST=$$test MAX_CYCLES=$(MAX_CYCLES); then \
			PASSED=$$((PASSED + 1)); \
			echo -e "$(GREEN)[✓ PASS]$(RESET) $$test"; \
		else \
			FAILED=$$((FAILED + 1)); \
			echo -e "$(RED)[✗ FAIL]$(RESET) $$test"; \
		fi; \
	done < "$(SIM_DIR)/test/custom_tests.flist"; \
	echo ""; \
	echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"; \
	echo -e "$(CYAN)Test Results:$(RESET)"; \
	echo -e "  Total:   $$TOTAL"; \
	echo -e "  $(GREEN)Passed:  $$PASSED$(RESET)"; \
	if [ $$FAILED -gt 0 ]; then \
		echo -e "  $(RED)Failed:  $$FAILED$(RESET)"; \
	else \
		echo -e "  Failed:  $$FAILED"; \
	fi; \
	echo -e "$(CYAN)═══════════════════════════════════════════════════════════$(RESET)"

# ============================================================================
# Integration Targets
# ============================================================================

# Add to main help
help: custom_help_integration

custom_help_integration:
	@echo ""
	@echo -e "$(CYAN)Custom Tests:$(RESET)"
	@echo -e "  make custom_help             Show custom test help"
	@echo -e "  make custom_list             List available tests"
	@echo -e "  make custom_config           Show configuration"
	@echo -e "  make custom_test TEST=<name> Build and run single test"
	@echo -e "  make custom_build_all        Build all custom tests"
	@echo -e "  make custom_run_all          Run all custom tests from flist"
	@echo ""

.PHONY: custom_help_integration
