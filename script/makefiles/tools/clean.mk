# =========================================
# CERES RISC-V — Clean Rules
# =========================================

.PHONY: clean clean_all

# ============================================================
# Standard Clean (build + results)
# ============================================================
clean:
	@echo -e "$(RED)[CLEANING BUILD & RESULTS]$(RESET)"
	@$(RM) "$(BUILD_DIR)"
	@$(RM) "$(RESULTS_DIR)"
	@$(RM) transcript *.wlf *.vcd *.vstf wlft*
	@echo -e "$(GREEN)Clean complete.$(RESET)"

# ============================================================
# Full Clean (includes subrepos)
# ============================================================
clean_all: clean
	@echo -e "$(RED)[CLEANING SUBREPOS]$(RESET)"
	@$(RM) "$(ISA_ROOT)"
	@$(RM) "$(ARCH_ROOT)"
	@echo -e "$(GREEN)Full clean complete.$(RESET)"
