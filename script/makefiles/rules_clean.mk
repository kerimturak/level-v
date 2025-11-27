# =========================================
# Clean Rules
# =========================================

clean:
	@echo -e "$(RED)[CLEANING BUILD FILES FOR $(BUILD_MODE_NAME)]$(RESET)"
	$(RM) $(BUILD_DIR)
	$(RM) $(RESULTS_DIR)
	$(RM) transcript
	$(RM) *wlf
	$(RM) *vcd
	@echo -e "$(GREEN) Clean complete.$(RESET)"

clean_results:
	@echo -e "$(RED)[CLEANING RESULTS]$(RESET)"
	$(RM) $(RESULTS_DIR)
	$(RM) transcript
	$(RM) *wlf
	$(RM) *vcd
	@echo -e "$(GREEN) Clean complete.$(RESET)"

clean_all:
	@echo -e "$(RED)[CLEANING BUILD FILES FOR $(BUILD_MODE_NAME)]$(RESET)"
	$(RM) $(BUILD_DIR)
	$(RM) $(RESULTS_DIR)
	$(RM) transcript
	$(RM) *wlf
	$(RM) *vcd
	$(RM) *vstf
	$(RM) wlft*
	$(RM) -rf $(ISA_ROOT)
	$(RM) -rf $(KONATA_DIR)
	$(RM) -rf $(WORK_DIR) transcript vsim.wlf modelsim.ini
	$(RM) -f $(LOG_DIR)/vsim_*.log $(LOG_DIR)/compile.log
	$(RM) $(TEST_LOG_DIR) $(TEST_WORK_DIR)
	$(RM) $(OBJ_DIR) $(LOG_DIR)/verilator_*.log dump.vcd cov.dat perf.vlt ast_dump.json
	$(RM) -f $(REPORT_DIR)/yosys_check.log $(REPORT_DIR)/yosys_synth.log $(REPORT_DIR)/yosys_show.log
	$(RM) -f $(REPORT_DIR)/$(TOP_LEVEL)_netlist.v $(REPORT_DIR)/$(TOP_LEVEL)_netlist.json
	$(RM) -f $(REPORT_DIR)/$(TOP_LEVEL)_graph.svg
	@echo -e "$(GREEN) Clean complete.$(RESET)"