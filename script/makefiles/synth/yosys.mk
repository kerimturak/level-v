# =========================================
# CERES RISC-V — Yosys Synthesis & Analysis
# =========================================
# Performs static design checks such as:
#   - Unconnected nets
#   - Multiple drivers
#   - Combinational loops
# Also supports synthesis and graphical netlist visualization.
# =========================================

# -----------------------------------------
# Yosys Configuration
# -----------------------------------------
YOSYS_FLAGS := -q
YOSYS_CMD   := read_verilog -sv $(SV_SOURCES) $(TB_FILE); \
               hierarchy -check -top $(RTL_LEVEL); \
               proc; opt; check

# =========================================
# Targets
# =========================================

# ---- Structural Check ----
yosys_check:
	@echo -e "$(YELLOW)[RUNNING YOSYS STRUCTURAL CHECKS — $(BUILD_MODE_NAME)]$(RESET)"
	@$(MKDIR) -p $(REPORT_DIR)
	@($(YOSYS) $(YOSYS_FLAGS) -p "$(YOSYS_CMD)" 2>&1 | tee $(REPORT_DIR)/yosys_check.log); \
	EXIT_CODE=$$?; \
	if grep -qi "ERROR:" $(REPORT_DIR)/yosys_check.log; then \
		echo "$(RED)TEST_NAME Yosys check failed (see yosys_check.log).$(RESET)"; \
		exit 1; \
	elif [ $$EXIT_CODE -ne 0 ]; then \
		echo "$(RED)TEST_NAME Yosys exited with code $$EXIT_CODE.$(RESET)"; \
		exit $$EXIT_CODE; \
	fi; \
	if grep -qi "Combinational loop" $(REPORT_DIR)/yosys_check.log; then \
		echo "$(RED)TEST_NAME Combinational loop(s) detected!$(RESET)"; \
		exit 1; \
	else \
		echo "$(GREEN)TEST_NAME No combinational loops detected.$(RESET)"; \
	fi; \
	if grep -qi "multiple drivers" $(REPORT_DIR)/yosys_check.log; then \
		echo "$(RED) TEST_NAME Multiple driver(s) detected!$(RESET)"; \
		exit 1; \
	else \
		echo "$(GREEN) TEST_NAME No multiple driver issues found.$(RESET)"; \
	fi; \
	if grep -qi "unconnected" $(REPORT_DIR)/yosys_check.log; then \
		echo "$(YELLOW) TEST_NAME  Some unconnected nets found — review yosys_check.log.$(RESET)"; \
	else \
		echo "$(GREEN) TEST_NAME No unconnected nets found.$(RESET)"; \
	fi; \
	echo "$(GREEN)[Yosys structural check completed successfully]$(RESET)"

# ---- Synthesis ----
yosys_synth:
	@echo -e "$(YELLOW)[RUNNING YOSYS SYNTHESIS — $(BUILD_MODE_NAME)]$(RESET)"
	@$(MKDIR) -p $(REPORT_DIR)
	@($(YOSYS) $(YOSYS_FLAGS) -p "read_verilog -sv $(SV_SOURCES); \
		hierarchy -check -top $(TOP_LEVEL); synth -top $(TOP_LEVEL); \
		write_json $(REPORT_DIR)/$(TOP_LEVEL)_netlist.json; \
		write_verilog $(REPORT_DIR)/$(TOP_LEVEL)_netlist.v" \
		2>&1 | tee $(REPORT_DIR)/yosys_synth.log); \
	EXIT_CODE=$$?; \
	if grep -qi "ERROR:" $(REPORT_DIR)/yosys_synth.log; then \
		echo "$(RED)TEST_NAME Yosys synthesis failed (see yosys_synth.log).$(RESET)"; \
		exit 1; \
	elif [ $$EXIT_CODE -ne 0 ]; then \
		echo "$(RED)TEST_NAME Yosys exited with error code $$EXIT_CODE.$(RESET)"; \
		exit $$EXIT_CODE; \
	else \
		echo "$(GREEN)TEST_NAME Yosys synthesis completed successfully — netlist written to $(REPORT_DIR).$(RESET)"; \
	fi

# ---- Visualization ----
yosys_show:
	@echo -e "$(YELLOW)[GENERATING YOSYS GRAPHICAL NETLIST — $(BUILD_MODE_NAME)]$(RESET)"
	@$(MKDIR) -p $(REPORT_DIR)
	@($(YOSYS) $(YOSYS_FLAGS) -p "read_verilog -sv $(SV_SOURCES); \
		hierarchy -top $(TOP_LEVEL); proc; opt; synth -top $(TOP_LEVEL); \
		show -format svg -prefix $(REPORT_DIR)/$(TOP_LEVEL)_graph" \
		2>&1 | tee $(REPORT_DIR)/yosys_show.log); \
	if grep -qi "ERROR:" $(REPORT_DIR)/yosys_show.log; then \
		echo "$(RED)TEST_NAME Graph generation failed (see yosys_show.log).$(RESET)"; \
		exit 1; \
	fi; \
	if [ -f $(REPORT_DIR)/$(TOP_LEVEL)_graph.svg ]; then \
		echo "$(GREEN)TEST_NAME Netlist visualization generated:$(RESET) $(REPORT_DIR)/$(TOP_LEVEL)_graph.svg"; \
		echo "🌐 Open with: xdg-open $(REPORT_DIR)/$(TOP_LEVEL)_graph.svg"; \
	else \
		echo "$(RED)TEST_NAME No SVG output found. Check yosys_show.log.$(RESET)"; \
		exit 1; \
	fi

# ---- Cleanup ----
clean_yosys:
	@echo -e "$(RED)[CLEANING YOSYS REPORT FILES]$(RESET)"
	rm -f $(REPORT_DIR)/yosys_check.log $(REPORT_DIR)/yosys_synth.log $(REPORT_DIR)/yosys_show.log
	rm -f $(REPORT_DIR)/$(TOP_LEVEL)_netlist.v $(REPORT_DIR)/$(TOP_LEVEL)_netlist.json
	rm -f $(REPORT_DIR)/$(TOP_LEVEL)_graph.svg
	@echo -e "$(GREEN)🧹 Yosys logs and visualizations cleaned.$(RESET)"

# ============================================================
# Yosys Help — Display available Yosys static & synthesis targets
# ============================================================
yosys_help:
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)             CERES RISC-V — Yosys Structural Analysis          $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e ""
	@echo -e "$(YELLOW)Purpose:$(RESET)"
	@echo -e "  Run structural checks, synthesis, and visualization using Yosys."
	@echo -e "  Detects unconnected nets, multiple drivers, and combinational loops."
	@echo -e ""
	@echo -e "$(YELLOW)Main Targets:$(RESET)"
	@echo -e "  $(GREEN)yosys_check   $(RESET)– Run static structural analysis"
	@echo -e "  $(GREEN)yosys_synth   $(RESET)– Perform synthesis and export netlists"
	@echo -e "  $(GREEN)yosys_show    $(RESET)– Generate a graphical (SVG) netlist view"
	@echo -e "  $(GREEN)clean_yosys   $(RESET)– Remove Yosys reports, netlists, and graphs"
	@echo -e ""
	@echo -e "$(YELLOW)Reports:$(RESET)"
	@echo -e "  • yosys_check.log – Results of structural integrity checks"
	@echo -e "  • yosys_synth.log – Synthesis and netlist generation report"
	@echo -e "  • yosys_show.log  – SVG graph generation log"
	@echo -e ""
	@echo -e "$(YELLOW)Output Files:$(RESET)"
	@echo -e "  • $(REPORT_DIR)/$(TOP_LEVEL)_netlist.v"
	@echo -e "  • $(REPORT_DIR)/$(TOP_LEVEL)_netlist.json"
	@echo -e "  • $(REPORT_DIR)/$(TOP_LEVEL)_graph.svg"
	@echo -e ""
	@echo -e "$(YELLOW)Examples:$(RESET)"
	@echo -e "  make yosys_check TOP_LEVEL=ceres_wrapper"
	@echo -e "  make yosys_synth TOP_LEVEL=ceres_wrapper"
	@echo -e "  make yosys_show  TOP_LEVEL=ceres_wrapper"
	@echo -e "  make clean_yosys"
	@echo -e ""
	@echo -e "$(YELLOW)Tips:$(RESET)"
	@echo -e "  • Use yosys_show to visualize RTL hierarchy in SVG format."
	@echo -e "  • Run yosys_check regularly to catch structural design issues early."
	@echo -e "  • All generated reports are stored under $(REPORT_DIR)."
	@echo -e ""
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
	@echo -e "$(GREEN)   Tip: You can open the SVG with 'xdg-open' or any browser.   $(RESET)"
	@echo -e "$(GREEN)══════════════════════════════════════════════════════════════$(RESET)"
