# =========================================
# CERES RISC-V — OpenLane ASIC Flow
# =========================================

OPENLANE_SH := $(SCRIPT_DIR)/shell/openlane_flow.sh
ASIC_SUBREPO_SH := $(SCRIPT_DIR)/shell/setup_asic_subrepos.sh

.PHONY: asic_subrepos asic_setup asic_prep asic_run asic_report asic_clean

asic_subrepos:
	@echo -e "$(YELLOW)[ASIC TOOL SUBREPOS]$(RESET)"
	@bash $(ASIC_SUBREPO_SH)

asic_setup:
	@echo -e "$(YELLOW)[OPENLANE SETUP]$(RESET)"
	@bash $(OPENLANE_SH) setup

asic_prep:
	@echo -e "$(YELLOW)[OPENLANE PREPARE SOURCES]$(RESET)"
	@bash $(OPENLANE_SH) prep

asic_run:
	@echo -e "$(YELLOW)[OPENLANE FULL FLOW]$(RESET)"
	@bash $(OPENLANE_SH) run

asic_report:
	@echo -e "$(YELLOW)[OPENLANE REPORT]$(RESET)"
	@bash $(OPENLANE_SH) report

asic_clean:
	@echo -e "$(YELLOW)[OPENLANE CLEAN]$(RESET)"
	@bash $(OPENLANE_SH) clean
