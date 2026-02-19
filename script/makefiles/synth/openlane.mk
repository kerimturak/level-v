# =========================================
# CERES RISC-V — OpenLane ASIC Flow
# =========================================
#
# ┌─────────────────────────────────────────────────────────┐
# │  OpenLane Flow Aşamaları (Steps)                        │
# │                                                         │
# │   1. synthesis (Yosys)                                  │
# │   2. sta (OpenSTA - synthesis)                          │
# │   3. init_floorplan (area/die sizing)                   │
# │   4. ioplacer (pin placement)                           │
# │   5. ★ manual_macro_place (MACRO_PLACEMENT_CFG)         │
# │   6. pdn (power delivery network)                      │
# │   7. tap/decap cell insertion                           │
# │   8-10. global_placement (GPL)                          │
# │  11. resize/repair                                      │
# │  12-14. detailed_placement                              │
# │  15. cts (clock tree synthesis)                         │
# │  16-17. post-CTS optimization                          │
# │  18. global_routing (GRT)                               │
# │  19. fill_insertion                                     │
# │  20. detailed_routing (DRT)                             │
# │  21. spef_extraction                                    │
# │  22-23. sta (signoff)                                   │
# │  24-29. magic/klayout/lvs/drc/antenna                   │
# │  30. final views & summary                             │
# └─────────────────────────────────────────────────────────┘
#
# SRAM Macro Yerleştirme Akışı:
#   Step 5'te (manual_macro_place) yapılır. Bunun için:
#   1. make asic_sram       → SRAM LEF/GDS/LIB indir
#   2. make asic_prep       → RTL'i sv2v ile dönüştür
#   3. make asic_synth_only → Sadece synthesis + floorplan çalıştır
#   4. make asic_dump_names → ODB'den gerçek instance isimlerini çıkar
#   5. macro_placement.cfg'yi gerçek isimlerle güncelle
#   6. config.tcl'de MACRO_PLACEMENT_CFG satırını aç
#   7. make asic_run        → Tam akışı başlat
#
# =========================================

# -----------------------------------------
# Paths & Defaults
# -----------------------------------------
OPENLANE_SH       := $(SCRIPT_DIR)/shell/openlane_flow.sh
SRAM_GEN_SH       := $(SCRIPT_DIR)/shell/generate_sram_macros.sh
ASIC_SUBREPO_SH   := $(SCRIPT_DIR)/shell/setup_asic_subrepos.sh

ASIC_DESIGN_DIR   := $(ROOT_DIR)/asic/openlane/designs/ceres_wrapper
ASIC_RUNS_DIR     := $(RESULTS_DIR)/asic/openlane/ceres_wrapper/runs
ASIC_CONFIG       := $(ASIC_DESIGN_DIR)/config.tcl
MACRO_CFG         := $(ASIC_DESIGN_DIR)/macro_placement.cfg
SRAM_MACRO_DIR    := $(ASIC_DESIGN_DIR)/macros/sky130_sram_1kbyte_1rw1r_32x256_8

# OpenLane / Docker settings (override via env or command line)
OPENLANE_IMAGE    ?= efabless/openlane:2023.09.07
PDK_ROOT          ?= $(HOME)/.volare
PDK               ?= sky130A
ASIC_TAG          ?= run_$(shell date +%Y%m%d_%H%M%S)
DOCKER_CPUS       ?=
DOCKER_CPU_SHARES ?=

# SRAM macro name
SRAM_MACRO_NAME   ?= sky130_sram_1kbyte_1rw1r_32x256_8
SRAM_MACRO_REPO   ?= https://github.com/efabless/sky130_sram_macros.git

# -----------------------------------------
# Docker helper
# -----------------------------------------
DOCKER_BASE = docker run --rm \
	-u "$$(id -u):$$(id -g)" \
	-e PDK_ROOT="$(PDK_ROOT)" \
	-e PDK="$(PDK)" \
	$(if $(DOCKER_CPUS),--cpus $(DOCKER_CPUS),) \
	$(if $(DOCKER_CPU_SHARES),--cpu-shares $(DOCKER_CPU_SHARES),) \
	-v "$(ROOT_DIR):$(ROOT_DIR)" \
	-v "$(PDK_ROOT):$(PDK_ROOT)" \
	-w "$(ROOT_DIR)"

DOCKER_RUN = $(DOCKER_BASE) $(OPENLANE_IMAGE)

# Interactive mode (with terminal)
DOCKER_RUN_IT = docker run --rm -it \
	-u "$$(id -u):$$(id -g)" \
	-e PDK_ROOT="$(PDK_ROOT)" \
	-e PDK="$(PDK)" \
	$(if $(DOCKER_CPUS),--cpus $(DOCKER_CPUS),) \
	$(if $(DOCKER_CPU_SHARES),--cpu-shares $(DOCKER_CPU_SHARES),) \
	-v "$(ROOT_DIR):$(ROOT_DIR)" \
	-v "$(PDK_ROOT):$(PDK_ROOT)" \
	-w "$(ROOT_DIR)" \
	$(OPENLANE_IMAGE)

# -----------------------------------------
# Latest run directory helper
# -----------------------------------------
LATEST_RUN = $(shell ls -1dt $(ASIC_RUNS_DIR)/* 2>/dev/null | head -n1)

# ==============================================================
# SRAM Macro Targets
# ==============================================================

.PHONY: asic_sram asic_sram_clean asic_sram_info sram

## SRAM makrolarını indir ve materialize et (LEF/GDS/LIB/V)
asic_sram:
	@echo -e "$(CYAN)[SRAM]$(RESET) Generating SRAM macro: $(SRAM_MACRO_NAME)"
	@MACRO_NAME="$(SRAM_MACRO_NAME)" MACRO_REPO_URL="$(SRAM_MACRO_REPO)" \
		bash $(SRAM_GEN_SH)
	@echo -e "$(GREEN)$(SUCCESS) SRAM macro ready$(RESET)"

## SRAM makro dosyalarını temizle
asic_sram_clean:
	@echo -e "$(YELLOW)[SRAM CLEAN]$(RESET)"
	@bash $(SRAM_GEN_SH) --clean
	@echo -e "$(GREEN)$(SUCCESS) SRAM macros cleaned$(RESET)"

## SRAM makro dosyalarının durumunu göster
asic_sram_info:
	@echo -e "$(CYAN)[SRAM INFO]$(RESET)"
	@echo "  Macro name : $(SRAM_MACRO_NAME)"
	@echo "  Macro dir  : $(SRAM_MACRO_DIR)"
	@if [ -d "$(SRAM_MACRO_DIR)" ]; then \
		echo -e "  Status     : $(GREEN)$(SUCCESS) Files present$(RESET)"; \
		ls -lh $(SRAM_MACRO_DIR)/ | tail -n +2 | sed 's/^/  /'; \
	else \
		echo -e "  Status     : $(RED)$(ERROR) Not found$(RESET)"; \
		echo "  Run: make asic_sram"; \
	fi

## Kısa yol: make sram → make asic_sram
sram: asic_sram

# ==============================================================
# Source Preparation
# ==============================================================

.PHONY: asic_prep

## RTL kaynaklarını kopyala ve sv2v dönüşümü yap
asic_prep:
	@echo -e "$(CYAN)[OPENLANE PREP]$(RESET) Preparing sources (sv2v)..."
	@bash $(OPENLANE_SH) prep
	@echo -e "$(GREEN)$(SUCCESS) Sources ready$(RESET)"

# ==============================================================
# Setup & Dependencies
# ==============================================================

.PHONY: asic_setup asic_subrepos asic_check

## OpenLane Docker image ve SRAM makrolarını hazırla
asic_setup: asic_sram
	@echo -e "$(CYAN)[OPENLANE SETUP]$(RESET)"
	@bash $(OPENLANE_SH) setup
	@echo -e "$(GREEN)$(SUCCESS) Setup complete$(RESET)"

## ASIC araç subrepo'larını kur
asic_subrepos:
	@echo -e "$(YELLOW)[ASIC TOOL SUBREPOS]$(RESET)"
	@bash $(ASIC_SUBREPO_SH)

## Akış için gereken tüm bağımlılıkları kontrol et
asic_check:
	@echo -e "$(CYAN)[ASIC CHECK]$(RESET) Checking dependencies..."
	@echo -n "  Docker         : "; \
		command -v docker >/dev/null 2>&1 && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(RED)MISSING$(RESET)"
	@echo -n "  OpenLane image : "; \
		docker image inspect $(OPENLANE_IMAGE) >/dev/null 2>&1 && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(RED)MISSING → make asic_setup$(RESET)"
	@echo -n "  PDK ($(PDK))   : "; \
		[ -d "$(PDK_ROOT)/$(PDK)" ] && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(RED)MISSING$(RESET)"
	@echo -n "  SRAM macros    : "; \
		[ -f "$(SRAM_MACRO_DIR)/$(SRAM_MACRO_NAME).lef" ] && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(RED)MISSING → make asic_sram$(RESET)"
	@echo -n "  sv2v sources   : "; \
		[ -f "$(ASIC_DESIGN_DIR)/src/ceres_wrapper_sv2v.v" ] && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(YELLOW)Not prepared → make asic_prep$(RESET)"
	@echo -n "  config.tcl     : "; \
		[ -f "$(ASIC_CONFIG)" ] && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(RED)MISSING$(RESET)"
	@echo -n "  macro_place cfg: "; \
		[ -f "$(MACRO_CFG)" ] && echo -e "$(GREEN)OK$(RESET)" || echo -e "$(YELLOW)Not found (optional)$(RESET)"

# ==============================================================
# Full Flow
# ==============================================================

.PHONY: asic_run asic_run_clean asic

## Tam OpenLane akışı: SRAM + kaynaklar + flow.tcl
asic_run: asic_sram asic_prep
	@echo -e "$(CYAN)[OPENLANE RUN]$(RESET) Starting full flow..."
	@echo "  Tag        : $(ASIC_TAG)"
	@echo "  Config     : $(ASIC_CONFIG)"
	@echo "  Runs dir   : $(ASIC_RUNS_DIR)"
	@mkdir -p $(ASIC_RUNS_DIR)
	@TAG="$(ASIC_TAG)" RESULTS_ROOT="$(RESULTS_DIR)/asic/openlane/ceres_wrapper" \
		bash $(OPENLANE_SH) run
	@echo -e "$(GREEN)$(SUCCESS) Flow completed$(RESET)"

## Sıfırdan başla: clean + full run
asic_run_clean: asic_clean asic_run

## Kısa yol: make asic → make asic_run
asic: asic_run

# ==============================================================
# Step-by-Step Interactive Flow
# ==============================================================

.PHONY: asic_interactive asic_interactive_raw asic_shell

## OpenLane interactive modda aç (auto-prep: package require + prep otomatik)
asic_interactive: asic_sram asic_prep
	@echo -e "$(CYAN)[OPENLANE INTERACTIVE]$(RESET) Auto-initializing..."
	@mkdir -p $(ASIC_RUNS_DIR)
	docker run --rm -it \
		-u "$$(id -u):$$(id -g)" \
		-e PDK_ROOT="$(PDK_ROOT)" \
		-e PDK="$(PDK)" \
		-e CERES_DESIGN_DIR="$(ASIC_DESIGN_DIR)" \
		-e CERES_RUN_TAG="$(ASIC_TAG)" \
		-e CERES_RUNS_DIR="$(ASIC_RUNS_DIR)" \
		$(if $(DOCKER_CPUS),--cpus $(DOCKER_CPUS),) \
		$(if $(DOCKER_CPU_SHARES),--cpu-shares $(DOCKER_CPU_SHARES),) \
		-v "$(ROOT_DIR):$(ROOT_DIR)" \
		-v "$(PDK_ROOT):$(PDK_ROOT)" \
		-w "$(ROOT_DIR)" \
		$(OPENLANE_IMAGE) \
		/bin/bash -lc '{ \
			echo "package require openlane" ; \
			echo "prep -design $(ASIC_DESIGN_DIR) -tag $(ASIC_TAG) -run_path $(ASIC_RUNS_DIR) -overwrite" ; \
			echo "puts \\\"\"" ; \
			echo "puts \\\"[CERES] Ready! Type: run_synthesis, run_floorplan, etc.\\\"" ; \
			echo "puts \\\"\"" ; \
			cat ; \
		} | tclsh /openlane/flow.tcl -interactive'

## OpenLane interactive modda aç (bare — kendi prep komutlarını gir)
asic_interactive_raw: asic_sram asic_prep
	@echo -e "$(CYAN)[OPENLANE INTERACTIVE RAW]$(RESET)"
	@echo "  Aşağıdaki komutları girin:"
	@echo "    package require openlane"
	@echo "    prep -design $(ASIC_DESIGN_DIR) -tag $(ASIC_TAG) -run_path $(ASIC_RUNS_DIR)"
	@echo "  Veya tek komutla:"
	@echo "    source $(ROOT_DIR)/asic/openlane/interactive_init.tcl"
	@echo ""
	@mkdir -p $(ASIC_RUNS_DIR)
	docker run --rm -it \
		-u "$$(id -u):$$(id -g)" \
		-e PDK_ROOT="$(PDK_ROOT)" \
		-e PDK="$(PDK)" \
		-e CERES_DESIGN_DIR="$(ASIC_DESIGN_DIR)" \
		-e CERES_RUN_TAG="$(ASIC_TAG)" \
		-e CERES_RUNS_DIR="$(ASIC_RUNS_DIR)" \
		$(if $(DOCKER_CPUS),--cpus $(DOCKER_CPUS),) \
		$(if $(DOCKER_CPU_SHARES),--cpu-shares $(DOCKER_CPU_SHARES),) \
		-v "$(ROOT_DIR):$(ROOT_DIR)" \
		-v "$(PDK_ROOT):$(PDK_ROOT)" \
		-w "$(ROOT_DIR)" \
		$(OPENLANE_IMAGE) \
		/bin/bash -lc "tclsh /openlane/flow.tcl -interactive"

## OpenLane konteynerine bash shell aç (debug/inceleme için)
asic_shell:
	@echo -e "$(CYAN)[OPENLANE SHELL]$(RESET) Opening bash in container..."
	$(DOCKER_RUN_IT) /bin/bash

# ==============================================================
# Synthesis-Only (for name discovery)
# ==============================================================

.PHONY: asic_synth_only

## Sadece synthesis + floorplan çalıştır (instance isim keşfi için)
asic_synth_only: asic_sram asic_prep
	@echo -e "$(CYAN)[SYNTH ONLY]$(RESET) Running synthesis + floorplan..."
	@mkdir -p $(ASIC_RUNS_DIR)
	docker run --rm \
		-u "$$(id -u):$$(id -g)" \
		-e PDK_ROOT="$(PDK_ROOT)" \
		-e PDK="$(PDK)" \
		-e CERES_DESIGN_DIR="$(ASIC_DESIGN_DIR)" \
		-e CERES_RUNS_DIR="$(ASIC_RUNS_DIR)" \
		$(if $(DOCKER_CPUS),--cpus $(DOCKER_CPUS),) \
		$(if $(DOCKER_CPU_SHARES),--cpu-shares $(DOCKER_CPU_SHARES),) \
		-v "$(ROOT_DIR):$(ROOT_DIR)" \
		-v "$(PDK_ROOT):$(PDK_ROOT)" \
		-w "$(ROOT_DIR)" \
		$(OPENLANE_IMAGE) \
		/bin/bash -lc "tclsh /openlane/flow.tcl -interactive -file $(ROOT_DIR)/asic/openlane/synth_only.tcl"
	@echo -e "$(GREEN)$(SUCCESS) Synthesis + floorplan done$(RESET)"
	@echo "  Run dir: $(ASIC_RUNS_DIR)/synth_discovery"
	@echo "  Next  : make asic_dump_names"

# ==============================================================
# Macro Instance Name Discovery
# ==============================================================

.PHONY: asic_dump_names

## Floorplan ODB'den SRAM macro instance isimlerini çıkar
##   make asic_dump_names           → synth_discovery veya son run'dan
##   make asic_dump_names RUN=name  → belirli run'dan
asic_dump_names:
	@echo -e "$(CYAN)[DUMP NAMES]$(RESET) Extracting macro instance names from ODB..."
	@SEARCH_DIR=""; \
	if [ -n "$(RUN)" ] && [ -d "$(ASIC_RUNS_DIR)/$(RUN)" ]; then \
		SEARCH_DIR="$(ASIC_RUNS_DIR)/$(RUN)"; \
	elif [ -d "$(ASIC_RUNS_DIR)/synth_discovery" ]; then \
		SEARCH_DIR="$(ASIC_RUNS_DIR)/synth_discovery"; \
	elif [ -n "$(LATEST_RUN)" ]; then \
		SEARCH_DIR="$(LATEST_RUN)"; \
	else \
		echo -e "$(RED)$(ERROR) No run found. Run 'make asic_synth_only' first$(RESET)"; \
		exit 1; \
	fi; \
	echo "  Using run: $$SEARCH_DIR"; \
	ODB=$$(find "$$SEARCH_DIR" -name '*.odb' -path '*/floorplan/*' 2>/dev/null | sort | tail -1); \
	if [ -z "$$ODB" ]; then \
		ODB=$$(find "$$SEARCH_DIR" -name '*.odb' 2>/dev/null | sort | tail -1); \
	fi; \
	if [ -z "$$ODB" ]; then \
		echo -e "$(RED)$(ERROR) No ODB file found in $$SEARCH_DIR$(RESET)"; \
		exit 1; \
	fi; \
	echo "  ODB file: $$ODB"; \
	echo ""; \
	$(DOCKER_BASE) $(OPENLANE_IMAGE) /bin/bash -lc \
		"openroad -python $(ROOT_DIR)/script/python/dump_macro_names.py $$ODB"; \
	echo ""; \
	echo -e "$(GREEN)$(SUCCESS) Done. Copy the names above into macro_placement.cfg$(RESET)"

# ==============================================================
# Resume a Previous Run
# ==============================================================

.PHONY: asic_resume

## Önceki bir run'ı kaldığı yerden devam ettir
##   make asic_resume RUN=run_20260218_123456
##   make asic_resume  (en son run'ı devam ettirir)
asic_resume:
	@echo -e "$(CYAN)[OPENLANE RESUME]$(RESET)"
	@RUN_DIR=""; \
	if [ -n "$(RUN)" ] && [ -d "$(ASIC_RUNS_DIR)/$(RUN)" ]; then \
		RUN_DIR="$(ASIC_RUNS_DIR)/$(RUN)"; \
	elif [ -n "$(LATEST_RUN)" ]; then \
		RUN_DIR="$(LATEST_RUN)"; \
	else \
		echo -e "$(RED)$(ERROR) No run found to resume$(RESET)"; \
		exit 1; \
	fi; \
	TAG_NAME=$$(basename "$$RUN_DIR"); \
	echo "  Resuming: $$RUN_DIR"; \
	echo "  Tag     : $$TAG_NAME"; \
	$(DOCKER_RUN_IT) /bin/bash -lc "\
		tclsh /openlane/flow.tcl -interactive << 'TCLEOF' \
\npackage require openlane \
\nprep -design $(ASIC_DESIGN_DIR) -tag $$TAG_NAME -run_path $(ASIC_RUNS_DIR) -overwrite \
\nputs \"CURRENT_INDEX = \\\$$::env(CURRENT_INDEX)\" \
\nputs \"CURRENT_DEF   = \\\$$::env(CURRENT_DEF)\" \
\nTCLEOF"

# ==============================================================
# Reports & Inspection
# ==============================================================

.PHONY: asic_report asic_runs asic_metrics asic_timing

## Son run'ın raporlarını göster
asic_report:
	@echo -e "$(CYAN)[OPENLANE REPORT]$(RESET)"
	@bash $(OPENLANE_SH) report

## Mevcut run dizinlerini listele
asic_runs:
	@echo -e "$(CYAN)[ASIC RUNS]$(RESET)"
	@if [ -d "$(ASIC_RUNS_DIR)" ]; then \
		for d in $(ASIC_RUNS_DIR)/*/; do \
			[ -d "$$d" ] || continue; \
			tag=$$(basename "$$d"); \
			step=$$(grep -oP 'Step \K[0-9]+' "$$d/openlane.log" 2>/dev/null | tail -1 || echo "?"); \
			done_mark=""; \
			[ -f "$$d/results/final/gds/ceres_wrapper.gds" ] && done_mark=" $(GREEN)$(SUCCESS)$(RESET)"; \
			echo -e "  $$tag  (last step: $$step)$$done_mark"; \
		done; \
	else \
		echo "  No runs yet."; \
	fi

## Son run'ın metriklerini göster (area, cell count, etc.)
asic_metrics:
	@if [ -n "$(LATEST_RUN)" ] && [ -f "$(LATEST_RUN)/reports/metrics.csv" ]; then \
		echo -e "$(CYAN)[METRICS]$(RESET) $(LATEST_RUN)/reports/metrics.csv"; \
		head -2 "$(LATEST_RUN)/reports/metrics.csv" | column -t -s,; \
	else \
		echo -e "$(RED)No metrics found$(RESET)"; \
	fi

## Son run'ın timing raporunu göster
asic_timing:
	@if [ -n "$(LATEST_RUN)" ]; then \
		STA=$$(find "$(LATEST_RUN)" -name '*sta*summary*' -o -name '*timing*' 2>/dev/null | sort | tail -3); \
		if [ -n "$$STA" ]; then \
			echo -e "$(CYAN)[TIMING]$(RESET)"; \
			for f in $$STA; do echo "--- $$f ---"; head -30 "$$f"; echo ""; done; \
		else \
			echo -e "$(RED)No timing reports found$(RESET)"; \
		fi; \
	else \
		echo -e "$(RED)No runs found$(RESET)"; \
	fi

# ==============================================================
# GUI & Visualization
# ==============================================================
# Kullanım:
#   make asic_view_floorplan                 → Floorplan + SRAM makro yerleşimi
#   make asic_view_placement                 → Standart hücre yerleşimi
#   make asic_view_cts                       → Clock tree synthesis sonrası
#   make asic_view_routing                   → Routing sonrası (varsa)
#   make asic_view_final                     → Final GDS
#   make asic_view_all                       → Tüm aşamaları aynı anda aç
#   make asic_gui                            → OpenROAD GUI (ODB, interaktif)
#   make asic_gds                            → Final GDS (KLayout)
#
# Belirli bir run seçmek için: RUN=run_name
# Viewer seçimi: VIEWER=klayout (default) | openroad
# ==============================================================

VIEWER ?= klayout
ASIC_VIEW_RUN = $(if $(RUN),$(ASIC_RUNS_DIR)/$(RUN),$(LATEST_RUN))

# ── Internal: resolve DEF/ODB for a given stage ──
# $(1) = stage name for display
# $(2) = search path fragment (e.g., floorplan, placement, cts, routing)
# $(3) = optional filename pattern
define _asic_find_def
$(shell \
	RD="$(ASIC_VIEW_RUN)"; \
	if [ -n "$$RD" ]; then \
		f=$$(find "$$RD" -name '*.def' -path '*/$(2)/*' 2>/dev/null | sort | tail -1); \
		echo "$$f"; \
	fi \
)
endef

define _asic_find_odb
$(shell \
	RD="$(ASIC_VIEW_RUN)"; \
	if [ -n "$$RD" ]; then \
		f=$$(find "$$RD" -name '*.odb' -path '*/$(2)/*' 2>/dev/null | sort | tail -1); \
		echo "$$f"; \
	fi \
)
endef

# ── Internal: open a file with the chosen viewer ──
# $(1) = stage description
# $(2) = DEF file path (for KLayout)
# $(3) = ODB file path (for OpenROAD)
define _asic_view_file
	@DEF_FILE="$(2)"; \
	ODB_FILE="$(3)"; \
	if [ "$(VIEWER)" = "openroad" ]; then \
		if [ -z "$$ODB_FILE" ]; then \
			echo -e "$(RED)$(ERROR) $(1): ODB dosyası bulunamadı$(RESET)"; \
			if [ -z "$(ASIC_VIEW_RUN)" ]; then \
				echo "  Henüz run yok. Önce: make asic_run"; \
			else \
				echo "  Run: $(ASIC_VIEW_RUN)"; \
				echo "  Bu aşama henüz tamamlanmamış olabilir."; \
			fi; \
			exit 1; \
		fi; \
		echo -e "$(CYAN)[VIEW $(1)]$(RESET) $$ODB_FILE"; \
		echo "  Viewer: OpenROAD GUI (Docker)"; \
		TCL=$$(mktemp /tmp/asic_view_XXXXXX.tcl); \
		echo "read_db $$ODB_FILE" > "$$TCL"; \
		docker run --rm -it \
			-e DISPLAY=$$DISPLAY \
			-v /tmp/.X11-unix:/tmp/.X11-unix \
			-v "$(ROOT_DIR):$(ROOT_DIR):ro" \
			-v "$(PDK_ROOT):$(PDK_ROOT):ro" \
			-v "$$TCL:$$TCL:ro" \
			$(OPENLANE_IMAGE) \
			openroad -gui "$$TCL"; \
		rm -f "$$TCL"; \
	else \
		if [ -z "$$DEF_FILE" ]; then \
			echo -e "$(RED)$(ERROR) $(1): DEF dosyası bulunamadı$(RESET)"; \
			if [ -z "$(ASIC_VIEW_RUN)" ]; then \
				echo "  Henüz run yok. Önce: make asic_run"; \
			else \
				echo "  Run: $(ASIC_VIEW_RUN)"; \
				echo "  Bu aşama henüz tamamlanmamış olabilir."; \
			fi; \
			exit 1; \
		fi; \
		echo -e "$(CYAN)[VIEW $(1)]$(RESET) $$DEF_FILE"; \
		echo "  Viewer: KLayout (arka planda)"; \
		klayout "$$DEF_FILE" & \
	fi
endef

.PHONY: asic_view_floorplan asic_view_placement asic_view_cts
.PHONY: asic_view_routing asic_view_final asic_view_all
.PHONY: asic_gui asic_gds

## Floorplan + SRAM makro yerleşimini görüntüle (Step 5 sonrası)
##   VIEWER=klayout (default) | VIEWER=openroad
asic_view_floorplan:
	$(call _asic_view_file,FLOORPLAN,$(call _asic_find_def,floorplan,floorplan),$(call _asic_find_odb,floorplan,floorplan))

## Standart hücre yerleşimini görüntüle (Step 11 sonrası)
asic_view_placement:
	$(call _asic_view_file,PLACEMENT,$(call _asic_find_def,placement,placement),$(call _asic_find_odb,placement,placement))

## CTS sonrası yerleşimi görüntüle (Step 13 sonrası)
asic_view_cts:
	$(call _asic_view_file,CTS,$(call _asic_find_def,cts,cts),$(call _asic_find_odb,cts,cts))

## Routing sonrası görüntüle (Step 20 sonrası)
asic_view_routing:
	$(call _asic_view_file,ROUTING,$(call _asic_find_def,routing,routing),$(call _asic_find_odb,routing,routing))

## Final GDS'i görüntüle (Step 30 sonrası)
asic_view_final:
	@GDS=""; \
	if [ -n "$(ASIC_VIEW_RUN)" ]; then \
		GDS=$$(find "$(ASIC_VIEW_RUN)" -name '*.gds' -path '*/final/*' 2>/dev/null | head -1); \
	fi; \
	if [ -n "$$GDS" ]; then \
		echo -e "$(CYAN)[VIEW FINAL GDS]$(RESET) $$GDS"; \
		echo "  Viewer: KLayout (arka planda)"; \
		klayout "$$GDS" & \
	else \
		echo -e "$(RED)$(ERROR) Final GDS bulunamadı$(RESET)"; \
		echo "  Flow tamamlanmamış olabilir."; \
	fi

## Tüm mevcut aşamaları aynı anda aç
##   VIEWER=klayout (default) | VIEWER=openroad
asic_view_all:
	@echo -e "$(CYAN)[VIEW ALL]$(RESET) Mevcut aşamalar açılıyor..."
	@RD="$(ASIC_VIEW_RUN)"; \
	if [ -z "$$RD" ]; then \
		echo -e "$(RED)$(ERROR) Henüz run yok$(RESET)"; \
		exit 1; \
	fi; \
	echo "  Run   : $$RD"; \
	echo "  Viewer: $(VIEWER)"; \
	opened=0; \
	for stage in floorplan placement cts routing; do \
		if [ "$(VIEWER)" = "openroad" ]; then \
			FILE=$$(find "$$RD" -name '*.odb' -path "*results/$$stage/*" 2>/dev/null | sort | tail -1); \
		else \
			FILE=$$(find "$$RD" -name '*.def' -path "*results/$$stage/*" 2>/dev/null | sort | tail -1); \
		fi; \
		if [ -n "$$FILE" ]; then \
			echo -e "  $(GREEN)✓$(RESET) $$stage → $$FILE"; \
			if [ "$(VIEWER)" = "openroad" ]; then \
				TCL=$$(mktemp /tmp/asic_view_XXXXXX.tcl); \
				echo "read_db $$FILE" > "$$TCL"; \
				docker run --rm -d \
					-e DISPLAY=$$DISPLAY \
					-v /tmp/.X11-unix:/tmp/.X11-unix \
					-v "$(ROOT_DIR):$(ROOT_DIR):ro" \
					-v "$(PDK_ROOT):$(PDK_ROOT):ro" \
					-v "$$TCL:$$TCL:ro" \
					$(OPENLANE_IMAGE) \
					openroad -gui "$$TCL" >/dev/null 2>&1; \
			else \
				klayout "$$FILE" & \
			fi; \
			opened=$$((opened + 1)); \
			sleep 1; \
		else \
			echo -e "  $(DIM)·$(RESET) $$stage → (yok)"; \
		fi; \
	done; \
	GDS=$$(find "$$RD" -name '*.gds' -path '*/final/*' 2>/dev/null | head -1); \
	if [ -n "$$GDS" ]; then \
		echo -e "  $(GREEN)✓$(RESET) final/gds → $$GDS"; \
		klayout "$$GDS" & \
		opened=$$((opened + 1)); \
	else \
		echo -e "  $(DIM)·$(RESET) final/gds → (yok)"; \
	fi; \
	echo ""; \
	echo -e "$(GREEN)$(SUCCESS) $$opened pencere açıldı$(RESET)"

## OpenROAD GUI'de son run'ı aç (ODB, interaktif TCL konsolu ile)
asic_gui:
	@RD="$(ASIC_VIEW_RUN)"; \
	if [ -z "$$RD" ]; then \
		echo -e "$(RED)$(ERROR) No runs found$(RESET)"; \
		exit 1; \
	fi; \
	ODB=$$(find "$$RD" -name '*.odb' -path '*/results/*' 2>/dev/null | sort | tail -1); \
	if [ -z "$$ODB" ]; then \
		ODB=$$(find "$$RD" -name '*.odb' 2>/dev/null | sort | tail -1); \
	fi; \
	if [ -n "$$ODB" ]; then \
		echo -e "$(CYAN)[GUI]$(RESET) Opening: $$ODB"; \
		TCL=$$(mktemp /tmp/asic_gui_XXXXXX.tcl); \
		echo "read_db $$ODB" > "$$TCL"; \
		docker run --rm -it \
			-e DISPLAY=$$DISPLAY \
			-v /tmp/.X11-unix:/tmp/.X11-unix \
			-v "$(ROOT_DIR):$(ROOT_DIR):ro" \
			-v "$(PDK_ROOT):$(PDK_ROOT):ro" \
			-v "$$TCL:$$TCL:ro" \
			$(OPENLANE_IMAGE) \
			openroad -gui "$$TCL"; \
		rm -f "$$TCL"; \
	else \
		echo -e "$(RED)No ODB file found$(RESET)"; \
	fi

## KLayout ile GDS dosyasını aç
asic_gds:
	@if [ -n "$(ASIC_VIEW_RUN)" ] && [ -f "$(ASIC_VIEW_RUN)/results/final/gds/ceres_wrapper.gds" ]; then \
		echo -e "$(CYAN)[GDS]$(RESET) Opening GDS..."; \
		klayout "$(ASIC_VIEW_RUN)/results/final/gds/ceres_wrapper.gds" & \
	else \
		echo -e "$(RED)No final GDS found$(RESET)"; \
	fi

# ==============================================================
# Clean
# ==============================================================

.PHONY: asic_clean asic_clean_runs asic_clean_src

## Tüm ASIC çıktılarını temizle (runs + sources)
asic_clean:
	@echo -e "$(YELLOW)[OPENLANE CLEAN]$(RESET)"
	@bash $(OPENLANE_SH) clean
	@echo -e "$(GREEN)$(SUCCESS) Cleaned$(RESET)"

## Sadece run çıktılarını temizle (sources kalsın)
asic_clean_runs:
	@echo -e "$(YELLOW)[CLEAN RUNS]$(RESET)"
	@if [ -d "$(ASIC_RUNS_DIR)" ]; then \
		rm -rf $(ASIC_RUNS_DIR); \
		echo -e "$(GREEN)$(SUCCESS) Runs cleaned$(RESET)"; \
	else \
		echo "  Nothing to clean."; \
	fi

## Sadece sv2v kaynaklarını temizle
asic_clean_src:
	@echo -e "$(YELLOW)[CLEAN SRC]$(RESET)"
	@rm -rf $(ASIC_DESIGN_DIR)/src $(ASIC_DESIGN_DIR)/sources_manifest.txt
	@echo -e "$(GREEN)$(SUCCESS) Sources cleaned$(RESET)"

# ==============================================================
# Help
# ==============================================================

.PHONY: asic_help

asic_help:
	@echo ""
	@echo -e "$(BOLD)╔══════════════════════════════════════════════════════════════╗$(RESET)"
	@echo -e "$(BOLD)║          CERES RISC-V — OpenLane ASIC Flow                  ║$(RESET)"
	@echo -e "$(BOLD)╚══════════════════════════════════════════════════════════════╝$(RESET)"
	@echo ""
	@echo -e "$(CYAN)SRAM Macro:$(RESET)"
	@echo "  make asic_sram           SRAM makrolarını indir (LEF/GDS/LIB/V)"
	@echo "  make sram                Kısa yol (= asic_sram)"
	@echo "  make asic_sram_clean     SRAM dosyalarını temizle"
	@echo "  make asic_sram_info      SRAM dosya durumunu göster"
	@echo ""
	@echo -e "$(CYAN)Kaynak Hazırlık:$(RESET)"
	@echo "  make asic_prep           RTL → sv2v dönüşümü"
	@echo "  make asic_check          Tüm bağımlılıkları kontrol et"
	@echo "  make asic_setup          Docker image + SRAM hazırla"
	@echo ""
	@echo -e "$(CYAN)Tam Akış:$(RESET)"
	@echo "  make asic_run            SRAM + prep + tam OpenLane akışı"
	@echo "  make asic_run_clean      Temizle + sıfırdan tam akış"
	@echo "  make asic                Kısa yol (= asic_run)"
	@echo ""
	@echo -e "$(CYAN)Adım Adım / İnteraktif:$(RESET)"
	@echo "  make asic_interactive    OpenLane tclsh interactive mod"
	@echo "  make asic_shell          Konteyner bash shell"
	@echo "  make asic_synth_only     Sadece synthesis + floorplan"
	@echo "  make asic_resume         Kaldığı yerden devam et"
	@echo "    RUN=run_name             Belirli run'ı devam ettir"
	@echo ""
	@echo -e "$(CYAN)Macro Yerleştirme:$(RESET)"
	@echo "  make asic_dump_names     ODB'den SRAM instance isimlerini çıkar"
	@echo "    RUN=run_name             Belirli run'dan oku"
	@echo ""
	@echo -e "$(CYAN)Raporlar:$(RESET)"
	@echo "  make asic_report         Son run raporu"
	@echo "  make asic_runs           Tüm run'ları listele"
	@echo "  make asic_metrics        Metrikler (area, cell count)"
	@echo "  make asic_timing         Timing raporu"
	@echo ""
	@echo -e "$(CYAN)Görselleştirme:$(RESET)"
	@echo "  make asic_view_floorplan  Floorplan + SRAM makro yerleşimi"
	@echo "  make asic_view_placement  Standart hücre yerleşimi"
	@echo "  make asic_view_cts        CTS sonrası"
	@echo "  make asic_view_routing    Routing sonrası"
	@echo "  make asic_view_final      Final GDS"
	@echo "  make asic_view_all        Tüm aşamaları aynı anda aç"
	@echo "  make asic_gui             OpenROAD GUI (ODB, interaktif)"
	@echo "  make asic_gds             KLayout ile final GDS aç"
	@echo "    RUN=run_name              Belirli run'dan aç"
	@echo "    VIEWER=openroad           OpenROAD GUI kullan (default: klayout)"
	@echo ""
	@echo -e "$(CYAN)Temizlik:$(RESET)"
	@echo "  make asic_clean          Tüm ASIC çıktılarını temizle"
	@echo "  make asic_clean_runs     Sadece run'ları temizle"
	@echo "  make asic_clean_src      Sadece sv2v kaynaklarını temizle"
	@echo ""
	@echo -e "$(CYAN)Ortam Değişkenleri:$(RESET)"
	@echo "  ASIC_TAG=name            Run etiketi (default: timestamp)"
	@echo "  OPENLANE_IMAGE=img       Docker image"
	@echo "  PDK_ROOT=path            PDK kök dizini"
	@echo "  PDK=variant              PDK varyantı (sky130A)"
	@echo "  DOCKER_CPUS=N            Docker CPU limiti"
	@echo "  SRAM_MACRO_NAME=name     SRAM macro adı"
	@echo "  SRAM_MACRO_REPO=url      SRAM macro repo URL"
	@echo ""
	@echo -e "$(BOLD)Macro Yerleştirme Akışı (Step 5):$(RESET)"
	@echo "  ┌─────────────────────────────────────────────────────────┐"
	@echo "  │ 1. make asic_sram          → SRAM dosyalarını indir    │"
	@echo "  │ 2. make asic_synth_only    → Synthesis + floorplan     │"
	@echo "  │ 3. make asic_dump_names    → Gerçek instance isimleri  │"
	@echo "  │ 4. macro_placement.cfg'yi düzenle (isim + koordinat)   │"
	@echo "  │ 5. config.tcl'de MACRO_PLACEMENT_CFG satırını aç      │"
	@echo "  │ 6. make asic_run           → Tam akışı başlat         │"
	@echo "  └─────────────────────────────────────────────────────────┘"
	@echo ""
