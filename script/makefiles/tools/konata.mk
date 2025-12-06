# ============================================================
# Konata Log Viewer Makefile
# Kullanım:
#   make konata SIM=verilator TEST_NAME=rv32ui-p-add
# ============================================================

# Logların bulunduğu path
LOG_ROOT   := $(RESULTS_DIR)/logs

# Parametreler
SIM        ?= verilator
TEST_NAME  ?= rv32ui-p-add

# Üretilen log dosyası
KONATA_LOG := $(LOG_ROOT)/$(SIM)/$(TEST_NAME)/ceres.log

# Konata binary (symlink varsa /usr/local/bin/konata çalışır)
KONATA_BIN ?= konata   # direk konata çalıştırır
# veya direkt path:
# KONATA_BIN ?= $(HOME)/tools/konata/konata.sh

.PHONY: konata show-log check-log

# --------------------------------------------------------------------------
# Konata ile log aç
# --------------------------------------------------------------------------
konata: check-log
	@echo ""
	@echo "🔍 Opening Konata for:"
	@echo "   SIM       = $(SIM)"
	@echo "   TEST_NAME = $(TEST_NAME)"
	@echo "   LOG FILE  = $(KONATA_LOG)"
	@echo ""
	$(KONATA_BIN) $(KONATA_LOG)

# --------------------------------------------------------------------------
# Log dosyası var mı kontrol et
# --------------------------------------------------------------------------
check-log:
	@if [ ! -f "$(KONATA_LOG)" ]; then \
		echo "$(ERROR) Log bulunamadı:"; \
		echo "   $(KONATA_LOG)"; \
		echo ""; \
		echo "ℹ️  Önce test çalıştırın:"; \
		echo "   make sim SIM=$(SIM) TEST_NAME=$(TEST_NAME)"; \
		exit 1; \
	fi

# --------------------------------------------------------------------------
# Log dosyasını ekrana bas (debug amaçlı)
# --------------------------------------------------------------------------
show-log: check-log
	@echo "-----------------------------------------"
	@echo "Log File: $(KONATA_LOG)"
	@echo "-----------------------------------------"
	@cat $(KONATA_LOG)
