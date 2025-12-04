# =========================================
# CERES RISC-V — Test Configuration Loader
# =========================================
# Merkezi test konfigürasyon yönetimi
#
# Bu dosya JSON konfigürasyon dosyalarını okur ve
# Make değişkenlerine dönüştürür.
#
# Kullanım:
#   make isa                     # isa.json kullanır
#   make bench TEST_CONFIG=fast  # fast profilini kullanır
#   make run TEST_CONFIG=isa     # isa konfigürasyonunu kullanır
# =========================================

# -----------------------------------------
# Configuration Paths
# -----------------------------------------
TEST_CONFIG_DIR   := $(ROOT_DIR)/script/config/tests
CONFIG_PARSER     := $(ROOT_DIR)/script/shell/parse_test_config.sh

# -----------------------------------------
# Auto-detect TEST_CONFIG from TEST_TYPE
# -----------------------------------------
# TEST_CONFIG belirtilmediyse TEST_TYPE'dan çıkar
ifndef TEST_CONFIG
  ifeq ($(TEST_TYPE),isa)
    TEST_CONFIG := isa
  else ifeq ($(TEST_TYPE),arch)
    TEST_CONFIG := arch
  else ifeq ($(TEST_TYPE),imperas)
    TEST_CONFIG := imperas
  else ifeq ($(TEST_TYPE),bench)
    TEST_CONFIG := bench
  else ifeq ($(TEST_TYPE),embench)
    TEST_CONFIG := embench
  else ifeq ($(TEST_TYPE),dhrystone)
    TEST_CONFIG := dhrystone
  else ifeq ($(TEST_TYPE),torture)
    TEST_CONFIG := torture
  else ifeq ($(TEST_TYPE),riscv-dv)
    TEST_CONFIG := riscv-dv
  else ifeq ($(TEST_TYPE),custom)
    TEST_CONFIG := custom
  else
    TEST_CONFIG := default
  endif
endif

# -----------------------------------------
# Load Configuration from JSON
# -----------------------------------------
# jq mevcut mu kontrol et
JQ_EXISTS := $(shell command -v jq 2>/dev/null)

ifdef JQ_EXISTS
  # Konfigürasyon dosyası var mı kontrol et
  TEST_CONFIG_FILE := $(TEST_CONFIG_DIR)/$(TEST_CONFIG).json
  
  ifneq ($(wildcard $(TEST_CONFIG_FILE)),)
    # Önbellek dosyası oluştur (tekrar parse etmemek için)
    CONFIG_CACHE := $(BUILD_DIR)/.test_config_$(TEST_CONFIG).mk
    
    # Önbellek güncel mi kontrol et
    CONFIG_DEPS := $(TEST_CONFIG_FILE) $(TEST_CONFIG_DIR)/default.json
    
    # Konfigürasyonu yükle
    -include $(CONFIG_CACHE)
    
    # Önbellek yoksa veya eskiyse yeniden oluştur
    $(CONFIG_CACHE): $(CONFIG_DEPS) | $(BUILD_DIR)
		@echo -e "$(YELLOW)[CONFIG]$(RESET) Loading $(TEST_CONFIG) configuration..."
		@chmod +x $(CONFIG_PARSER) 2>/dev/null || true
		@$(CONFIG_PARSER) $(TEST_CONFIG) --make > $@ 2>/dev/null || \
			echo "# Config parse failed, using defaults" > $@
  endif
endif

# -----------------------------------------
# Apply Config Values (with fallbacks)
# -----------------------------------------
# Konfigürasyon değerlerini uygula (kullanıcı override'ları öncelikli)

# MAX_CYCLES: Kullanıcı belirtmediyse config'den al
ifndef MAX_CYCLES_USER
  ifdef CFG_MAX_CYCLES
    MAX_CYCLES := $(CFG_MAX_CYCLES)
  endif
endif

# FAST_SIM: Kullanıcı belirtmediyse config'den al
ifndef FAST_SIM_USER
  ifdef CFG_FAST_SIM
    ifeq ($(CFG_FAST_SIM),1)
      FAST_SIM := 1
    endif
  endif
endif

# BP_LOG: Kullanıcı belirtmediyse config'den al
ifndef BP_LOG_USER
  ifdef CFG_BP_LOG
    ifeq ($(CFG_BP_LOG),1)
      BP_LOG := 1
    endif
  endif
endif

# NO_ADDR: Kullanıcı belirtmediyse config'den al
ifndef NO_ADDR_USER
  ifdef CFG_NO_ADDR
    NO_ADDR := $(CFG_NO_ADDR)
  endif
endif

# MODE: Kullanıcı belirtmediyse config'den al
ifndef MODE_USER
  ifdef CFG_MODE
    MODE := $(CFG_MODE)
  endif
endif

# TRACE: Kullanıcı belirtmediyse config'den al
ifndef TRACE_USER
  ifdef CFG_TRACE
    ifeq ($(CFG_TRACE),0)
      TRACE := 0
    endif
  endif
endif

# SV_DEFINES: Config'den gelen define'ları ekle
ifdef CFG_SV_DEFINES
  SV_DEFINES += $(CFG_SV_DEFINES)
endif

# -----------------------------------------
# Spike Configuration from JSON
# -----------------------------------------
# Override toolchain.mk defaults with JSON config values

# ISA: Default from toolchain.mk, can be overridden by JSON config
ifdef CFG_SPIKE_ISA
  SPIKE_ISA := $(CFG_SPIKE_ISA)
endif

# Privilege level
ifdef CFG_SPIKE_PRIV
  SPIKE_PRIV := $(CFG_SPIKE_PRIV)
endif

# PC start address
ifdef CFG_SPIKE_PC
  SPIKE_PC := $(CFG_SPIKE_PC)
endif

# Triggers count
ifdef CFG_SPIKE_TRIGGERS
  SPIKE_TRIGGERS := $(CFG_SPIKE_TRIGGERS)
else
  SPIKE_TRIGGERS := 1
endif

# PMP regions
ifdef CFG_SPIKE_PMP_REGIONS
  SPIKE_PMP_REGIONS := $(CFG_SPIKE_PMP_REGIONS)
else
  SPIKE_PMP_REGIONS := 0
endif

# PMP granularity
ifdef CFG_SPIKE_PMP_GRANULARITY
  SPIKE_PMP_GRANULARITY := $(CFG_SPIKE_PMP_GRANULARITY)
else
  SPIKE_PMP_GRANULARITY := 4
endif

# Build SPIKE_ARGS from config values
SPIKE_ARGS := --isa=$(SPIKE_ISA) --pc=$(SPIKE_PC) --priv=$(SPIKE_PRIV)
SPIKE_ARGS += --triggers=$(SPIKE_TRIGGERS)

# Add optional PMP configuration
ifneq ($(SPIKE_PMP_REGIONS),0)
  SPIKE_ARGS += --pmpregions=$(SPIKE_PMP_REGIONS)
  SPIKE_ARGS += --pmpgranularity=$(SPIKE_PMP_GRANULARITY)
endif

# Misaligned access support
ifeq ($(CFG_SPIKE_MISALIGNED),1)
  SPIKE_ARGS += --misaligned
endif

# Log commits (usually always enabled for comparison)
ifeq ($(CFG_SPIKE_LOG_COMMITS),1)
  SPIKE_ARGS += --log-commits
else ifdef CFG_SPIKE_LOG_COMMITS
  # Not set in config, use default (enabled)
else
  SPIKE_ARGS += --log-commits
endif

# -----------------------------------------
# Debug: Show loaded config
# -----------------------------------------
.PHONY: show-config config-info

show-config config-info:
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  Current Test Configuration$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  TEST_CONFIG     = $(GREEN)$(TEST_CONFIG)$(RESET)"
	@echo -e "  TEST_TYPE       = $(TEST_TYPE)"
	@echo -e "  MAX_CYCLES      = $(MAX_CYCLES)"
	@echo -e "  FAST_SIM        = $(FAST_SIM)"
	@echo -e "  BP_LOG          = $(BP_LOG)"
	@echo -e "  NO_ADDR         = $(NO_ADDR)"
	@echo -e "  MODE            = $(MODE)"
	@echo -e "  TRACE           = $(TRACE)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  Spike Configuration$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "  SPIKE_ISA       = $(SPIKE_ISA)"
	@echo -e "  SPIKE_PC        = $(SPIKE_PC)"
	@echo -e "  SPIKE_PRIV      = $(SPIKE_PRIV)"
	@echo -e "  SPIKE_TRIGGERS  = $(SPIKE_TRIGGERS)"
	@echo -e "  SPIKE_PMP_REGIONS= $(SPIKE_PMP_REGIONS)"
	@echo -e "  SPIKE_ARGS      = $(SPIKE_ARGS)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
ifdef JQ_EXISTS
	@echo ""
	@echo -e "$(YELLOW)JSON Config:$(RESET)"
	@$(CONFIG_PARSER) $(TEST_CONFIG) 2>/dev/null || echo "  (config parser not available)"
endif

# -----------------------------------------
# List available configs
# -----------------------------------------
.PHONY: list-configs configs

list-configs configs:
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
	@echo -e "$(CYAN)  Available Test Configurations$(RESET)"
	@echo -e "$(CYAN)━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━$(RESET)"
ifdef JQ_EXISTS
	@$(CONFIG_PARSER) --list 2>/dev/null || \
		for f in $(TEST_CONFIG_DIR)/*.json; do \
			[ -f "$$f" ] && basename "$$f" .json | grep -v schema; \
		done
else
	@for f in $(TEST_CONFIG_DIR)/*.json; do \
		[ -f "$$f" ] && basename "$$f" .json | grep -v schema; \
	done
endif
	@echo ""
	@echo -e "$(YELLOW)Usage:$(RESET)"
	@echo -e "  make run TEST_CONFIG=isa"
	@echo -e "  make bench                 # Auto-selects bench config"
	@echo -e "  make show-config           # Show current config values"
