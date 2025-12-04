
ifndef SV_DEFINES_COMPILED
SV_DEFINES_COMPILED := 1
# =========================================
# CERES RISC-V — Common Simulation Defines
# =========================================
# Bu dosya ana makefile tarafından include edilir.
# Tüm simülatörler için merkezi LOG/TRACE/SIM kontrolleri burada tanımlanır.
#
# Yeni bir LOG_* değişkeni eklemek için sadece LOG_VAR_LIST'e ekleyin.
# =========================================

# -----------------------------------------
# 1. Backward Compatibility Aliases
# -----------------------------------------
# Eski değişken isimlerini yeni isimlere çevir (tek seferlik)
# Kullanım: BP_LOG=1 → LOG_BP=1 olur

# Alias tablosu: OLD_NAME -> NEW_NAME
ifdef BP_LOG
  LOG_BP ?= $(BP_LOG)
endif
ifdef BP_VERBOSE
  LOG_BP_VERBOSE ?= $(BP_VERBOSE)
endif
ifdef FAST_SIM
  SIM_FAST ?= $(FAST_SIM)
endif
ifdef COVERAGE
  SIM_COVERAGE ?= $(COVERAGE)
endif

# -----------------------------------------
# 2. LOG Değişkenleri → SV_DEFINES Mapping
# -----------------------------------------
# Her LOG_* değişkeni için +define+ üretimi
# Kullanım: make run LOG_COMMIT=1 LOG_BP=1


# Geçici define biriktirici
_SV_DEFINES_TMP :=
ifeq ($(LOG_COMMIT),1)
  _SV_DEFINES_TMP += +define+LOG_COMMIT
endif
ifeq ($(LOG_PIPELINE),1)
  _SV_DEFINES_TMP += +define+LOG_PIPELINE
endif
ifeq ($(LOG_RAM),1)
  _SV_DEFINES_TMP += +define+LOG_RAM
endif
ifeq ($(LOG_UART),1)
  _SV_DEFINES_TMP += +define+LOG_UART
endif
ifeq ($(LOG_BP),1)
  _SV_DEFINES_TMP += +define+LOG_BP
endif
ifeq ($(LOG_BP_VERBOSE),1)
  _SV_DEFINES_TMP += +define+LOG_BP +define+LOG_BP_VERBOSE
endif

# -----------------------------------------
# 3. TRACE Kontrolleri
# -----------------------------------------
ifeq ($(KONATA_TRACER),1)
  _SV_DEFINES_TMP += +define+KONATA_TRACER
endif

# -----------------------------------------
# 4. SIM Kontrolleri
# -----------------------------------------
ifeq ($(SIM_FAST),1)
  _SV_DEFINES_TMP += +define+SIM_FAST
  DISABLE_TRACE := 1
endif

ifeq ($(SIM_UART_MONITOR),1)
  _SV_DEFINES_TMP += +define+SIM_UART_MONITOR
endif

ifeq ($(SIM_COVERAGE),1)
  _SV_DEFINES_TMP += +define+SIM_COVERAGE
  ENABLE_COVERAGE := 1
endif

# -----------------------------------------
# 5. TEST_TYPE'a göre otomatik ayarlar
# -----------------------------------------
ifeq ($(TEST_TYPE),bench)
  _SV_DEFINES_TMP += +define+SIM_UART_MONITOR
endif

# -----------------------------------------
# 6. Debug/Release mode'a göre ek define'lar
# -----------------------------------------
ifeq ($(MODE),debug)
  _SV_DEFINES_TMP += +define+DEBUG
endif
ifeq ($(MODE),test)
  _SV_DEFINES_TMP += +define+TEST_ENV +define+RISCV_TEST
endif

# -----------------------------------------
# 7. Varsayılan commit tracer (çoğu test için gerekli)
# -----------------------------------------
_SV_DEFINES_TMP += +define+COMMIT_TRACER


# Son olarak SV_DEFINES'ı birleştir
SV_DEFINES := $(strip $(_SV_DEFINES_TMP))

endif