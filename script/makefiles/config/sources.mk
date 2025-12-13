# =========================================
# CERES RISC-V — RTL Source Files
# =========================================

# -----------------------------------------
# Top Level Modules
# -----------------------------------------
RTL_LEVEL     := ceres_wrapper
TB_LEVEL      := tb_wrapper
TOP_LEVEL     ?= $(RTL_LEVEL)

# -----------------------------------------
# Logger Source (for Verilator)
# -----------------------------------------
LOGGER_SRC    ?= $(RTL_DIR)/tracer/konata_logger.sv

# -----------------------------------------
# RTL Source Files
# -----------------------------------------
SV_SOURCES := \
  $(RTL_DIR)/pkg/ceres_param.sv \
  $(wildcard $(RTL_DIR)/core/*.sv) \
  $(wildcard $(RTL_DIR)/core/bus/*.sv) \
  $(wildcard $(RTL_DIR)/core/pmp_pma/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage01_fetch/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage02_decode/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage03_execute/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage03_execute/mul_div/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage03_execute/mul_div/wallace8x8/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage03_execute/mul_div/wallace32x32/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage04_memory/*.sv) \
  $(wildcard $(RTL_DIR)/core/stage05_writeback/*.sv) \
  $(wildcard $(RTL_DIR)/core/mmu/*.sv) \
  $(wildcard $(RTL_DIR)/util/*.sv) \
  $(wildcard $(RTL_DIR)/periph/gpio/*.sv) \
  $(wildcard $(RTL_DIR)/periph/plic/*.sv) \
  $(wildcard $(RTL_DIR)/periph/timer/*.sv) \
  $(wildcard $(RTL_DIR)/periph/wdt/*.sv) \
  $(wildcard $(RTL_DIR)/periph/dma/*.sv) \
  $(wildcard $(RTL_DIR)/periph/pwm/*.sv) \
  $(wildcard $(RTL_DIR)/periph/vga/*.sv) \
  $(wildcard $(RTL_DIR)/periph/i2c/*.sv) \
  $(wildcard $(RTL_DIR)/periph/spi/*.sv) \
  $(wildcard $(RTL_DIR)/periph/uart/*.sv) \
  $(wildcard $(RTL_DIR)/ram/*.sv) \
  $(wildcard $(RTL_DIR)/wrapper/*.sv) \
  $(wildcard $(RTL_DIR)/wrapper/*.v)
