# =========================================
# CERES RISC-V — Test Type Configuration
# =========================================
# Merkezi TEST_TYPE → dizin/uzantı eşleme tablosu.
# Yeni bir test tipi eklemek için sadece bu tablolara satır ekleyin.
# =========================================

# -----------------------------------------
# 1. TEST_TYPE → TEST_ROOT Eşleme Tablosu
# -----------------------------------------
# Format: TEST_TYPE_<type>_ROOT := <path>
# Kullanım: $(call GET_TEST_ROOT,$(TEST_TYPE)) → ilgili dizin

TEST_TYPE_isa_ROOT       := $(BUILD_DIR)/tests/riscv-tests
TEST_TYPE_arch_ROOT      := $(BUILD_DIR)/tests/riscv-arch-test
TEST_TYPE_imperas_ROOT   := $(BUILD_DIR)/tests/imperas
TEST_TYPE_bench_ROOT     := $(BUILD_DIR)/tests/riscv-benchmarks
TEST_TYPE_dhrystone_ROOT := $(BUILD_DIR)/tests/dhrystone
TEST_TYPE_embench_ROOT   := $(BUILD_DIR)/tests/embench
TEST_TYPE_torture_ROOT   := $(BUILD_DIR)/tests/torture
TEST_TYPE_riscv-dv_ROOT  := $(BUILD_DIR)/tests/riscv-dv
TEST_TYPE_custom_ROOT    := $(BUILD_DIR)/tests/custom
TEST_TYPE_coremark_ROOT  := $(BUILD_DIR)/tests/coremark

# Geçerli test tipleri listesi
VALID_TEST_TYPES := isa arch imperas bench dhrystone embench torture riscv-dv custom coremark

# -----------------------------------------
# 2. TEST_TYPE → ELF Uzantısı Eşlemesi
# -----------------------------------------
# Bazı test suiteleri .elf uzantısı kullanır, bazıları kullanmaz
# Format: TEST_TYPE_<type>_ELF_EXT := .elf veya boş

TEST_TYPE_isa_ELF_EXT       :=
TEST_TYPE_arch_ELF_EXT      := .elf
TEST_TYPE_imperas_ELF_EXT   := .elf
TEST_TYPE_bench_ELF_EXT     :=
TEST_TYPE_dhrystone_ELF_EXT := .elf
TEST_TYPE_embench_ELF_EXT   := .elf
TEST_TYPE_torture_ELF_EXT   := .elf
TEST_TYPE_riscv-dv_ELF_EXT  := .elf
TEST_TYPE_custom_ELF_EXT    := .elf
TEST_TYPE_coremark_ELF_EXT  := .elf

# -----------------------------------------
# 3. Helper Fonksiyonlar
# -----------------------------------------

# TEST_TYPE'dan TEST_ROOT al
# Kullanım: $(call GET_TEST_ROOT,isa) → .../riscv-tests
define GET_TEST_ROOT
$(or $(TEST_TYPE_$(1)_ROOT),$(error Unknown TEST_TYPE: $(1). Valid types: $(VALID_TEST_TYPES)))
endef

# TEST_TYPE'dan ELF uzantısı al
# Kullanım: $(call GET_ELF_EXT,arch) → .elf
define GET_ELF_EXT
$(TEST_TYPE_$(1)_ELF_EXT)
endef

# -----------------------------------------
# 4. Değişkenleri Ayarla (run_test.mk yerine)
# -----------------------------------------
# Eğer TEST_TYPE geçerli ise, TEST_ROOT ve ELF_EXT'i ayarla

ifneq ($(filter $(TEST_TYPE),$(VALID_TEST_TYPES)),)
  # Geçerli test tipi
  TEST_ROOT ?= $(call GET_TEST_ROOT,$(TEST_TYPE))
  ELF_EXT   ?= $(call GET_ELF_EXT,$(TEST_TYPE))
else ifneq ($(MEM_DIR),)
  # MEM_DIR verilmişse, custom path kullan
  TEST_ROOT ?= $(dir $(MEM_DIR))
  ELF_EXT   ?=
else ifneq ($(TEST_TYPE),)
  $(warning Unknown TEST_TYPE="$(TEST_TYPE)". Valid: $(VALID_TEST_TYPES))
endif

# -----------------------------------------
# 5. Derived Paths (ortak kullanım için)
# -----------------------------------------
# Bu değişkenler run_test.mk'de override edilebilir

ELF_DIR  ?= $(TEST_ROOT)/elf
MEM_DIR  ?= $(TEST_ROOT)/mem
HEX_DIR  ?= $(TEST_ROOT)/hex
DUMP_DIR ?= $(TEST_ROOT)/dump
ADDR_DIR ?= $(TEST_ROOT)/pass_fail_addr

# ELF dosya yolu
ELF_FILE ?= $(ELF_DIR)/$(TEST_NAME)$(ELF_EXT)

# -----------------------------------------
# 6. Pattern-Based TEST_TYPE Detection
# -----------------------------------------
# Eğer TEST_TYPE belirtilmemişse, TEST_NAME'den otomatik tespit et
#
# Patterns:
#   rv32*-p-*, rv64*-p-*  → isa
#   *-01, *-02, ...       → arch  
#   I-*, M-*, A-*, C-*    → imperas (ama -01 ile bitiyorsa arch)
#   median, dhrystone...  → bench

# Test tipi detection fonksiyonu (Makefile pattern matching)
# Bu fonksiyon config.mk'de zaten var, buradan çağırılır
# TEST_TYPE ?= ... (config.mk'de ayarlanır)

