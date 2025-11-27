# RISC-V toolchain örnek yolları:
#   /opt/riscv/bin/riscv64-unknown-elf-
#   /home/kerim/rv32i/bin/riscv32-unknown-elf-
#
# Ana Makefile genelde CC'yi dışarıdan ayarlıyor:
#   örn:  make PORT_DIR=barebones CC=/home/kerim/rv32i/bin/riscv32-unknown-elf-gcc

# Flag : OUTFLAG
#   Use this flag to define how to get an executable (e.g -o)
OUTFLAG = -o

# ------------------------------------------------------------------------------
# Derleme bayrakları
# ------------------------------------------------------------------------------

# PORT_CFLAGS:
#   - Sadece platforma özgü derleyici bayrakları
#   - Linker script veya kütüphane bağlantılarını buraya koyma!
PORT_CFLAGS = \
  -O2 \
  -mcmodel=medany \
  -std=gnu99 \
  -fno-common \
  -fno-builtin \
  -ffunction-sections

# FLAGS_STR:
#   Çalışma sırasında raporlanmak üzere derleme/link bayraklarını string olarak tutar
FLAGS_STR = "$(PORT_CFLAGS) $(XCFLAGS) $(XLFLAGS) $(LFLAGS_END)"

# CFLAGS:
#   Genel derleme bayrakları (ISA, ABI, include path vs.)
CFLAGS = $(PORT_CFLAGS) \
         -march=rv32imc_zicsr \
         -mabi=ilp32 \
         -I$(PORT_DIR) \
         -I. \
         -DFLAGS_STR=\"$(FLAGS_STR)\"
# -DCORE_DEBUG gibi ek tanımlar istersen buraya ekleyebilirsin

# ------------------------------------------------------------------------------
# Linker bayrakları
# ------------------------------------------------------------------------------

# LFLAGS_END:
#   Link komutunun SONUNA eklenecek bayraklar (linker script ve kütüphaneler)
#   Bare-metal:
#     - nostartfiles / nostdlib: kendi crt.S ve syscalls.c kullanıyoruz
#     - static: tam statik link
#     - T link.ld: linker script
#     -lm -lgcc: libm + libgcc (riscv-unknown-elf toolchain içindeki)
LFLAGS_END += \
  -nostdlib \
  -nostartfiles \
  -static \
  -T $(PORT_DIR)/link.ld \
  -lm \
  -lgcc

# ------------------------------------------------------------------------------
# Port'a özgü kaynak dosyalar
# ------------------------------------------------------------------------------

# Flag: PORT_SRCS
#   Port-specific source files
PORT_SRCS = \
  $(PORT_DIR)/ceres.h \
  $(PORT_DIR)/core_portme.c \
  $(PORT_DIR)/ee_printf.c \
  $(PORT_DIR)/crt.S 
# Flag: ITERATIONS
#   CoreMark iş yükünün en az 10 saniye koşmasını sağlayacak iteration sayısı.
#   Örnek: ~4 CoreMark/MHz @ 50MHz:
#     4 * 50 * 10 = 2000
ITERATIONS = 2000

# ------------------------------------------------------------------------------
# Yükleme / Çalıştırma (LOAD / RUN)
# ------------------------------------------------------------------------------

# Flag: LOAD
#   Cross-compile ortamında hedefe kopyalama / flash etme komutu
LOAD = echo Loading done

# Flag: RUN
#   Cross ortamda hedefte çalıştırma komutu.
#   Örneğin spike ile çalıştırmak istersen:
#   RUN = spike --isa=RV32IMC $(EXE)
# Şimdilik boş bırakıyoruz; üst Makefile doğrudan .exe'yi çalıştırabilir.
# RUN =

# ------------------------------------------------------------------------------
# Çıktı isimleri
# ------------------------------------------------------------------------------

OEXT = .o
EXE  = _baremetal.riscv

# ------------------------------------------------------------------------------
# SEPARATE_COMPILE (isteğe bağlı)
#   Derleme ve link aşamalarını ayırmak istersen SEPARATE_COMPILE tanımlanır.
# ------------------------------------------------------------------------------

ifdef SEPARATE_COMPILE

LD      = $(CC)
OBJOUT  = -o
LFLAGS  =
OFLAG   = -o
COUT    = -c

# Flag: PORT_OBJS
#   Port-specific object files
PORT_OBJS  = \
  $(PORT_DIR)/core_portme$(OEXT) \
  $(PORT_DIR)/ee_printf$(OEXT) \
  $(PORT_DIR)/crt$(OEXT) \
  $(PORT_DIR)/syscalls$(OEXT)

PORT_CLEAN = *$(OEXT)

$(OPATH)%$(OEXT) : %.c
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

endif

# ------------------------------------------------------------------------------
# PGO (Profil guidance) – isteğe bağlı
# ------------------------------------------------------------------------------

ifdef PGO
 ifeq (,$(findstring $(PGO),gen))
  PGO_STAGE = build_pgo_gcc
  CFLAGS   += -fprofile-use
 endif
 PORT_CLEAN += *.gcda *.gcno gmon.out
endif

.PHONY: port_prebuild
port_prebuild: $(PGO_STAGE)

.PHONY: build_pgo_gcc
build_pgo_gcc:
	$(MAKE) PGO=gen XCFLAGS="$(XCFLAGS) -fprofile-generate -DTOTAL_DATA_SIZE=1200" ITERATIONS=10 gen_pgo_data REBUILD=1

# ------------------------------------------------------------------------------
# Post / Pre hook hedefleri (şu an boş)
# ------------------------------------------------------------------------------

.PHONY: port_postbuild
port_postbuild:

.PHONY: port_postrun
port_postrun:

.PHONY: port_prerun
port_prerun:

.PHONY: port_postload
port_postload:

.PHONY: port_preload
port_preload:

# ------------------------------------------------------------------------------
# Diğer yardımcı ayarlar
# ------------------------------------------------------------------------------

# FLAG: OPATH
#   Derlenmiş objelerin çıkacağı klasör. Varsayılan: mevcut klasör
OPATH = ./

MKDIR = mkdir -p

# FLAG: PERL
#   Geometric mean hesaplamak için (ayrı çalıştırma modunda)
PERL = /usr/bin/perl
