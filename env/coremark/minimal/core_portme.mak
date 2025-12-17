# Minimal RISC-V CoreMark Port Makefile
# No UART, CSR-based timing, minimal dependencies

# Compiler
CC = riscv32-unknown-elf-gcc
LD = riscv32-unknown-elf-gcc
OBJDUMP = riscv32-unknown-elf-objdump
OBJCOPY = riscv32-unknown-elf-objcopy

# Architecture
ARCH = rv32imc_zicsr
ABI = ilp32

# Flags
PORT_CFLAGS = -O2 -march=$(ARCH) -mabi=$(ABI) -static
PORT_CFLAGS += -nostdlib -nostartfiles
PORT_CFLAGS += -fno-common -ffunction-sections -fdata-sections
PORT_CFLAGS += -DHAS_PRINTF=0 -DHAS_STDIO=0 -DPERFORMANCE_RUN=1
PORT_CFLAGS += -Dee_printf='while(0)' '-DMEM_LOCATION="STACK"'

FLAGS_STR = "$(PORT_CFLAGS) $(XCFLAGS) $(XLFLAGS) $(LFLAGS_END)"
CFLAGS = $(PORT_CFLAGS) -I$(PORT_DIR) -I. -DFLAGS_STR=\"$(FLAGS_STR)\"

# Linker flags
LFLAGS = -march=$(ARCH) -mabi=$(ABI) -static -nostdlib -nostartfiles
LFLAGS += -Wl,--gc-sections
LFLAGS_END = -T$(PORT_DIR)/link.ld

# Output flags
OUTFLAG = -o
OFLAG = -o
OBJOUT = -o
COUT = -c

# Port sources
PORT_SRCS = $(PORT_DIR)/core_portme.c $(PORT_DIR)/start.S
vpath %.c $(PORT_DIR)
vpath %.S $(PORT_DIR)
vpath %.h $(PORT_DIR)
vpath %.mak $(PORT_DIR)

# Extra dependencies
EXTRA_DEPENDS += $(PORT_DIR)/core_portme.mak $(PORT_DIR)/link.ld

# Object file extension
OEXT = .o
EXE =

# Separate compilation
SEPARATE_COMPILE = 1
PORT_OBJS = $(OPATH)$(PORT_DIR)/core_portme$(OEXT) $(OPATH)$(PORT_DIR)/start$(OEXT)
PORT_CLEAN = *$(OEXT) $(PORT_DIR)/*$(OEXT) *.bin *.dump *.hex *.mem

# XCFLAGS are overridden by CoreMark Makefile, so definitions are in PORT_CFLAGS above

# Compilation rules
$(OPATH)%$(OEXT) : %.c
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

$(OPATH)$(PORT_DIR)/%$(OEXT) : $(PORT_DIR)/%.c
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

$(OPATH)$(PORT_DIR)/%$(OEXT) : $(PORT_DIR)/%.S
	$(CC) $(PORT_CFLAGS) $(COUT) $< $(OBJOUT) $@

# Load and run commands
LOAD = echo "Binary ready: $(OUTFILE)"
RUN = echo "Cannot run RV32 binary on host - skipping"

# Port hooks
.PHONY: port_prebuild port_postbuild port_prerun port_postrun port_preload port_postload
port_prebuild:
port_postbuild:
	@$(OBJCOPY) -O binary $(OUTFILE) $(OUTFILE).bin
	@$(OBJDUMP) -d $(OUTFILE) > $(OUTFILE).dump
	@echo "Created: $(OUTFILE).bin and $(OUTFILE).dump"
port_prerun:
port_postrun:
port_preload:
port_postload:

# Path settings
OPATH = ./
MKDIR = mkdir -p
