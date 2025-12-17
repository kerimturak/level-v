# CoreMark Makefile for RISC-V Spike + pk

# Compiler
CC = riscv32-unknown-elf-gcc
LD = riscv32-unknown-elf-gcc

# Flags
PORT_CFLAGS = -O2 -march=rv32imc -mabi=ilp32 -static
FLAGS_STR = "$(PORT_CFLAGS) $(XCFLAGS) $(XLFLAGS) $(LFLAGS_END)"
CFLAGS = $(PORT_CFLAGS) -I$(PORT_DIR) -I. -DFLAGS_STR=\"$(FLAGS_STR)\"

# Linker flags
LFLAGS = -static -march=rv32imc -mabi=ilp32
LFLAGS_END = -lm

# Output flags
OUTFLAG = -o
OFLAG = -o
OBJOUT = -o
COUT = -c

# Port sources
PORT_SRCS = $(PORT_DIR)/core_portme.c
vpath %.c $(PORT_DIR)
vpath %.h $(PORT_DIR)
vpath %.mak $(PORT_DIR)

# Extra dependencies
EXTRA_DEPENDS += $(PORT_DIR)/core_portme.mak

# Object file extension
OEXT = .o
EXE = .exe

# Separate compilation
SEPARATE_COMPILE = 1
PORT_OBJS = $(PORT_DIR)/core_portme$(OEXT)
PORT_CLEAN = *$(OEXT) $(PORT_DIR)/*$(OEXT)

# Compilation rules
$(OPATH)%$(OEXT) : %.c
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

$(OPATH)$(PORT_DIR)/%$(OEXT) : $(PORT_DIR)/%.c
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

# Load and run commands
LOAD = echo "Ready to run on Spike"
RUN =

# Empty targets
.PHONY: port_prebuild port_postbuild port_prerun port_postrun port_preload port_postload
port_prebuild:
port_postbuild:
port_prerun:
port_postrun:
port_preload:
port_postload:

# Path settings
OPATH = ./
MKDIR = mkdir -p
