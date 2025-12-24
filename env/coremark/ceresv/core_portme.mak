# Copyright 2018 Embedded Microprocessor Benchmark Consortium (EEMBC)
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# 
# Original Author: Shay Gal-on
# Modified for Ceres-V RV32IMC_Zicsr processor

#File : core_portme.mak

# RISC-V Toolchain
RISCV_PREFIX ?= riscv32-unknown-elf-

# Flag : OUTFLAG
#	Use this flag to define how to to get an executable (e.g -o)
OUTFLAG= -o

# Flag : CC
#	Use this flag to define compiler to use
CC 		= $(RISCV_PREFIX)gcc

# Flag : LD
#	Use this flag to define linker to use
LD		= $(RISCV_PREFIX)gcc

# Flag : AS
#	Use this flag to define assembler to use
AS		= $(RISCV_PREFIX)as

# Additional tools for output generation
OBJCOPY = $(RISCV_PREFIX)objcopy
OBJDUMP = $(RISCV_PREFIX)objdump
SIZE    = $(RISCV_PREFIX)size

# Architecture flags for Ceres-V RV32IMC_Zicsr
ARCH_FLAGS = -march=rv32imc_zicsr -mabi=ilp32

# Linker script location
LINKER_SCRIPT = $(PORT_DIR)/link.ld

# Flag : CFLAGS
#	Use this flag to define compiler options.
PORT_CFLAGS = -O2 -g $(ARCH_FLAGS) -fno-builtin -fno-common -nostdlib -nostartfiles
FLAGS_STR = "$(PORT_CFLAGS) $(XCFLAGS) $(XLFLAGS) $(LFLAGS_END)"
CFLAGS = $(PORT_CFLAGS) -I$(PORT_DIR) -I. -DFLAGS_STR=\"$(FLAGS_STR)\" 

# Flag : LFLAGS_END
#	Define any libraries needed for linking or other flags that should come at the end of the link line
LFLAGS_END = -lm -lgcc

# Flag : SEPARATE_COMPILE
SEPARATE_COMPILE=1

# Flag : SEPARATE_COMPILE
# You must also define below how to create an object file, and how to link.
OBJOUT 	= -o
LFLAGS 	= $(ARCH_FLAGS) -T$(LINKER_SCRIPT) -nostdlib -nostartfiles
ASFLAGS = $(ARCH_FLAGS)
OFLAG 	= -o
COUT 	= -c

# Flag : PORT_SRCS
# 	Port specific source files can be added here
#	You may also need cvt.c if the fcvt functions are not provided as intrinsics by your compiler!
PORT_SRCS = $(PORT_DIR)/core_portme.c $(PORT_DIR)/ee_printf.c $(PORT_DIR)/cvt.c $(PORT_DIR)/crt0.S
PORT_OBJS = $(OPATH)$(PORT_DIR)/core_portme$(OEXT) $(OPATH)$(PORT_DIR)/ee_printf$(OEXT) $(OPATH)$(PORT_DIR)/cvt$(OEXT) $(OPATH)$(PORT_DIR)/crt0$(OEXT)
vpath %.c $(PORT_DIR)
vpath %.S $(PORT_DIR)

# Flag : LOAD
#	For a simple port, we assume self hosted compile and run, no load needed.

# Flag : RUN
#	For a simple port, we assume self hosted compile and run, simple invocation of the executable

LOAD = echo "Load to Ceres-V via JTAG or simulation"
RUN = echo "Run on Ceres-V simulation or hardware"

OEXT = .o
EXE = .elf

# Object file rule for C files in PORT_DIR
$(OPATH)$(PORT_DIR)/%$(OEXT) : %.c
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

# Object file rule for C files
$(OPATH)%$(OEXT) : %.c
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

# Object file rule for assembly files in PORT_DIR
$(OPATH)$(PORT_DIR)/%$(OEXT) : %.S
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

# Target : port_pre% and port_post%
# For the purpose of this simple port, no pre or post steps needed.

.PHONY : port_prebuild port_postbuild port_prerun port_postrun port_preload port_postload

port_prebuild:

port_postbuild: $(OUTFILE)
	@echo "Generating output files for Ceres-V..."
	$(SIZE) $(OUTFILE)
	$(OBJDUMP) -D $(OUTFILE) > $(OUTFILE:.elf=.dump)
	$(OBJCOPY) --set-section-flags .bss=alloc,load,contents -O binary $(OUTFILE) $(OUTFILE:.elf=.bin)
	$(OBJCOPY) -O ihex $(OUTFILE) $(OUTFILE:.elf=.hex)
	@echo "Generating .mem file for simulation..."
	$(OBJCOPY) -O verilog $(OUTFILE) $(OUTFILE:.elf=.mem)
	@echo ""
	@echo "Output files generated:"
	@echo "  $(OUTFILE)           - ELF executable"
	@echo "  $(OUTFILE:.elf=.dump) - Disassembly"
	@echo "  $(OUTFILE:.elf=.bin)  - Binary (BSS included)"
	@echo "  $(OUTFILE:.elf=.hex)  - Intel HEX"
	@echo "  $(OUTFILE:.elf=.mem)  - Verilog memory file"

port_prerun:

port_postrun:

port_preload:

port_postload:

# FLAG : OPATH
# Path to the output folder. Default - current folder.
OPATH = ./
MKDIR = mkdir -p
