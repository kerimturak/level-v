# Makefile for RISC-V binary file operations and cache-line formatting
# Supports .bin, .hex, .mem, .dump, .riscv (ELF) files

# Default parameters
INPUT ?= coremark.hex
OUTPUT ?= $(basename $(INPUT))_cacheline.mem
CACHELINE_BYTES ?= 64
FILE ?= coremark

# Calculate words per cache line (each word is 4 bytes = 32 bits)
WORDS_PER_LINE = $(shell echo $$(($(CACHELINE_BYTES) / 4)))

# Tools
OBJDUMP ?= riscv32-unknown-elf-objdump
OBJCOPY ?= riscv32-unknown-elf-objcopy
READELF ?= riscv32-unknown-elf-readelf

.PHONY: help convert info info-all clean clean-all list-cacheline

# Default target
all: help

help:
	@echo "==============================================="
	@echo "RISC-V Binary File Operations Makefile"
	@echo "==============================================="
	@echo ""
	@echo "=== Cache Line Conversion ==="
	@echo "  make convert [INPUT=<file>] [OUTPUT=<file>] [CACHELINE_BYTES=<bytes>]"
	@echo "    Convert hex/mem file to cache-line format"
	@echo ""
	@echo "  Examples:"
	@echo "    make convert INPUT=coremark.hex CACHELINE_BYTES=64"
	@echo "    make convert INPUT=test.mem OUTPUT=test_128.mem CACHELINE_BYTES=128"
	@echo ""
	@echo "  Common cache line sizes:"
	@echo "    32 bytes  = 8 words/line    64 bytes  = 16 words/line"
	@echo "    128 bytes = 32 words/line   256 bytes = 64 words/line"
	@echo ""
	@echo "=== File Information ==="
	@echo "  make info FILE=<basename>    - Show info about a file (auto-detect type)"
	@echo "  make info-hex FILE=<file>    - Info about .hex file"
	@echo "  make info-mem FILE=<file>    - Info about .mem file"
	@echo "  make info-bin FILE=<file>    - Info about .bin file"
	@echo "  make info-dump FILE=<file>   - Show .dump file contents"
	@echo "  make info-elf FILE=<file>    - Info about .riscv (ELF) file"
	@echo "  make info-all FILE=<base>    - Show all available info for basename"
	@echo ""
	@echo "  Examples:"
	@echo "    make info FILE=coremark"
	@echo "    make info-hex FILE=coremark.hex"
	@echo "    make info-all FILE=coremark"
	@echo ""
	@echo "=== Binary Conversions ==="
	@echo "  make elf2hex FILE=<file.riscv>   - Convert ELF to .hex"
	@echo "  make elf2bin FILE=<file.riscv>   - Convert ELF to .bin"
	@echo "  make elf2dump FILE=<file.riscv>  - Create disassembly .dump"
	@echo "  make elf2all FILE=<file.riscv>   - Generate all formats from ELF"
	@echo ""
	@echo "=== Analysis Commands ==="
	@echo "  make analyze-hex FILE=<file>     - Analyze hex file statistics"
	@echo "  make compare-sizes FILE=<base>   - Compare file sizes"
	@echo "  make list-cacheline              - List all cache-line mem files"
	@echo ""
	@echo "=== Cleanup ==="
	@echo "  make clean      - Remove generated cache-line mem files"
	@echo "  make clean-all  - Remove all generated files"
	@echo ""

# ============================================
# Cache Line Conversion
# ============================================

convert:
	@echo "Converting $(INPUT) to cache-line format..."
	@echo "Cache line size: $(CACHELINE_BYTES) bytes ($(WORDS_PER_LINE) words per line)"
	@python3 convert_cacheline.py $(INPUT) $(OUTPUT) $(WORDS_PER_LINE)
	@echo "✓ Output written to: $(OUTPUT)"

# ============================================
# File Information Commands
# ============================================

info:
	@echo "=== File Information for: $(FILE) ==="
	@echo ""
	@if [ -f "$(FILE).riscv" ]; then \
		$(MAKE) --no-print-directory info-elf FILE=$(FILE).riscv; \
	fi
	@if [ -f "$(FILE).hex" ]; then \
		$(MAKE) --no-print-directory info-hex FILE=$(FILE).hex; \
	fi
	@if [ -f "$(FILE).bin" ]; then \
		$(MAKE) --no-print-directory info-bin FILE=$(FILE).bin; \
	fi
	@if [ -f "$(FILE).dump" ]; then \
		echo ""; echo "=== Disassembly (.dump) ==="; \
		echo "Lines: $$(wc -l < $(FILE).dump)"; \
		echo "Size:  $$(du -h $(FILE).dump | cut -f1)"; \
	fi

info-all:
	@$(MAKE) --no-print-directory info FILE=$(FILE)
	@echo ""
	@echo "=== Available Files ==="
	@ls -lh $(FILE).* 2>/dev/null || echo "No files found for $(FILE)"

info-hex:
	@echo "=== HEX File Info: $(FILE) ==="
	@if [ ! -f "$(FILE)" ]; then echo "Error: File not found!"; exit 1; fi
	@echo "Total words:  $$(grep -v '^#' $(FILE) | grep -v '^//' | grep -c .)"
	@echo "File size:    $$(du -h $(FILE) | cut -f1)"
	@echo "Format:       32-bit words (8 hex chars per line)"
	@echo ""
	@echo "First 5 words:"
	@head -5 $(FILE)
	@echo "..."
	@echo "Last 5 words:"
	@tail -5 $(FILE)

info-mem:
	@echo "=== MEM File Info: $(FILE) ==="
	@if [ ! -f "$(FILE)" ]; then echo "Error: File not found!"; exit 1; fi
	@echo "Total lines:     $$(wc -l < $(FILE))"
	@echo "File size:       $$(du -h $(FILE) | cut -f1)"
	@CHARS=$$(head -1 $(FILE) | wc -c); \
	BYTES=$$(($$CHARS - 1)); \
	echo "Chars per line:  $$CHARS"; \
	echo "Hex bytes/line:  $$(($$BYTES / 2))"; \
	echo "Words per line:  $$(($$BYTES / 8))"
	@echo ""
	@echo "First 3 lines:"
	@head -3 $(FILE)
	@echo "..."
	@echo "Last 2 lines:"
	@tail -2 $(FILE)

info-bin:
	@echo "=== BIN File Info: $(FILE) ==="
	@if [ ! -f "$(FILE)" ]; then echo "Error: File not found!"; exit 1; fi
	@echo "File size:    $$(du -h $(FILE) | cut -f1) ($$(stat -c%s $(FILE)) bytes)"
	@echo "File type:    $$(file -b $(FILE))"
	@echo ""
	@echo "First 64 bytes (hex):"
	@hexdump -C $(FILE) | head -5

info-dump:
	@echo "=== Disassembly File: $(FILE) ==="
	@if [ ! -f "$(FILE)" ]; then echo "Error: File not found!"; exit 1; fi
	@echo "Total lines:  $$(wc -l < $(FILE))"
	@echo "File size:    $$(du -h $(FILE) | cut -f1)"
	@echo ""
	@echo "First 20 lines:"
	@head -20 $(FILE)

info-elf:
	@echo "=== ELF File Info: $(FILE) ==="
	@if [ ! -f "$(FILE)" ]; then echo "Error: File not found!"; exit 1; fi
	@echo "File size:    $$(du -h $(FILE) | cut -f1) ($$(stat -c%s $(FILE)) bytes)"
	@echo "File type:    $$(file -b $(FILE))"
	@echo ""
	@if command -v $(READELF) >/dev/null 2>&1; then \
		echo "=== ELF Header ==="; \
		$(READELF) -h $(FILE) | grep -E "(Class|Machine|Entry point|Start of)"; \
		echo ""; \
		echo "=== Section Headers ==="; \
		$(READELF) -S $(FILE) | grep -E "(Name|\.text|\.data|\.bss|\.rodata)"; \
		echo ""; \
		echo "=== Program Headers ==="; \
		$(READELF) -l $(FILE) | head -15; \
	else \
		echo "Note: $(READELF) not found. Install riscv-gnu-toolchain for detailed info."; \
		file $(FILE); \
	fi

# ============================================
# Binary Conversion Commands
# ============================================

elf2hex:
	@echo "Converting ELF to HEX: $(FILE) -> $(basename $(FILE)).hex"
	@if [ ! -f "$(FILE)" ]; then echo "Error: File not found!"; exit 1; fi
	@if ! command -v $(OBJCOPY) >/dev/null 2>&1; then \
		echo "Error: $(OBJCOPY) not found. Install riscv-gnu-toolchain."; \
		exit 1; \
	fi
	@$(OBJCOPY) -O verilog $(FILE) $(basename $(FILE)).hex
	@echo "✓ Created: $(basename $(FILE)).hex"

elf2bin:
	@echo "Converting ELF to BIN: $(FILE) -> $(basename $(FILE)).bin"
	@if [ ! -f "$(FILE)" ]; then echo "Error: File not found!"; exit 1; fi
	@if ! command -v $(OBJCOPY) >/dev/null 2>&1; then \
		echo "Error: $(OBJCOPY) not found. Install riscv-gnu-toolchain."; \
		exit 1; \
	fi
	@$(OBJCOPY) -O binary $(FILE) $(basename $(FILE)).bin
	@echo "✓ Created: $(basename $(FILE)).bin"

elf2dump:
	@echo "Creating disassembly: $(FILE) -> $(basename $(FILE)).dump"
	@if [ ! -f "$(FILE)" ]; then echo "Error: File not found!"; exit 1; fi
	@if ! command -v $(OBJDUMP) >/dev/null 2>&1; then \
		echo "Error: $(OBJDUMP) not found. Install riscv-gnu-toolchain."; \
		exit 1; \
	fi
	@$(OBJDUMP) -D $(FILE) > $(basename $(FILE)).dump
	@echo "✓ Created: $(basename $(FILE)).dump"

elf2all:
	@echo "Generating all formats from: $(FILE)"
	@$(MAKE) --no-print-directory elf2hex FILE=$(FILE)
	@$(MAKE) --no-print-directory elf2bin FILE=$(FILE)
	@$(MAKE) --no-print-directory elf2dump FILE=$(FILE)
	@echo ""
	@echo "✓ All formats generated:"
	@ls -lh $(basename $(FILE)).{hex,bin,dump}

# ============================================
# Analysis Commands
# ============================================

analyze-hex:
	@echo "=== Analyzing HEX file: $(FILE) ==="
	@python3 -c "import sys; data = [l.strip() for l in open('$(FILE)') if l.strip() and not l.startswith('#')]; print(f'Total instructions/data: {len(data)}'); print(f'Memory range: 0x0 - 0x{len(data)*4:X} ({len(data)*4} bytes)'); print(f'Unique values: {len(set(data))}'); zeros = sum(1 for x in data if x == '00000000'); print(f'Zero words: {zeros} ({zeros*100//len(data)}%)')"

compare-sizes:
	@echo "=== File Size Comparison for $(FILE) ==="
	@for ext in riscv bin hex dump; do \
		if [ -f "$(FILE).$$ext" ]; then \
			size=$$(du -h $(FILE).$$ext | cut -f1); \
			bytes=$$(stat -c%s $(FILE).$$ext 2>/dev/null || echo "?"); \
			printf "  %-15s %6s  (%s bytes)\n" "$(FILE).$$ext" "$$size" "$$bytes"; \
		fi; \
	done

list-cacheline:
	@echo "=== Available Cache-line MEM Files ==="
	@if ls *_cacheline.mem 1> /dev/null 2>&1; then \
		for file in *_cacheline.mem; do \
			lines=$$(wc -l < $$file); \
			chars=$$(head -1 $$file | wc -c); \
			words=$$((($$chars - 1) / 8)); \
			bytes=$$(($$words * 4)); \
			size=$$(du -h $$file | cut -f1); \
			printf "  %-30s  %4d lines x %2d words = %3d bytes/line  (Total: %s)\n" \
				"$$file" "$$lines" "$$words" "$$bytes" "$$size"; \
		done; \
	else \
		echo "  No cache-line mem files found."; \
		echo "  Run 'make convert' to create one."; \
	fi

# ============================================
# Cleanup
# ============================================

clean:
	@rm -f *_cacheline.mem
	@echo "✓ Cleaned up cache-line mem files"

clean-all:
	@echo "Warning: This will remove all generated files (.hex, .bin, .dump, *_cacheline.mem)"
	@echo "Press Ctrl+C to cancel, or Enter to continue..."
	@read dummy
	@rm -f *.hex *.bin *.dump *_cacheline.mem
	@echo "✓ Cleaned up all generated files"
