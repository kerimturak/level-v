# Python Scripts - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Converter Scripts](#converter-scripts)
3. [Generator Scripts](#generator-scripts)
4. [Analysis Scripts](#analysis-scripts)
5. [Makefile Helpers](#makefile-helpers)

---

## Genel Bakış

### Dizin Yapısı

```
script/python/
├── requirements.txt        # Python bağımlılıkları
├── requirements-dev.txt    # Geliştirme bağımlılıkları
│
├── elf_to_mem.py          # ELF/binary → .mem converter
├── gen_linker.py          # Linker script generator
├── hex2mem_32to128.py     # HEX format converter
├── get_static_hex.py      # Static hex extractor
├── convert_dump_to_elf_hex.py  # Dump converter
│
├── torture_gen.py         # Torture test generator
├── simple_torture_gen.py  # Basit torture generator
├── multiply.py            # Multiplier test generator
├── riscv_dv_gen.py        # RISCV-DV generator
├── riscv_dv_config.py     # RISCV-DV konfigürasyon
│
├── compare_bp_stats.py    # Branch predictor analizi
├── slang_lint.py          # Slang linter wrapper
├── download_pdfs.py       # PDF downloader utility
│
├── fpga/                  # FPGA araçları
│
├── makefile/              # Makefile için Python helpers
│   ├── isa_pipeline.py    # ISA test import pipeline
│   ├── arch_pipeline.py   # Arch test import pipeline
│   ├── elf_to_mem.py      # ELF → MEM converter
│   ├── hex_to_mem.py      # HEX → MEM converter
│   ├── compare_logs.py    # Log karşılaştırma
│   ├── generate_test_dashboard.py  # Test dashboard
│   └── html_diff_generator.py      # HTML diff
│
└── tests/                 # Python test scriptleri
```

### Bağımlılıklar

```txt
# requirements.txt
pyyaml>=6.0          # YAML parsing
pyelftools>=0.29     # ELF file parsing
```

```txt
# requirements-dev.txt
pyslang>=4.0         # SystemVerilog linting
pytest>=7.0          # Unit testing
black>=23.0          # Code formatting
```

---

## Converter Scripts

### elf_to_mem.py - ELF/Binary Converter

**Dosya:** `script/python/elf_to_mem.py`

#### Amaç

ELF veya binary dosyalarını `.mem` formatına çevirir. RAM initialization için `$readmemh` ile uyumlu hex lines üretir.

#### Kullanım

```bash
# Binary → .mem
riscv32-unknown-elf-objcopy -O binary test.elf test.bin
python3 elf_to_mem.py --in test.bin --out test.mem --addr 0x80000000

# Full options
python3 elf_to_mem.py \
    --in test.bin \
    --out test.mem \
    --addr 0x80000000 \
    --block-bytes 16 \
    --word-size 4 \
    --word-endian little \
    --word-order high-to-low
```

#### Parametreler

| Parametre | Default | Açıklama |
|-----------|---------|----------|
| `--in` | (required) | Input binary dosyası |
| `--out` | (required) | Output .mem dosyası |
| `--addr` | 0x80000000 | Base address (informational) |
| `--block-bytes` | 16 | Bytes per .mem line (128-bit block) |
| `--word-size` | 4 | Word size in bytes |
| `--word-endian` | little | Byte order in word (little/big) |
| `--word-order` | high-to-low | Word print order in block |
| `--pad` | 0x00 | Pad byte value |

#### Çıktı Formatı

```
# Input: 16 bytes = 4 words (32-bit each)
# Word 0: 0x12345678, Word 1: 0xABCDEF00, Word 2: 0x11223344, Word 3: 0x55667788

# high-to-low order (default):
5566778811223344abcdef0012345678

# low-to-high order:
12345678abcdef00112233445566778
```

#### Kod Yapısı

```python
def main():
    # Read binary
    data = infile.read_bytes()
    
    # Pad to block boundary
    if len(data) % block_bytes != 0:
        pad_len = block_bytes - (len(data) % block_bytes)
        data = data + bytes([pad_byte]) * pad_len
    
    lines = []
    for i in range(0, len(data), block_bytes):
        block = data[i:i+block_bytes]
        words = []
        
        for w in range(words_per_block):
            wbytes = block[w*word_size:(w+1)*word_size]
            if word_endian == 'little':
                val = int.from_bytes(wbytes, 'little')
            else:
                val = int.from_bytes(wbytes, 'big')
            words.append(val)
        
        # Order words
        if word_order == 'high-to-low':
            ordered = list(reversed(words))
        else:
            ordered = words
        
        # Format line
        fmt = ''.join(f"{w:0{word_size*2}x}" for w in ordered)
        lines.append(fmt)
    
    # Write output
    with outfile.open('w') as f:
        for ln in lines:
            f.write(ln + '\n')
```

---

### gen_linker.py - Linker Script Generator

**Dosya:** `script/python/gen_linker.py`

#### Amaç

YAML memory map dosyasından GCC linker script ve C header dosyası üretir.

#### Kullanım

```bash
# Basic usage
python3 gen_linker.py memory_map.yaml output.ld

# With C header
python3 gen_linker.py memory_map.yaml output.ld --header memory_map.h
```

#### Memory Map YAML Formatı

```yaml
# memory_map.yaml
processor:
  name: "Ceres-V"
  isa: "RV32IMC_Zicsr"

memory:
  rom:
    origin: 0x80000000
    length: "32K"
    type: "rx"
  ram:
    origin: 0x80008000
    length: "32K"
    type: "rwx"

stack:
  size: "4K"

heap:
  size: "0"

entry: "_start"
```

#### Üretilen Linker Script

```ld
/*
 * Auto-generated Linker Script for Ceres-V
 * ISA: RV32IMC_Zicsr
 * 
 * Memory Layout:
 *   ROM: 0x80000000 - 0x80007FFF (32K)
 *   RAM: 0x80008000 - 0x8000FFFF (32K)
 *   Stack: 4K
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
    ROM (rx)  : ORIGIN = 0x80000000, LENGTH = 32K
    RAM (rwx) : ORIGIN = 0x80008000, LENGTH = 32K
}

SECTIONS
{
    .text : { *(.text*) } > ROM
    .rodata : { *(.rodata*) } > ROM
    .data : { *(.data*) } > RAM AT> ROM
    .bss : { *(.bss*) } > RAM
    
    _stack_top = ORIGIN(RAM) + LENGTH(RAM);
}
```

#### Üretilen C Header

```c
/* Auto-generated memory map header */
#ifndef MEMORY_MAP_H
#define MEMORY_MAP_H

#define ROM_BASE    0x80000000
#define ROM_SIZE    0x00008000
#define RAM_BASE    0x80008000
#define RAM_SIZE    0x00008000
#define STACK_SIZE  0x00001000
#define STACK_TOP   0x80010000

#endif /* MEMORY_MAP_H */
```

---

### hex2mem_32to128.py - HEX Format Converter

**Dosya:** `script/python/hex2mem_32to128.py`

#### Amaç

32-bit hex dosyalarını 128-bit block formatına çevirir.

#### Kullanım

```bash
python3 hex2mem_32to128.py input.hex output.mem
```

#### Dönüşüm

```
# Input (32-bit per line):
12345678
ABCDEF00
11223344
55667788

# Output (128-bit per line, 4 words combined):
5566778811223344ABCDEF0012345678
```

---

## Generator Scripts

### torture_gen.py - Torture Test Generator

**Dosya:** `script/python/torture_gen.py`

#### Amaç

Random ama valid RISC-V instruction sequences üretir. Processor stress testing için kullanılır.

#### Kullanım

```bash
python3 torture_gen.py \
    --seed 12345 \
    --max-instructions 1000 \
    --march rv32imc \
    --output torture_test.S
```

#### Parametreler

| Parametre | Default | Açıklama |
|-----------|---------|----------|
| `--seed` | random | Random seed (deterministic results) |
| `--max-instructions` | 1000 | Maximum instruction count |
| `--march` | rv32imc | Target architecture |
| `--output` | stdout | Output file |

#### Instruction Mix Configuration

```python
@dataclass
class GeneratorConfig:
    seed: int
    max_instructions: int = 1000
    march: str = 'rv32imc'
    
    # Instruction mix weights (percentages)
    weight_r_type: int = 30      # ADD, SUB, AND, OR, XOR, etc.
    weight_i_type: int = 25      # ADDI, ANDI, ORI, etc.
    weight_shift: int = 10       # SLL, SRL, SRA
    weight_load: int = 10        # LW, LH, LB
    weight_store: int = 10       # SW, SH, SB
    weight_lui_auipc: int = 5    # LUI, AUIPC
    weight_compressed: int = 10  # C.ADDI, C.LW, etc.
    
    # Branch configuration
    branch_probability: float = 0.05
    max_branch_distance: int = 10
    
    # Memory configuration
    data_region_size: int = 256
```

#### Register Management

```python
class RegisterFile:
    def __init__(self):
        self.all_regs = [f'x{i}' for i in range(1, 32)]
        # Reserved: x2 (sp), x3 (gp), x10 (data pointer)
        self.reserved = ['x2', 'x3', 'x10']
        self.usable = [r for r in self.all_regs if r not in self.reserved]
    
    def random_src(self) -> str:
        return random.choice(self.usable)
    
    def random_dst(self) -> str:
        return random.choice(self.usable)
```

#### Üretilen Test Örneği

```asm
# Auto-generated torture test
# Seed: 12345, Instructions: 100, March: rv32imc

.section .text
.global _start
_start:
    # Initialize data pointer
    la x10, _data
    
    # Random instruction sequence
    addi x5, x0, 42
    add x6, x5, x5
    c.addi x7, 10
    lw x8, 0(x10)
    sw x6, 4(x10)
    ...

.section .data
_data:
    .word 0x12345678
    .word 0xABCDEF00
    ...
```

---

### riscv_dv_gen.py - RISCV-DV Generator

**Dosya:** `script/python/riscv_dv_gen.py`

#### Amaç

RISCV-DV framework ile random test generation. Comprehensive verification için.

#### Kullanım

```bash
python3 riscv_dv_gen.py \
    --test riscv_arithmetic_basic_test \
    --iterations 10 \
    --seed 42 \
    --output-dir build/tests/riscv-dv
```

---

## Analysis Scripts

### compare_bp_stats.py - Branch Predictor Analysis

**Dosya:** `script/python/compare_bp_stats.py`

#### Amaç

Branch predictor istatistiklerini analiz eder. Farklı konfigürasyonları karşılaştırır.

#### Kullanım

```bash
python3 compare_bp_stats.py \
    --log1 results/logs/verilator/test1/bp_stats.log \
    --log2 results/logs/verilator/test2/bp_stats.log \
    --output comparison.html
```

#### İstatistikler

- Total branches
- Correctly predicted
- Mispredicted
- Prediction accuracy (%)
- BTB hits/misses
- RAS push/pop counts

---

### slang_lint.py - Slang Linter Wrapper

**Dosya:** `script/python/slang_lint.py`

#### Amaç

Slang (pyslang) SystemVerilog linter wrapper. Makefile integration için.

#### Kullanım

```bash
python3 slang_lint.py rtl/core/*.sv rtl/pkg/*.sv

# With options
python3 slang_lint.py \
    --include rtl/include \
    --top ceres_wrapper \
    --report results/lint/slang.json \
    rtl/**/*.sv
```

#### Kod Yapısı

```python
import pyslang

def lint_files(files, includes, top_module):
    # Create compilation
    comp = pyslang.Compilation()
    
    # Add include paths
    for inc in includes:
        comp.addSearchDirectory(inc)
    
    # Add source files
    for f in files:
        comp.addSyntaxTree(pyslang.SyntaxTree.fromFile(f))
    
    # Get diagnostics
    diags = comp.getAllDiagnostics()
    
    for d in diags:
        print(f"{d.location}: {d.severity}: {d.message}")
    
    return len([d for d in diags if d.severity == 'error']) == 0
```

---

## Makefile Helpers

### isa_pipeline.py - ISA Test Import

**Dosya:** `script/python/makefile/isa_pipeline.py`

#### Amaç

riscv-tests suite'den ISA testlerini import eder. ELF → MEM/HEX/DUMP dönüşümü yapar.

#### Kullanım

```bash
python3 isa_pipeline.py \
    --isa-dir subrepo/riscv-tests/isa \
    --ceres-root /path/to/ceres
```

#### Pipeline Adımları

1. ELF dosyalarını bul
2. objcopy ile binary'e çevir
3. elf_to_mem.py ile .mem oluştur
4. objdump ile .dump oluştur
5. Pass/fail address'lerini çıkar
6. Sonuçları build/tests/riscv-tests/ altına kopyala

---

### compare_logs.py - Log Karşılaştırma

**Dosya:** `script/python/makefile/compare_logs.py`

#### Amaç

RTL commit log ile Spike commit log'unu karşılaştırır. Test pass/fail kararı verir.

#### Kullanım

```bash
python3 compare_logs.py \
    results/logs/verilator/test/commit.log \
    results/logs/spike/test/commit.log
```

#### Karşılaştırma Kriterleri

- PC values
- Instruction opcodes
- Register write-back values
- Memory store values

#### Çıktı

```
[COMPARE] Comparing RTL log with Spike log...
[INFO] RTL commits: 1234
[INFO] Spike commits: 1234
[PASS] All commits match!

# Or on mismatch:
[FAIL] Mismatch at commit #456
  RTL:   PC=0x80000100 x5=0x12345678
  Spike: PC=0x80000100 x5=0x12345679
```

---

### generate_test_dashboard.py - HTML Dashboard

**Dosya:** `script/python/makefile/generate_test_dashboard.py`

#### Amaç

Test sonuçlarından HTML dashboard oluşturur.

#### Kullanım

```bash
python3 generate_test_dashboard.py \
    --results results/regression/*.json \
    --output results/reports/dashboard.html
```

#### Dashboard İçeriği

- Test suite summary (pass/fail counts)
- Per-test results table
- Execution time statistics
- Failure details with logs
- Historical trends (if available)

---

## Özet

Python scripts:

1. **Converters**: ELF/HEX/BIN → .mem dönüşümleri
2. **Generators**: Linker script, torture test, RISCV-DV
3. **Analysis**: Branch predictor stats, log comparison
4. **Linting**: Slang wrapper
5. **Makefile Helpers**: ISA import, log compare, dashboard
6. **Modular Design**: Her script tek bir işe odaklı
7. **CLI Interface**: argparse ile consistent interface
