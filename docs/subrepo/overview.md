# Subrepo - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [riscv-tests](#riscv-tests)
3. [riscv-arch-test](#riscv-arch-test)
4. [imperas-riscv-tests](#imperas-riscv-tests)
5. [CoreMark](#coremark)
6. [Embench-IoT](#embench-iot)
7. [RISCV-DV](#riscv-dv)
8. [RISCV-Formal](#riscv-formal)

---

## Genel Bakış

### Dizin Yapısı

```
subrepo/
├── riscv-tests/           # Official RISC-V ISA Tests
├── riscv-arch-test/       # RISC-V Architecture Tests
├── imperas-riscv-tests/   # Imperas Extended Tests
├── coremark/              # EEMBC CoreMark Benchmark
├── embench-iot/           # Embench-IoT Benchmark Suite
├── riscv-dv/              # RISCV-DV Random Test Generator
└── riscv-formal/          # RISC-V Formal Verification
```

### Test Suite Karşılaştırması

| Suite | Amaç | Test Sayısı | Kaynak |
|-------|------|-------------|--------|
| riscv-tests | ISA compliance | ~100+ | RISC-V Foundation |
| riscv-arch-test | Architecture compliance | ~200+ | RISC-V International |
| imperas-riscv-tests | Extended coverage | ~500+ | Imperas |
| coremark | Performance benchmark | 1 | EEMBC |
| embench-iot | Embedded benchmark | 19 | Embench |
| riscv-dv | Random testing | Generated | Google |
| riscv-formal | Formal verification | N/A | Claire Wolf |

### Git Submodule Yönetimi

```bash
# Submodule'leri clone etme
git submodule update --init --recursive

# Belirli submodule'ü güncelleme
git submodule update --remote subrepo/riscv-tests

# Tüm submodule'leri güncelleme
git submodule update --remote --merge
```

---

## riscv-tests

**Dizin:** `subrepo/riscv-tests/`
**Kaynak:** https://github.com/riscv-software-src/riscv-tests

### Amaç

RISC-V Foundation tarafından sağlanan resmi ISA compliance testleri. Her instruction için unit test içerir.

### Dizin Yapısı

```
riscv-tests/
├── isa/
│   ├── rv32ui/        # RV32 User Integer
│   │   ├── add.S
│   │   ├── addi.S
│   │   ├── and.S
│   │   └── ...
│   ├── rv32um/        # RV32 User Multiply
│   │   ├── mul.S
│   │   ├── mulh.S
│   │   └── ...
│   ├── rv32uc/        # RV32 User Compressed
│   │   ├── rvc.S
│   │   └── ...
│   ├── rv32mi/        # RV32 Machine Integer
│   │   ├── csr.S
│   │   ├── mcsr.S
│   │   └── ...
│   └── rv32si/        # RV32 Supervisor Integer
├── benchmarks/        # Simple benchmarks
│   ├── dhrystone/
│   ├── median/
│   ├── qsort/
│   ├── rsort/
│   ├── towers/
│   └── vvadd/
├── env/               # Test environments
│   └── p/             # Physical memory test env
└── debug/             # Debug module tests
```

### Test İsimlendirme

```
rv32<ext>-<env>-<test>

Örnek: rv32ui-p-add
  - rv32: RV32 architecture
  - ui: User Integer extension
  - p: Physical memory environment
  - add: ADD instruction test
```

### Extension Kodları

| Kod | Açıklama |
|-----|----------|
| `ui` | User Integer (base) |
| `um` | User Multiply |
| `ua` | User Atomic |
| `uc` | User Compressed |
| `uf` | User Float |
| `ud` | User Double |
| `mi` | Machine Integer |
| `si` | Supervisor Integer |

### Kullanım

```bash
# Tüm ISA testlerini çalıştır
make isa

# Tek test çalıştır
make t T=rv32ui-p-add

# RV32I testleri
make isa_rv32i

# RV32M testleri
make isa_rv32m
```

---

## riscv-arch-test

**Dizin:** `subrepo/riscv-arch-test/`
**Kaynak:** https://github.com/riscv-non-isa/riscv-arch-test

### Amaç

RISC-V International tarafından yönetilen resmi architecture compliance test suite. riscv-tests'ten daha kapsamlı ve güncel.

### Dizin Yapısı

```
riscv-arch-test/
├── riscv-test-suite/
│   ├── rv32i_m/
│   │   ├── I/              # RV32I tests
│   │   │   ├── src/
│   │   │   │   ├── add-01.S
│   │   │   │   ├── addi-01.S
│   │   │   │   └── ...
│   │   │   └── references/  # Golden signatures
│   │   ├── M/              # RV32M tests
│   │   ├── C/              # RV32C tests
│   │   ├── Zicsr/          # CSR tests
│   │   └── Zifencei/       # Fence.I tests
│   └── rv64i_m/            # RV64 tests
├── riscv-target/           # Target configurations
│   └── ceres/              # Ceres target (custom)
└── doc/                    # Documentation
```

### Test İsimlendirme

```
<instruction>-<variant>.S

Örnek: add-01.S
  - add: ADD instruction
  - 01: Test variant 1
```

### Reference Signatures

Her test bir "signature" üretir ve golden reference ile karşılaştırılır:

```
test output → signature → compare → golden reference
                                         ↓
                                    PASS/FAIL
```

### Kullanım

```bash
# Tüm arch testlerini çalıştır
make arch

# Tek test
make run T=add-01 TEST_TYPE=arch

# I extension testleri
make arch_i

# M extension testleri
make arch_m
```

---

## imperas-riscv-tests

**Dizin:** `subrepo/imperas-riscv-tests/`
**Kaynak:** https://github.com/riscv-ovpsim/imperas-riscv-tests

### Amaç

Imperas tarafından sağlanan genişletilmiş test suite. Corner case'ler ve edge condition'lar için daha kapsamlı testler.

### Dizin Yapısı

```
imperas-riscv-tests/
├── riscv-test-suite/
│   └── rv32i/
│       ├── I/
│       │   ├── I-ADD-01.S
│       │   ├── I-ADDI-01.S
│       │   ├── I-AND-01.S
│       │   └── ...
│       ├── M/
│       │   ├── M-MUL-01.S
│       │   └── ...
│       └── C/
│           ├── C-ADDI-01.S
│           └── ...
└── riscv-ovpsim/           # Imperas OVP simulator
```

### Test Özellikleri

- riscv-arch-test'e benzer format
- Daha fazla edge case coverage
- Exception/interrupt testleri
- PMP testleri

### Kullanım

```bash
# Tüm Imperas testlerini çalıştır
make imperas

# Tek test
make ti T=I-ADD-01

# M extension
make imperas_m
```

---

## CoreMark

**Dizin:** `subrepo/coremark/`
**Kaynak:** https://github.com/eembc/coremark

### Amaç

EEMBC tarafından geliştirilen endüstri standardı CPU benchmark. CoreMark/MHz performans metriği verir.

### Dizin Yapısı

```
coremark/
├── core_list_join.c
├── core_main.c
├── core_matrix.c
├── core_state.c
├── core_util.c
├── coremark.h
└── barebones/           # Baremetal port template
```

### Benchmark İçeriği

| Test | Açıklama |
|------|----------|
| List Processing | Linked list operations |
| Matrix Processing | Matrix multiplication |
| State Machine | Finite state machine |
| CRC Calculation | CRC-16 calculation |

### Performans Metrikleri

```
CoreMark Score = Iterations / Time(seconds)
CoreMark/MHz = CoreMark Score / CPU_MHz

Örnek: 50 CoreMark @ 50MHz = 1.0 CoreMark/MHz
```

### Kullanım

```bash
# CoreMark build ve run
make cm

# Sadece run (rebuild atla)
make cm_run

# Verbose mode
make cm LOG_UART=1 SIM_UART_MONITOR=1
```

### Sonuç Örneği

```
2K performance run parameters for coremark.
CoreMark Size    : 666
Total tance      : 1000
Total time (secs): 20.00
Iterations/Sec   : 50
CoreMark 1.0     : 50.00 / GCC 12.2 -O3 -march=rv32imc
CoreMark/MHz     : 1.00
```

---

## Embench-IoT

**Dizin:** `subrepo/embench-iot/`
**Kaynak:** https://github.com/embench/embench-iot

### Amaç

Gömülü sistemler için modern benchmark suite. Gerçek dünya embedded uygulamalarını temsil eder.

### Dizin Yapısı

```
embench-iot/
├── src/
│   ├── aha-mont64/
│   ├── crc32/
│   ├── cubic/
│   ├── edn/
│   ├── huffbench/
│   ├── matmult-int/
│   ├── md5sum/
│   ├── minver/
│   ├── nbody/
│   ├── nettle-aes/
│   ├── nettle-sha256/
│   ├── nsichneu/
│   ├── picojpeg/
│   ├── primecount/
│   ├── qrduino/
│   ├── sglib-combined/
│   ├── slre/
│   ├── st/
│   ├── statemate/
│   ├── tarfind/
│   ├── ud/
│   └── wikisort/
├── support/            # Common support code
├── config/             # Target configurations
└── doc/                # Documentation
```

### Benchmark Listesi

| Benchmark | Açıklama | Kategori |
|-----------|----------|----------|
| aha-mont64 | Montgomery multiplication | Crypto |
| crc32 | CRC-32 calculation | Data |
| cubic | Cubic root solver | Math |
| edn | EDN parser | Parser |
| huffbench | Huffman encoding | Compression |
| matmult-int | Integer matrix multiply | Math |
| md5sum | MD5 hash | Crypto |
| minver | Matrix inversion | Math |
| nbody | N-body simulation | Physics |
| nettle-aes | AES encryption | Crypto |
| nettle-sha256 | SHA-256 hash | Crypto |
| nsichneu | Neural network | AI |
| picojpeg | JPEG decoding | Image |
| primecount | Prime counting | Math |
| qrduino | QR code | Image |
| sglib-combined | Library functions | General |
| slre | Regex engine | Parser |
| st | Statistics | Math |
| statemate | State machine | Control |
| tarfind | Archive search | Search |
| ud | Undefined behavior | General |
| wikisort | Sorting algorithm | Sort |

### Kullanım

```bash
# Build Embench
make embench

# Run Embench
make embench_run

# Specific benchmark
make embench_single B=crc32
```

---

## RISCV-DV

**Dizin:** `subrepo/riscv-dv/`
**Kaynak:** https://github.com/chipsalliance/riscv-dv

### Amaç

Google tarafından geliştirilen constrained random instruction generator. Otomatik test üretimi ve coverage analizi.

### Dizin Yapısı

```
riscv-dv/
├── src/
│   ├── riscv_instr_gen.sv
│   ├── riscv_instr_base_test.sv
│   ├── riscv_instr_sequence.sv
│   └── ...
├── target/                # Target configurations
│   └── rv32imc/
├── scripts/               # Generation scripts
│   ├── run.py
│   ├── gen_csr_test.py
│   └── ...
├── yaml/                  # Configuration YAML
└── pygen/                 # Python generator
```

### Özellikler

- Constrained random instruction generation
- Configurable instruction mix
- Exception generation
- Interrupt injection
- Memory pattern generation

### Test Tipleri

| Tip | Açıklama |
|-----|----------|
| riscv_arithmetic_basic_test | Basic arithmetic |
| riscv_rand_instr_test | Random instructions |
| riscv_jump_stress_test | Jump/branch stress |
| riscv_loop_test | Loop patterns |
| riscv_mmu_stress_test | MMU stress |

### Kullanım

```bash
# Generate tests
make riscv_dv

# Run generated tests
make riscv_dv_run

# Generate specific test type
make riscv_dv_gen TYPE=riscv_rand_instr_test
```

---

## RISCV-Formal

**Dizin:** `subrepo/riscv-formal/`
**Kaynak:** https://github.com/SymbioticEDA/riscv-formal

### Amaç

Claire Wolf tarafından geliştirilen formal verification framework. RVFI (RISC-V Formal Interface) kullanarak matematiksel doğrulama.

### Dizin Yapısı

```
riscv-formal/
├── checks/
│   ├── rvfi_insn_check.sv
│   ├── rvfi_pc_check.sv
│   ├── rvfi_reg_check.sv
│   └── ...
├── cores/                 # Example core integrations
├── docs/                  # Documentation
└── insns/                 # Per-instruction checks
    ├── insn_add.v
    ├── insn_addi.v
    └── ...
```

### RVFI Sinyalleri

```systemverilog
// Instruction retirement
output        rvfi_valid
output [63:0] rvfi_order
output [31:0] rvfi_insn

// Exception handling
output        rvfi_trap
output        rvfi_halt
output        rvfi_intr

// Register file
output [ 4:0] rvfi_rs1_addr
output [31:0] rvfi_rs1_rdata
output [ 4:0] rvfi_rs2_addr
output [31:0] rvfi_rs2_rdata
output [ 4:0] rvfi_rd_addr
output [31:0] rvfi_rd_wdata

// Program counter
output [31:0] rvfi_pc_rdata
output [31:0] rvfi_pc_wdata

// Memory
output [31:0] rvfi_mem_addr
output [ 3:0] rvfi_mem_rmask
output [ 3:0] rvfi_mem_wmask
output [31:0] rvfi_mem_rdata
output [31:0] rvfi_mem_wdata
```

### Verification Checks

| Check | Açıklama |
|-------|----------|
| insn_check | Instruction correctness |
| pc_check | PC update correctness |
| reg_check | Register file correctness |
| mem_check | Memory access correctness |
| liveness | No deadlock |

### Kullanım

```bash
# Run formal verification
make formal

# Bounded model checking
make formal_bmc

# Full proof
make formal_prove
```

---

## Test Suite Comparison

### Coverage Comparison

```
┌─────────────────────────────────────────────────────────────────┐
│                    TEST SUITE COVERAGE                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Feature          │ riscv │ arch │ imperas │ formal │ dv      │
│  ─────────────────┼───────┼──────┼─────────┼────────┼─────────│
│  RV32I            │   ✓   │  ✓   │    ✓    │   ✓    │    ✓    │
│  RV32M            │   ✓   │  ✓   │    ✓    │   ✓    │    ✓    │
│  RV32C            │   ✓   │  ✓   │    ✓    │   ✓    │    ✓    │
│  Zicsr            │   ✓   │  ✓   │    ✓    │   ✓    │    ✓    │
│  Zifencei         │   △   │  ✓   │    ✓    │   △    │    ✓    │
│  Exceptions       │   △   │  ✓   │    ✓    │   ✓    │    ✓    │
│  Interrupts       │   △   │  △   │    ✓    │   △    │    ✓    │
│  Random           │   ✗   │  ✗   │    ✗    │   ✗    │    ✓    │
│  Edge Cases       │   △   │  ✓   │    ✓    │   ✓    │    ✓    │
│  Performance      │   ✗   │  ✗   │    ✗    │   ✗    │    ✗    │
│                                                                  │
│  ✓ = Full   △ = Partial   ✗ = None                              │
└─────────────────────────────────────────────────────────────────┘
```

### Recommended Test Flow

```
1. Development
   └── make isa          # Quick ISA sanity check

2. Integration
   └── make arch         # Architecture compliance

3. Extended Testing
   └── make imperas      # Edge case coverage

4. Performance
   └── make cm           # CoreMark benchmark

5. Stress Testing
   └── make riscv_dv     # Random testing

6. Final Verification
   └── make formal       # Formal proof
```

---

## Özet

Subrepo dizini:

1. **riscv-tests**: Official ISA tests, quick sanity check
2. **riscv-arch-test**: Architecture compliance, certification
3. **imperas-riscv-tests**: Extended coverage, edge cases
4. **coremark**: Industry standard benchmark
5. **embench-iot**: Real-world embedded benchmarks
6. **riscv-dv**: Random test generation, coverage
7. **riscv-formal**: Mathematical verification

Her suite farklı amaçlara hizmet eder ve kapsamlı verification için birlikte kullanılmalıdır.
