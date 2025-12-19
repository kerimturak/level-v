---
title: "Tasarım Kustomizasyonu"
description: "Ceres RISC-V Tasarımının Parametrik Kustomizasyonu Rehberi"
date: 2025-12-01
draft: false
weight: 200
---

# Ceres RISC-V Tasarım Kustomizasyonu

Bu rehber, Ceres RISC-V procesörünün parametrik sistemini kullanarak tasarımı özelleştirmeyi açıklamaktadır.

---

## 1. Giriş

Ceres, tamamen parametrik bir tasarımdır. Komut seti uzantılarından exception priority'sine kadar hemen hemen her şey konfigüre edilebilir.

### Konfigürasyon Seviyeleri

```
┌─────────────────────────────────────────────────┐
│     1. Rtl/pkg/ceres_param.sv (Temel)           │
│        - ISA uzantıları (M, C, V, vb)           │
│        - Bellek boyutları                       │
│        - Cache parametreleri                    │
└─────────────────────────────────────────────────┘
                      │
┌─────────────────────▼─────────────────────────┐
│  2. Rtl/include/exception_priority.svh         │
│     (Exception Priority Şablonları)           │
│     - Varsayılan (RISC-V Spec)                │
│     - Custom kombinasyonlar                   │
└───────────────────────────────────────────────┘
                      │
┌─────────────────────▼─────────────────────────┐
│  3. Verilator Config (sim/tb/verilator.vlt)  │
│     - Simulation parametreleri                │
│     - Trace ayarları                          │
└───────────────────────────────────────────────┘
                      │
┌─────────────────────▼─────────────────────────┐
│  4. Makefile & Build Scripts                  │
│     - Compile flags                           │
│     - Test seçenekleri                        │
└───────────────────────────────────────────────┘
```

---

## 2. Temel Parametreler (ceres_param.sv)

### 2.1 Dosya Konumu

```
rtl/pkg/ceres_param.sv
```

### 2.2 ISA Uzantıları

#### RV32M (Multiply/Divide) Devre Dışı Bırakma

**Varsayılan**:
```systemverilog
localparam bit ENABLE_RV32M = 1'b1;
```

**Devre dışı**:
```systemverilog
localparam bit ENABLE_RV32M = 1'b0;  // MUL/DIV komutları disable
```

**Etki**:
- Multiplier hardware kaldırılır (alan tasarrufu)
- DIV komutları `ILLEGAL_INSTRUCTION` exception oluşturur
- Performans: Biraz artabilir (MUL hazard'ı yok)

#### RV32C (Compressed Instructions) Devre Dışı Bırakma

**Varsayılan**:
```systemverilog
localparam bit ENABLE_RV32C = 1'b1;
```

**Devre dışı**:
```systemverilog
localparam bit ENABLE_RV32C = 1'b0;  // 16-bit komutlar disable
```

**Etki**:
- Compressed instruction decoder kaldırılır
- Dekoder daha basit olur
- Code size artar (~30% fazla bellek)

### 2.3 Bellek Parametreleri

#### Instruction Memory Boyutu

```systemverilog
localparam int INSTR_MEM_SIZE = 32'h10000;  // 64 KB (varsayılan)

// Alternatif boyutlar:
// 16 KB:    32'h4000
// 32 KB:    32'h8000
// 64 KB:    32'h10000    <- Varsayılan
// 128 KB:   32'h20000
// 256 KB:   32'h40000
// 512 KB:   32'h80000
// 1 MB:     32'h100000
```

**Not**: Boyutlar 2'nin kuvveti olmalıdır!

#### Data Memory Boyutu

```systemverilog
localparam int DATA_MEM_SIZE = 32'h4000;  // 16 KB (varsayılan)

// Alternatif boyutlar:
// 4 KB:    32'h1000
// 8 KB:    32'h2000
// 16 KB:   32'h4000    <- Varsayılan
// 32 KB:   32'h8000
// 64 KB:   32'h10000
```

#### Reset Vector (Başlama Adresi)

```systemverilog
localparam logic [31:0] PC_RESET_VALUE = 32'h8000_0000;

// Alternatifler:
// 0x00000000:  Internal ROM
// 0x80000000:  External Flash (RISC-V Standard)
```

### 2.4 Cache Parametreleri

#### Cache Line Size (Cacheline Boyutu)

```systemverilog
localparam int CACHE_LINE_SIZE = 16;  // bytes (varsayılan)

// Alternatif boyutlar:
// 8 bytes:     16-bit access
// 16 bytes:    32-bit cache line    <- Varsayılan
// 32 bytes:    64-bit cache line
// 64 bytes:    128-bit cache line
```

**Not**: Bellek hizalanması otomatik ayarlanır.

#### Cache Set Sayısı

```systemverilog
localparam int CACHE_SETS = 128;  // (varsayılan)

// Alternatif:
// 64 sets:     256 bytes total
// 128 sets:    2 KB total         <- Varsayılan
// 256 sets:    4 KB total
// 512 sets:    8 KB total
```

#### Cache Associativity (Yol Sayısı)

```systemverilog
localparam int CACHE_WAYS = 2;  // 2-way (varsayılan)

// Alternatif:
// 1:   Direct-mapped
// 2:   2-way associative          <- Varsayılan
// 4:   4-way associative
// 8:   8-way associative
```

**Toplam Cache Boyutu** = `CACHE_SETS × CACHE_WAYS × CACHE_LINE_SIZE`

**Örnek**:
```
128 × 2 × 16 = 4 KB cache
```

#### Replacement Policy

```systemverilog
localparam cache_policy_t CACHE_POLICY = CACHE_POLICY_LRU;

// Alternatif:
// CACHE_POLICY_LRU:   Least Recently Used    <- Varsayılan
// CACHE_POLICY_FIFO:  First In First Out
// CACHE_POLICY_RANDOM: Rastgele
```

### 2.5 Multiplier/Divider Konfigürasyonu

#### Multiplier Radix Seviyesi

```systemverilog
localparam int MUL_RADIX = 4;  // Radix-4 (varsayılan)

// Alternatif:
// 2:   Radix-2  (yavaş, 32 cycle)
// 4:   Radix-4  (orta, 2 cycle)      <- Varsayılan
// 8:   Radix-8  (hızlı, 1 cycle) [Verilog version yok]
```

#### Divider Algoritması

```systemverilog
localparam divider_type_t DIV_TYPE = DIVIDER_NON_RESTORING;

// Alternatif:
// DIVIDER_NON_RESTORING:  Non-restoring (34 cycle)    <- Varsayılan
// DIVIDER_RESTORING:      Restoring (daha hızlı)
// DIVIDER_SRT:            SRT algorithm (en hızlı)
```

### 2.6 Pipeline Yapılandırması

#### Pipeline Aşama Sayısı

```systemverilog
localparam int PIPELINE_STAGES = 5;  // 5-stage (varsayılan)

// Alternatif:
// 3:   IF -> ID/EX -> MEM/WB (daha basit)
// 5:   IF -> ID -> EX -> MEM -> WB (varsayılan)
// 7:   Daha uzun (advanced)
```

---

## 3. Exception Priority Konfigürasyonu

### 3.1 Dosya Konumu

```
rtl/include/exception_priority.svh
```

### 3.2 Varsayılan Konfigürasyon (RISC-V Spec)

```systemverilog
`ifdef EXCEPTION_PRIORITY_DEBUG_FIRST
    // Debug Breakpoint first (default RISC-V)
    localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_1;
    localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_2;
    localparam exc_priority_t EXC_PRIORITY_INSTR_ACCESS_FAULT = PRIORITY_3;
    localparam exc_priority_t EXC_PRIORITY_ILLEGAL = PRIORITY_4;
    localparam exc_priority_t EXC_PRIORITY_EBREAK = PRIORITY_5;
    localparam exc_priority_t EXC_PRIORITY_ECALL = PRIORITY_6;
`endif
```

### 3.3 Custom Priority Tanımı

Yeni bir konfigürasyon eklemek için:

```systemverilog
// exception_priority.svh dosyasında

`else ifdef EXCEPTION_PRIORITY_CUSTOM_TEST_1
    // Custom test: Misaligned first
    localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_1;
    localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_2;
    localparam exc_priority_t EXC_PRIORITY_INSTR_ACCESS_FAULT = PRIORITY_3;
    localparam exc_priority_t EXC_PRIORITY_ILLEGAL = PRIORITY_4;
    localparam exc_priority_t EXC_PRIORITY_EBREAK = PRIORITY_5;
    localparam exc_priority_t EXC_PRIORITY_ECALL = PRIORITY_6;
`else ifdef EXCEPTION_PRIORITY_CUSTOM_TEST_2
    // Custom test: Illegal first
    localparam exc_priority_t EXC_PRIORITY_ILLEGAL = PRIORITY_1;
    localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_2;
    // ... diğerleri
`else
    // Varsayılan
    localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_1;
    // ... (varsayılan olarak)
`endif
```

### 3.4 Makefile'dan Konfigürasyon Seçme

**Makefile'de**:

```makefile
# Varsayılan (RISC-V Spec)
SIM_FLAGS ?= -DEXCEPTION_PRIORITY_DEBUG_FIRST

# Custom için
SIM_FLAGS = -DEXCEPTION_PRIORITY_CUSTOM_TEST_1

# Veya variable olarak
EXCEPTION_PRIORITY ?= EXCEPTION_PRIORITY_DEBUG_FIRST
SIM_FLAGS = -D$(EXCEPTION_PRIORITY)
```

**Komut satırından**:

```bash
# Custom priority ile derle
make SIM_FLAGS=-DEXCEPTION_PRIORITY_CUSTOM_TEST_1 verilator_build

# Test çalıştır
make SIM_FLAGS=-DEXCEPTION_PRIORITY_CUSTOM_TEST_1 quick
```

---

## 4. Verilator Konfigürasyonu

### 4.1 Dosya Konumu

```
sim/tb/verilator.vlt
```

### 4.2 Trace Ayarları

```systemverilog
// Trace buffer boyutu
`define VL_DEBUG_LEVEL 10

// VCD dump ayarları
--trace --trace-depth 5

// Trace file boyutu limiti
--trace-max-size 1000000
```

### 4.3 Optimization Ayarları

```systemverilog
// Faster compilation (daha az optimization)
--O0

// Balanced (varsayılan)
--O1

// Aggressive optimization
--O2

// Maximum optimization
--O3
```

### 4.4 Warning Kontrolleri

```systemverilog
// Tüm warning'leri göster
--Wall

// Specific warning'leri kapat
--Wno-UNOPTFLAT
--Wno-WIDTH

// Strict mode (tüm warning'ler hata gibi)
--Werror
```

---

## 5. Build System Konfigürasyonu

### 5.1 Makefile Parametreleri

```bash
# Parallelizasyon seviyesi
make -j4 build     # 4 parallel jobs

# Verbose mode (detaylı çıktı)
make V=1 build

# Debug symbols (GDB debugging)
make DEBUG=1 build

# Coverage etkinleştir
make COVERAGE=1 build
```

### 5.2 Test Konfigürasyonu

```bash
# Test timeout (saniye)
make TEST_TIMEOUT=120 quick

# Verbose test output
make TEST_VERBOSE=1 quick

# Specific test çalıştır
make TEST_FILTER=test_add quick

# Repeat count
make TEST_REPEAT=5 quick
```

---

## 6. Pratik Örnekler

### Örnek 1: Minimal Tasarım (Öğrenme)

```systemverilog
// rtl/pkg/ceres_param.sv
// Maksimum alan tasarrufu

localparam bit ENABLE_RV32M = 1'b0;    // No multiply/divide
localparam bit ENABLE_RV32C = 1'b1;    // Compressed ok
localparam int INSTR_MEM_SIZE = 32'h4000;  // 16 KB
localparam int DATA_MEM_SIZE = 32'h1000;   // 4 KB
localparam int CACHE_SETS = 32;       // Minimal cache
localparam int CACHE_WAYS = 1;        // Direct mapped
```

**Avantajlar**:
- Minimum area
- Basit tasarım
- Anlaşılması kolay

**Dezavantajlar**:
- Slow MUL (emulated)
- Limited memory

### Örnek 2: Performans Tasarımı

```systemverilog
// rtl/pkg/ceres_param.sv
// Maksimum performans

localparam bit ENABLE_RV32M = 1'b1;    // Full M extension
localparam bit ENABLE_RV32C = 1'b1;    // Compressed too
localparam int INSTR_MEM_SIZE = 32'h100000;  // 1 MB
localparam int DATA_MEM_SIZE = 32'h80000;    // 512 KB
localparam int CACHE_SETS = 512;      // Large cache
localparam int CACHE_WAYS = 4;        // 4-way associative
localparam int MUL_RADIX = 4;         // Fast multiplier
```

**Avantajlar**:
- Hızlı MUL/DIV
- Geniş bellek
- Büyük cache

**Dezavantajlar**:
- Large area
- Higher power

### Örnek 3: FPGA Deployment

```systemverilog
// rtl/pkg/ceres_param.sv
// Balanced FPGA tasarım

localparam bit ENABLE_RV32M = 1'b1;
localparam bit ENABLE_RV32C = 1'b1;
localparam int INSTR_MEM_SIZE = 32'h8000;   // 32 KB
localparam int DATA_MEM_SIZE = 32'h4000;    // 16 KB
localparam int CACHE_SETS = 128;
localparam int CACHE_WAYS = 2;
```

---

## 7. Derleme ve Test

### 7.1 Özel Konfigürasyon ile Derleme

```bash
# 1. Parametreleri düzenle
nano rtl/pkg/ceres_param.sv

# 2. Exception priority konfigürasyonunu seç
nano rtl/include/exception_priority.svh

# 3. Clean build yap
make distclean

# 4. Verilator modelini derle
make verilator_build

# 5. Hızlı test
make quick
```

### 7.2 Validation

```bash
# Coverage raporu oluştur (design validation)
make coverage

# Waveform analiz
make wave

# Performance benchmark
make coremark
```

### 7.3 Regression Testing (Farklı Konfigürasyonlar)

```bash
#!/bin/bash
# test_all_configs.sh

configs=(
    "MINIMAL"
    "BALANCED"
    "PERFORMANCE"
)

for config in "${configs[@]}"; do
    echo "Testing $config configuration..."
    
    # Update config
    # (... düzen kodu ...)
    
    # Build and test
    make distclean
    make verilator_build
    make quick
    
    # Check results
    if [ $? -ne 0 ]; then
        echo "FAILED: $config"
        exit 1
    fi
done

echo "All configurations passed!"
```

---

## 8. Advanced Kustomizasyon

### 8.1 Yeni ISA Uzantısı Ekleme

Varsayalım RV32F (Floating-Point) eklemek istiyorsunuz:

1. **Parameter ekle**:
```systemverilog
localparam bit ENABLE_RV32F = 1'b1;
```

2. **Decoder'ı güncelle**:
```systemverilog
// rtl/core/stage02_decode/decoder.sv
if (ENABLE_RV32F && opcode == 7'b0010011) begin
    // Float operations
    instr_type = FADD;
    // ...
end
```

3. **ALU'yu genişlet**:
```systemverilog
// rtl/core/stage03_execute/alu.sv
if (ENABLE_RV32F) begin
    float_add_unit fadd(
        .a(operand1_float),
        .b(operand2_float),
        .result(fadd_result)
    );
end
```

4. **Test et**:
```bash
make clean
make verilator_build
make quick
```

### 8.2 Yeni Exception Tipi Ekleme

1. **Exception tanımını ekle**:
```systemverilog
// rtl/pkg/ceres_param.sv
typedef enum logic [3:0] {
    // ... existing
    CUSTOM_TRAP = 4'h0A  // Yeni
} exception_code_t;
```

2. **Priority atama**:
```systemverilog
// rtl/include/exception_priority.svh
localparam exc_priority_t EXC_PRIORITY_CUSTOM_TRAP = PRIORITY_7;
```

3. **Detection logic**:
```systemverilog
// Uygun aşamada
has_custom_trap = /* your condition */;

// Priority check ile
if (has_custom_trap && check_exc_priority(EXC_PRIORITY_CUSTOM_TRAP, PRIORITY_7)) begin
    exc_type = CUSTOM_TRAP;
end
```

---

## 9. İşler Ters Giderse

### Debug Tips

```bash
# 1. Verilator hata mesajını oku
cat build/logs/verilator_build.log | tail -50

# 2. Simulation sırasında stall
# Waveform'u görüntüle
gtkwave build/work/waveform.vcd &

# 3. Specific signal trace et
./sim/tb/run_with_trace.sh signal_name

# 4. Kısa test çalıştır
make TEST_TIMEOUT=5 quick
```

### Common Issues

| Sorun | Sebep | Çözüm |
|-------|-------|-------|
| Derleme hatası | Syntax error | `nano rtl/pkg/ceres_param.sv` - kontrol et |
| Simulation crash | Memory issue | `make -j1 quick` - sırayla çalıştır |
| Test timeout | Sonsuz loop | Waveform'u kontrol et, logic hatası |
| Coverage düşük | Parametre test edilmedi | Test case ekle |

---

## 10. Kontrol Listesi

Kustomizasyon öncesi:

- [ ] Varsayılan konfigürasyon `make quick` ile çalışıyor
- [ ] Parametreleri anladım
- [ ] Backup kopya oluşturdum (`git commit -am "backup"`)
- [ ] Değişiklikleri dokumente ettim

Kustomizasyon sonrası:

- [ ] Değişiklikleri yaptım
- [ ] `make distclean && make verilator_build` başarılı
- [ ] `make quick` testleri pass
- [ ] Coverage raporu kontrol ettim
- [ ] Waveform sonuçları makul

---

## 📞 Referanslar

- [Ceres Mimari Tasarım](./architecture.md) - Detaylı parametre açıklamaları
- [Exception Priority](./PARAMETRIC_EXCEPTION_PRIORITY.md) - Priority sistemi
- [RISC-V ISA Spec](https://riscv.org/specifications/) - İse uzantı tanımları

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025

