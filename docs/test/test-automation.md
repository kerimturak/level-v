# Ceres-V Test Otomasyonu

## Genel Bakış

Ceres-V projesi, kapsamlı bir test otomasyonu altyapısına sahiptir. Bu dokümantasyon, mevcut test pipeline'larını, kullanım yöntemlerini ve konfigürasyon seçeneklerini açıklar.

## Test Türleri

| Test Türü | Kaynak | Açıklama | Komut |
|-----------|--------|----------|-------|
| ISA Tests | riscv-tests | Temel RISC-V ISA testleri | `make isa` |
| Arch Tests | riscv-arch-test | Resmi mimari uyumluluk testleri | `make arch` |
| Imperas Tests | imperas-riscv-tests | Genişletilmiş I testleri | `make imperas` |
| Benchmarks | riscv-tests/benchmarks | Performans testleri | `make bench` |
| CoreMark | EEMBC CoreMark | Endüstri standardı benchmark | `make cm` |

## Hızlı Başlangıç

### Tüm Test Türlerini Hazırlama

```bash
# ISA testleri (zaten mevcut olmalı)
make isa_auto

# Arch testleri (M, C, Zicsr dahil)
make arch_auto

# Imperas testleri (sadece I extension)
make imperas_auto

# CoreMark
make coremark
```

### Testleri Çalıştırma

```bash
# ISA testleri
make isa

# Benchmarks
make bench

# Arch testleri
make arch

# Imperas testleri
make imperas

# CoreMark
make cm
```

## Tekil Test Çalıştırma

```bash
# ISA testi
make t T=rv32ui-p-add

# Benchmark
make tb T=dhrystone MAX_CYCLES=1000000

# Arch testi
make ta T=I-add-01

# Imperas testi
make ti T=I-ADD-01
```

## Log Yönetimi

### Logları Temizleme

Batch test çalıştırmadan önce eski logları temizlemek için:

```bash
make isa CLEAN_LOGS=1
make bench CLEAN_LOGS=1
make arch CLEAN_LOGS=1
make imperas CLEAN_LOGS=1
```

### Log Konumları

```
results/logs/
├── verilator/          # Verilator simülasyon logları
│   ├── <test_name>/
│   │   ├── rtl_sim.log
│   │   ├── spike.log
│   │   ├── diff.log
│   │   ├── diff.html
│   │   └── commit_trace.log
├── tests_passed.list   # Geçen testler
└── tests_failed.list   # Başarısız testler
```

## Konfigürasyon

### MAX_CYCLES

Test türüne göre varsayılan cycle limitleri (`config.mk`):

| Test Türü | MAX_CYCLES |
|-----------|------------|
| isa | 10,000 |
| arch | 100,000 |
| imperas | 200,000 |
| bench | 1,000,000 |

Override etmek için:

```bash
make t T=rv32ui-p-add MAX_CYCLES=50000
```

### Simülatör Seçimi

```bash
# Verilator (varsayılan)
make isa SIM=verilator

# ModelSim (eğer kurulu ise)
make isa SIM=modelsim
```

### Build Profilleri

```bash
make verilate MODE=debug    # Full tracing, assertions ON
make verilate MODE=release  # Optimized, minimal logging
make verilate MODE=test     # RISC-V tests & assertions
```

## Test Pipeline Mimarisi

### Genel Akış

```
1. Clone Repository (xxx_clone)
2. Setup Environment (xxx_setup)
3. Build Tests (xxx_build)
   - Compile .S → .elf
   - Generate .dump (disassembly)
   - Convert to .hex (verilog format)
4. Import (xxx_import)
   - Convert .hex → .mem (simulation format)
   - Extract pass/fail addresses
5. Run Tests (xxx veya run_flist)
   - RTL simulation
   - Spike reference
   - Compare logs
```

### Dosya Formatları

| Format | Açıklama | Kullanım |
|--------|----------|----------|
| .S | Assembly kaynak | Derleme girişi |
| .elf | Executable | Spike, debugging |
| .dump | Disassembly | Adres çıkarımı |
| .hex | Verilog hex | Ara format |
| .mem | 32-bit words | RTL simülasyonu |
| _addr.txt | Pass/Fail adresleri | Test sonucu kontrolü |

## Extension Desteği

### Desteklenen Extensionlar (RV32IMC_Zicsr)

| Extension | ISA Tests | Arch Tests | Imperas |
|-----------|-----------|------------|---------|
| I (Base) | ✅ | ✅ | ✅ |
| M (Multiply) | ✅ | ✅ | ❌ |
| C (Compressed) | ✅ | ✅ | ❌ |
| Zicsr (CSR) | ✅ | ✅ | ❌ |
| Zifencei | ✅ | ✅ | ❌ |

## Yardım Komutları

```bash
make help           # Genel yardım
make help_test      # Test komutları yardımı
make help_lists     # Test listesi komutları
make arch_help      # Arch test yardımı
make imperas_help   # Imperas test yardımı
make coremark_help  # CoreMark yardımı
```

## Örnek İş Akışları

### Yeni bir RTL değişikliğini test etme

```bash
# 1. Verilator modelini rebuild et
make verilate

# 2. Hızlı ISA testi
make t T=rv32ui-p-add

# 3. Tüm ISA testleri
make isa CLEAN_LOGS=1

# 4. Başarısız testleri kontrol et
cat results/logs/tests_failed.list
```

### Kapsamlı regresyon testi

```bash
# Tüm test türlerini çalıştır
make isa CLEAN_LOGS=1
make arch CLEAN_LOGS=1
make imperas CLEAN_LOGS=1
make bench CLEAN_LOGS=1
make cm
```

### Belirli bir testin debug'ı

```bash
# Detaylı log ile çalıştır
make t T=rv32ui-p-add VERBOSE=1

# HTML diff raporunu incele
firefox results/logs/verilator/rv32ui-p-add/diff.html

# Waveform (eğer trace açıksa)
gtkwave results/logs/verilator/rv32ui-p-add/trace.fst
```

## Sorun Giderme

### "Test list file not found"

```bash
# Test listesini oluştur
make arch_gen_flist
make imperas_flist
```

### "ELF file not found"

```bash
# Testleri rebuild et
make arch_build
make imperas_build
```

### Tüm testler timeout oluyor

```bash
# MAX_CYCLES artır
make isa MAX_CYCLES=100000
```

### Spike ve RTL uyuşmuyor

```bash
# Detaylı diff incele
cat results/logs/verilator/<test>/diff_visual_diff.log

# veya HTML
firefox results/logs/verilator/<test>/diff.html
```

## İlgili Dokümantasyon

- [Imperas Tests](imperas-tests.md) - Imperas test detayları
- [CoreMark Build](../COREMARK_BUILD.md) - CoreMark yapılandırması
- [RISC-V Tests](../riscv-test.md) - ISA test detayları
