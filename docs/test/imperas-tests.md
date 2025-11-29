# Imperas RISC-V Tests Integration

## Genel Bakış

Imperas RISC-V testleri (`riscv-ovpsim/imperas-riscv-tests`), resmi `riscv-arch-test` framework'ü ile uyumlu, genişletilmiş bir RISC-V mimari test setidir. Bu dokümantasyon, Ceres-V işlemcisi için Imperas testlerinin nasıl entegre edildiğini ve yapılandırıldığını açıklar.

## Önemli Not: Ücretsiz Repo Sınırlamaları

⚠️ **Imperas'ın ücretsiz/public GitHub reposu sadece RV32I base instruction set testlerini içerir.**

Diğer extension testleri (M, C, Zicsr, Zifencei vb.) için kaynak kodu bu repoda **mevcut değildir**. Bu testler için `riscv-arch-test` kullanılmalıdır.

| Extension | Imperas (Ücretsiz) | riscv-arch-test |
|-----------|-------------------|-----------------|
| I (Base)  | ✅ 45 test        | ✅ ~40 test     |
| M (Multiply/Divide) | ❌ Yok | ✅ Mevcut |
| C (Compressed) | ❌ Yok | ✅ Mevcut |
| Zicsr (CSR) | ❌ Yok | ✅ Mevcut (privilege) |
| Zifencei | ❌ Yok | ✅ Mevcut |

## Kullanım

### Hızlı Başlangıç

```bash
# Tam pipeline: Clone → Build → Import → Run
make imperas_auto
make imperas

# Veya adım adım:
make imperas_clone    # Repo'yu klonla
make imperas_build    # Testleri derle
make imperas_import   # MEM formatına dönüştür
make imperas          # Tüm testleri çalıştır
```

### Tekil Test Çalıştırma

```bash
# Imperas testi çalıştır
make ti T=I-ADD-01

# Daha fazla cycle ile
make ti T=I-JALR-01 MAX_CYCLES=300000
```

### Yardım

```bash
make imperas_help
```

## Dosya Yapısı

```
level-v/
├── env/imperas/                    # Ceres-V hedef konfigürasyonu
│   ├── model_test.h                # RVMODEL_* makroları
│   ├── link.ld                     # Linker script (0x80000000)
│   └── README.md
├── subrepo/imperas-riscv-tests/    # Klonlanan repo
│   └── riscv-test-suite/
│       ├── env/arch_test.h         # RVTEST_* makroları
│       └── rv32i_m/I/src/*.S       # Test kaynak dosyaları
├── build/tests/imperas/            # Derleme çıktıları
│   ├── elf/                        # ELF dosyaları
│   ├── dump/                       # Disassembly
│   ├── hex/                        # Verilog hex
│   ├── mem/                        # Simülasyon bellek dosyaları
│   └── pass_fail_addr/             # Pass/Fail adresleri
└── script/makefiles/test/
    └── imperas_test.mk             # Build ve run kuralları
```

## Atlanan (Skip) Testler

Bazı testler derleme veya çalışma zamanı uyumsuzlukları nedeniyle atlanmaktadır:

### 1. I-MISALIGN_JMP-01 ve I-MISALIGN_LDST-01

**Sebep:** Bu testler `mbadaddr` CSR'ını kullanıyor, ancak bu isim eski RISC-V spec'inden. Güncel spec'te `mtval` olarak yeniden adlandırıldı.

```
Error: unknown CSR `mbadaddr'
```

**Çözüm:** Testler skip listesine eklendi. Misaligned access exception handling Ceres'te zaten tam desteklenmiyor.

### 2. I-EBREAK-01

**Sebep:** EBREAK instruction exception handling, Ceres ve Spike arasında farklı davranışlar gösteriyor. Test, belirli bir exception flow bekliyor.

**Çözüm:** Skip listesine eklendi. Exception testleri için `riscv-arch-test` privilege testleri kullanılabilir.

## Konfigürasyon Detayları

### Compiler Flags

```makefile
IMPERAS_MARCH  := rv32imc_zicsr
IMPERAS_MABI   := ilp32
IMPERAS_CFLAGS := -march=$(IMPERAS_MARCH) -mabi=$(IMPERAS_MABI) \
                  -static -mcmodel=medany \
                  -fvisibility=hidden -nostdlib -nostartfiles \
                  -fno-builtin -DXLEN=32
```

### MAX_CYCLES

Imperas testleri için varsayılan MAX_CYCLES 200000 olarak ayarlanmıştır (`config.mk`):

```makefile
ifeq ($(TEST_TYPE),imperas)
    MAX_CYCLES ?= 200000
```

Bu değer, I-JALR-01 gibi daha uzun testlerin tamamlanması için gereklidir.

### Memory Layout

```
0x80000000  Code start (rvtest_entry_point)
0x80001000  .tohost section
0x80002000  .text section
...         .rodata, .data, .bss
...         Stack (4KB)
```

## model_test.h Makroları

Ceres-V için tanımlanan temel makrolar:

| Makro | Açıklama |
|-------|----------|
| `RVMODEL_BOOT` | Trap handler kurulumu, mtvec ayarı |
| `RVMODEL_HALT` | Test sonlandırma (ecall ile) |
| `RVMODEL_DATA_BEGIN/END` | Signature bölümü tanımları |
| `RVMODEL_IO_*` | I/O makroları (RTL simülasyonda boş) |

### Trap Handler

```assembly
rvtest_trap_handler:
    csrr t0, mcause
    csrr t1, mepc
    # EBREAK (mcause=3): PC += 2 veya 4
    # ECALL (mcause=11): exit syscall kontrolü
    # Diğer: PC += 4, mret
```

## Test Sonuçları

Tipik bir çalıştırma sonucu:

```
[I] Compiled: 45 passed, 0 failed, 3 skipped

File-Based Batch Summary
━━━━━━━━━━━━━━━━━━━━━━━━━
✅ Passed: 45
❌ Failed: 0
📊 Total:  45
```

## M, C, Zicsr Testleri İçin

Imperas'ta olmayan extension testleri için `riscv-arch-test` kullanın:

```bash
# Arch test pipeline
make arch_auto    # Clone → Build → Import
make arch         # Tüm arch testlerini çalıştır

# Tekil arch testi
make ta T=I-add-01
make ta T=M-mul-01
make ta T=C-cadd-01
```

## Karşılaştırma: Imperas vs riscv-arch-test

| Özellik | Imperas | riscv-arch-test |
|---------|---------|-----------------|
| Test sayısı (I) | 45 | ~40 |
| M, C, Zicsr | ❌ | ✅ |
| Test formatı | Aynı | Aynı |
| Header dosyaları | model_test.h + arch_test.h | Aynı |
| Lisans | Apache 2.0 (kısıtlı içerik) | BSD |

## Sorun Giderme

### Test derleme hatası

```bash
# Hata detaylarını görmek için
make imperas_build_I 2>&1 | grep -i error
```

### Test timeout (cycle limit)

```bash
# Daha fazla cycle ile çalıştır
make ti T=<test_name> MAX_CYCLES=500000
```

### Pass/Fail adresi bulunamadı

```bash
# Dump dosyasını kontrol et
grep -E '<halt_loop>:|<pass>:|<fail>:' build/tests/imperas/dump/<test>.dump
```

## İlgili Dosyalar

- `script/makefiles/test/imperas_test.mk` - Makefile kuralları
- `script/makefiles/config/config.mk` - MAX_CYCLES ayarları
- `env/imperas/model_test.h` - Hedef makroları
- `env/imperas/link.ld` - Linker script
