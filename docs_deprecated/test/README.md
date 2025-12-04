# Ceres-V Test Dokümantasyonu

Bu dizin, Ceres-V RISC-V işlemcisi için test altyapısı dokümantasyonunu içerir.

## İçerik

| Dosya | Açıklama |
|-------|----------|
| [test-automation.md](test-automation.md) | Genel test otomasyonu rehberi |
| [imperas-tests.md](imperas-tests.md) | Imperas RISC-V testleri entegrasyonu |
| [riscv-test/](riscv-test/) | RISC-V test detayları |

## Hızlı Referans

### Test Komutları

```bash
# Tüm ISA testleri
make isa

# Tüm benchmarklar
make bench

# Tüm arch testleri (M, C, Zicsr dahil)
make arch

# Imperas testleri (sadece I extension)
make imperas

# CoreMark
make cm
```

### Tekil Test

```bash
make t T=rv32ui-p-add      # ISA testi
make tb T=dhrystone        # Benchmark
make ta T=I-add-01         # Arch testi
make ti T=I-ADD-01         # Imperas testi
```

### Test Pipeline Kurulumu

```bash
make isa_auto      # ISA testleri hazırla
make arch_auto     # Arch testleri hazırla
make imperas_auto  # Imperas testleri hazırla
```

## Test Kapsamı

| Extension | ISA | Arch | Imperas | Benchmark |
|-----------|-----|------|---------|-----------|
| RV32I | ✅ | ✅ | ✅ | ✅ |
| M | ✅ | ✅ | ❌ | ✅ |
| C | ✅ | ✅ | ❌ | ❌ |
| Zicsr | ✅ | ✅ | ❌ | ❌ |
