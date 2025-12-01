---
title: "Ceres RISC-V Dokumentasyon"
description: "Ceres RISC-V Procesörü Kapsamlı Dökümantasyonu"
date: 2025-12-01
draft: false
---

# Ceres RISC-V Dokumentasyon

Ceres-RISC-V, RV32IMC komut setini destekleyen hafif ve modüler 32-bit RISC-V processor çekirdeğidir. Bu dökümantasyon, tasarım, kurulum, test ve debug konularında kapsamlı bilgi sunmaktadır.

## 📚 Dökümantasyon Yapısı

### Başlangıç
- **[Hızlı Başlangıç](./README.md)** - Temel kurulum ve çalıştırma
- **[Sistem Gereksinimleri](./TOOLS.md)** - Yazılım ve donanım gereksinimler

### Mimari & Tasarım
- **[Mimari Tasarım](./architecture.md)** ⭐ **YENİ** - Detaylı tasarım dökümantasyonu
  - Fetch, Decode, Execute, Memory, Write-Back aşamaları
  - Exception Priority sistemi
  - CSR ve İstisna Yönetimi
  - Cache Mimarisi
  - Debug & Trace

- **[İmplementasyon Özeti](./IMPLEMENTATION_SUMMARY.md)** - Parametrik Exception Priority
- **[MISA Parametrik Sistem](./defines.md)** - ISA uzantı tanımları

### Test & Validation
- **[Test Otomasyonu](./test/test-automation-summary.md)** - Test pipeline açıklaması
- **[RISC-V ISA Testleri](./riscv-test.md)** - ISA test kurulum ve çalıştırma
- **[CoreMark Build](./COREMARK_BUILD.md)** - Benchmark kurulum

### Gelişmiş Konular
- **[Exception Priority Detayları](./PARAMETRIC_EXCEPTION_PRIORITY.md)** - Derinlemesine teknik bilgi
- **[FENCE.I İmplementasyonu](./fence_i_implementation.md)** - Memory bariyerleri
- **[RAS (Return Address Stack)](./ras.md)** - Branch prediction
- **[RAD Guide](./rad_guide.md)** - RAM Access Debugging

### Ek Kaynaklar
- **[UART Test Rehberi](./CUSTOM_UART_TEST_GUIDE.md)** - Özel UART test yazma
- **[Hata Raporu 002](./bug_report_002.md)** - Bilinen sorunlar ve çözümler

## 🎯 Kullanım Senaryoları

### Tasarımı Anlamak İstiyorum
👉 Başla: [Mimari Tasarım](./architecture.md) → Bölüm 1-2

### Test Yazmak İstiyorum
👉 Başla: [Test Otomasyonu](./test/test-automation-summary.md) → [RISC-V ISA Testleri](./riscv-test.md)

### Debug Etmek İstiyorum
👉 Başla: [Mimari Tasarım](./architecture.md) Bölüm 14 → [RAD Guide](./rad_guide.md)

### Performans Optimize Etmek İstiyorum
👉 Başla: [İmplementasyon Özeti](./IMPLEMENTATION_SUMMARY.md) → [RAS](./ras.md)

### Exception Handling Öğrenmek İstiyorum
👉 Başla: [Mimari Tasarım](./architecture.md) Bölüm 8 → [Exception Priority](./PARAMETRIC_EXCEPTION_PRIORITY.md)

---

## 🚀 Hızlı Komutlar

### Build ve Run
```bash
# Verilator modeli derle
make verilator_build

# Hızlı test (~5 min)
make quick

# Tam regression (~30 min)
make full

# Coverage raporu
make coverage
```

### Test Çalıştırma
```bash
# ISA testleri
make test_isa

# Arch testleri
make test_arch

# Benchmark
make coremark
```

### Debug & Analiz
```bash
# Waveform (VCD) oluştur
make wave

# Trace almak
make trace

# HTML coverage raporu
firefox build/logs/coverage/index.html
```

---

## 📊 Test Kapsamı

| Test Kategorisi | Sayı | Durum |
|-----------------|------|-------|
| ISA Tests | 50 | ✅ Passing |
| Architecture Tests | 91 | ✅ Passing |
| CoreMark | 1 | ✅ Passing |
| Custom Tests | 20+ | ✅ Passing |
| **Toplam** | **160+** | **✅ All Pass** |

---

## 🔧 Sistem Mimarisi (Özet)

```
CPU Pipeline (5-stage):
┌──────────┬──────────┬──────────┬──────────┬──────────┐
│ Fetch    │ Decode   │ Execute  │ Memory   │Write-Back│
│   (IF)   │   (ID)   │   (EX)   │  (MEM)   │   (WB)   │
└──────────┴──────────┴──────────┴──────────┴──────────┘

Key Features:
✓ 32x32-bit Register File
✓ 4KB L1 Data Cache (2-way associative)
✓ RV32M (Multiply/Divide)
✓ RV32C (Compressed Instructions)
✓ Parametric Exception Priority
✓ Debug Trigger Support
✓ CSR Implementation
```

---

## 💡 Önemli Dosyalar

| Dosya | Amaç |
|-------|------|
| `rtl/core/` | Verilog tasarım dosyaları |
| `rtl/pkg/ceres_param.sv` | Parametrik tanımlar |
| `rtl/include/exception_priority.svh` | Exception priority configs |
| `sim/tb/` | Test bench dosyaları |
| `script/python/` | Python test scriptleri |
| `env/*/` | Simulasyon ortamları |

---

## 📞 Destek ve İletişim

### Belgeler
- **Issues & Bug Reports**: `docs/bug_report_002.md`
- **Technical Reference**: [RISC-V ISA Spec](https://riscv.org/)
- **Community**: [RISC-V Software Foundation](https://riscv.org/)

### Ceres Specific
- **GitHub Repo**: [level-v](https://github.com/yourusername/level-v)
- **License**: See `LICENSE` file

---

## 🎓 Öğrenme Yolu (Önerilen Sıra)

### Seviye 1: Temel Kullanıcı (1-2 gün)
1. [Hızlı Başlangıç](./README.md)
2. [Sistem Gereksinimleri](./TOOLS.md)
3. `make quick` çalıştır
4. Waveform'u GTKWave ile aç

### Seviye 2: Test Yazıcısı (1-2 hafta)
1. [Mimari Tasarım](./architecture.md) - Bölüm 1-3
2. [Test Otomasyonu](./test/test-automation-summary.md)
3. [RISC-V ISA Testleri](./riscv-test.md)
4. Kendi testini yaz

### Seviye 3: Tasarımcı (2-4 hafta)
1. [Mimari Tasarım](./architecture.md) - Tüm bölümler
2. [Exception Priority](./PARAMETRIC_EXCEPTION_PRIORITY.md)
3. [İmplementasyon Özeti](./IMPLEMENTATION_SUMMARY.md)
4. RTL kodu incele

### Seviye 4: Uzman (Devam eden)
1. RISC-V Spec'i oku
2. Verilator Dokumentasyonu
3. Tasarım optimize et
4. Yeni özellikler ekle

---

## 📝 Son Güncellemeler

- **1 Aralık 2025**: Detaylı Mimari Tasarım belgesi eklendi (`architecture.md`)
- **v1.0**: İlk Ceres releasesi

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025  
**Durum**: ✅ Aktif Geliştirme

