---
title: "Başlangıç Rehberi"
description: "Ceres RISC-V Procesöründe Başlamak İçin Adım Adım Rehber"
date: 2025-12-01
draft: false
weight: 1
---

# Ceres RISC-V Başlangıç Rehberi

Bu rehber, Ceres RISC-V procesörü kullanmaya yeni başlayan kullanıcılar için adım adım talimatlar sunmaktadır.

---

## 📋 Ön Koşullar

### Yazılım Gereksinimleri

```bash
# 1. Verilator (Verilog simulator)
verilator --version  # 5.0 veya üzeri

# 2. RISC-V Toolchain
riscv32-unknown-elf-gcc --version

# 3. Python 3
python3 --version

# 4. Make
make --version

# 5. lcov (isteğe bağlı, coverage raporları için)
lcov --version
```

### Sistem Gereksinimleri

- **İşletim Sistemi**: Linux (Ubuntu 18.04+, Debian 10+) veya macOS
- **CPU**: Minimum 4 cores (önerilen 8+)
- **RAM**: Minimum 8 GB
- **Disk**: Minimum 5 GB boş alan

### Windows Kullanıcıları

Windows'ta çalıştırmak için WSL2 (Windows Subsystem for Linux 2) kullanınız:

```bash
# WSL2 Ubuntu kurulu olduğunu varsayarak
wsl --install -d Ubuntu-22.04
wsl -d Ubuntu-22.04
```

---

## 🔧 Kurulum Adımları

### Adım 1: Repository'i Klonla

```bash
git clone https://github.com/yourusername/level-v.git
cd level-v
```

### Adım 2: Bağımlılıkları Kur

```bash
# Ubuntu/Debian
sudo apt-get update
sudo apt-get install -y verilator riscv-gnu-toolchain python3 make lcov

# macOS (Homebrew)
brew install verilator riscv-gnu-toolchain python3 lcov
```

### Adım 3: Verilator Modelini Derle

```bash
make verilator_build
```

**Beklenen çıktı**:
```
Verilator RTL build successful
Build time: ~2-3 minutes
Output: build/obj_dir/Vceres_wrapper
```

### Adım 4: Hızlı Test Çalıştır

```bash
make quick
```

**Beklenen sonuç**:
```
Tests passing: 100%
Test execution time: ~5 minutes
```

---

## 🎯 Temel Kullanım

### Yapı Kodu (Build)

```bash
# Tüm bileşenleri derle
make build

# Verilator modelini derle
make verilator_build

# Python scriptlerini derle
make python_build
```

### Test Çalıştırma

```bash
# Hızlı test sürüsü (~5 min)
make quick

# Tam regression testi (~30 min)
make full

# Gece testleri (tüm testler, ~2 saat)
make nightly

# Belirli bir test kategorisi
make test_isa          # ISA testleri
make test_arch         # Architecture testleri
make coremark          # CoreMark benchmark
```

### Temizleme

```bash
# Derleme ürünlerini sil
make clean

# Tüm çıktıları sil (test sonuçları, loglar, vb)
make distclean

# Belirli klasörü temizle
make clean_build  # build/ klasörü
make clean_logs   # Logları sil
```

---

## 📊 Çıktı Analizi

### Test Sonuçları

```bash
# Tüm test sonuçlarını gör
cat build/logs/test_summary.log

# Başarısız testleri listele
grep -i "fail\|error" build/logs/test_summary.log

# Belirli test kategorisinin detaylarını gör
cat build/logs/isa_tests.log
```

### Waveform Analizi

```bash
# VCD dosyasını oluştur
make wave

# GTKWave ile görüntüle
gtkwave build/work/waveform.vcd &

# Alternatif: Surfer (ileri analiz)
surfer build/work/waveform.vcd &
```

### Coverage Raporu

```bash
# Coverage raporu oluştur
make coverage

# HTML raporu aç
firefox build/logs/coverage/index.html &

# Coverage özeti oku
cat build/logs/coverage/coverage.txt
```

---

## 💻 Komut Hızlı Referansı

| Komut | Açıklama | Süre |
|-------|----------|------|
| `make build` | Tüm derlemeleri yap | 5-10 min |
| `make quick` | Hızlı test sürüsü | 5 min |
| `make full` | Tam test sürüsü | 30 min |
| `make coverage` | Coverage raporu | 20 min |
| `make wave` | VCD oluştur | 2 min |
| `make clean` | Çıktıları temizle | <1 min |
| `make help` | Tüm komutları listele | — |
| `make help_lists` | Test komutlarını listele | — |

---

## 🐛 Sorun Giderme

### Sorun: "verilator: command not found"

**Çözüm**:
```bash
# Verilator'u kur
sudo apt-get install verilator

# Veya homebrew ile (macOS)
brew install verilator

# Path'i kontrol et
which verilator
```

### Sorun: "riscv32-unknown-elf-gcc: command not found"

**Çözüm**:
```bash
# RISC-V toolchain'i kur
sudo apt-get install riscv-gnu-toolchain

# Veya manuel indirme:
# https://github.com/riscv-collab/riscv-gnu-toolchain

# Path'i ekle (manuel kurulum durumunda)
export PATH=$PATH:/opt/riscv/bin
```

### Sorun: "make: command not found"

**Çözüm**:
```bash
# Build tools'u kur
sudo apt-get install build-essential

# macOS'ta:
brew install make
```

### Sorun: Test başarısız oluyor ("Tests failed")

**Çözüm**:
```bash
# 1. Clean build yap
make distclean
make verilator_build

# 2. İlk test'i çalıştır
make quick

# 3. Logları kontrol et
tail -100 build/logs/quick_test.log

# 4. Specific test'i debug mode'da çalıştır
./sim/test/run_single_test.sh test_name --verbose
```

### Sorun: "Out of memory" hatası

**Çözüm**:
```bash
# 1. Paralellizasyon'u azalt
make -j2 quick  # 2 job yerine

# 2. Veya sırayla çalıştır
make -j1 quick

# 3. Sistem belleğini kontrol et
free -h

# 4. Arka planda çalışan işlemleri kapat
killall firefox # Diğer heavy apps
```

---

## 📖 Sonraki Adımlar

### Test Yazıcılar İçin
1. [Test Otomasyonu Rehberi](../docs/test-automation.md)
2. [RISC-V ISA Testleri](../docs/riscv-test.md)
3. İlk test'ini yaz

### Tasarımcılar İçin
1. [Mimari Tasarım](../docs/architecture.md)
2. [Exception Priority](../docs/PARAMETRIC_EXCEPTION_PRIORITY.md)
3. RTL kodu incele (`rtl/core/`)

### Debug Etmek İsteyenler
1. [Debug Guide](../docs/debug.md)
2. [RAD Guide](../docs/rad_guide.md)
3. Breakpoint ayarla ve trace analiz et

---

## 🎓 Eğitim Kaynakları

### Öğrenme Yolu (Önerilen)

1. **Hafta 1**: Kurulum ve temel testler
   - Bölüm: Kurulum Adımları ✓
   - Bölüm: Temel Kullanım ✓
   - Bölüm: Çıktı Analizi

2. **Hafta 2**: Mimari anlaşılması
   - [Mimari Tasarım](../docs/architecture.md) - Bölüm 1-3
   - Pipeline aşamaları
   - Waveform analiziyle işletim gözleme

3. **Hafta 3**: Test yazma
   - [Test Otomasyonu](../docs/test-automation.md)
   - ISA testleri örneği
   - Kendi testini yaz

4. **Hafta 4+**: İleri konular
   - Exception handling
   - CSR operasyonları
   - Debug trigger'lar

### Mühendislik Kaynakları

```bash
# RISC-V Specifikasyonu
# https://riscv.org/specifications/

# Verilator Kullanım Kılavuzu
# https://verilator.org/guide/latest/

# RISC-V GNU Toolchain
# https://github.com/riscv-collab/riscv-gnu-toolchain
```

---

## ✅ Kontrol Listesi

Başlamadan önce aşağıdaki kutuları işaretleyin:

- [ ] Verilator kurulu (`verilator --version`)
- [ ] RISC-V Toolchain kurulu (`riscv32-unknown-elf-gcc --version`)
- [ ] Python 3 kurulu (`python3 --version`)
- [ ] Make kurulu (`make --version`)
- [ ] Repository klonlandı (`ls level-v`)
- [ ] Verilator model derlendi (`make verilator_build`)
- [ ] Hızlı test başarılı (`make quick`)

Tüm kutular işaretlendiyse, **Başlamaya hazırsınız!** 🎉

---

## 📞 Yardım ve Destek

### Sorun Raporlama

Bir sorunla karşılaşırsanız:

1. **Repository Issues**'ni kontrol edin: [Issues](https://github.com/yourusername/level-v/issues)
2. **Yeni issue oluşturun** şu bilgileri ekleyerek:
   - Kullanılan OS ve sürüm
   - Hata mesajının tam metni
   - Kullanılan komut
   - Adımlar (tekrar üretmek için)

### Katkı

Pull request'ler memnuniyetle karşılanır! Lütfen öncesinde bir issue açın.

---

## 📝 Notlar

- İlk derlemeler ~10 dakika sürebilir
- Daha sonraki derlemeler daha hızlı olacaktır (cached)
- WSL2'de rasgele yavaşlamalar olabilir (yavaşsa native Linux kullanın)

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025

