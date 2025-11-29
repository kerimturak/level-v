# CERES RISC-V — Development Tools Guide

Bu döküman, CERES RISC-V projesinde kullanılan açık kaynak geliştirme araçlarını, kurulumlarını ve kullanım örneklerini açıklar.

---

## 📊 Araç Özeti

| Araç | Kategori | Güçlülük | Lisans | Açıklama |
|------|----------|:--------:|--------|----------|
| **Verilator** | Simülasyon | ⭐⭐⭐⭐⭐ | LGPL | En hızlı açık kaynak RTL simülatörü |
| **Spike** | RISC-V ISS | ⭐⭐⭐⭐⭐ | BSD | Resmi RISC-V referans simülatörü |
| **Slang (pyslang)** | Linting | ⭐⭐⭐⭐⭐ | MIT | En kapsamlı SV parser/linter |
| **Yosys** | Sentez | ⭐⭐⭐⭐⭐ | ISC | RTL sentez framework |
| **svlint** | Linting | ⭐⭐⭐⭐ | MIT | Hızlı SV stil linter |
| **GTKWave** | Waveform | ⭐⭐⭐⭐ | GPL | Olgun VCD/FST viewer |
| **Surfer** | Waveform | ⭐⭐⭐⭐ | MIT | Modern, GPU-hızlandırmalı viewer |
| **Icarus Verilog** | Simülasyon | ⭐⭐⭐ | GPL | Basit Verilog simülatörü |

> **Güçlülük Skalası:** ⭐ Temel → ⭐⭐⭐⭐⭐ Profesyonel

---

## 🚀 Simülasyon Araçları

### Verilator (Önerilen)

**Versiyon:** 5.026  
**Güçlülük:** ⭐⭐⭐⭐⭐  
**Website:** https://verilator.org

Verilator, SystemVerilog/Verilog RTL'i C++/SystemC'ye derleyen en hızlı açık kaynak simülatördür.

#### Özellikler
- ✅ SystemVerilog 2017 desteği
- ✅ Çok iş parçacıklı simülasyon
- ✅ Lint ve statik analiz
- ✅ Coverage analizi
- ✅ FST/VCD waveform çıktısı
- ✅ C++ testbench entegrasyonu

#### Kurulum
```bash
# Ubuntu 24.04
sudo apt install verilator

# Kaynak koddan (önerilen, daha güncel)
git clone https://github.com/verilator/verilator
cd verilator && git checkout v5.026
autoconf && ./configure --prefix=/opt/verilator
make -j$(nproc) && sudo make install
```

#### Kullanım
```bash
make verilate                    # Model derle
make run_verilator TEST_NAME=rv32ui-p-add
make verilator_static            # Lint kontrolü
```

---

### Spike (RISC-V ISS)

**Güçlülük:** ⭐⭐⭐⭐⭐  
**Website:** https://github.com/riscv-software-src/riscv-isa-sim

Resmi RISC-V Instruction Set Simulator. Golden model olarak kullanılır.

#### Özellikler
- ✅ Tüm RISC-V ISA uzantıları
- ✅ Commit trace log çıktısı
- ✅ Interactive debugging
- ✅ Memory model desteği

#### Kullanım
```bash
make spike TEST_NAME=rv32ui-p-add   # Spike ile çalıştır
make compare_logs                    # RTL vs Spike karşılaştır
```

---

### Icarus Verilog

**Güçlülük:** ⭐⭐⭐  
**Website:** http://iverilog.icarus.com

Basit Verilog simülatörü. **Not:** CERES RTL'i Icarus ile uyumlu değildir (advanced SV özellikleri kullanıyor).

#### Sınırlamalar
- ❌ `inside` operatörü desteklenmiyor
- ❌ `automatic` değişkenler sınırlı
- ❌ Struct parametreleri desteklenmiyor

#### Kurulum
```bash
sudo apt install iverilog gtkwave
```

---

## 🔍 Linting Araçları

### Slang (pyslang)

**Versiyon:** 9.1.0  
**Güçlülük:** ⭐⭐⭐⭐⭐  
**Website:** https://sv-lang.com

En kapsamlı SystemVerilog parser ve linter. IEEE 1800-2023 tam uyumlu.

#### Özellikler
- ✅ Tam SV 2023 desteği
- ✅ Semantik analiz
- ✅ Type checking
- ✅ 200+ lint kuralı
- ✅ Python bindings (pyslang)

#### Kurulum
```bash
pip install pyslang
# veya
make lint_install
```

#### Kullanım
```bash
make slang_lint      # Lint çalıştır
make slang_check     # Detaylı analiz
```

#### Örnek Çıktı
```
rtl/core/cpu.sv:182:78: error: no implicit conversion from 'int' to 'spec_type_e'
rtl/core/cpu.sv:309:16: warning: 'case' marked 'unique' has 'default' label
```

---

### svlint

**Versiyon:** 0.9.5  
**Güçlülük:** ⭐⭐⭐⭐  
**Website:** https://github.com/dalance/svlint

Hızlı SystemVerilog stil ve naming linter. Rust tabanlı.

#### Özellikler
- ✅ Hızlı çalışma
- ✅ TOML konfigürasyon
- ✅ Özelleştirilebilir kurallar
- ✅ CI/CD uyumlu

#### Kurulum
```bash
make lint_install
# veya
cargo install svlint
```

#### Kullanım
```bash
make svlint          # Lint çalıştır
```

#### Konfigürasyon (.svlint.toml)
```toml
[option]
exclude_paths = ["subrepo/", "build/"]

[rules]
prefix_module = false
style_keyword_1space = true
case_default = true
```

---

### Verilator Lint

**Güçlülük:** ⭐⭐⭐⭐  

Verilator'ın dahili lint özelliği.

#### Kullanım
```bash
make verilator_static    # Statik analiz
```

---

## 📊 Waveform Viewer

### GTKWave

**Güçlülük:** ⭐⭐⭐⭐  
**Website:** http://gtkwave.sourceforge.net

Olgun ve yaygın kullanılan waveform viewer.

#### Özellikler
- ✅ VCD, FST, LXT2 desteği
- ✅ TCL scripting
- ✅ Signal search
- ✅ Analog waveform

#### Kurulum
```bash
sudo apt install gtkwave
```

#### Kullanım
```bash
make gtkwave                    # Son waveform'u aç
make run_verilator TRACE=1      # Trace ile simülasyon
```

---

### Surfer

**Güçlülük:** ⭐⭐⭐⭐  
**Website:** https://surfer-project.org

Modern, GPU-hızlandırmalı waveform viewer. Rust tabanlı.

#### Özellikler
- ✅ GPU hızlandırma
- ✅ Modern UI
- ✅ Hızlı büyük dosya yükleme
- ✅ VCD, FST, GHW desteği

#### Kurulum
```bash
make surfer_install
# veya
cargo install --git https://gitlab.com/surfer-project/surfer surfer
```

#### Kullanım
```bash
make surfer                     # Waveform aç
make surfer_file WAVE_FILE=path # Belirli dosya aç
make wave_compare               # GTKWave vs Surfer karşılaştır
```

---

## 🔨 Sentez Araçları

### Yosys

**Güçlülük:** ⭐⭐⭐⭐⭐  
**Website:** https://yosyshq.net/yosys

Açık kaynak RTL sentez framework.

#### Özellikler
- ✅ Verilog/SystemVerilog parsing
- ✅ Çeşitli optimizasyon geçişleri
- ✅ FPGA ve ASIC hedefleri
- ✅ Formal verification desteği

#### Kurulum
```bash
sudo apt install yosys
```

#### Kullanım
```bash
make yosys_check                # Sentez kontrolü
make yosys_synth                # Tam sentez
```

---

## 🧪 Test Framework

### riscv-tests

Resmi RISC-V ISA test suite.

```bash
make isa                        # Tüm ISA testlerini çalıştır
make t T=rv32ui-p-add           # Tek test
```

### riscv-arch-test

RISC-V mimari uyumluluk testleri.

```bash
make arch                       # Tüm arch testlerini çalıştır
```

### CoreMark

Gömülü sistem benchmark.

```bash
make cm                         # CoreMark çalıştır
```

---

## 📋 Hızlı Başvuru Tablosu

| Komut | Açıklama |
|-------|----------|
| `make verilate` | Verilator modeli derle |
| `make run_verilator TEST_NAME=...` | Simülasyon çalıştır |
| `make svlint` | svlint çalıştır |
| `make slang_lint` | Slang lint çalıştır |
| `make lint_all` | Tüm linterları çalıştır |
| `make lint_install` | Lint araçlarını kur |
| `make gtkwave` | GTKWave aç |
| `make surfer` | Surfer aç |
| `make yosys_check` | Yosys sentez kontrolü |
| `make isa` | ISA testlerini çalıştır |
| `make html` | Test dashboard oluştur |

---

## 🔧 Sorun Giderme

### Verilator Hataları

**BLKLOOPINIT hatası:**
```bash
# verilator.mk'de --Wno-BLKLOOPINIT eklendi
```

**VL_SYSTEM_IN hatası:**
```bash
# Verilator 5.026'ya yükseltin
```

### svlint Konfigürasyon Hatası
```bash
# .svlint.toml dosyasını kontrol edin
# Geçersiz kural isimleri olabilir
```

### pyslang Import Hatası
```bash
pip install --upgrade pyslang
```

---

## 📚 Ek Kaynaklar

- [Verilator Manual](https://verilator.org/guide/latest/)
- [Slang Documentation](https://sv-lang.com/)
- [svlint Manual](https://github.com/dalance/svlint/blob/master/MANUAL.md)
- [Yosys Manual](https://yosyshq.readthedocs.io/)
- [RISC-V Specifications](https://riscv.org/technical/specifications/)

---

*Son güncelleme: Kasım 2025*
