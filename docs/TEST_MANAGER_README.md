# CERES RISC-V Test Manager & Debug System

## 📋 İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Özellikler](#özellikler)
3. [Hızlı Başlangıç](#hızlı-başlangıç)
4. [Test Manager Kullanımı](#test-manager-kullanımı)
5. [Debug Rapor Sistemi](#debug-rapor-sistemi)
6. [Test Registry](#test-registry)
7. [Makefile Entegrasyonu](#makefile-entegrasyonu)
8. [Örnekler](#örnekler)
9. [Sorun Giderme](#sorun-giderme)

---

## 🎯 Genel Bakış

Bu sistem, CERES RISC-V projesi için geliştirilmiş modern bir test yönetim ve debug altyapısıdır. Temel özellikleri:

- **JSON Tabanlı Test Registry**: Tüm testleri merkezi bir JSON dosyasında yönetin
- **Python CLI Tool**: Testleri kolayca çalıştırın, listeleyin, ekleyin/çıkarın
- **Otomatik Debug Raporları**: Her test çalıştırması için detaylı debug raporu
- **Tag-Based Filtering**: Testleri etiketlere göre filtreleyip çalıştırın
- **Makefile Entegrasyonu**: Mevcut Makefile yapısıyla tam uyumlu

---

## ✨ Özellikler

### 1. Test Yönetimi
- ✅ Test suite'lerini JSON'da tanımlayın
- ✅ Testleri tag'lere göre gruplandırın
- ✅ Tek komutla test ekleyin/çıkarın
- ✅ Test listelerini filtreleyin
- ✅ Paralel test çalıştırma (gelecek)

### 2. Debug Raporları
- ✅ Her adımın detaylı kaydı
- ✅ Execution flow tracking
- ✅ File access monitoring
- ✅ Performance metrikleri
- ✅ Error/warning aggregation
- ✅ Rapor karşılaştırma

### 3. Makefile Entegrasyonu
- ✅ Geriye dönük uyumluluk
- ✅ Yeni test-manager target'ları
- ✅ Debug rapor görüntüleme target'ları
- ✅ Kolay debug aktif/pasif etme

---

## 🚀 Hızlı Başlangıç

### Adım 1: Test Listesi

Mevcut test suite'lerini görüntüleyin:

```bash
make -f Makefile.verilator test-list
```

### Adım 2: Test Çalıştırma

Tek bir test çalıştırın (debug aktif):

```bash
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

### Adım 3: Debug Raporunu Görüntüleme

Son debug raporunu görüntüleyin:

```bash
make -f Makefile.verilator debug-latest
```

---

## 📦 Test Manager Kullanımı

### Test Çalıştırma

#### Tek Test
```bash
# Makefile üzerinden
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add

# Doğrudan Python CLI
python3 script/python/test_manager.py run --test rv32ui-p-add

# Ek parametrelerle
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add MAX_CYCLES=50000
```

#### Test Suite
```bash
# ISA basic test suite
make -f Makefile.verilator test-run-suite SUITE=isa_basic

# Benchmark suite
make -f Makefile.verilator test-run-suite SUITE=benchmarks
```

#### Tag-Based Çalıştırma
```bash
# Quick testleri çalıştır
make -f Makefile.verilator test-run-tags TAGS=quick

# ISA ve compliance testleri
make -f Makefile.verilator test-run-tags TAGS=isa,compliance

# Benchmark testleri
make -f Makefile.verilator test-run-tags TAGS=benchmark
```

### Test Listeleme

```bash
# Tüm suite'leri listele
make -f Makefile.verilator test-list

# Belirli bir suite'deki testleri listele
make -f Makefile.verilator test-list SUITE=benchmarks

# Tag'e göre filtrele
make -f Makefile.verilator test-list TAGS=quick
```

### Test Ekleme/Çıkarma

```bash
# Yeni test ekle
make -f Makefile.verilator test-add \
    TEST_NAME=my_new_test \
    SUITE=custom_tests

# Konfigürasyon ile ekle
make -f Makefile.verilator test-add \
    TEST_NAME=my_test \
    SUITE=custom_tests \
    CONFIG=script/config/tests/custom.json

# Test çıkar
make -f Makefile.verilator test-remove TEST_NAME=my_test
```

---

## 🔍 Debug Rapor Sistemi

### Debug Raporu Yapısı

Her test çalıştırmasında otomatik olarak oluşturulan debug raporu şunları içerir:

```json
{
  "metadata": {
    "test_name": "rv32ui-p-add",
    "timestamp": "2025-12-13T14:30:22",
    "git_commit": "1b39651",
    "session_id": "a7f3d9e2"
  },
  "execution_flow": [
    {
      "step": 1,
      "type": "makefile_target",
      "name": "build",
      "command": "verilator --cc ...",
      "duration_ms": 5432,
      "exit_code": 0
    }
  ],
  "result": {
    "status": "PASSED",
    "duration_total_ms": 17777
  }
}
```

### Debug Raporu Görüntüleme

```bash
# En son raporu görüntüle
make -f Makefile.verilator debug-latest

# Belirli test için son raporu görüntüle
make -f Makefile.verilator debug-latest TEST_NAME=rv32ui-p-add

# Belirli bir raporu görüntüle
make -f Makefile.verilator debug-view \
    REPORT=build/debug_reports/run_20251213_143022_rv32ui-p-add.json

# Sadece hataları göster
make -f Makefile.verilator debug-errors TEST_NAME=rv32ui-p-add

# Özet istatistikleri göster
make -f Makefile.verilator debug-summary TEST_NAME=rv32ui-p-add
```

### Rapor Karşılaştırma

İki farklı çalıştırmayı karşılaştırın:

```bash
make -f Makefile.verilator debug-compare \
    REPORT1=build/debug_reports/run_20251213_143022_rv32ui-p-add.json \
    REPORT2=build/debug_reports/run_20251213_150000_rv32ui-p-add.json
```

### Debug Rapor Listesi

```bash
# Tüm debug raporlarını listele
make -f Makefile.verilator debug-list

# Debug raporlarını temizle
make -f Makefile.verilator debug-clean
```

### Debug'ı Devre Dışı Bırakma

```bash
# Debug olmadan test çalıştır
DEBUG_ENABLE=0 make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add

# Python CLI'da
python3 script/python/test_manager.py run --test rv32ui-p-add --no-debug
```

---

## 📝 Test Registry

Test registry dosyası: `script/config/test_registry.json`

### Yapı

```json
{
  "test_suites": {
    "isa_basic": {
      "description": "Basic RISC-V ISA compliance tests",
      "config": "script/config/tests/default.json",
      "flist": "sim/test/riscv_test_list.flist",
      "tags": ["isa", "compliance", "quick"],
      "enabled": true
    },
    "benchmarks": {
      "description": "Performance benchmarks",
      "tests": {
        "coremark": {
          "description": "CoreMark CPU benchmark",
          "config": "script/config/tests/coremark.json",
          "tags": ["benchmark", "performance", "slow"],
          "enabled": true,
          "max_cycles": 50000000
        }
      }
    }
  }
}
```

### Yeni Suite Ekleme

`test_registry.json` dosyasını düzenleyin:

```json
{
  "test_suites": {
    "my_custom_suite": {
      "description": "My custom test suite",
      "config": "script/config/tests/custom.json",
      "flist": "sim/test/custom_tests.flist",
      "tags": ["custom", "experimental"],
      "enabled": true
    }
  }
}
```

### Tag Groups

Mantıksal tag grupları tanımlayın:

```json
{
  "tag_groups": {
    "quick": {
      "description": "Fast tests for quick validation",
      "includes": ["isa", "quick"]
    },
    "full": {
      "description": "Full regression suite",
      "includes": ["isa", "compliance", "arch", "benchmark"]
    }
  }
}
```

---

## 🔧 Makefile Entegrasyonu

### Yeni Target'lar

#### Test Manager
- `test-run` - Tek test çalıştır
- `test-run-suite` - Suite çalıştır
- `test-run-tags` - Tag'e göre testler çalıştır
- `test-list` - Testleri listele
- `test-add` - Test ekle
- `test-remove` - Test çıkar

#### Debug Reports
- `debug-latest` - Son raporu göster
- `debug-view` - Belirli raporu göster
- `debug-errors` - Sadece hataları göster
- `debug-summary` - Özet göster
- `debug-compare` - İki raporu karşılaştır
- `debug-list` - Tüm raporları listele
- `debug-clean` - Raporları temizle

### Mevcut Target'larla Uyumluluk

Eski tüm target'lar çalışmaya devam eder:

```bash
# Eski yöntem - hala çalışır
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add
make -f Makefile.verilator isa
make -f Makefile.verilator verilator-coremark

# Yeni yöntem - debug ile
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
make -f Makefile.verilator test-run-suite SUITE=isa_basic
```

---

## 📚 Örnekler

### Örnek 1: Quick Validation

Hızlı doğrulama için quick testleri çalıştırın:

```bash
# Quick testleri listele
make -f Makefile.verilator test-list TAGS=quick

# Quick testleri çalıştır
make -f Makefile.verilator test-run-tags TAGS=quick

# Sonucu görüntüle
make -f Makefile.verilator debug-latest
```

### Örnek 2: Performance Benchmark

Benchmark testleri çalıştırıp sonuçları karşılaştırın:

```bash
# İlk çalıştırma
make -f Makefile.verilator test-run TEST_NAME=coremark

# Rapor dosyasını kaydet
REPORT1=$(ls -t build/debug_reports/run_*_coremark.json | head -1)

# Optimizasyon sonrası ikinci çalıştırma
make -f Makefile.verilator test-run TEST_NAME=coremark MODE=release

# İkinci raporu kaydet
REPORT2=$(ls -t build/debug_reports/run_*_coremark.json | head -1)

# Karşılaştır
make -f Makefile.verilator debug-compare REPORT1=$REPORT1 REPORT2=$REPORT2
```

### Örnek 3: Hata Ayıklama

Test başarısız olduğunda debug raporunu kullanın:

```bash
# Test çalıştır (başarısız olsun)
make -f Makefile.verilator test-run TEST_NAME=problematic_test

# Sadece hataları göster
make -f Makefile.verilator debug-errors TEST_NAME=problematic_test

# Tam raporu görüntüle
make -f Makefile.verilator debug-latest TEST_NAME=problematic_test

# Log dosyalarını kontrol et
# Debug raporu hangi dosyaların oluşturulduğunu gösterir
```

### Örnek 4: Yeni Test Ekleme

```bash
# 1. Testi registry'ye ekle
make -f Makefile.verilator test-add \
    TEST_NAME=my_custom_test \
    SUITE=custom_tests \
    CONFIG=script/config/tests/custom.json

# 2. Test dosyalarını hazırla
# - ELF dosyası: build/tests/.../my_custom_test.elf
# - MEM dosyası: build/tests/.../my_custom_test.mem

# 3. Testi çalıştır
make -f Makefile.verilator test-run TEST_NAME=my_custom_test

# 4. Sonucu kontrol et
make -f Makefile.verilator debug-latest TEST_NAME=my_custom_test
```

---

## 🐛 Sorun Giderme

### Debug Raporu Oluşturulmuyor

**Sorun**: Debug raporu oluşturulmuyor.

**Çözüm**:
```bash
# DEBUG_ENABLE'ın aktif olduğunu kontrol edin
echo $DEBUG_ENABLE  # 1 olmalı

# Veya açıkça belirtin
DEBUG_ENABLE=1 make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add

# Python modüllerini kontrol edin
python3 -c "from script.python.debug_logger import DebugLogger; print('OK')"
```

### Test Registry Bulunamıyor

**Sorun**: `Error: Test registry not found`

**Çözüm**:
```bash
# Registry dosyasının varlığını kontrol edin
ls -la script/config/test_registry.json

# Eğer yoksa, şablonu kullanın
cp script/config/test_registry.json.example script/config/test_registry.json
```

### Test Bulunamıyor

**Sorun**: Test suite veya test bulunamıyor.

**Çözüm**:
```bash
# Mevcut testleri listeleyin
make -f Makefile.verilator test-list

# Belirli suite'i kontrol edin
make -f Makefile.verilator test-list SUITE=isa_basic

# Registry dosyasını kontrol edin
cat script/config/test_registry.json | jq '.test_suites'
```

### Python Import Hatası

**Sorun**: `ImportError: No module named 'psutil'`

**Çözüm**:
```bash
# Gerekli Python paketlerini yükleyin
pip3 install psutil

# Veya requirements.txt varsa
pip3 install -r requirements.txt
```

### Makefile Target Çalışmıyor

**Sorun**: Yeni target'lar tanınmıyor.

**Çözüm**:
```bash
# Makefile.verilator'ın güncellendiğinden emin olun
grep -n "test-run:" Makefile.verilator

# Make cache'i temizleyin
make -f Makefile.verilator clean

# Doğru makefile'ı kullandığınızdan emin olun
make -f Makefile.verilator help | grep test-run
```

---

## 🔗 İlgili Dosyalar

### Python Scripts
- `script/python/test_manager.py` - Ana test manager CLI
- `script/python/debug_logger.py` - Debug logging kütüphanesi
- `script/python/debug_viewer.py` - Debug rapor görüntüleyici

### Konfigürasyon
- `script/config/test_registry.json` - Test registry
- `script/config/test_registry.schema.json` - Registry schema
- `script/config/tests/*.json` - Test suite konfigürasyonları

### Makefile
- `Makefile.verilator` - Ana Verilator makefile (güncellenmiş)

### Dokümantasyon
- `docs/TEST_MANAGER_README.md` - Bu dosya

---

## 📞 Destek

Sorunlarınız veya önerileriniz için:

1. Debug raporunu inceleyin: `make debug-latest`
2. Log dosyalarını kontrol edin: `build/debug_reports/*/`
3. Test registry'yi doğrulayın: `cat script/config/test_registry.json | jq`

---

## 🎉 Sonuç

Bu sistem ile artık:

✅ Testlerinizi merkezi bir yerden yönetebilirsiniz
✅ Her test çalıştırmasının detaylı kaydını tutabilirsiniz
✅ Sorunları hızlıca tespit edip çözebilirsiniz
✅ Test ekleme/çıkarma işlemlerini saniyeler içinde yapabilirsiniz
✅ Mevcut iş akışınızı bozmadan yeni özellikleri kullanabilirsiniz

**İyi testler! 🚀**
