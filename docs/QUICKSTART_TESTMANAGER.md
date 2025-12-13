# 🚀 Test Manager - Hızlı Başlangıç Kılavuzu

## 5 Dakikada Test Manager

### 1️⃣ Test Listesini Görüntüle

```bash
make -f Makefile.verilator test-list
```

**Çıktı:**
```
Available Test Suites:

  ✓ isa_basic            ( 51 tests) - Basic RISC-V ISA compliance tests
  ✓ benchmarks           (  2 tests) - Performance benchmarks
  ✓ branch_tests         (  8 tests) - Branch predictor tests
  ...
```

### 2️⃣ İlk Testini Çalıştır

```bash
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

**Ne olur?**
- Test çalıştırılır ✅
- Debug raporu otomatik oluşturulur 📝
- Sonuç ekrana yazılır ✅/✗

### 3️⃣ Debug Raporunu Görüntüle

```bash
make -f Makefile.verilator debug-latest
```

**Çıktı:**
```
================================================================================
DEBUG REPORT: rv32ui-p-add
================================================================================

Metadata:
  Test:        rv32ui-p-add
  Timestamp:   2025-12-13T14:30:22
  Session ID:  a7f3d9e2

Result:
  Status:      PASSED
  Duration:    17.78s

Execution Flow:
─────────────────────────────────────────────────────────────
  ✓ Step 1: run_test
    Type:     makefile_target
    Duration: 17.78s
```

---

## 🎯 Yaygın Kullanım Senaryoları

### Scenario 1: Hızlı Doğrulama

```bash
# Quick testleri çalıştır
make -f Makefile.verilator test-run-tags TAGS=quick

# Sonucu kontrol et
make -f Makefile.verilator debug-summary
```

### Scenario 2: Benchmark Çalıştır

```bash
# CoreMark benchmark
make -f Makefile.verilator test-run TEST_NAME=coremark

# Sonuçları karşılaştır
make -f Makefile.verilator debug-latest TEST_NAME=coremark
```

### Scenario 3: Tüm ISA Testleri

```bash
# ISA basic suite'ini çalıştır
make -f Makefile.verilator test-run-suite SUITE=isa_basic

# Başarısız testleri göster
make -f Makefile.verilator debug-errors
```

### Scenario 4: Yeni Test Ekle

```bash
# 1. Testi ekle
make -f Makefile.verilator test-add \
    TEST_NAME=my_test \
    SUITE=custom_tests

# 2. Test dosyalarını hazırla (manuel)
# - my_test.elf
# - my_test.mem

# 3. Çalıştır
make -f Makefile.verilator test-run TEST_NAME=my_test
```

---

## 📊 Debug Raporları

### Son Raporu Görüntüle
```bash
make -f Makefile.verilator debug-latest
```

### Sadece Hataları Göster
```bash
make -f Makefile.verilator debug-errors TEST_NAME=rv32ui-p-add
```

### Özet İstatistikler
```bash
make -f Makefile.verilator debug-summary TEST_NAME=rv32ui-p-add
```

### İki Çalıştırmayı Karşılaştır
```bash
make -f Makefile.verilator debug-compare \
    REPORT1=build/debug_reports/run_20251213_143022_test1.json \
    REPORT2=build/debug_reports/run_20251213_150000_test1.json
```

### Tüm Raporları Listele
```bash
make -f Makefile.verilator debug-list
```

---

## 🔧 Parametreler

### Test Çalıştırma Parametreleri

| Parametre | Açıklama | Örnek |
|-----------|----------|-------|
| `TEST_NAME` | Test adı | `TEST_NAME=rv32ui-p-add` |
| `SUITE` | Test suite | `SUITE=isa_basic` |
| `TAGS` | Tag listesi | `TAGS=quick,isa` |
| `MAX_CYCLES` | Maksimum cycle | `MAX_CYCLES=50000` |
| `NO_TRACE` | Trace devre dışı | `NO_TRACE=1` |
| `MODE` | Build modu | `MODE=release` |
| `DEBUG_ENABLE` | Debug aktif/pasif | `DEBUG_ENABLE=0` |

### Örnekler

```bash
# Maksimum cycle ayarla
make -f Makefile.verilator test-run \
    TEST_NAME=rv32ui-p-add \
    MAX_CYCLES=10000

# Trace olmadan çalıştır (daha hızlı)
make -f Makefile.verilator test-run \
    TEST_NAME=rv32ui-p-add \
    NO_TRACE=1

# Release modunda çalıştır
make -f Makefile.verilator test-run \
    TEST_NAME=rv32ui-p-add \
    MODE=release

# Debug raporlama olmadan
DEBUG_ENABLE=0 make -f Makefile.verilator test-run \
    TEST_NAME=rv32ui-p-add
```

---

## 📁 Önemli Dosyalar

### Konfigürasyon
- `script/config/test_registry.json` - Test veritabanı
- `script/config/tests/*.json` - Test suite ayarları

### Debug Raporları
- `build/debug_reports/run_*.json` - Debug raporları
- `build/debug_reports/latest_*.json` - Son rapor linkleri

### Log Dosyaları
- `build/log/verilator/TEST_NAME/` - Test logları
- `build/debug_reports/TIMESTAMP_TEST/step*.log` - Adım logları

---

## ⚡ Pro Tips

### Tip 1: Alias Kullanın

```bash
# .bashrc veya .zshrc'ye ekleyin
alias vtest='make -f Makefile.verilator test-run TEST_NAME='
alias vlist='make -f Makefile.verilator test-list'
alias vdebug='make -f Makefile.verilator debug-latest'

# Kullanım
vtest rv32ui-p-add
vlist TAGS=quick
vdebug
```

### Tip 2: Tag Kombinasyonları

```bash
# Hızlı ve ISA testleri
make -f Makefile.verilator test-run-tags TAGS=quick,isa

# Benchmark testleri
make -f Makefile.verilator test-run-tags TAGS=benchmark

# Compliance testleri
make -f Makefile.verilator test-run-tags TAGS=compliance
```

### Tip 3: Debug Raporlarını Analiz Etme

```bash
# JSON raporunu direkt okuma
cat build/debug_reports/latest_rv32ui-p-add.json | jq '.result'

# En yavaş adımları bulma
cat build/debug_reports/latest_rv32ui-p-add.json | \
    jq '.execution_flow | sort_by(.duration_ms) | reverse | .[0:3]'

# Hataları çıkarma
cat build/debug_reports/latest_rv32ui-p-add.json | \
    jq '.result.errors'
```

### Tip 4: Batch İşlemler

```bash
# Tüm ISA testlerini çalıştırıp rapor oluştur
for tag in isa_basic isa_compressed isa_multiply; do
    make -f Makefile.verilator test-run-suite SUITE=$tag
    make -f Makefile.verilator debug-summary
done
```

---

## 🐛 Hızlı Sorun Giderme

### Test Bulunamadı
```bash
# Önce test listesini kontrol edin
make -f Makefile.verilator test-list

# Registry'de var mı?
cat script/config/test_registry.json | jq '.test_suites'
```

### Debug Raporu Yok
```bash
# DEBUG_ENABLE kontrolü
echo $DEBUG_ENABLE

# Açıkça aktif edin
DEBUG_ENABLE=1 make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

### Python Hatası
```bash
# Python modüllerini kontrol edin
python3 -c "from script.python.test_manager import *; print('OK')"

# Debug logger
python3 -c "from script.python.debug_logger import *; print('OK')"
```

---

## 📚 Daha Fazla Bilgi

Detaylı dokümantasyon için:

```bash
# Ana README
cat docs/TEST_MANAGER_README.md

# Makefile help
make -f Makefile.verilator help
```

---

## ✅ Checklist: İlk Kullanım

- [ ] Test listesini görüntüledim
- [ ] İlk testimi çalıştırdım
- [ ] Debug raporunu görüntüledim
- [ ] Test suite çalıştırdım
- [ ] Tag-based filtering denedim
- [ ] Yeni test ekledim
- [ ] Debug raporlarını karşılaştırdım

**Tüm adımları tamamladınız mı? Tebrikler! 🎉**

Test Manager'ı artık etkin şekilde kullanabilirsiniz!
