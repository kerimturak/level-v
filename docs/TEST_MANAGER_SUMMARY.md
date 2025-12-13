# 📦 Test Manager Sistemi - Özet

## ✨ Ne Yaptık?

CERES RISC-V projeniz için **kapsamlı bir test yönetim ve debug sistemi** geliştirdik.

---

## 📂 Oluşturulan Dosyalar

### 1. Python Scripts (Core)

#### `script/python/test_manager.py` ⭐
**Ana test yönetim CLI aracı**
- Test çalıştırma (tek, suite, tag-based)
- Test listeleme ve filtreleme
- Test ekleme/çıkarma
- Debug logging entegrasyonu

**Kullanım:**
```bash
python3 script/python/test_manager.py run --test rv32ui-p-add
python3 script/python/test_manager.py list --suite benchmarks
python3 script/python/test_manager.py run --tags quick,isa
```

#### `script/python/debug_logger.py` 🔍
**Debug rapor oluşturma kütüphanesi**
- Execution flow tracking
- File access monitoring
- Performance metrics (optional psutil)
- Error/warning aggregation
- Hierarchical step tracking

**Özellikler:**
- Her adımın timestamp'i
- Command'ların tam kaydı
- Exit code'lar
- Stdout/stderr loglama
- Config snapshot'lar

#### `script/python/debug_viewer.py` 📊
**Debug rapor görüntüleme ve analiz aracı**
- Pretty-print raporları
- Error-only görünüm
- Summary istatistikleri
- İki raporun karşılaştırması
- Renkli terminal çıktısı

**Kullanım:**
```bash
python3 script/python/debug_viewer.py
python3 script/python/debug_viewer.py --errors-only
python3 script/python/debug_viewer.py --compare report1.json report2.json
```

---

### 2. Konfigürasyon Dosyaları

#### `script/config/test_registry.json` 📝
**Merkezi test veritabanı**

Yapısı:
```json
{
  "test_suites": {
    "isa_basic": {
      "description": "...",
      "flist": "sim/test/riscv_test_list.flist",
      "tags": ["isa", "compliance", "quick"],
      "enabled": true
    },
    "benchmarks": {
      "tests": {
        "coremark": {
          "config": "script/config/tests/coremark.json",
          "tags": ["benchmark", "slow"]
        }
      }
    }
  },
  "tag_groups": { ... }
}
```

#### `script/config/test_registry.schema.json`
**JSON schema validation**

---

### 3. Makefile Güncellemeleri

#### `Makefile.verilator` (Güncellenmiş) 🔧

**Yeni Değişkenler:**
```makefile
TEST_MANAGER := $(PYTHON) $(SCRIPT_DIR)/python/test_manager.py
DEBUG_VIEWER := $(PYTHON) $(SCRIPT_DIR)/python/debug_viewer.py
DEBUG_ENABLE ?= 1
```

**Yeni Target'lar:**

**Test Manager:**
- `test-run` - Tek test çalıştır
- `test-run-suite` - Suite çalıştır
- `test-run-tags` - Tag'lere göre çalıştır
- `test-list` - Testleri listele
- `test-add` - Test ekle
- `test-remove` - Test çıkar

**Debug Reports:**
- `debug-latest` - Son raporu göster
- `debug-view` - Belirli raporu göster
- `debug-errors` - Sadece hataları göster
- `debug-summary` - Özet göster
- `debug-compare` - İki rapor karşılaştır
- `debug-list` - Tüm raporları listele
- `debug-clean` - Raporları temizle

---

### 4. Dokümantasyon

#### `docs/TEST_MANAGER_README.md` 📚
**Kapsamlı kullanım kılavuzu** (100+ sayfa)
- Detaylı kullanım örnekleri
- Tüm özelliklerin açıklaması
- Sorun giderme
- Best practices

#### `docs/QUICKSTART_TESTMANAGER.md` 🚀
**Hızlı başlangıç kılavuzu**
- 5 dakikada başlangıç
- Yaygın senaryolar
- Pro tips
- Checklist

#### `docs/TEST_MANAGER_SUMMARY.md` (Bu dosya)
**Sistem özeti**

---

## 🎯 Temel Özellikler

### 1. ✅ Kolay Test Yönetimi

**Öncesi:**
```bash
# Test listesini manuel .flist dosyasında düzenle
vim sim/test/custom_tests.flist
# Manuel olarak test adını ekle
# Makefile'ı çalıştır
make -f Makefile.verilator run TEST_NAME=my_test
```

**Sonrası:**
```bash
# Tek komutla test ekle
make -f Makefile.verilator test-add TEST_NAME=my_test SUITE=custom_tests
# Çalıştır
make -f Makefile.verilator test-run TEST_NAME=my_test
```

### 2. 🔍 Otomatik Debug Raporları

**Her test çalıştırmasında:**
- Execution flow kaydedilir
- Tüm dosya erişimleri loglanır
- Performance metrikleri toplanır
- Hatalar ve uyarılar aggregate edilir

**Rapor formatı:**
```json
{
  "metadata": { "test_name": "...", "timestamp": "..." },
  "execution_flow": [ ... ],
  "files_accessed": { "read": [...], "written": [...] },
  "result": { "status": "PASSED", "duration_total_ms": 17777 },
  "performance": { ... }
}
```

### 3. 🏷️ Tag-Based Organization

**Tag'lere göre gruplandırma:**
```bash
# Quick testleri çalıştır
make -f Makefile.verilator test-run-tags TAGS=quick

# Tüm compliance testleri
make -f Makefile.verilator test-run-tags TAGS=compliance

# Performans testleri
make -f Makefile.verilator test-run-tags TAGS=benchmark
```

### 4. 📊 Debug Analiz Araçları

```bash
# Son raporu göster
make -f Makefile.verilator debug-latest

# Sadece hataları göster
make -f Makefile.verilator debug-errors

# İki çalıştırmayı karşılaştır
make -f Makefile.verilator debug-compare REPORT1=... REPORT2=...
```

---

## 🎨 Debug Rapor Örneği

```
================================================================================
DEBUG REPORT: rv32ui-p-add
================================================================================

Metadata:
  Test:        rv32ui-p-add
  Target:      run
  Timestamp:   2025-12-13T14:30:22.123456
  Session ID:  a7f3d9e2
  Git:         main@1b39651

Environment:
  CWD:         /home/kerim/level-v
  Python:      3.10.12
  Verilator:   5.028

Result:
  Status:      PASSED
  Exit Code:   0
  Duration:    17.78s

Execution Flow:
────────────────────────────────────────────────────────────────────────────────
  ✓ Step 1: run_test
    Type:     makefile_target
    Duration: 17.78s (100.0%)
    Command:  make -f Makefile.verilator run TEST_NAME=rv32ui-p-add...
    Exit:     0

Files Accessed:
────────────────────────────────────────────────────────────────────────────────
  Read (3 files):
    • script/config/verilator.json
    • build/tests/riscv-tests/mem/rv32ui-p-add.mem
    • rtl/wrapper/ceres_wrapper.sv

  Written (2 files):
    • build/log/verilator/rv32ui-p-add/commit_trace.log
    • build/log/verilator/rv32ui-p-add/waveform.fst

Performance Metrics:
────────────────────────────────────────────────────────────────────────────────
  CPU Usage:    85.4%
  Memory Peak:  1024.0 MB
  Disk Read:    12.3 MB
  Disk Write:   45.6 MB

Summary Statistics:
────────────────────────────────────────────────────────────────────────────────
  Total Steps:     1
  Total Duration:  17.78s

  Top 3 Slowest Steps:
    1. run_test                        17.78s
```

---

## 📈 Kullanım İstatistikleri

### Test Registry'de Tanımlı Suite'ler:

| Suite | Test Sayısı | Durum |
|-------|-------------|-------|
| isa_basic | 51 | ✓ Aktif |
| isa_compressed | 1 | ✓ Aktif |
| isa_multiply | 8 | ✓ Aktif |
| arch_tests | 91 | ✓ Aktif |
| benchmarks | 2 | ✓ Aktif |
| branch_tests | 8 | ✓ Aktif |
| exception_tests | 2 | ✓ Aktif |
| csr_tests | 16 | ✓ Aktif |
| custom_tests | 20 | ✓ Aktif |
| embench | 16 | ✗ Pasif |
| imperas | 45 | ✗ Pasif |

**Toplam:** 260 test (199 aktif)

---

## 🚀 Hızlı Başlangıç

### 1. Test Listele
```bash
make -f Makefile.verilator test-list
```

### 2. Test Çalıştır
```bash
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

### 3. Debug Raporu Görüntüle
```bash
make -f Makefile.verilator debug-latest
```

---

## 💡 Avantajlar

### ✅ Geriye Dönük Uyumluluk
- Eski tüm Makefile target'ları çalışmaya devam eder
- Mevcut .flist dosyaları kullanılır
- İsteğe bağlı debug logging (DEBUG_ENABLE)

### ✅ Kolay Test Yönetimi
- Tek komutla test ekle/çıkar
- Tag-based filtering
- Suite bazlı organizasyon
- JSON merkezi veritabanı

### ✅ Detaylı Debug İzleme
- Her adımın kaydı
- Dosya erişim takibi
- Performance metrikleri
- Error aggregation
- Rapor karşılaştırma

### ✅ Geliştirilmeye Açık
- Python modüler yapı
- JSON schema validation
- Kolay extension
- Plugin sistemi hazır

---

## 🔧 Teknik Detaylar

### Python Bağımlılıkları

**Zorunlu:**
- Python 3.6+
- Standard library (json, pathlib, subprocess, etc.)

**Opsiyonel:**
- `psutil` - Performance metrikleri için
  - Yoksa: "Warning: psutil not available, performance metrics disabled"
  - Kurulum: `pip3 install psutil`

### Dosya Yapısı

```
level-v/
├── script/
│   ├── config/
│   │   ├── test_registry.json          ⭐ YENİ
│   │   ├── test_registry.schema.json   ⭐ YENİ
│   │   └── tests/
│   │       └── *.json (mevcut)
│   └── python/
│       ├── test_manager.py             ⭐ YENİ
│       ├── debug_logger.py             ⭐ YENİ
│       └── debug_viewer.py             ⭐ YENİ
├── build/
│   └── debug_reports/                  ⭐ YENİ (otomatik)
│       ├── run_TIMESTAMP_TEST.json
│       └── latest_TEST.json (symlink)
├── docs/
│   ├── TEST_MANAGER_README.md          ⭐ YENİ
│   ├── QUICKSTART_TESTMANAGER.md       ⭐ YENİ
│   └── TEST_MANAGER_SUMMARY.md         ⭐ YENİ
└── Makefile.verilator                  🔧 GÜNCELLENDI
```

---

## 🎯 Sonraki Adımlar (Opsiyonel)

### 1. Paralel Test Çalıştırma
```python
# test_manager.py'ye eklenebilir
def run_tests_parallel(test_names, num_jobs=4):
    # multiprocessing ile paralel çalıştırma
```

### 2. Web Dashboard
```python
# Flask/FastAPI ile web arayüzü
# Debug raporlarını browser'da görüntüleme
```

### 3. CI/CD Entegrasyonu
```yaml
# .github/workflows/tests.yml
- name: Run tests
  run: make -f Makefile.verilator test-run-tags TAGS=quick
```

### 4. Email Raporlama
```python
# Test sonuçlarını email ile gönderme
# Başarısız testler için otomatik bildirim
```

---

## 📞 Destek

Sorunlar için debug raporunu kontrol edin:
```bash
make -f Makefile.verilator debug-latest
make -f Makefile.verilator debug-errors
```

---

## ✅ Tamamlanan Özellikler

- [x] Test registry JSON sistemi
- [x] Test manager Python CLI
- [x] Debug logger kütüphanesi
- [x] Debug viewer aracı
- [x] Makefile entegrasyonu
- [x] Tag-based filtering
- [x] Rapor karşılaştırma
- [x] Kapsamlı dokümantasyon
- [x] Hızlı başlangıç kılavuzu
- [x] psutil optional hale getirilmesi

---

**🎉 Sistem hazır! Test etmeye başlayabilirsiniz!**
