# 🔍 CERES RISC-V Validation System

## 📋 Genel Bakış

Test validation sistemini **3 katmana** ayırdık:

```
┌─────────────────────────────────────────┐
│ Layer 1: RTL Simulation                │
│ ├─ verilator_runner.py                 │
│ └─ Sonuç: SIMULATION_COMPLETED/CRASHED │
└─────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────┐
│ Layer 2: Validation                    │
│ ├─ Makefile.spike (Spike çalıştır)    │
│ ├─ validation_runner.py (Orkestra)    │
│ └─ Sonuç: VALIDATED_PASS/FAIL          │
└─────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────┐
│ Layer 3: Test Management               │
│ ├─ test_manager.py (Koordinasyon)     │
│ └─ Final: PASS/FAIL + Debug Report     │
└─────────────────────────────────────────┘
```

---

## 🎯 Sorumluluk Ayrımı

### 1️⃣ **RTL Simülasyon** (`verilator_runner.py`)

**Sorumluluk:** Sadece simülasyonu çalıştırmak
**Başarı Kriteri:** Crash olmadan bitmek

```python
# verilator_runner.py
if exit_code == 0:
    print("✓ Simülasyon Başarılı")  # ← Doğru: Crash olmadı
    return 0
else:
    print("✗ Simülasyon Çöktü")
    return 1
```

**Sonuç Mesajları:**
- ✅ `SIMULATION_COMPLETED` - Simülasyon crash olmadan bitti
- ❌ `SIMULATION_CRASHED` - Simülasyon crash oldu

**ÖNEMLİ:** Bu katman **test pass/fail** kararı **VERMEMELİ**!

---

### 2️⃣ **Validation** (`Makefile.spike` + `validation_runner.py`)

**Sorumluluk:** RTL çıktısını Spike ile karşılaştırmak
**Başarı Kriteri:** RTL commit log == Spike commit log

```bash
# Makefile.spike kullanımı
make -f Makefile.spike run-spike \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=build/log/verilator/rv32ui-p-add

make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=build/log/.../commit_trace.log \
    SPIKE_LOG=build/log/.../spike_commit.log
```

```python
# validation_runner.py kullanımı
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add

# Sonuç:
{
  "status": "VALIDATED_PASS",
  "rtl_instructions": 2900,
  "spike_instructions": 2900,
  "matched_instructions": 2900,
  "match_percentage": 100.0
}
```

**Sonuç Durumları:**
- ✅ `VALIDATED_PASS` - Loglar tam eşleşti
- ❌ `VALIDATED_FAIL` - Loglar farklı
- ⚠️ `SPIKE_FAILED` - Spike çalıştırılamadı
- ⚠️ `RTL_LOG_MISSING` - RTL log yok
- ⚠️ `SPIKE_SKIPPED` - Validation atlandı

---

### 3️⃣ **Test Manager** (`test_manager.py`)

**Sorumluluk:** Tüm pipeline'ı koordine etmek
**Final Karar:** Pass/Fail + Debug Report

```python
# test_manager.py workflow
1. RTL simülasyonu çalıştır → verilator_runner.py
2. Eğer simulation_completed:
     a. Validation çalıştır → validation_runner.py
     b. Validation sonucuna göre PASS/FAIL
3. Debug raporu oluştur
4. Kullanıcıya sonucu bildir
```

**Final Sonuçlar:**
- ✅ `TEST_PASSED` - Simülasyon + Validation başarılı
- ❌ `TEST_FAILED` - Validation başarısız (loglar eşleşmedi)
- ❌ `SIMULATION_CRASHED` - Simülasyon crash oldu
- ⚠️ `VALIDATION_SKIPPED` - Validation yapılmadı (benchmark mode)

---

## 📁 Yeni Dosyalar

### 1. `Makefile.spike`
**Standalone Spike Makefile**

Özellikler:
- Bağımsız Spike çalıştırma
- Log karşılaştırma
- Auto-detect test type
- Minimal dependencies

Kullanım:
```bash
# Spike çalıştır
make -f Makefile.spike run-spike TEST_NAME=rv32ui-p-add LOG_DIR=build/log/test

# Logları karşılaştır
make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=build/log/test/commit_trace.log \
    SPIKE_LOG=build/log/test/spike_commit.log

# Full validation
make -f Makefile.spike validate \
    TEST_NAME=rv32ui-p-add \
    BUILD_DIR=build \
    LOG_DIR=build/log/test \
    RTL_LOG=build/log/test/commit_trace.log
```

### 2. `script/python/validation_runner.py`
**Validation orkestra aracı**

Özellikler:
- Spike + Compare tek komutta
- Metrics extraction
- JSON output
- Error handling

Kullanım:
```bash
# Basit kullanım
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add

# Spike atla (sadece karşılaştır)
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add \
    --skip-spike

# JSON çıktı
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add \
    --json-output validation_result.json
```

---

## 🔄 Tam Workflow

### Senaryo 1: Tam Validation

```bash
# 1. RTL Simulation
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add
# → Sonuç: build/log/verilator/rv32ui-p-add/commit_trace.log

# 2. Validation
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add
# → Spike çalışır, logları karşılaştırır

# 3. Sonuç
# ✅ VALIDATED_PASS - Test geçti
# ❌ VALIDATED_FAIL - Test başarısız
```

### Senaryo 2: Benchmark (Validation Yok)

```bash
# Benchmark testlerde validation atlanır
make -f Makefile.verilator test-run TEST_NAME=coremark
# → Sadece simülasyon
# → Sonuç: SIMULATION_COMPLETED (validation yok)
```

### Senaryo 3: Manuel Validation

```bash
# Önce RTL
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add

# Sonra Spike (ayrı)
make -f Makefile.spike run-spike \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=build/log/verilator/rv32ui-p-add

# Sonra Compare (ayrı)
make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=build/log/verilator/rv32ui-p-add/commit_trace.log \
    SPIKE_LOG=build/log/verilator/rv32ui-p-add/spike_commit.log
```

---

## 📊 Validation Sonuç Formatı

### JSON Output

```json
{
  "test_name": "rv32ui-p-add",
  "status": "VALIDATED_PASS",
  "passed": true,
  "rtl_log_exists": true,
  "spike": {
    "ran": true,
    "success": true
  },
  "comparison": {
    "ran": true,
    "logs_match": true
  },
  "metrics": {
    "rtl_instructions": 2900,
    "spike_instructions": 2900,
    "matched_instructions": 2900,
    "first_mismatch_line": null,
    "match_percentage": 100.0
  },
  "errors": [],
  "warnings": []
}
```

### Başarısız Test Örneği

```json
{
  "test_name": "rv32ui-p-buggy",
  "status": "VALIDATED_FAIL",
  "passed": false,
  "metrics": {
    "rtl_instructions": 2900,
    "spike_instructions": 2900,
    "matched_instructions": 2850,
    "first_mismatch_line": 2851,
    "match_percentage": 98.3
  },
  "errors": [],
  "warnings": ["First mismatch at line 2851"]
}
```

---

## 🎯 Avantajlar

### ✅ Sorumluluk Ayrımı
- Her katman kendi işini yapar
- RTL simülasyonu validation'dan bağımsız
- Validation RTL'den bağımsız

### ✅ Modüler Yapı
- Spike'ı standalone çalıştırabilirsiniz
- Validation'ı tekrar çalıştırabilirsiniz
- Test manager olmadan da kullanılabilir

### ✅ Debug-Friendly
- Her adım ayrı log üretir
- JSON çıktılar parse edilebilir
- Hata ayıklama kolay

### ✅ Geriye Dönük Uyumlu
- Eski `make run` hala çalışır
- Mevcut test workflow'ları korunur
- Yeni özellikler optional

---

## 🔧 Gelecek İyileştirmeler

### 1. Test Manager Entegrasyonu
```python
# test_manager.py'de
def run_test_with_validation(test_name):
    # 1. RTL simülasyon
    rtl_result = run_rtl_simulation(test_name)

    # 2. Eğer simulation başarılı
    if rtl_result.status == "COMPLETED":
        # 3. Validation çalıştır
        validation = run_validation(test_name)

        # 4. Final karar
        if validation.passed:
            return "TEST_PASSED"
        else:
            return "TEST_FAILED"
    else:
        return "SIMULATION_CRASHED"
```

### 2. Debug Raporu Genişletme
```json
{
  "result": {
    "simulation": "COMPLETED",  # RTL simülasyon durumu
    "validation": "FAILED",     # Validation durumu
    "final_status": "FAILED"    # Final karar
  },
  "validation_details": {
    "rtl_instructions": 2900,
    "spike_instructions": 2900,
    "match_percentage": 98.3,
    "first_mismatch": {
      "line": 2851,
      "rtl_pc": "0x80001234",
      "spike_pc": "0x80001238"
    }
  }
}
```

### 3. Auto-Enable Validation
```json
// test_registry.json
{
  "test_suites": {
    "isa_basic": {
      "validation": {
        "enabled": true,
        "spike_isa": "rv32imc_zicsr"
      }
    },
    "benchmarks": {
      "validation": {
        "enabled": false  // Benchmark'lerde validation yok
      }
    }
  }
}
```

---

## 📞 Kullanım Örnekleri

### Örnek 1: Quick Test + Validation

```bash
# Test çalıştır (RTL only)
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add

# Validation ekle
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add
```

### Örnek 2: Sadece Validation (RTL zaten çalıştı)

```bash
# RTL çalıştı, sadece validation yap
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add
```

### Örnek 3: Spike Parametreleri Özelleştir

```bash
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-custom \
    --log-dir build/log/verilator/rv32ui-p-custom \
    --spike-isa rv32im_zicsr \
    --spike-pc 0x80000000
```

### Örnek 4: Resync Mode (Farklılıkları Otla)

```bash
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add \
    --resync
```

---

## ✅ Özet

| Katman | Sorumluluk | Başarı Kriteri | Çıktı |
|--------|------------|----------------|-------|
| **RTL Sim** | Simülasyon çalıştır | Crash olma | `COMPLETED`/`CRASHED` |
| **Validation** | Spike + Compare | RTL == Spike | `VALIDATED_PASS`/`FAIL` |
| **Test Manager** | Orkestra + Karar | Full pipeline | `TEST_PASSED`/`FAILED` |

**Altın Kural:** Her katman sadece kendi sorumluluğunda karar verir!

---

## 🎉 Sonuç

Artık:
- ✅ RTL simülasyonu validation'dan ayrı
- ✅ Spike standalone çalışabilir
- ✅ Validation tekrar çalıştırılabilir
- ✅ Test pass/fail kriteri net
- ✅ Debug-friendly yapı
- ✅ Modüler ve genişletilebilir

**Test sonucu artık doğru:**
- Simülasyon çalıştı ≠ Test geçti
- RTL == Spike → Test geçti ✅
