# 🔧 Makefile Sorumluluk Ayrımı

## 📅 Date: 2025-12-13

## 🎯 Problem

Önceden **Makefile.verilator** hem Verilator hem de Spike işlerini yapıyordu. Bu karışıklığa yol açıyordu:
- Verilator Makefile'ı Spike çalıştırıyordu
- `ENABLE_SPIKE`, `ENABLE_COMPARE` flag'leri karmaşık
- Sorumluluklar net değildi

## ✅ Çözüm: Sorumluluk Ayrımı

Her Makefile artık **sadece kendi işinden** sorumlu:

```
┌─────────────────────────────────────────┐
│ Makefile.verilator                     │
│ └─ Sadece Verilator işleri            │
│    ├─ Build (verilate)                 │
│    ├─ Run RTL simulation               │
│    └─ Waveform açma                    │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│ Makefile.spike                         │
│ └─ Sadece Spike işleri                │
│    ├─ Spike çalıştır                   │
│    ├─ Log karşılaştır                  │
│    └─ Validate                         │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│ test_manager.py                        │
│ └─ Orkestrasyon                        │
│    ├─ RTL çalıştır                     │
│    ├─ Validation çalıştır (opsiyonel)  │
│    └─ HTML rapor oluştur               │
└─────────────────────────────────────────┘
```

---

## 📁 Makefile.verilator - Sadece Verilator

### Sorumluluğu:
- ✅ Verilator build (verilate)
- ✅ RTL simulation çalıştır
- ✅ Waveform oluştur
- ✅ Logları kaydet

### Kaldırılanlar:
- ❌ `run-spike` target (→ Makefile.spike)
- ❌ `compare-logs` target (→ Makefile.spike)
- ❌ `html-report` target (→ test_manager.py)
- ❌ `ENABLE_SPIKE` flag
- ❌ `ENABLE_COMPARE` flag
- ❌ `ENABLE_HTML_REPORT` flag

### Kullanım:

**Sadece RTL simülasyonu (validation yok):**
```bash
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add
```

**Sonuç:**
- `results/logs/verilator/rv32ui-p-add/commit_trace.log`
- `results/logs/verilator/rv32ui-p-add/waveform.fst`
- `results/logs/verilator/rv32ui-p-add/uart_output.log`
- **Spike çalışmaz!** ✅

---

## 📁 Makefile.spike - Sadece Spike

### Sorumluluğu:
- ✅ Spike çalıştır
- ✅ RTL ve Spike loglarını karşılaştır
- ✅ diff.log oluştur

### Target'lar:
- `run-spike` - Spike golden reference çalıştır
- `compare` - RTL vs Spike karşılaştır
- `validate` - Spike + Compare (tek komut)

### Kullanım:

**Spike çalıştır:**
```bash
make -f Makefile.spike run-spike \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=results/logs/verilator/rv32ui-p-add
```

**Logları karşılaştır:**
```bash
make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=results/logs/verilator/rv32ui-p-add/commit_trace.log \
    SPIKE_LOG=results/logs/verilator/rv32ui-p-add/spike_commit.log
```

**Full validation (Spike + Compare):**
```bash
make -f Makefile.spike validate \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=results/logs/verilator/rv32ui-p-add \
    RTL_LOG=results/logs/verilator/rv32ui-p-add/commit_trace.log
```

**Sonuç:**
- `results/logs/verilator/rv32ui-p-add/spike_commit.log`
- `results/logs/verilator/rv32ui-p-add/diff.log`

---

## 🐍 test_manager.py - Orkestrasyon

### Sorumluluğu:
- ✅ RTL simulation çağır (Makefile.verilator)
- ✅ Validation çağır (validation_runner.py → Makefile.spike)
- ✅ HTML rapor oluştur
- ✅ Test pass/fail kararı

### Kullanım:

**Otomatik validation ile test:**
```bash
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

**Ne yapar:**
1. `make -f Makefile.verilator run TEST_NAME=rv32ui-p-add` (RTL)
2. `validation_runner.py --test-name rv32ui-p-add` (Spike + Compare)
3. HTML report oluştur
4. Final sonuç: `TEST PASSED - VALIDATED` veya `TEST FAILED`

---

## 🔄 Workflow Örnekleri

### Senaryo 1: Sadece RTL Simulation (Hızlı Test)

```bash
# Sadece Verilator, validation yok
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add
```

**Kullanım Alanı:**
- Hızlı RTL değişiklik testi
- Waveform'a bakmak
- Crash olup olmadığını görmek

---

### Senaryo 2: RTL + Validation (Full Test)

```bash
# test_manager.py ile otomatik validation
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

**Ne Olur:**
1. RTL simulation çalışır
2. Spike otomatik çalışır
3. Loglar karşılaştırılır
4. HTML rapor oluşur
5. Sonuç: PASSED/FAILED

**Kullanım Alanı:**
- Regression testing
- Test doğruluğunu garanti etme
- CI/CD pipeline

---

### Senaryo 3: Manuel Adım Adım

```bash
# 1. RTL simulation
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add

# 2. Spike çalıştır
make -f Makefile.spike run-spike \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=results/logs/verilator/rv32ui-p-add

# 3. Karşılaştır
make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=results/logs/verilator/rv32ui-p-add/commit_trace.log \
    SPIKE_LOG=results/logs/verilator/rv32ui-p-add/spike_commit.log
```

**Kullanım Alanı:**
- Debug yaparken
- Spike parametrelerini özelleştirme
- Adım adım kontrol

---

## 🎯 Avantajlar

### ✅ Sorumluluk Ayrımı
- Verilator Makefile → Sadece Verilator
- Spike Makefile → Sadece Spike
- test_manager.py → Orkestrasyon

### ✅ Bağımsızlık
- Makefileler birbirinden bağımsız
- İstediğinizi çalıştırabilirsiniz
- Karışıklık yok

### ✅ Esneklik
- Sadece RTL → Hızlı test
- RTL + Validation → Full test
- Manuel adımlar → Debug

### ✅ Bakım Kolaylığı
- Her Makefile kendi işine bakar
- Değişiklikler kolay
- Anlaşılır yapı

---

## 📚 Komut Özeti

| Ne İstiyorum? | Komut |
|---------------|-------|
| **Sadece RTL** | `make -f Makefile.verilator run TEST_NAME=...` |
| **RTL + Validation** | `make -f Makefile.verilator test-run TEST_NAME=...` |
| **Sadece Spike** | `make -f Makefile.spike run-spike TEST_NAME=... LOG_DIR=...` |
| **Spike + Compare** | `make -f Makefile.spike validate TEST_NAME=... LOG_DIR=... RTL_LOG=...` |
| **Waveform aç** | `make -f Makefile.verilator view TEST_NAME=...` |

---

## 🔧 Geçiş Rehberi

### Eski Komut → Yeni Komut

```bash
# ESKİ (artık çalışmaz):
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add \
    ENABLE_SPIKE=1 ENABLE_COMPARE=1 ENABLE_HTML_REPORT=1

# YENİ:
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

```bash
# ESKİ (artık yok):
make -f Makefile.verilator run-spike TEST_NAME=rv32ui-p-add

# YENİ:
make -f Makefile.spike run-spike \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=results/logs/verilator/rv32ui-p-add
```

```bash
# ESKİ (artık yok):
make -f Makefile.verilator compare-logs TEST_NAME=rv32ui-p-add

# YENİ:
make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=results/logs/verilator/rv32ui-p-add/commit_trace.log \
    SPIKE_LOG=results/logs/verilator/rv32ui-p-add/spike_commit.log
```

---

## ✅ Düzeltilen Hatalar

### 1. mkdir Hatası
**Problem:** `mkdir: cannot create directory '': No such file or directory`

**Sebep:** `VERILATOR_LOG` değişkeni `TEST_NAME` olmadan boş kalıyordu

**Çözüm:**
```makefile
# ESKİ:
dirs:
	@mkdir -p "$(BUILD_DIR)" "$(OBJ_DIR)" "$(LOG_DIR)" "$(VERILATOR_LOG)"

# YENİ:
dirs:
	@mkdir -p "$(BUILD_DIR)" "$(OBJ_DIR)" "$(RESULTS_DIR)/logs"
	@if [ -n "$(TEST_NAME)" ]; then mkdir -p "$(VERILATOR_LOG)"; fi
```

### 2. Sorumluluk Karışıklığı
**Problem:** Verilator Makefile Spike işlerini de yapıyordu

**Çözüm:**
- Spike target'ları kaldırıldı
- Validation test_manager.py'ye taşındı
- Her Makefile sadece kendi işini yapar

---

## 🎉 Sonuç

Artık:
- ✅ Makefileler birbirinden bağımsız
- ✅ Sorumluluklar net
- ✅ Kullanımı kolay
- ✅ mkdir hatası yok
- ✅ Verilator sadece Verilator
- ✅ Spike sadece Spike
- ✅ test_manager.py orkestrasyon

**Temiz, modüler, anlaşılır!** 🚀
