# 🔧 Test Sistemi Düzeltme Planı

## 🎯 Tespit Edilen Sorunlar

### 1. ❌ Log Dizini Yanlış
**Sorun:** `build/log/verilator/TEST` yerine `results/logs/verilator/TEST` olmalı

**Çözüm:**
- Makefile.verilator: `LOG_DIR` değişkenini değiştir
- test_manager.py: Log path'i düzelt
- validation_runner.py: results/ kullan

---

### 2. ❌ Validation Otomatik Çağrılmıyor
**Sorun:** `test-run` komutu sadece RTL çalıştırıyor, Spike validation yok

**Çözüm:**
```python
# test_manager.py içinde
def run_test_with_validation(test_name):
    # 1. RTL simulation
    rtl_ok = run_rtl_simulation(test_name)

    if not rtl_ok:
        return "SIMULATION_CRASHED"

    # 2. Validation (opsiyonel - suite'e göre)
    if should_validate(test_name):
        validation = run_validation(test_name)
        return "VALIDATED_PASS" if validation.passed else "VALIDATED_FAIL"
    else:
        return "SIMULATION_COMPLETED"
```

---

### 3. ❌ Yanlış Mesajlar
**Sorun:**
- "✓ Test PASSED" → Yanlış! Sadece simülasyon tamamlandı
- "✓ Simülasyon Başarılı" → Doğru ama validation yok

**Çözüm:**
```python
# verilator_runner.py
if exit_code == 0:
    print("✓ SIMULATION COMPLETED")  # Test değil, simülasyon
```

```python
# test_manager.py
if simulation_ok and validation_ok:
    print("✅ TEST PASSED - VALIDATED")
elif simulation_ok:
    print("✓ SIMULATION COMPLETED (validation skipped)")
else:
    print("❌ SIMULATION CRASHED")
```

---

### 4. ❌ Simülasyon Süresi 0.0
**Sorun:** verilator_runner.py timing hesabı yanlış

**Çözüm:**
```python
start_time = datetime.now()
# ... simulation ...
end_time = datetime.now()
elapsed = (end_time - start_time).total_seconds()
print(f"Süre: {elapsed:.2f} saniye")  # .2f formatı
```

---

### 5. ❌ Debug Log Klasörleri Boş
**Sorun:** Debug logger dosya yazmıyor

**Çözüm:**
- debug_logger.py: File write hatalarını kontrol et
- Permission check ekle
- Directory creation güvence altına al

---

### 6. ❌ Verilator Logları Ekranda
**Sorun:** Verilator çıktısı ekranı doldurur, özet görmek zor

**Çözüm:**
```python
# verilator_runner.py
LOG_FILE = log_dir / "verilator_full.log"

with open(LOG_FILE, 'w') as logf:
    process = subprocess.run(
        cmd,
        stdout=logf,
        stderr=subprocess.STDOUT
    )

# Sadece özet göster
print("✓ Simulation completed - Full log: {LOG_FILE}")
```

---

### 7. ❌ HTML Rapor Yok
**Sorun:** HTML rapor otomatik oluşmuyor

**Çözüm:**
```python
# test_manager.py
if validation.passed:
    generate_html_report(test_name, validation)
```

---

### 8. ❌ Debug Loglarında Parametre Yok
**Sorun:** Hangi komutlar çalıştı bilinmiyor

**Çözüm:**
```python
# debug_logger.py - step içinde
step.command("verilator --cc ...")
step.arguments(["--test", "rv32ui-p-add", "--max-cycles", "100000"])

# JSON'da:
{
  "execution_flow": [
    {
      "command": "verilator --cc ...",
      "args": ["--test", "rv32ui-p-add"],
      "env": {"MAX_CYCLES": "100000"}
    }
  ]
}
```

---

## 🔨 Uygulama Sırası

### Faz 1: Log Dizin Yapısı (Kritik)
1. Makefile.verilator: `LOG_DIR` → `results/logs/verilator/`
2. test_manager.py: Path güncelleme
3. validation_runner.py: Path güncelleme

### Faz 2: Mesaj Düzeltmeleri (Kolay)
1. verilator_runner.py: "Test PASSED" → "SIMULATION COMPLETED"
2. test_manager.py: Final karar mantığı

### Faz 3: Validation Entegrasyonu (Orta)
1. test_manager.py: `run_validation()` fonksiyonu
2. test_registry.json: `validation_enabled` flag
3. Otomatik çağrı

### Faz 4: Debug İyileştirmeleri (Kolay)
1. Timing fix
2. Command logging
3. Output redirection

### Faz 5: HTML Rapor (Opsiyonel)
1. html_report_generator.py entegrasyonu

---

## 📝 Öncelikli Düzeltmeler

### ÖNCELİK 1: Log Dizini
**Etki:** Yüksek - Tüm dosyalar yanlış yerde

```makefile
# Makefile.verilator
-LOG_DIR := $(BUILD_DIR)/log/verilator/$(TEST_NAME)
+LOG_DIR := $(RESULTS_DIR)/logs/verilator/$(TEST_NAME)
```

### ÖNCELİK 2: Validation Çağrısı
**Etki:** Kritik - Test doğruluğu bilinmiyor

```python
# test_manager.py - cmd_run() içinde
results = runner.run_tests_with_validation(tests_to_run, **kwargs)
```

### ÖNCELİK 3: Mesajlar
**Etki:** Orta - Kullanıcı kafası karışık

```python
print("✓ SIMULATION COMPLETED")  # "Test PASSED" değil
```

---

## 🧪 Test Planı

Her düzeltmeden sonra:
```bash
# Test et
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add

# Kontrol et
ls -la results/logs/verilator/rv32ui-p-add/
cat results/logs/verilator/rv32ui-p-add/diff.log
```

---

## ✅ Başarı Kriterleri

Düzeltme başarılı sayılır eğer:
- ✅ Loglar `results/logs/SIMULATOR/TEST/` altında
- ✅ Validation otomatik çalışıyor
- ✅ Mesajlar doğru: "SIMULATION COMPLETED" vs "TEST PASSED (VALIDATED)"
- ✅ Süre doğru gösteriliyor
- ✅ Debug logs dolu ve bilgilendirici
- ✅ Verilator çıktısı dosyada, ekranda özet
- ✅ HTML rapor otomatik
- ✅ Permission errorları yok
