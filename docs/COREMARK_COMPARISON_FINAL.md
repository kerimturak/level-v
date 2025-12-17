# CoreMark Karşılaştırma - Final Guide

## 🎯 Hızlı Başlangıç

### Tek Komutla Tam Karşılaştırma
```bash
make cm_compare COREMARK_ITERATIONS=10 MAX_CYCLES=50000000
```

Bu komut:
1. ✅ CoreMark'ı Ceres-V'de koşturur
2. ✅ CoreMark'ı Spike'ta koşturur
3. ✅ `compare_logs.py` ile commit logları karşılaştırır
4. ✅ HTML ve text raporları oluşturur
5. ✅ Farkları gösterir

## 📁 Sonuç Dosyaları

```
results/
├── logs/
│   ├── verilator/coremark/
│   │   ├── uart_output.log       # CoreMark çıktısı
│   │   ├── commit_trace.log      # Instruction trace
│   │   ├── ceres.log             # Pipeline detayları
│   │   └── waveform.fst          # Dalga formu
│   │
│   └── spike/coremark/
│       ├── uart_output.log       # CoreMark çıktısı
│       └── spike_commits.log     # Instruction trace
│
└── comparison/coremark/
    ├── comparison_report.txt     # Ana rapor
    ├── diff.log                  # Detaylı farklar
    └── diff.html                 # HTML rapor (opsiyonel)
```

## 🔧 Karşılaştırma Özellikleri

### compare_logs.py Özellikleri

Sistem, `run_test.mk`'deki aynı Python scriptini kullanıyor:
- ✅ PC ve instruction karşılaştırması
- ✅ Register yazma karşılaştırması
- ✅ Memory erişim karşılaştırması
- ✅ CSR skip modu (`--skip-csr`)
- ✅ Resynchronization desteği
- ✅ Disassembly entegrasyonu
- ✅ Renkli konsol çıktısı
- ✅ HTML raporu (otomatik)
- ✅ JSON export desteği

### Kullanım Örnekleri

```bash
# 1. Quick test (1 iteration)
make cm_compare_quick

# 2. Normal test (10 iterations)
make cm_compare COREMARK_ITERATIONS=10 MAX_CYCLES=50000000

# 3. Uzun test (100 iterations)
make cm_compare COREMARK_ITERATIONS=100 MAX_CYCLES=500000000

# 4. Sadece Spike
make cm_spike COREMARK_ITERATIONS=5

# 5. Sadece Ceres-V
make cm COREMARK_ITERATIONS=5
```

## 📊 Karşılaştırma Raporu Örneği

### Diff Log Formatı
```
======================================
CoreMark Comparison Report
Ceres-V (Verilator) vs Spike (ISS)
======================================

Iterations: 10
Date: 2025-12-17

--- Ceres-V Output ---
CoreMark Size    : 666
Total ticks      : 1234567
Iterations/Sec   : 8.1
[0]crcfinal      : 0xf24c
Correct operation validated.

--- Spike Output ---
CoreMark Size    : 666
Total ticks      : 1759011350
Iterations/Sec   : 0
[0]crcfinal      : 0xf24c
Correct operation validated.

--- Commit Log Comparison Summary ---
[MATCH] Instructions executed: 1,899,433
[MATCH] Register writes: 823,445
[INFO] CSR accesses skipped (--skip-csr)
✓ All instructions match!
```

## 🎨 HTML Raporu

`compare_logs.py` otomatik olarak HTML raporu oluşturur:
- Yan yana instruction karşılaştırma
- Disassembly görünümü
- Renklendirilmiş farklar
- Interactive scroll
- İstatistikler

Görüntülemek için:
```bash
firefox results/comparison/coremark/diff.html
```

## 🔍 Manuel Karşılaştırma

Direkt olarak Python scriptini çalıştırabilirsin:

```bash
python3 script/python/makefile/compare_logs.py \
    --rtl results/logs/verilator/coremark/commit_trace.log \
    --spike results/logs/spike/coremark/spike_commits.log \
    --output results/comparison/coremark/manual_diff.log \
    --test-name "coremark" \
    --dump build/tests/coremark/coremark.dump \
    --skip-csr \
    --verbose
```

### Script Parametreleri

```bash
--rtl PATH          # Ceres-V commit log
--spike PATH        # Spike commit log
--output PATH       # Diff output dosyası
--test-name NAME    # Test ismi (raporlarda görünür)
--dump PATH         # Disassembly dosyası (.dump)
--skip-csr          # CSR işlemlerini atla
--resync            # Otomatik resync (önerilen)
--window N          # Resync window size (default: 8)
--verbose           # Detaylı çıktı
--quiet             # Sessiz mod (sadece hatalar)
--max-errors N      # Max hata sayısı (default: 100)
--context N         # Hata etrafında gösterilecek satır
--json              # JSON formatında çıktı
--no-fail           # Exit code 0 (CI/CD için)
```

## 📈 Performans Karşılaştırması

### Timing Farkları (Normal!)

**Ceres-V (Gerçek Donanım):**
- Timing: Gerçek CPU cycle count
- Timer: Hardware timer @ 25 MHz
- Sonuç: Gerçek performans (Iterations/Sec anlamlı)

**Spike (Simülatör):**
- Timing: `gettimeofday()` syscall (simülasyon zamanı)
- Timer: Simüle edilmiş zaman
- Sonuç: Çok yavaş görünür (normal!)

### Önemli Metrikler

| Metrik | Nerede | Karşılaştırma |
|--------|--------|---------------|
| **CRC Sonuçları** | UART output | Mutlaka eşleşmeli ✓ |
| **Instruction Count** | Commit logs | Çok yakın olmalı (~%1 fark) |
| **PC Sequence** | Commit logs | Aynı olmalı ✓ |
| **Register States** | Commit logs | Aynı olmalı ✓ |
| **Timing (sec)** | UART output | Farklı olacak (normal) |

## ⚙️ İleri Seviye Kullanım

### Resynchronization

Bazı durumlarda instruction sırası hafif farklı olabilir (interrupt timing, cache miss vb.). Resync mode bu farkları tolere eder:

```bash
python3 script/python/makefile/compare_logs.py \
    --rtl ... \
    --spike ... \
    --resync \
    --window 16
```

### CSR Skip

CSR (Control and Status Register) erişimleri implementation-specific olabilir. Bunları karşılaştırmayı atla:

```bash
--skip-csr
```

### JSON Export

CI/CD için JSON formatında sonuç:

```bash
python3 script/python/makefile/compare_logs.py \
    --rtl ... \
    --spike ... \
    --json \
    --no-fail \
    > comparison.json
```

## 🐛 Sorun Giderme

### "Commit logs differ"

Normal! Farklı implementasyonlar farklı instruction sırası kullanabilir. Önemli olan:
1. CRC sonuçları eşleşiyor mu?
2. Instruction count yakın mı?
3. Ana execution flow aynı mı?

### "RTL log not found"

Ceres-V simülasyonu çalışmadı. Kontrol et:
```bash
ls -la results/logs/verilator/coremark/commit_trace.log
```

Yoksa:
```bash
make cm COREMARK_ITERATIONS=5
```

### "Spike log not found"

Spike çalışmadı. Kontrol et:
```bash
ls -la results/logs/spike/coremark/spike_commits.log
```

Yoksa:
```bash
make cm_spike COREMARK_ITERATIONS=5
```

## 📚 Ek Kaynaklar

- **Detaylı Kullanım**: [COREMARK_COMPARISON.md](COREMARK_COMPARISON.md)
- **Hızlı Başlangıç**: [COREMARK_QUICK_START.md](COREMARK_QUICK_START.md)
- **Spike-pk Detayları**: `subrepo/coremark/SPIKE_PK_README.md`
- **compare_logs.py**: `script/python/makefile/compare_logs.py`

## 🎉 Özet Komutlar

```bash
# Hepsi bir arada - TAM KARŞILAŞTIRMA
make cm_compare COREMARK_ITERATIONS=10

# Hızlı test (1 iteration)
make cm_compare_quick

# Sadece logları göster
cat results/comparison/coremark/comparison_report.txt

# HTML raporunu aç
firefox results/comparison/coremark/diff.html
```

Başarılar! 🚀
