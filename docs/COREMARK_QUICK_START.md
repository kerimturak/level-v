# CoreMark Quick Start Guide

## TL;DR - Hızlı Kullanım

### 1. Sadece Spike'ta Koştur (En Hızlı Test)
```bash
make cm_spike COREMARK_ITERATIONS=5
```

**Sonuçlar:**
- Output: `results/logs/spike/coremark/uart_output.log`
- Commits: `results/logs/spike/coremark/spike_commits.log`

### 2. Her İki Platformda da Koştur ve Karşılaştır
```bash
make cm_compare COREMARK_ITERATIONS=10 MAX_CYCLES=50000000
```

**Sonuçlar:**
- Ceres-V logs: `results/logs/verilator/coremark/`
- Spike logs: `results/logs/spike/coremark/`
- Karşılaştırma: `results/comparison/coremark/comparison_report.txt`

### 3. Python Script ile Commit Logları Karşılaştır
```bash
python3 your_compare_script.py \
    results/logs/verilator/coremark/ceres_commits.log \
    results/logs/spike/coremark/spike_commits.log
```

## Dizin Yapısı

```
results/logs/
├── verilator/coremark/      # Ceres-V (kendi işlemcin)
│   ├── uart_output.log      # CoreMark sonuçları
│   ├── ceres_commits.log    # Instruction trace
│   └── waveform.fst         # Dalga formu (opsiyonel)
│
├── spike/coremark/          # Spike (referans ISS)
│   ├── uart_output.log      # CoreMark sonuçları
│   └── spike_commits.log    # Instruction trace
│
└── comparison/coremark/     # Karşılaştırma
    └── comparison_report.txt
```

## Iterasyon Önerileri

| Iterations | Instructions | Süre (tahmini) | Kullanım |
|------------|--------------|----------------|----------|
| 1          | ~10M         | ~1 dakika      | Hızlı test |
| 5          | ~50M         | ~5 dakika      | Geliştirme |
| 10         | ~100M        | ~10 dakika     | Hafif benchmark |
| 100        | ~1B          | ~60 dakika     | Tam benchmark |

## Commit Log Formatı

Her iki platform da aynı formatı kullanıyor:

```
core   0: 3 0x80000000 (0x2000006f)                    # PC ve instruction
core   0: 3 0x80000200 (0x00000093) x1  0x00000000     # Register yazma
core   0: 3 0x8000020c (0x00028067) mem 0x00001018     # Memory erişimi
```

Format: `core ID : privilege : PC (instruction) [reg updates] [mem accesses]`

## Önemli Notlar

1. **Timing farkı**: Spike gettimeofday() kullandığı için simülasyon zamanını gösterir (çok yavaş görünür ama normal)
2. **Commit sayısı**: Her iki platformda da instruction count aynı olmalı
3. **CRC değerleri**: Correct operation için CRC'ler eşleşmeli
4. **Dosya boyutu**: ~10 iteration için ~1.9M instruction, ~90MB commit log

## Sorun Giderme

### "Spike not found"
```bash
# Spike yolunu kontrol et
ls -la /home/kerim/tools/spike/bin/spike
```

### "pk not found"
```bash
# pk yolunu kontrol et
ls -la /home/kerim/tools/pk32/riscv32-unknown-elf/bin/pk
```

### Commit log çok büyük
```bash
# Daha az iterasyon kullan
make cm_spike COREMARK_ITERATIONS=1
```

## Daha Fazla Bilgi

Detaylı kullanım için: [COREMARK_COMPARISON.md](COREMARK_COMPARISON.md)
