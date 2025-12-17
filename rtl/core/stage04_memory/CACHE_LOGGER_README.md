# Cache Logger - Kullanım Kılavuzu

## Genel Bakış

`cache_logger.sv` modülü, memory stage'deki unified cache'e giren tüm istekleri ve dönen cevapları tablo formatında loglayan bir debug aracıdır.

## Özellikler

### Log Edilen Bilgiler

**Request (İstek):**
- ⏰ **Time**: İsteğin zamanı (ns)
- ✓ **Valid**: İsteğin geçerli olup olmadığı
- 📍 **Address**: Erişilen bellek adresi (hex)
- 🔄 **Operation**: READ veya WRITE
- 📏 **Size**: İşlem boyutu (1B, 2B, 4B)
- 📝 **Write Data**: Write işlemlerinde yazılan veri (hex)
- 🔓 **Uncached**: Uncached erişim flag'i

**Response (Cevap):**
- ⏰ **Time**: Cevabın zamanı (ns)
- ✓ **Valid**: Cevabın geçerli olup olmadığı
- 🎯 **Miss/Hit**: Cache miss veya hit durumu
- 🚦 **Ready**: Cache'in hazır olup olmadığı
- 📖 **Read Data**: Read işlemlerinde okunan veri (hex)

## Kullanım

### 1. Verilator ile Simülasyon

Cache loglarını aktif etmek için:

```bash
make verilate LOG_CACHE=1
make run:your_test LOG_CACHE=1
```

### 2. Örnek Komutlar

```bash
# RISC-V ISA testlerini cache log ile çalıştır
make run:rv32ui-p-add LOG_CACHE=1

# CoreMark benchmark'ı cache log ile çalıştır
make cm_quick LOG_CACHE=1

# Özel test programını cache log ile çalıştır
make verilate LOG_CACHE=1
./build/obj_dir/Vceres_wrapper +firmware=your_program.hex
```

### 3. Diğer Log'larla Birlikte Kullanım

```bash
# Cache + Commit trace
make run:rv32ui-p-add LOG_CACHE=1 LOG_COMMIT=1

# Cache + UART + RAM logs
make run:your_test LOG_CACHE=1 LOG_UART=1 LOG_RAM=1

# Tüm debug logları
make run:your_test LOG_CACHE=1 LOG_COMMIT=1 LOG_UART=1 LOG_RAM=1 LOG_BP=1
```

## Çıktı Formatı

```
╔═══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                         CACHE TRANSACTION LOG                                                         ║
╠═════════╦═══════════╦════════════╦═════════╦═════════╦═══════════════╦═══════════════════════════════════════════════╣
║  Time   ║    REQ    ║  Address   ║  Op     ║  Size   ║  Write Data   ║                RESPONSE                       ║
║   (ns)  ║  Valid    ║   (hex)    ║ (R/W)   ║ (bytes) ║     (hex)     ║  Valid  │  Miss  │  Ready  │   Read Data      ║
╠═════════╬═══════════╬════════════╬═════════╬═════════╬═══════════════╬═════════╪════════╪═════════╪══════════════════╣
║    1500 ║     1     ║ 0x80000000 ║ READ    ║  4B     ║       -       ║    -    │   -    │    -    │        -         ║
║    1520 ║     -     ║     -      ║    -    ║    -    ║       -       ║    1    │  MISS  │  YES   │  0x00000013      ║
║    1540 ║     1     ║ 0x80000004 ║ WRITE   ║  4B     ║  0xdeadbeef   ║    -    │   -    │    -    │        -         ║
║    1560 ║     -     ║     -      ║    -    ║    -    ║       -       ║    1    │  HIT   │  YES   │  0x00000000      ║
║    1580 ║     1     ║ 0x10000000 ║ READ    ║  1B     ║       -       ║    -    │   -    │    -    │        -         ║
║         ║           ║            ║ [UNCACHED ACCESS]                                                                  ║
║    1600 ║     -     ║     -      ║    -    ║    -    ║       -       ║    1    │  MISS  │  YES   │  0x000000ff      ║
╚═════════╩═══════════╩════════════╩═════════╩═════════╩═══════════════╩═════════╧════════╧═════════╧══════════════════╝
```

## Implementasyon Detayları

### Dosya Konumları

- **Logger Modülü**: `rtl/core/stage04_memory/cache_logger.sv`
- **Entegrasyon**: `rtl/core/stage04_memory/memory.sv` içinde instantiate edilmiş
- **Defines**: `rtl/include/ceres_defines.svh` içinde `LOG_CACHE` flag'i
- **Makefile**: `script/makefiles/sim/verilator.mk` içinde flag tanımı

### Sinyaller

Logger, memory stage'den şu sinyalleri alır:

```systemverilog
input dcache_req_t cache_req_i;  // Cache'e giden istek
input dcache_res_t cache_res_i;  // Cache'den gelen cevap
```

### Performans Notu

- Logger yalnızca `LOG_CACHE=1` ile aktif edildiğinde çalışır
- Aktif olmadığında synthesize edilmez (sıfır overhead)
- Simülasyon hızına minimal etki eder

## Troubleshooting

### Log çıktısı görünmüyor

1. `LOG_CACHE=1` flag'ini kullandığınızdan emin olun
2. Verilator build'ini yeniden yapın: `make verilate LOG_CACHE=1`
3. Simülasyon sırasında cache erişimi olup olmadığını kontrol edin

### Log çok fazla satır üretiyor

Cache logları oldukça verbose olabilir. Filtreleme için:

```bash
make run:your_test LOG_CACHE=1 | grep "READ "
make run:your_test LOG_CACHE=1 | grep "WRITE"
make run:your_test LOG_CACHE=1 | grep "MISS"
```

## İlgili Dökümanlar

- Memory Stage: `rtl/core/stage04_memory/memory.sv`
- Cache Implementation: `rtl/core/cache/cache.sv` veya `rtl/core/mmu/dcache.sv`
- Defines Reference: `rtl/include/ceres_defines.svh`
