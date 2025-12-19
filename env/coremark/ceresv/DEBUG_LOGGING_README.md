# CoreMark Debug Logging Sistemi

Bu klasörde CoreMark benchmark'ını debug etmek için detaylı bir logging sistemi hazırlanmıştır. İşlemcinizin nerede takıldığını bulmak için UART üzerinden ayrıntılı log mesajları gönderir.

## Dosya Yapısı

```
env/coremark/ceresv/
├── debug_log.h                    # Debug logging header dosyası
├── core_portme.c                  # Debug log içeren platform kodu
├── core_portme.h                  # Platform tanımları
├── ee_printf.c                    # Printf implementasyonu
├── cvt.c                          # Printf yardımcı fonksiyonları
└── DEBUG_LOGGING_README.md        # Bu dosya
```

## Debug Log Fonksiyonları

`debug_log.h` şu fonksiyonları sağlar:

- `debug_log(msg)` - Basit mesaj yazdır
- `debug_log_int(msg, val)` - Mesaj + integer değer
- `debug_log_hex(msg, val)` - Mesaj + hex değer
- `debug_log_int2(msg, val1, val2)` - Mesaj + 2 integer
- `debug_checkpoint(num)` - Checkpoint marker

## Log Yerleşimi

Debug logları şu kritik noktalara eklenmiştir:

### 1. core_portme.c
- UART başlatma (CHECKPOINT-1, CHECKPOINT-2)
- Platform init tamamlanması

### 2. core_main.c
- Main başlangıcı (CHECKPOINT-10, CHECKPOINT-11)
- Iterasyon konfigürasyonu
- Bellek tahsisi (CHECKPOINT-20)
- Algoritma init'leri (List, Matrix, State)
- Init tamamlanması (CHECKPOINT-30)
- Final iterasyon sayısı (CHECKPOINT-40)
- Benchmark başlatma (CHECKPOINT-50)
- iterate() fonksiyonu dönüşü
- Benchmark sonlandırma (CHECKPOINT-60)

### 3. iterate() fonksiyonu
- Iterasyon başlangıcı
- Her 10 iterasyonda bir ilerleme raporu
- İlk iterasyon CRC değeri

### 4. core_bench_list()
- List benchmark başlangıcı
- finder_idx değeri

### 5. core_bench_matrix()
- Matrix benchmark başlangıcı (zaten patch'te)

### 6. core_bench_state()
- State benchmark başlangıcı (zaten patch'te)

## Kullanım

### Debug Logging'i Aktif/Pasif Yapma

Debug logging varsayılan olarak AKTİFtir. Kapatmak için:

```c
// debug_log.h içinde
#define DEBUG_LOGGING_ENABLED 0  // 1'den 0'a çevirin
```

### Derleme

CoreMark normal şekilde derlendiğinde debug loglar otomatik olarak dahil edilir:

```bash
cd /home/kerim/level-v/subrepo/coremark
make PORT_DIR=ceresv
```

veya

```bash
cd /home/kerim/level-v/sim/test/coremark
make compile
```

### UART Çıktısını İzleme

Debug mesajları şu formatta UART üzerinden gelir:

```
[DEBUG] iterate() started
[DEBUG] Starting iterations: 1000
[CHECKPOINT-50]
[DEBUG] Iteration progress: 0
[DEBUG] Iteration progress: 10
[DEBUG] Iteration progress: 20
...
```

## Checkpoint'ler

Checkpoint numaraları ve anlamları:

- **1-2**: UART init
- **10-11**: Main başlangıcı ve portable_init
- **20**: Bellek tahsisi tamamlandı
- **30**: Tüm algoritmalar init edildi
- **40**: Final iterasyon sayısı belirlendi
- **50**: Benchmark timer başlatıldı
- **60**: Benchmark timer durduruldu

## Takılma Noktasını Bulma

Eğer CoreMark belirli bir noktada takılıyorsa:

1. En son görünen CHECKPOINT numarasına bakın
2. En son görünen debug mesajına bakın
3. Bu iki bilgi sizin nerede takıldığınızı gösterir

Örnek:
```
[CHECKPOINT-30]
[DEBUG] Starting benchmark timer
[CHECKPOINT-50]
[DEBUG] iterate() started
[DEBUG] Starting iterations: 1000
[DEBUG] Iteration progress: 0
[DEBUG] core_bench_list() started
[DEBUG] finder_idx: 1
```

Yukarıda eğer "finder_idx: 1" den sonra hiçbir log gelmiyorsa,
core_bench_list fonksiyonu içinde takılma var demektir.

## Ek Logging Ekleme

Kendi log noktalarınızı eklemek için:

1. İlgili .c dosyasına `#include "../ceresv/debug_log.h"` ekleyin
2. Kod içinde istediğiniz yerde debug fonksiyonlarını kullanın:

```c
debug_log("My custom checkpoint");
debug_log_int("Loop counter", i);
debug_log_hex("Register value", reg_val);
```

## Performans Etkisi

- Debug logging UART üzerinden çıktı yaptığı için programı **yavaşlatır**
- Sadece debug amaçlı kullanın
- Production/benchmark çalıştırmaları için `DEBUG_LOGGING_ENABLED 0` yapın

## Sorun Giderme

### Log mesajları garbled/bozuk geliyorsa:
- UART baud rate'i kontrol edin (core_portme.h'de BAUD_RATE)
- CPU_CLK doğru ayarlandığından emin olun

### Hiç log gelmiyorsa:
- UART init'in çalıştığından emin olun
- UART TX bağlantısını kontrol edin
- DEBUG_LOGGING_ENABLED 1 olduğundan emin olun

## Örnek Debug Çıktısı

Normal bir çalıştırmada şöyle bir çıktı beklenir:

```
CoreMark on Ceres-V RV32IMC_Zicsr
=================================
CPU Clock: 25000000 Hz
UART Baud: 115200

[DEBUG] portable_init completed
[CHECKPOINT-10]
[CHECKPOINT-11]
[DEBUG] Iterations configured: 0
[DEBUG] Execs mask: 0x7
[DEBUG] Memory allocation and assignment complete
[CHECKPOINT-20]
[DEBUG] Initializing list
[DEBUG] List init complete
[DEBUG] Initializing matrix
[DEBUG] Matrix init complete
[DEBUG] Initializing state
[DEBUG] State init complete
[CHECKPOINT-30]
[DEBUG] Auto-determining iteration count
...
```

## Yapılanlar

✅ debug_log.h header dosyası oluşturuldu
✅ core_portme.c'ye logging eklendi
✅ core_main.c'ye kapsamlı logging eklendi
✅ iterate() fonksiyonuna logging eklendi
✅ core_bench_list()'e logging eklendi
✅ core_bench_matrix()'e logging eklendi (zaten patch'te vardı)
✅ core_bench_state()'e logging eklendi (zaten patch'te vardı)
✅ Checkpoint sistemi eklendi
✅ Derleme test edildi

## İletişim / Katkı

Bu logging sistemi CoreMark'ın nerede takıldığını bulmak için hazırlanmıştır.
Ek önerileriniz için issue açabilir veya pull request gönderebilirsiniz.
