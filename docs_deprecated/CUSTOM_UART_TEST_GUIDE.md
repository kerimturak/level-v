# 🎯 Ceres-V Kustom UART Test Sistemi - Hızlı Referans

## ✅ Kurulum Tamamlandı

Artık **Ceres-V RV32IMC_Zicsr** işlemciniz için kendi C testlerini yazabilir, derleyebilir ve simülasyonda çalıştırabilirsiniz!

---

## 📦 Oluşturulan Sistem Bileşenleri

| Dosya | Lokasyon | Açıklama |
|-------|----------|----------|
| **uart_hello_test.c** | `sim/test/custom/` | Örnek UART test (hepsi bir referans) |
| **build_custom_test.sh** | `script/shell/` | Derleme ve çalıştırma scripti |
| **custom_test.mk** | `script/makefiles/` | Makefile entegrasyonu |
| **README.md** | `sim/test/custom/` | Detaylı rehber ve örnekler |
| **uart_test_quickstart.sh** | `script/shell/` | Quick start kılavuzu |

---

## 🚀 Başlamak İçin

### 1️⃣ Kök dizine gidin
```bash
cd /home/kerim/level-v
```

### 2️⃣ Örnek testi derle ve çalıştır
```bash
make custom_test TEST=uart_hello_test
```

### 3️⃣ UART çıktısını gör
```bash
cat uart_output.log
```

---

## 📝 Kendi Test Yazma

### Adım 1: Yeni dosya oluştur
```bash
cp sim/test/custom/uart_hello_test.c sim/test/custom/my_test.c
```

### Adım 2: C kodunuzu yazın
```c
#include <stdint.h>

#define UART_CTRL        (*(volatile uint32_t*)0x20000000)
#define UART_STATUS      (*(volatile uint32_t*)0x20000004)
#define UART_WDATA       (*(volatile uint32_t*)0x2000000c)
#define UART_STATUS_TX_FULL 0x1
#define CPU_CLK 50000000
#define BAUD_RATE 115200

void uart_init(void) {
    uint32_t baud_div = CPU_CLK / BAUD_RATE;
    UART_CTRL = (baud_div << 16) | 0x3;
}

void uart_putc(char c) {
    while (UART_STATUS & UART_STATUS_TX_FULL);
    UART_WDATA = c;
}

int main(void) {
    uart_init();
    uart_putc('H');
    uart_putc('i');
    while (1);
    return 0;
}
```

### Adım 3: Derle ve çalıştır
```bash
make custom_test TEST=my_test
```

---

## 🔧 Util Makefile Komutları

```bash
# Test listesi
make custom_list

# Derle
make custom_build TEST=my_test

# Çalıştır
make custom_run TEST=my_test MAX_CYCLES=100000

# Derle + Çalıştır
make custom_test TEST=my_test

# Temizle
make custom_clean TEST=my_test
make custom_clean  # Hepsi

# Disassembly
make custom_disass TEST=my_test

# Dosya boyutu
make custom_size TEST=my_test

# Info
make custom_info TEST=my_test

# Help
make custom_help
```

---

## 📌 Hazır UART Fonksiyonları

`uart_hello_test.c` dosyasında tanımlanmış:

- `uart_init()` - UART başlat
- `uart_putc(char)` - Bir karakter gönder
- `uart_puts(const char*)` - String gönder
- `uart_puthex(uint32_t)` - Hex sayı gönder (ör: 0xDEADBEEF)
- `uart_putdec(int32_t)` - Decimal sayı gönder (ör: 12345)

---

## 🎮 Örnek Testler

### "Merhaba Dünya"
```c
int main(void) {
    uart_init();
    uart_puts("Merhaba Dunya!\n");
    while (1);
    return 0;
}
```

### Döngü Testi
```c
int main(void) {
    uart_init();
    for (int i = 0; i < 10; i++) {
        uart_putdec(i);
        uart_putc(' ');
    }
    uart_puts("\n");
    while (1);
    return 0;
}
```

### Hafıza Adresi Göster
```c
int main(void) {
    uart_init();
    uint32_t val = 0x12345678;
    uart_puts("Adres: ");
    uart_puthex((uint32_t)&val);
    uart_puts(" = ");
    uart_puthex(val);
    uart_puts("\n");
    while (1);
    return 0;
}
```

### Timer Oku
```c
int main(void) {
    uart_init();
    
    #define TIMER_LOW (*(volatile uint32_t*)0x30000000)
    
    uint32_t cycles = TIMER_LOW;
    uart_puts("Cycles: ");
    uart_putdec(cycles);
    uart_puts("\n");
    
    while (1);
    return 0;
}
```

---

## 🔧 Hardware Adresleri

### UART Registers (0x20000000+)
```
0x20000000  UART_CTRL      (Control: [31:16] baud_div, [1] rx_en, [0] tx_en)
0x20000004  UART_STATUS    (Status: tx_full, rx_full, tx_empty, rx_empty)
0x20000008  UART_RDATA     (RX Data - okuma)
0x2000000c  UART_WDATA     (TX Data - yazma)
```

### Timer (0x30000000+)
```
0x30000000  TIMER_LOW      (64-bit timer alt 32-bit)
0x30000004  TIMER_HIGH     (64-bit timer üst 32-bit)
```

### CPU Özellikleri
```
ISA:        RV32IMC_Zicsr
Clock:      50 MHz
UART Baud:  115200 bps
```

---

## 📂 Dosya Yapısı

```
level-v/
├── sim/test/custom/
│   ├── uart_hello_test.c    # Örnek test
│   ├── README.md             # Detaylı rehber
│   └── (kendi testleriniz)
├── script/shell/
│   ├── build_custom_test.sh  # Build scripti
│   └── uart_test_quickstart.sh # Quick start
├── script/makefiles/
│   └── custom_test.mk        # Makefile entegrasyon
└── build/tests/custom/
    ├── my_test.elf           # Executable
    ├── my_test.mem           # Verilog memory
    ├── my_test.hex           # Intel HEX
    ├── my_test.bin           # Binary
    └── my_test.disass        # Disassembly
```

---

## 🐛 Sorun Giderme

| Problem | Çözüm |
|---------|--------|
| **UART çıktısı boş** | uart_init() çağrıldığını kontrol et; MAX_CYCLES artır |
| **"gcc not found"** | RISC-V toolchain kurulu mu? `which riscv32-unknown-elf-gcc` |
| **Derleme hatası** | -nostartfiles bayrağını kaldırmayı dene veya startup kodu ekle |
| **Simülasyon çöktü** | MAX_CYCLES değerini azalt; register adresleri doğru mu? |

---

## 💾 Simülasyon Çıktıları

Her test çalıştırıldığında oluşturulan dosyalar:

- **uart_output.log** - UART TX çıktısı
- **build/tests/custom/sim.log** - Simülasyon log'u
- **build/tests/custom/compile.log** - Derleme log'u

---

## 📚 Referanslar

- Detaylı rehber: `sim/test/custom/README.md`
- UART register tanımları: `subrepo/coremark/ceresv/core_portme.h`
- Linker script: `subrepo/coremark/ceresv/link.ld`
- Mevcut CoreMark örneği: `subrepo/coremark/ceresv/core_portme.c`

---

## ✨ Sonraki Adımlar

1. Basit "Merhaba" testi yazıp çalıştır
2. UART print debugging'i test et
3. Loop ve karar yapıları deneyimle
4. Timer okumalarını ekle
5. Daha karmaşık işlemler yap

---

**Son Güncelleme:** 2025-12-01  
**Ceres-V Sürümü:** RV32IMC_Zicsr  
**Status:** ✅ Hazır Kullanıma

Sorularınız varsa, ilgili dosyaları kontrol edin veya build script'i çalıştırırken `-v` bayrağı (verbose) kullanın.
