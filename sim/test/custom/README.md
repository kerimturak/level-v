# Custom UART Test Programs - Ceres-V

Bu dizinde kendi UART test programlarınızı yazabilir, derleyebilir ve Ceres-V işlemcinizde çalıştırabilirsiniz.

## 📁 Dizin Yapısı

```
sim/test/custom/
├── uart_hello_test.c          # Örnek: Basit UART merhaba mesajı
├── README.md                   # Bu dosya
└── (diğer test dosyaları)
```

## 🔧 Hazırlık

### RISC-V Toolchain Kurulumu

```bash
# Gerekli araçlar
- riscv32-unknown-elf-gcc
- riscv32-unknown-elf-objcopy
- riscv32-unknown-elf-objdump
```

## 📝 Test Yazma

### Minimum Şablon

```c
#include <stdint.h>

/* UART Register Adresleri */
#define UART_CTRL        (*(volatile uint32_t*)0x20000000)
#define UART_STATUS      (*(volatile uint32_t*)0x20000004)
#define UART_WDATA       (*(volatile uint32_t*)0x2000000c)

#define UART_STATUS_TX_FULL   0x1
#define UART_CTRL_TX_EN       0x1
#define UART_CTRL_RX_EN       0x2

#define CPU_CLK          50000000
#define BAUD_RATE        115200

void uart_init(void) {
    uint32_t baud_div = CPU_CLK / BAUD_RATE;
    UART_CTRL = (baud_div << 16) | UART_CTRL_TX_EN | UART_CTRL_RX_EN;
}

void uart_putc(char c) {
    while (UART_STATUS & UART_STATUS_TX_FULL);
    UART_WDATA = (uint32_t)c;
}

int main(void) {
    uart_init();
    uart_putc('H');
    uart_putc('i');
    while (1);
    return 0;
}
```

### Kullanılabilir UART Fonksiyonları

Hazır fonksiyonlar için `uart_hello_test.c` dosyasını referans alın:

- `uart_init()` - UART başlatması
- `uart_putc(char)` - Tek karakter gönder
- `uart_puts(const char*)` - String gönder
- `uart_puthex(uint32_t)` - Hexadecimal sayı gönder
- `uart_putdec(int32_t)` - Decimal sayı gönder

## 🔨 Derleme ve Çalıştırma

### Hızlı Başlangıç (Build Scripti ile)

```bash
# Build script'ini çalıştırılabilir yap
chmod +x /home/kerim/level-v/script/shell/build_custom_test.sh

# Test'i derle ve çalıştır
./script/shell/build_custom_test.sh uart_hello_test

# Diğer testler için
./script/shell/build_custom_test.sh my_custom_test
```

### Manuel Derleme

```bash
cd /home/kerim/level-v

# 1. Kaynak kodu derle
riscv32-unknown-elf-gcc \
    -march=rv32imc -mabi=ilp32 \
    -static -mcmodel=medany \
    -fvisibility=hidden -nostdlib -nostartfiles \
    -Wl,--gc-sections \
    -Wl,-Ttext=0x80000000 \
    -o build/tests/custom/uart_hello_test.elf \
    sim/test/custom/uart_hello_test.c

# 2. Binary dosyalar oluştur
riscv32-unknown-elf-objcopy -O binary \
    build/tests/custom/uart_hello_test.elf \
    build/tests/custom/uart_hello_test.bin

# 3. Memory dosyası oluştur
riscv32-unknown-elf-objcopy -O verilog \
    build/tests/custom/uart_hello_test.elf \
    build/tests/custom/uart_hello_test.mem
```

### Simülasyonda Çalıştırma

```bash
cd /home/kerim/level-v

# Verilator ile çalıştır
make run_verilator TEST_FILE=build/tests/custom/uart_hello_test.mem MAX_CYCLES=100000

# UART çıktısını gözle
tail -f uart_output.log
```

## 📊 Çıktı Kontrolü

Test programınız UART'a veri yazdığında, çıktı `uart_output.log` dosyasına yazılır:

```bash
# UART çıktısını görüntüle
cat uart_output.log

# Simülasyon sırasında gerçek zamanda izle
make run_verilator TEST_FILE=build/tests/custom/uart_hello_test.mem MAX_CYCLES=100000 && cat uart_output.log
```

## 🧪 Test Örnekleri

### Örnek 1: Basit Mesaj

```c
int main(void) {
    uart_init();
    uart_puts("Hello from Ceres!\n");
    while (1);
    return 0;
}
```

### Örnek 2: Döngü Testi

```c
int main(void) {
    uart_init();
    for (int i = 0; i < 5; i++) {
        uart_putc('0' + i);
        uart_putc(' ');
    }
    uart_puts("\n");
    while (1);
    return 0;
}
```

### Örnek 3: Hafıza Testi

```c
int main(void) {
    uart_init();
    
    uint32_t value = 0x12345678;
    uart_puts("Value at ");
    uart_puthex((uint32_t)&value);
    uart_puts(" = ");
    uart_puthex(value);
    uart_puts("\n");
    
    while (1);
    return 0;
}
```

## 🐛 Sorun Giderme

### Derleme Hataları

**Hata**: `riscv32-unknown-elf-gcc: command not found`
- Çözüm: RISC-V toolchain'i kurun veya PATH'e ekleyin

**Hata**: `undefined reference to 'main'`
- Çözüm: `-nostartfiles` bayrağını kaldırın veya startup kodu ekleyin

### Simülasyon Hataları

**Sorun**: UART çıktısı boş
- Kontrol: `uart_init()` çağrıldığından emin olun
- Kontrol: Register adresleri doğru olduğundan emin olun
- Kontrol: Simülasyon süresi yeterli olduğundan emin olun (`MAX_CYCLES`)

**Sorun**: Sonsuz döngüde takılı kalıyor
- Test: İlk komut çalışıyor mu? `uart_putc('X')` ile test edin
- Kontrol: `uart_status` register'ını okuyup durumunu kontrol edin

## 📚 Referanslar

- UART Register Tanımları: `subrepo/coremark/ceresv/core_portme.h`
- Linking Script: `subrepo/coremark/ceresv/link.ld`
- UART Implementasyonu: `rtl/periph/uart.sv`
- Mevcut Test Örnekleri: `subrepo/coremark/ceresv/`

## 🔗 Yararlı Komutlar

```bash
# Test binaries'inin boyutunu göster
size build/tests/custom/uart_hello_test.elf

# Disassembly'yi görüntüle
riscv32-unknown-elf-objdump -d build/tests/custom/uart_hello_test.elf | less

# Hex dump göster
riscv32-unknown-elf-objdump -h build/tests/custom/uart_hello_test.elf

# Symbol tablosunu göster
riscv32-unknown-elf-nm build/tests/custom/uart_hello_test.elf
```

## 💡 İpuçları

1. **Başlamak**: `uart_hello_test.c` dosyasını kopyalayarak yeni test oluşturun
2. **Debugging**: UART çıktısı ile printf debugging yapabilirsiniz
3. **Timing**: 50 MHz clock'ta bir cycle = 20 nanosecond
4. **Stack**: Stack pointer'ı linker script'te tanımlı RAM bölgesi içinde olacak şekilde ayarlayın

---

**Son Güncelleme**: 2025-12-01
**Ceres-V Sürümü**: RV32IMC_Zicsr
