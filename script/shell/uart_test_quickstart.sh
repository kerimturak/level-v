#!/bin/bash
# ============================================================================
# UART Custom Test - Quick Start Guide
# ============================================================================
# Ceres-V işlemcinizde kendi UART testlerini yazmak için hızlı rehber

cat << 'EOF'

╔════════════════════════════════════════════════════════════════════════════╗
║          CERES-V CUSTOM UART TEST - QUICK START GUIDE                     ║
╚════════════════════════════════════════════════════════════════════════════╝

🚀 ADIM 1: Test Dosyası Oluştur
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  mkdir -p /home/kerim/level-v/sim/test/custom
  
  # Örneği kopyala veya yeni dosya oluştur:
  cp /home/kerim/level-v/sim/test/custom/uart_hello_test.c \
     /home/kerim/level-v/sim/test/custom/my_test.c

🔨 ADIM 2: Derle
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  cd /home/kerim/level-v
  
  # Build script ile (önerilir):
  ./script/shell/build_custom_test.sh my_test
  
  # Veya manuel:
  riscv32-unknown-elf-gcc \
    -march=rv32imc -mabi=ilp32 \
    -static -mcmodel=medany \
    -fvisibility=hidden -nostdlib -nostartfiles \
    -Wl,--gc-sections \
    -Wl,-Ttext=0x80000000 \
    -o build/tests/custom/my_test.elf \
    sim/test/custom/my_test.c

🎮 ADIM 3: Çalıştır
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  # Memory dosyası oluştur:
  riscv32-unknown-elf-objcopy -O verilog \
    build/tests/custom/my_test.elf \
    build/tests/custom/my_test.mem
  
  # Simülasyonda çalıştır:
  make run_verilator TEST_FILE=build/tests/custom/my_test.mem MAX_CYCLES=100000

📊 ADIM 4: Çıktıyı Göster
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  cat uart_output.log

════════════════════════════════════════════════════════════════════════════

📝 TEMEL KOD ŞABLONU
════════════════════════════════════════════════════════════════════════════

  #include <stdint.h>
  
  #define UART_CTRL        (*(volatile uint32_t*)0x20000000)
  #define UART_STATUS      (*(volatile uint32_t*)0x20000004)
  #define UART_WDATA       (*(volatile uint32_t*)0x2000000c)
  #define UART_STATUS_TX_FULL 0x1
  
  #define CPU_CLK    50000000
  #define BAUD_RATE  115200
  
  void uart_init(void) {
      uint32_t baud_div = CPU_CLK / BAUD_RATE;
      UART_CTRL = (baud_div << 16) | 0x3;  // TX/RX enable
  }
  
  void uart_putc(char c) {
      while (UART_STATUS & UART_STATUS_TX_FULL);
      UART_WDATA = c;
  }
  
  void uart_puts(const char *s) {
      while (*s) uart_putc(*s++);
  }
  
  int main(void) {
      uart_init();
      uart_puts("Hello!\n");
      while (1);
      return 0;
  }

════════════════════════════════════════════════════════════════════════════

✨ FAYDALI FONKSIYONLAR (uart_hello_test.c içinde)
════════════════════════════════════════════════════════════════════════════

  uart_init()              - UART başlat
  uart_putc(char)          - Tek karakter gönder
  uart_puts(const char*)   - String gönder
  uart_puthex(uint32_t)    - Hex sayı: 0xDEADBEEF
  uart_putdec(int32_t)     - Decimal sayı: 12345

════════════════════════════════════════════════════════════════════════════

💻 KOMUT HIZLI REFERANSI
════════════════════════════════════════════════════════════════════════════

  # Derle ve çalıştır (hepsi bir komut):
  ./script/shell/build_custom_test.sh my_test && cat uart_output.log
  
  # Disassembly göster:
  riscv32-unknown-elf-objdump -d build/tests/custom/my_test.elf | head -30
  
  # Dosya boyutu:
  size build/tests/custom/my_test.elf
  
  # Memory map:
  riscv32-unknown-elf-objdump -t build/tests/custom/my_test.elf
  
  # Clean build:
  rm -rf build/tests/custom/my_test.*
  ./script/shell/build_custom_test.sh my_test

════════════════════════════════════════════════════════════════════════════

🐛 SORUN ÇÖZÜMLERI
════════════════════════════════════════════════════════════════════════════

  Problem: UART çıktısı boş
  Çözüm:
    1. uart_init() çağrıldığını kontrol et
    2. MAX_CYCLES'ı artır (MIN_CYCLES=100000)
    3. uart_output.log dosyasının oluştuğunu kontrol et
  
  Problem: Derleme hatası
  Çözüm:
    1. RISC-V toolchain kurulu mu? → which riscv32-unknown-elf-gcc
    2. Linker scriptinin yolu doğru mu?
    3. Başlangıç kodu gerekli mi? (-nostartfiles yalnızca basit testler için)

════════════════════════════════════════════════════════════════════════════

📚 ÖRNEK TESTLER
════════════════════════════════════════════════════════════════════════════

  1. Hello World:
     uart_puts("Hello from Ceres-V!\n");
  
  2. Döngü Testi:
     for (int i = 0; i < 10; i++) {
         uart_putc('0' + i);
         uart_putc(' ');
     }
  
  3. Hafıza Testi:
     uint32_t val = 0x12345678;
     uart_puts("Value: ");
     uart_puthex(val);
  
  4. Timer Okuma:
     uint32_t cycles = *(volatile uint32_t*)0x30000000;
     uart_puts("Cycles: ");
     uart_putdec(cycles);

════════════════════════════════════════════════════════════════════════════

🔗 İÇ DOSYALAR
════════════════════════════════════════════════════════════════════════════

  Hâlihazırda kopyalanan dosyalar:

  1. Test Örneği:
     /home/kerim/level-v/sim/test/custom/uart_hello_test.c
     
  2. Build Script:
     /home/kerim/level-v/script/shell/build_custom_test.sh
     
  3. Bu Rehber:
     /home/kerim/level-v/sim/test/custom/README.md

════════════════════════════════════════════════════════════════════════════

Daha fazla bilgi için:
  - Detaylı rehber: sim/test/custom/README.md
  - Test örneği: sim/test/custom/uart_hello_test.c
  - UART register tanımları: subrepo/coremark/ceresv/core_portme.h

════════════════════════════════════════════════════════════════════════════

EOF

# List available files
echo ""
echo "📂 MEVCUT DOSYALAR:"
echo ""
ls -lh /home/kerim/level-v/sim/test/custom/ 2>/dev/null || echo "  Dizin henüz oluşturulmadı"

echo ""
echo "✅ Hazırsınız! İlk testinizi oluşturmaya başlayın:"
echo ""
echo "  cd /home/kerim/level-v"
echo "  ./script/shell/build_custom_test.sh uart_hello_test"
echo ""
