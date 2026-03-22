#!/bin/bash
# ============================================================================
# UART Custom Test - Quick Start Guide
# ============================================================================
# Quick guide to writing your own UART tests on the Level-V CPU

cat << 'EOF'

╔════════════════════════════════════════════════════════════════════════════╗
║          LEVEL-V CUSTOM UART TEST - QUICK START GUIDE                       ║
╚════════════════════════════════════════════════════════════════════════════╝

🚀 STEP 1: Create test file
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  mkdir -p /home/kerim/level-v/sim/test/custom
  
  # Copy the example or create a new file:
  cp /home/kerim/level-v/sim/test/custom/uart_hello_test.c \
     /home/kerim/level-v/sim/test/custom/my_test.c

🔨 STEP 2: Build
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  cd /home/kerim/level-v
  
  # With build script (recommended):
  ./script/shell/build_level_custom_c_test.sh my_test
  
  # Or manually:
  riscv32-unknown-elf-gcc \
    -march=rv32imc -mabi=ilp32 \
    -static -mcmodel=medany \
    -fvisibility=hidden -nostdlib -nostartfiles \
    -Wl,--gc-sections \
    -Wl,-Ttext=0x80000000 \
    -o build/tests/custom/my_test.elf \
    sim/test/custom/my_test.c

🎮 STEP 3: Run
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  # Create memory file:
  riscv32-unknown-elf-objcopy -O verilog \
    build/tests/custom/my_test.elf \
    build/tests/custom/my_test.mem
  
  # Run in simulation:
  make run_verilator TEST_FILE=build/tests/custom/my_test.mem MAX_CYCLES=100000

📊 STEP 4: View output
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  cat uart_output.log

════════════════════════════════════════════════════════════════════════════

📝 BASIC CODE TEMPLATE
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

✨ HELPER FUNCTIONS (in uart_hello_test.c)
════════════════════════════════════════════════════════════════════════════

  uart_init()              - Initialize UART
  uart_putc(char)          - Send one character
  uart_puts(const char*)   - Send string
  uart_puthex(uint32_t)    - Hex number: 0xDEADBEEF
  uart_putdec(int32_t)     - Decimal number: 12345

════════════════════════════════════════════════════════════════════════════

💻 COMMAND QUICK REFERENCE
════════════════════════════════════════════════════════════════════════════

  # Build and run (one command):
  ./script/shell/build_level_custom_c_test.sh my_test && cat uart_output.log
  
  # Show disassembly:
  riscv32-unknown-elf-objdump -d build/tests/custom/my_test.elf | head -30
  
  # File size:
  size build/tests/custom/my_test.elf
  
  # Memory map:
  riscv32-unknown-elf-objdump -t build/tests/custom/my_test.elf
  
  # Clean build:
  rm -rf build/tests/custom/my_test.*
  ./script/shell/build_level_custom_c_test.sh my_test

════════════════════════════════════════════════════════════════════════════

🐛 TROUBLESHOOTING
════════════════════════════════════════════════════════════════════════════

  Problem: UART output is empty
  Fix:
    1. Ensure uart_init() is called
    2. Increase MAX_CYCLES (e.g. MIN_CYCLES=100000)
    3. Check that uart_output.log was created
  
  Problem: Build error
  Fix:
    1. Is the RISC-V toolchain installed? → which riscv32-unknown-elf-gcc
    2. Is the linker script path correct?
    3. Do you need startup code? (-nostartfiles is only for simple tests)

════════════════════════════════════════════════════════════════════════════

📚 EXAMPLE TESTS
════════════════════════════════════════════════════════════════════════════

  1. Hello World:
     uart_puts("Hello from Level-V!\n");
  
  2. Loop test:
     for (int i = 0; i < 10; i++) {
         uart_putc('0' + i);
         uart_putc(' ');
     }
  
  3. Memory test:
     uint32_t val = 0x12345678;
     uart_puts("Value: ");
     uart_puthex(val);
  
  4. Read timer:
     uint32_t cycles = *(volatile uint32_t*)0x30000000;
     uart_puts("Cycles: ");
     uart_putdec(cycles);

════════════════════════════════════════════════════════════════════════════

🔗 RELATED FILES
════════════════════════════════════════════════════════════════════════════

  Files you can copy from:

  1. Test example:
     /home/kerim/level-v/sim/test/custom/uart_hello_test.c
     
  2. Build script:
     /home/kerim/level-v/script/shell/build_level_custom_c_test.sh
     
  3. This guide:
     /home/kerim/level-v/sim/test/custom/README.md

════════════════════════════════════════════════════════════════════════════

More information:
  - Detailed guide: sim/test/custom/README.md
  - Test example: sim/test/custom/uart_hello_test.c
  - UART register definitions: subrepo/coremark/levelv/core_portme.h

════════════════════════════════════════════════════════════════════════════

EOF

# List available files
echo ""
echo "📂 EXISTING FILES:"
echo ""
ls -lh /home/kerim/level-v/sim/test/custom/ 2>/dev/null || echo "  Directory not created yet"

echo ""
echo "✅ You are ready to create your first test:"
echo ""
echo "  cd /home/kerim/level-v"
echo "  ./script/shell/build_level_custom_c_test.sh uart_hello_test"
echo ""
