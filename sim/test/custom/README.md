# Custom UART test programs (Level-V)

In this directory you can author, build, and run your own UART test programs on the Level-V core.

## Directory layout

```
sim/test/custom/
├── uart_hello_test.c          # Example: simple UART hello message
├── dsp_fir_mac_test.c         # DSP-style FIR + mcycle (MAC load)
├── crc32_demo_test.c          # CRC-32 over 4 KiB buffer (MiBench-like flavour)
├── vga_demo.c                 # 640×480 1bpp framebuffer in RAM + VGA enable
├── i2c_test.c / spi_test.c … # Peripherals (match pins on your FPGA board)
├── README.md                   # This file
└── (other test sources)
```

### FPGA / compliance

| Goal | What to use |
|------|-------------|
| UART demo / bring-up | `custom_build` tests here, Embench, Dhrystone, CoreMark |
| ISA / RE compliance | `make run_verilator TEST_NAME=... TEST_TYPE=isa` — finish via **tohost** / sim log, not UART |
| riscv-arch-test | `TEST_TYPE=arch` — PASS/FAIL **PC** in simulation |
| BEEBS (full suite) | `make beebs_clone` then port chip/board per `env/beebs/README.md` |

## Prerequisites

### RISC-V toolchain

```bash
# Required tools
- riscv32-unknown-elf-gcc
- riscv32-unknown-elf-objcopy
- riscv32-unknown-elf-objdump
```

## Writing tests

### Minimal template

```c
#include <stdint.h>

/* UART register addresses */
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

### UART helper routines

See `uart_hello_test.c` for a fuller example:

- `uart_init()` — initialize UART
- `uart_putc(char)` — send one character
- `uart_puts(const char*)` — send a string
- `uart_puthex(uint32_t)` — print hex
- `uart_putdec(int32_t)` — print decimal

## Build and run

### Quick path (build script)

```bash
chmod +x /path/to/level-v/script/shell/build_level_custom_c_test.sh

# Build and run one test
./script/shell/build_level_custom_c_test.sh uart_hello_test

# Other tests
./script/shell/build_level_custom_c_test.sh my_custom_test
```

### UART metin bozulması (FPGA / gerçek serial)

Baud, **CPU saatine** ve host ayarına bağlıdır. Tüm testler `env/common/cpu_clock.h` içindeki **`CPU_CLK_HZ`** ile **115200** bps hesaplar (RTL `level_param.sv` `CPU_CLK` ile aynı olmalı). Eski örneklerde 50 MHz + 5 Mbaud vardı; PC **115200** açıkken bu çıktıyı çöpler.

Farklı kristal kullanıyorsan: derlerken `-DCPU_CLK_HZ=...UL` ver veya `cpu_clock.h` / makefile’daki tanımı güncelle.

### Linker RAM size

`make custom_build` uses `env/custom/link.ld` (**40 KiB** RAM) to match typical Basys3-style BRAM budgets; `vga_demo` only paints the lines that fit below RAM top and relies on RTL black-fill past end of RAM.

### Manual build

```bash
cd /path/to/level-v

# 1. Compile
riscv32-unknown-elf-gcc \
    -march=rv32imc -mabi=ilp32 \
    -static -mcmodel=medany \
    -fvisibility=hidden -nostdlib -nostartfiles \
    -Wl,--gc-sections \
    -I env/common \
    -Wl,-T env/custom/link.ld \
    -o build/tests/custom/uart_hello_test.elf \
    sim/test/custom/startup.s sim/test/custom/uart_hello_test.c

# 2. Raw binary
riscv32-unknown-elf-objcopy -O binary \
    build/tests/custom/uart_hello_test.elf \
    build/tests/custom/uart_hello_test.bin

# 3. Verilog memory image
riscv32-unknown-elf-objcopy -O verilog \
    build/tests/custom/uart_hello_test.elf \
    build/tests/custom/uart_hello_test.mem
```

### Run in simulation

```bash
cd /path/to/level-v

# Verilator (adjust TEST_FILE / target per your makefile)
make run_verilator TEST_FILE=build/tests/custom/uart_hello_test.mem MAX_CYCLES=100000

# Watch UART output
tail -f uart_output.log
```

## Checking output

When the program writes to UART, output typically lands in `uart_output.log`:

```bash
cat uart_output.log

make run_verilator TEST_FILE=build/tests/custom/uart_hello_test.mem MAX_CYCLES=100000 && cat uart_output.log
```

## Examples

### Example 1: simple message

```c
int main(void) {
    uart_init();
    uart_puts("Hello from Level!\n");
    while (1);
    return 0;
}
```

### Example 2: loop

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

### Example 3: memory / address print

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

## Troubleshooting

### Build errors

**Error**: `riscv32-unknown-elf-gcc: command not found`  
**Fix**: Install a RISC-V toolchain and ensure it is on `PATH`.

**Error**: `undefined reference to 'main'`  
**Fix**: Drop `-nostartfiles` or add appropriate startup code.

### Simulation issues

**Problem**: empty UART log  
**Check**: `uart_init()` is called; register addresses match your SoC map; `MAX_CYCLES` is large enough.

**Problem**: appears stuck in a loop  
**Try**: emit a single `uart_putc('X')` first; read `UART_STATUS` in the waveform/log.

## References

- UART register layout: `env/coremark/levelv/core_portme.h` (CoreMark port example)
- Linker script example: `env/coremark/levelv/link.ld`
- UART RTL: `rtl/periph/uart/uart.sv` (path may vary slightly; see `rtl/periph/uart/`)

## Useful commands

```bash
size build/tests/custom/uart_hello_test.elf
riscv32-unknown-elf-objdump -d build/tests/custom/uart_hello_test.elf | less
riscv32-unknown-elf-objdump -h build/tests/custom/uart_hello_test.elf
riscv32-unknown-elf-nm build/tests/custom/uart_hello_test.elf
```

## Tips

1. **Starting out**: copy `uart_hello_test.c` and modify.
2. **Debug**: UART prints are your bare-metal “printf”.
3. **Timing**: at 50 MHz, one cycle is 20 ns.
4. **Stack**: keep the stack inside RAM defined by your linker script.

---

**Last updated**: 2025-12-01  
**Configuration**: RV32IMC_Zicsr
