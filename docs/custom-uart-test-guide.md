# Level-V Custom UART Test System — Quick Reference

## Setup Complete

You can now write, build, and run your own C tests in simulation for your **Level-V RV32IMC_Zicsr** core.

---

## System Components

| File | Location | Description |
|------|----------|-------------|
| **uart_hello_test.c** | `sim/test/custom/` | Sample UART test (all-in-one reference) |
| **build_level_custom_c_test.sh** | `script/shell/` | Build and run script |
| **custom test targets** | root `makefile` | Targets such as `custom_test` |
| **README.md** | `sim/test/custom/` | Detailed guide and examples |
| **guide_level_uart_custom_test.sh** | `script/shell/` | Quick start script |

---

## Getting Started

### 1. Go to the repository root
```bash
cd /home/kerim/level-v
```

### 2. Build and run the sample test
```bash
make custom_test TEST=uart_hello_test
```

### 3. View UART output
```bash
cat uart_output.log
```

---

## Writing Your Own Test

### Step 1: Create a new file
```bash
cp sim/test/custom/uart_hello_test.c sim/test/custom/my_test.c
```

### Step 2: Write your C code
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

### Step 3: Build and run
```bash
make custom_test TEST=my_test
```

---

## Utility Makefile Commands

```bash
# List tests
make custom_list

# Build
make custom_build TEST=my_test

# Run
make custom_run TEST=my_test MAX_CYCLES=100000

# Build + run
make custom_test TEST=my_test

# Clean
make custom_clean TEST=my_test
make custom_clean  # all

# Disassembly
make custom_disass TEST=my_test

# File size
make custom_size TEST=my_test

# Info
make custom_info TEST=my_test

# Help
make custom_help
```

---

## Ready-Made UART Helpers

Defined in `uart_hello_test.c`:

- `uart_init()` — initialize UART
- `uart_putc(char)` — send one character
- `uart_puts(const char*)` — send a string
- `uart_puthex(uint32_t)` — send hex (e.g. 0xDEADBEEF)
- `uart_putdec(int32_t)` — send decimal (e.g. 12345)

---

## Example Tests

### "Hello World"
```c
int main(void) {
    uart_init();
    uart_puts("Hello World!\n");
    while (1);
    return 0;
}
```

### Loop Test
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

### Show Memory Address
```c
int main(void) {
    uart_init();
    uint32_t val = 0x12345678;
    uart_puts("Address: ");
    uart_puthex((uint32_t)&val);
    uart_puts(" = ");
    uart_puthex(val);
    uart_puts("\n");
    while (1);
    return 0;
}
```

### Read Timer
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

## Hardware Addresses

### UART Registers (0x20000000+)
```
0x20000000  UART_CTRL      (Control: [31:16] baud_div, [1] rx_en, [0] tx_en)
0x20000004  UART_STATUS    (Status: tx_full, rx_full, tx_empty, rx_empty)
0x20000008  UART_RDATA     (RX data — read)
0x2000000c  UART_WDATA     (TX data — write)
```

### Timer (0x30000000+)
```
0x30000000  TIMER_LOW      (64-bit timer, low 32 bits)
0x30000004  TIMER_HIGH     (64-bit timer, high 32 bits)
```

### CPU Characteristics
```
ISA:        RV32IMC_Zicsr
Clock:      50 MHz
UART Baud:  115200 bps
```

---

## Directory Layout

```
level-v/
├── sim/test/custom/
│   ├── uart_hello_test.c    # Sample test
│   ├── README.md             # Detailed guide
│   └── (your tests)
├── script/shell/
│   ├── build_level_custom_c_test.sh  # Build script
│   └── guide_level_uart_custom_test.sh # Quick start
├── makefile                  # Includes custom_test targets
└── build/tests/custom/
    ├── my_test.elf           # Executable
    ├── my_test.mem           # Verilog memory
    ├── my_test.hex           # Intel HEX
    ├── my_test.bin           # Binary
    └── my_test.disass        # Disassembly
```

---

## Troubleshooting

| Problem | Solution |
|---------|----------|
| **Empty UART output** | Ensure `uart_init()` is called; increase MAX_CYCLES |
| **"gcc not found"** | Is the RISC-V toolchain installed? `which riscv32-unknown-elf-gcc` |
| **Compile error** | Try removing `-nostartfiles` or add startup code |
| **Simulation hang** | Lower MAX_CYCLES; verify register addresses |

---

## Simulation Outputs

Each test run may produce:

- **uart_output.log** — UART TX output
- **build/tests/custom/sim.log** — Simulation log
- **build/tests/custom/compile.log** — Compile log

---

## References

- Detailed guide: `sim/test/custom/README.md`
- UART register definitions: `subrepo/coremark/levelv/core_portme.h`
- Linker script: `subrepo/coremark/levelv/link.ld`
- CoreMark example: `subrepo/coremark/levelv/core_portme.c`

---

## Next Steps

1. Write and run a simple hello test
2. Try UART print debugging
3. Experiment with loops and control flow
4. Add timer reads
5. Build more complex behavior

---

**Last updated:** 2025-12-01  
**Level-V:** RV32IMC_Zicsr  
**Status:** Ready to use

If you have questions, check the relevant files or run the build script with the `-v` (verbose) flag.
