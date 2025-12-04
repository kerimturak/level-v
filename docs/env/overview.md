# Environment (env/) - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Common Environment](#common-environment)
3. [riscv-test Environment](#riscv-test-environment)
4. [riscv-arch-test Environment](#riscv-arch-test-environment)
5. [Imperas Environment](#imperas-environment)
6. [CoreMark Environment](#coremark-environment)
7. [Dhrystone Environment](#dhrystone-environment)
8. [Embench Environment](#embench-environment)
9. [Torture Environment](#torture-environment)
10. [RISCV-DV Environment](#riscv-dv-environment)
11. [RISCV-Formal Environment](#riscv-formal-environment)

---

## Genel Bakış

### Dizin Yapısı

```
env/
├── common/              # Ortak runtime dosyaları
│   ├── crt.S            # C runtime startup
│   ├── syscalls.c       # System call stubs
│   ├── test.ld          # Generic linker script
│   └── util.h           # Utility macros
├── riscv-test/          # riscv-tests environment
│   └── ceres/
│       ├── link.ld
│       └── riscv_test.h
├── riscv-arch-test/     # riscv-arch-test environment
│   └── ceres/
│       ├── link.ld
│       └── model_test.h
├── imperas/             # Imperas tests environment
│   ├── link.ld
│   └── model_test.h
├── coremark/            # CoreMark benchmark
│   └── ceresv/
│       ├── core_portme.c
│       ├── core_portme.h
│       ├── core_portme.mak
│       ├── crt0.S
│       ├── ee_printf.c
│       └── link.ld
├── dhrystone/           # Dhrystone benchmark
│   ├── crt0.S
│   ├── dhry.h
│   ├── dhry_1.c
│   ├── dhry_2.c
│   ├── link.ld
│   └── syscalls.c
├── embench/             # Embench-IoT benchmark
│   ├── boardsupport.c
│   ├── boardsupport.h
│   ├── crt0.S
│   ├── link.ld
│   └── syscalls.c
├── torture/             # Torture test
│   ├── crt0.S
│   └── link.ld
├── riscv-dv/            # RISCV-DV generated tests
│   └── link.ld
└── riscv-formal/        # Formal verification
    └── rvfi_wrapper.sv
```

### Environment Yapısı

Her test environment şunları içerir:

```
env/<suite>/
├── link.ld          # Linker script (memory map)
├── crt0.S           # C runtime startup assembly
├── model_test.h     # Test framework macros (RVMODEL_*)
└── syscalls.c       # System call implementations
```

---

## Common Environment

**Dizin:** `env/common/`

Tüm test'lerin ortak kullandığı runtime dosyaları.

### crt.S - C Runtime Startup

```riscv
#include "encoding.h"

#if __riscv_xlen == 64
# define LREG ld
# define SREG sd
# define REGBYTES 8
#else
# define LREG lw
# define SREG sw
# define REGBYTES 4
#endif

  .section ".text.init"
  .globl _start
_start:
  # Register initialization (x1-x31 = 0)
  li  x1, 0
  li  x2, 0
  # ... (x3-x31)
  
  # Enable FPU/Vector if present
  li t0, MSTATUS_FS | MSTATUS_XS | MSTATUS_VS
  csrs mstatus, t0

  # XLEN check
  li t0, 1
  slli t0, t0, 31
#if __riscv_xlen == 64
  bgez t0, 1f
#else
  bltz t0, 1f
#endif
  # XLEN mismatch: halt
2:
  li a0, 1
  sw a0, tohost, t0
  j 2b
1:
  # Continue to main
  ...
```

### test.ld - Generic Linker Script

```linkerscript
OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY {
  RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 32K
}

SECTIONS {
  . = ORIGIN(RAM);

  .text.init : { *(.text.init) } > RAM
  
  . = ALIGN(64);
  .tohost : { *(.tohost) } > RAM

  .text : { *(.text) } > RAM
  .data : { *(.data) } > RAM
  
  .sdata : {
    __global_pointer$ = . + 0x800;
    *(.srodata*)
    *(.sdata*)
  } > RAM

  .sbss : { *(.sbss*) *(.scommon) } > RAM
  .bss  : { *(.bss*) } > RAM

  .tdata : { _tdata_begin = .; *(.tdata) _tdata_end = .; } > RAM
  .tbss  : { *(.tbss) _tbss_end = .; } > RAM

  _end = .;
  _stack_top = ORIGIN(RAM) + LENGTH(RAM);
}
```

### syscalls.c - System Call Stubs

```c
#include <sys/stat.h>

// Minimal syscall implementations for bare-metal
int _close(int fd) { return -1; }
int _fstat(int fd, struct stat *st) { st->st_mode = S_IFCHR; return 0; }
int _isatty(int fd) { return 1; }
int _lseek(int fd, int ptr, int dir) { return 0; }
int _read(int fd, char *ptr, int len) { return 0; }

// Write to UART
int _write(int fd, char *ptr, int len) {
    for (int i = 0; i < len; i++) {
        // UART write
        *(volatile char*)0x20000000 = ptr[i];
    }
    return len;
}

void _exit(int status) {
    while (1);
}
```

---

## riscv-test Environment

**Dizin:** `env/riscv-test/ceres/`

riscv-tests ISA compliance testleri için environment.

### riscv_test.h

```cpp
#ifndef _ENV_PHYSICAL_SINGLE_CORE_H
#define _ENV_PHYSICAL_SINGLE_CORE_H

#include "../encoding.h"

// ═══════════════════════════════════════════════════════════════
// RV32IMC Configuration Macros
// ═══════════════════════════════════════════════════════════════

// RV32IMC için minimal init
#define RVTEST_RV32U   \
  .macro init;         \
  .endm

// RV64 variants (empty for RV32)
#define RVTEST_RV64U   \
  .macro init;         \
  .endm

// FPU/Vector support (disabled)
#define RVTEST_RV32UF  \
  .macro init;         \
  .endm

// ═══════════════════════════════════════════════════════════════
// Test Entry/Exit Macros
// ═══════════════════════════════════════════════════════════════

#define RVTEST_CODE_BEGIN           \
        .section .text.init;        \
        .align  6;                  \
        .globl _start;              \
_start:                             \
        /* Reset handler */         \
        j reset_vector;             \
        /* ... */

#define RVTEST_CODE_END

#define RVTEST_PASS                 \
        fence;                      \
        li TESTNUM, 1;              \
        la t0, tohost;              \
        sw TESTNUM, 0(t0);          \
        j .;

#define RVTEST_FAIL                 \
        fence;                      \
        sll TESTNUM, TESTNUM, 1;    \
        or TESTNUM, TESTNUM, 1;     \
        la t0, tohost;              \
        sw TESTNUM, 0(t0);          \
        j .;

// ═══════════════════════════════════════════════════════════════
// Data Section Macros
// ═══════════════════════════════════════════════════════════════

#define RVTEST_DATA_BEGIN           \
        .align 4;                   \
        .global begin_signature;    \
begin_signature:

#define RVTEST_DATA_END             \
        .align 4;                   \
        .global end_signature;      \
end_signature:                      \
        .align 4;                   \
        .global tohost;             \
tohost: .dword 0;                   \
        .global fromhost;           \
fromhost: .dword 0;

#endif
```

### Test Pass/Fail Mekanizması

```
┌─────────────────────────────────────────────────────────────────┐
│                    TEST PASS/FAIL MECHANISM                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   Test Code                  tohost Memory                       │
│   ─────────                  ─────────────                       │
│                                                                  │
│   RVTEST_PASS:               tohost = 1                          │
│   ├─ fence                   (PASS: odd number, testnum=1)       │
│   ├─ li TESTNUM, 1                                               │
│   ├─ sw TESTNUM, tohost                                          │
│   └─ j .                                                         │
│                                                                  │
│   RVTEST_FAIL:               tohost = (testnum << 1) | 1         │
│   ├─ fence                   (FAIL: odd number, testnum>1)       │
│   ├─ sll TESTNUM, 1                                              │
│   ├─ or TESTNUM, 1                                               │
│   ├─ sw TESTNUM, tohost                                          │
│   └─ j .                                                         │
│                                                                  │
│   Testbench monitors tohost:                                     │
│   ├─ tohost != 0 → test complete                                 │
│   ├─ tohost == 1 → PASS                                          │
│   └─ tohost != 1 → FAIL (testnum = tohost >> 1)                  │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## riscv-arch-test Environment

**Dizin:** `env/riscv-arch-test/ceres/`

RISC-V Architecture Test için environment.

### model_test.h

```cpp
#ifndef _MODEL_TEST_H
#define _MODEL_TEST_H

// ═══════════════════════════════════════════════════════════════
// RVMODEL Macros for riscv-arch-test
// ═══════════════════════════════════════════════════════════════

#define RVMODEL_BOOT                                                \
    j _rvtest_boot_continue;                                        \
    .align 4;                                                       \
    .global rvtest_trap_handler;                                    \
rvtest_trap_handler:                                                \
    /* Trap handler implementation */                               \
    csrr t0, mcause;                                                \
    csrr t1, mepc;                                                  \
    /* Handle EBREAK, ECALL, etc. */                                \
    ...                                                             \
_rvtest_boot_continue:                                              \
    la t0, rvtest_trap_handler;                                     \
    csrw mtvec, t0;

#define RVMODEL_HALT                                                \
    fence;                                                          \
    li a7, 93;                /* exit syscall */                    \
    li a0, 0;                 /* exit code 0 */                     \
    ecall;                                                          \
halt_loop:                                                          \
    j halt_loop;

#define RVMODEL_DATA_SECTION                                        \
    .pushsection .tohost,"aw",@progbits;                            \
    .align 8;                                                       \
    .global tohost;                                                 \
tohost: .dword 0;                                                   \
    .global fromhost;                                               \
fromhost: .dword 0;                                                 \
    .popsection;

#define RVMODEL_IO_WRITE_STR(_SP, _STR)     /* Not implemented */
#define RVMODEL_IO_CHECK()                  /* Not implemented */

#endif
```

---

## Imperas Environment

**Dizin:** `env/imperas/`

Imperas riscv-tests extended suite için environment.

### model_test.h

```cpp
#ifndef _MODEL_TEST_H
#define _MODEL_TEST_H

#define XLEN 32
#define ALIGNMENT 2
#define TESTNUM gp

// Boot sequence with trap handler
#define RVMODEL_BOOT                                                \
    j _rvtest_boot_continue;                                        \
    .align 4;                                                       \
    .global rvtest_trap_handler;                                    \
rvtest_trap_handler:                                                \
    csrr t0, mcause;                                                \
    csrr t1, mepc;                                                  \
    /* Check EBREAK (mcause = 3) */                                 \
    li t2, 3;                                                       \
    bne t0, t2, 1f;                                                 \
    /* EBREAK: check if compressed */                               \
    lhu t3, 0(t1);                                                  \
    andi t3, t3, 0x3;                                               \
    li t4, 0x3;                                                     \
    beq t3, t4, 2f;                                                 \
    addi t1, t1, 2;             /* Compressed: PC += 2 */           \
    j 3f;                                                           \
2:  addi t1, t1, 4;             /* 32-bit: PC += 4 */               \
3:  csrw mepc, t1;                                                  \
    mret;                                                           \
1:  /* Check ECALL (mcause = 11) */                                 \
    li t2, 11;                                                      \
    bne t0, t2, 4f;                                                 \
    /* ECALL: check exit syscall (a7 = 93) */                       \
    li t2, 93;                                                      \
    bne a7, t2, 5f;                                                 \
    j halt_loop;                                                    \
5:  addi t1, t1, 4;                                                 \
    csrw mepc, t1;                                                  \
    mret;                                                           \
4:  /* Other exceptions */                                          \
    addi t1, t1, 4;                                                 \
    csrw mepc, t1;                                                  \
    mret;                                                           \
_rvtest_boot_continue:                                              \
    la t0, rvtest_trap_handler;                                     \
    csrw mtvec, t0;

#define RVMODEL_HALT                                                \
    fence;                                                          \
    li a7, 93;                                                      \
    li a0, 0;                                                       \
    ecall;                                                          \
halt_loop:                                                          \
    j halt_loop;

#endif
```

---

## CoreMark Environment

**Dizin:** `env/coremark/ceresv/`

EEMBC CoreMark benchmark için Ceres-V port.

### Dosya Listesi

| Dosya | Açıklama |
|-------|----------|
| `core_portme.c` | Platform-specific implementations |
| `core_portme.h` | Platform configuration |
| `core_portme.mak` | Build configuration |
| `crt0.S` | Startup assembly |
| `ee_printf.c` | Embedded printf |
| `cvt.c` | Number conversion utilities |
| `link.ld` | CoreMark linker script |
| `memory_map.yaml` | Memory configuration |

### core_portme.h

```c
#ifndef CORE_PORTME_H
#define CORE_PORTME_H

// ═══════════════════════════════════════════════════════════════
// Ceres-V Hardware Configuration
// ═══════════════════════════════════════════════════════════════

#define CPU_CLK          50000000   /* 50 MHz */
#define BAUD_RATE        115200

// UART Registers
#define UART_CTRL        (*(volatile uint32_t*)0x20000000)
#define UART_STATUS      (*(volatile uint32_t*)0x20000004)
#define UART_RDATA       (*(volatile uint32_t*)0x20000008)
#define UART_WDATA       (*(volatile uint32_t*)0x2000000c)

#define UART_STATUS_TX_FULL   0x1
#define UART_CTRL_TX_EN       0x1
#define UART_CTRL_RX_EN       0x2

// Timer Registers (CLINT)
#define TIMER_LOW        (*(volatile uint32_t*)0x30000000)
#define TIMER_HIGH       (*(volatile uint32_t*)0x30000004)

// ═══════════════════════════════════════════════════════════════
// CoreMark Configuration
// ═══════════════════════════════════════════════════════════════

#define ITERATIONS       1000
#define CLOCKS_PER_SEC   CPU_CLK

typedef signed int   ee_s32;
typedef unsigned int ee_u32;
typedef ee_u32       CORE_TICKS;
typedef ee_u32       CORETIMETYPE;

#define HAS_FLOAT       0
#define HAS_TIME_H      0
#define USE_CLOCK       0
#define HAS_STDIO       0
#define HAS_PRINTF      0
#define MAIN_HAS_NOARGC 1
#define MAIN_HAS_NORETURN 0

#define COMPILER_VERSION "GCC"
#define COMPILER_FLAGS   "-O3 -march=rv32imc"
#define MEM_LOCATION     "STACK"

// Memory configuration
#define MEM_METHOD       MEM_STACK
#define SEED_METHOD      SEED_VOLATILE
#define MULTITHREAD      1
#define USE_PTHREAD      0
#define USE_FORK         0
#define USE_SOCKET       0

// Portable types
#define ee_ptr_int       unsigned int
#define align_mem(x)     (void *)(4 + ((((ee_ptr_int)(x) - 1) / 4) * 4))

#endif
```

### core_portme.c (özet)

```c
#include "coremark.h"
#include "core_portme.h"

// UART Functions
static void uart_init(void) {
    uint32_t baud_div = CPU_CLK / BAUD_RATE;
    UART_CTRL = (baud_div << 16) | UART_CTRL_TX_EN | UART_CTRL_RX_EN;
}

void uart_putc(char c) {
    while (UART_STATUS & UART_STATUS_TX_FULL);
    UART_WDATA = (uint32_t)c;
}

// Timer Functions
static CORETIMETYPE read_timer(void) {
    return TIMER_LOW;
}

// CoreMark Required Functions
void portable_init(core_portable *p, int *argc, char *argv[]) {
    uart_init();
    p->portable_id = 0;
}

void portable_fini(core_portable *p) {
    // Cleanup
}

CORE_TICKS get_time(void) {
    return read_timer();
}

secs_ret time_in_secs(CORE_TICKS ticks) {
    return (secs_ret)ticks / (secs_ret)CLOCKS_PER_SEC;
}
```

---

## Dhrystone Environment

**Dizin:** `env/dhrystone/`

Dhrystone benchmark için environment.

### Dosya Listesi

| Dosya | Açıklama |
|-------|----------|
| `dhry.h` | Dhrystone header |
| `dhry_1.c` | Dhrystone part 1 |
| `dhry_2.c` | Dhrystone part 2 |
| `crt0.S` | Startup |
| `syscalls.c` | System calls |
| `link.ld` | Linker script |

---

## Embench Environment

**Dizin:** `env/embench/`

Embench-IoT benchmark suite için environment.

### boardsupport.c

```c
#include "boardsupport.h"

// Timer read for cycle counting
uint64_t read_mcycle(void) {
    uint32_t lo, hi;
    asm volatile (
        "csrr %0, mcycle\n"
        "csrr %1, mcycleh\n"
        : "=r"(lo), "=r"(hi)
    );
    return ((uint64_t)hi << 32) | lo;
}

void initialise_board(void) {
    // Board-specific initialization
}

void start_trigger(void) {
    // Start performance measurement
}

void stop_trigger(void) {
    // Stop performance measurement
}
```

---

## Torture Environment

**Dizin:** `env/torture/`

Random instruction torture testleri için minimal environment.

### crt0.S

```riscv
.section .text.init
.globl _start

_start:
    # Initialize stack
    la sp, _stack_top
    
    # Clear BSS
    la t0, _bss_start
    la t1, _bss_end
1:  bgeu t0, t1, 2f
    sw zero, 0(t0)
    addi t0, t0, 4
    j 1b
2:
    # Jump to test
    jal ra, main
    
    # Halt
3:  j 3b
```

---

## RISCV-DV Environment

**Dizin:** `env/riscv-dv/`

RISCV-DV generated random testleri için environment.

### link.ld

```linkerscript
OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY {
  RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 128K
}

SECTIONS {
  .text : { *(.text*) } > RAM
  .data : { *(.data*) } > RAM
  .bss  : { *(.bss*)  } > RAM
  _stack_top = ORIGIN(RAM) + LENGTH(RAM);
}
```

---

## RISCV-Formal Environment

**Dizin:** `env/riscv-formal/`

Formal verification için RVFI wrapper.

### rvfi_wrapper.sv

```systemverilog
/* RISC-V Formal Interface (RVFI) Wrapper for Ceres-V */

`default_nettype none

module rvfi_wrapper (
    input wire clock,
    input wire reset,

    // RVFI output signals
    output wire        rvfi_valid,
    output wire [63:0] rvfi_order,
    output wire [31:0] rvfi_insn,
    output wire        rvfi_trap,
    output wire        rvfi_halt,
    output wire        rvfi_intr,
    output wire [ 1:0] rvfi_mode,
    output wire [ 1:0] rvfi_ixl,

    // Register file
    output wire [ 4:0] rvfi_rs1_addr,
    output wire [ 4:0] rvfi_rs2_addr,
    output wire [31:0] rvfi_rs1_rdata,
    output wire [31:0] rvfi_rs2_rdata,
    output wire [ 4:0] rvfi_rd_addr,
    output wire [31:0] rvfi_rd_wdata,

    // Program counter
    output wire [31:0] rvfi_pc_rdata,
    output wire [31:0] rvfi_pc_wdata,

    // Memory access
    output wire [31:0] rvfi_mem_addr,
    output wire [ 3:0] rvfi_mem_rmask,
    output wire [ 3:0] rvfi_mem_wmask,
    output wire [31:0] rvfi_mem_rdata,
    output wire [31:0] rvfi_mem_wdata
);

  // Simple Memory Model
  reg [31:0] mem [0:16383];  // 64KB

  // Instruction counter
  reg [63:0] insn_order;

  always @(posedge clock) begin
    if (reset) insn_order <= 64'h0;
    else if (rvfi_valid) insn_order <= insn_order + 1;
  end

  // TODO: Connect to actual CPU RVFI signals
  // Current implementation is placeholder

endmodule
```

---

## Memory Map Özeti

Tüm environment'lar aşağıdaki memory map'i kullanır:

| Adres | Boyut | Bölge |
|-------|-------|-------|
| 0x8000_0000 | 32-128KB | RAM (Code + Data + Stack) |
| 0x2000_0000 | 64KB | Peripherals |
| 0x3000_0000 | 64KB | CLINT (Timer) |

---

## Özet

Environment dizini:

1. **common/**: Ortak runtime (crt.S, syscalls.c, linker)
2. **riscv-test/**: ISA compliance macros
3. **riscv-arch-test/**: Architecture test macros
4. **imperas/**: Extended test macros
5. **coremark/**: CoreMark port
6. **dhrystone/**: Dhrystone benchmark
7. **embench/**: Embench-IoT support
8. **torture/**: Minimal torture environment
9. **riscv-dv/**: Random test support
10. **riscv-formal/**: RVFI wrapper
