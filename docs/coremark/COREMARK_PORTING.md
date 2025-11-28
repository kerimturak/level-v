# CoreMark Porting Guide for Ceres-V RV32IMC_Zicsr

Bu döküman, CoreMark benchmark'ının Ceres-V RV32IMC_Zicsr işlemcisi için nasıl port edildiğini açıklar.

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Dosya Yapısı](#dosya-yapısı)
3. [Donanım Konfigürasyonu](#donanım-konfigürasyonu)
4. [Port Dosyaları](#port-dosyaları)
5. [Derleme ve Kullanım](#derleme-ve-kullanım)
6. [Çıktı Dosyaları](#çıktı-dosyaları)
7. [Sorun Giderme](#sorun-giderme)

---

## Genel Bakış

CoreMark, EEMBC (Embedded Microprocessor Benchmark Consortium) tarafından geliştirilen, gömülü sistemler için standart bir benchmark'tır. Bu port, CoreMark'ın Ceres-V RV32IMC_Zicsr işlemcisinde çalışmasını sağlar.

### Hedef Platform
- **İşlemci**: Ceres-V
- **ISA**: RV32IMC_Zicsr (32-bit, Integer, Multiply, Compressed, CSR)
- **Clock**: 50 MHz
- **UART**: 115200 baud

---

## Dosya Yapısı

```
level-v/
├── env/coremark/ceresv/          # Port kaynak dosyaları (master copy)
│   ├── core_portme.h             # Platform konfigürasyonu
│   ├── core_portme.c             # Platform fonksiyonları
│   ├── core_portme.mak           # Build ayarları
│   ├── crt0.S                    # Startup kodu
│   ├── link.ld                   # Linker script
│   ├── ee_printf.c               # Printf implementasyonu
│   └── cvt.c                     # Float-to-string conversion
│
├── subrepo/coremark/             # CoreMark kaynak kodu (submodule)
│   └── ceresv/                   # Build sırasında kopyalanır
│
├── build/tests/coremark/         # Derlenen çıktılar
│   ├── coremark.elf
│   ├── coremark.bin
│   ├── coremark.hex
│   ├── coremark.mem
│   └── coremark.dump
│
└── script/makefiles/
    └── rules_coremark.mk         # Build kuralları
```

---

## Donanım Konfigürasyonu

### Memory Map

| Bölge | Başlangıç Adresi | Boyut | Açıklama |
|-------|------------------|-------|----------|
| Code (ROM) | 0x80000000 | 64 KB | Program kodu |
| Data (RAM) | 0x80010000 | 64 KB | Data + Stack |
| UART | 0x20000000 | 16 B | UART registers |
| Timer | 0x30000000 | 8 B | 64-bit timer |

### UART Registers

```c
#define UART_CTRL        (*(volatile uint32_t*)0x20000000)  // Control
#define UART_STATUS      (*(volatile uint32_t*)0x20000004)  // Status
#define UART_RDATA       (*(volatile uint32_t*)0x20000008)  // RX Data
#define UART_WDATA       (*(volatile uint32_t*)0x2000000c)  // TX Data
```

**UART Control Register (0x20000000)**:
- Bits [31:16]: Baud divider (CPU_CLK / BAUD_RATE)
- Bit [1]: RX Enable
- Bit [0]: TX Enable

**UART Status Register (0x20000004)**:
- Bit [3]: RX Empty
- Bit [2]: TX Empty
- Bit [1]: RX Full
- Bit [0]: TX Full

### Timer Registers

```c
#define TIMER_LOW        (*(volatile uint32_t*)0x30000000)  // Lower 32-bit
#define TIMER_HIGH       (*(volatile uint32_t*)0x30000004)  // Upper 32-bit
```

Timer, CPU clock hızında (50 MHz) çalışır.

---

## Port Dosyaları

### 1. core_portme.h

Platform-specific konfigürasyon:

```c
// Donanım tanımları
#define CPU_CLK          50000000   // 50 MHz
#define BAUD_RATE        115200

// CoreMark konfigürasyonu
#define HAS_FLOAT        0          // Hardware FPU yok
#define HAS_TIME_H       0          // Baremetal
#define USE_CLOCK        0
#define HAS_STDIO        0
#define HAS_PRINTF       0          // Kendi ee_printf kullanılır
#define MAIN_HAS_NOARGC  1          // argc/argv yok
#define SEED_METHOD      SEED_VOLATILE
#define MEM_METHOD       MEM_STACK

// Data tipleri (RV32 için)
typedef unsigned int   ee_u32;
typedef ee_u32         ee_ptr_int;  // 32-bit pointer
```

### 2. core_portme.c

Platform fonksiyonları:

```c
// UART başlatma
static void uart_init(void) {
    uint32_t baud_div = CPU_CLK / BAUD_RATE;
    UART_CTRL = (baud_div << 16) | UART_CTRL_TX_EN | UART_CTRL_RX_EN;
}

// Karakter gönderme
void uart_putc(char c) {
    while (UART_STATUS & UART_STATUS_TX_FULL);
    UART_WDATA = (uint32_t)c;
}

// Timer okuma
static CORETIMETYPE read_timer(void) {
    return TIMER_LOW;
}

// Zaman fonksiyonları
CORETIMETYPE barebones_clock() {
    return read_timer();
}

void start_time(void) {
    GETMYTIME(&start_time_val);
}

void stop_time(void) {
    GETMYTIME(&stop_time_val);
}

// Platform başlatma
void portable_init(core_portable *p, int *argc, char *argv[]) {
    uart_init();
    ee_printf("CoreMark on Ceres-V RV32IMC_Zicsr\n");
    // ...
}
```

### 3. crt0.S

Startup kodu:

```asm
_start:
    # Interrupt'ları kapat
    csrw mie, zero
    
    # Register'ları sıfırla
    li x1, 0
    # ... x31'e kadar
    
    # Global pointer ayarla
    la gp, __global_pointer$
    
    # Stack pointer ayarla
    la sp, _stack_top
    
    # BSS temizle
    la t0, _bss_start
    la t1, _bss_end
bss_clear:
    bge t0, t1, bss_done
    sw zero, 0(t0)
    addi t0, t0, 4
    j bss_clear
bss_done:

    # main çağır
    call main
    
    # Sonsuz döngü
_exit:
    j _exit
```

### 4. link.ld

Linker script:

```ld
OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY {
    ROM (rx)  : ORIGIN = 0x80000000, LENGTH = 64K
    RAM (rwx) : ORIGIN = 0x80010000, LENGTH = 64K
}

SECTIONS {
    .text : { *(.text.init) *(.text*) } > ROM
    .data : { *(.data*) } > RAM AT > ROM
    .bss  : { *(.bss*) } > RAM
    
    _stack_size = 8K;
    .stack : { . = . + _stack_size; _stack_top = .; } > RAM
}
```

### 5. core_portme.mak

Build konfigürasyonu:

```makefile
# RISC-V Toolchain
RISCV_PREFIX ?= riscv32-unknown-elf-
CC = $(RISCV_PREFIX)gcc
LD = $(RISCV_PREFIX)gcc

# Compiler flags
ARCH_FLAGS = -march=rv32imc_zicsr -mabi=ilp32
PORT_CFLAGS = -O2 -g $(ARCH_FLAGS) -fno-builtin -nostdlib -nostartfiles

# Linker flags
LFLAGS = $(ARCH_FLAGS) -T$(PORT_DIR)/link.ld -nostdlib -nostartfiles
LFLAGS_END = -lm -lgcc

# Port kaynak dosyaları
PORT_SRCS = $(PORT_DIR)/core_portme.c $(PORT_DIR)/ee_printf.c \
            $(PORT_DIR)/cvt.c $(PORT_DIR)/crt0.S
```

### 6. ee_printf.c

UART üzerinden printf:

```c
void uart_send_char(char c) {
    while (UART_STATUS & UART_STATUS_TX_FULL);
    UART_WDATA = (ee_u32)c;
}

int ee_printf(const char *fmt, ...) {
    char buf[1024];
    va_list args;
    va_start(args, fmt);
    ee_vsprintf(buf, fmt, args);
    va_end(args);
    
    char *p = buf;
    while (*p) {
        uart_send_char(*p++);
    }
    return strlen(buf);
}
```

---

## Derleme ve Kullanım

### Temel Kullanım

```bash
# CoreMark derle (1000 iterasyon)
make coremark

# Özel iterasyon sayısı
make coremark COREMARK_ITERATIONS=2000

# Temizle
make coremark_clean

# Yardım
make coremark_help
```

### Build Süreci

1. **coremark_check**: `subrepo/coremark` var mı kontrol eder, yoksa clone eder
2. **coremark_setup**: `env/coremark/ceresv/` → `subrepo/coremark/ceresv/` kopyalar
3. **coremark_build**: CoreMark derler, çıktıları `build/tests/coremark/` altına koyar

### İterasyon Sayısı Hesaplama

CoreMark en az 10 saniye çalışmalıdır. Formül:

```
ITERATIONS >= CoreMark/MHz × MHz × 10 saniye
```

Örnek (4 CoreMark/MHz, 50 MHz için):
```
ITERATIONS >= 4 × 50 × 10 = 2000
```

---

## Çıktı Dosyaları

Build sonrası `build/tests/coremark/` altında:

| Dosya | Açıklama |
|-------|----------|
| `coremark.elf` | ELF executable (debug bilgisi içerir) |
| `coremark.bin` | Raw binary |
| `coremark.hex` | Intel HEX format |
| `coremark.mem` | Verilog $readmemh formatı |
| `coremark.dump` | Disassembly listesi |

### Memory Dosyası Formatı

```
@80000000
73 10 40 30 73 10 40 34 81 40 01 41 ...
```

- `@80000000`: Başlangıç adresi
- Byte-addressable hex değerler

---

## Sorun Giderme

### 1. Toolchain Bulunamıyor

```bash
# PATH kontrol
which riscv32-unknown-elf-gcc

# Yoksa ekle
export PATH=$HOME/tools/riscv/bin:$PATH
```

### 2. Timer Overflow

32-bit timer 50 MHz'de ~85.9 saniyede overflow olur. Çok uzun testler için dikkat.

### 3. UART Çıktısı Yok

- Baud rate kontrol (115200)
- UART TX enable kontrol
- Simülasyonda UART modelini kontrol

### 4. Build Hataları

```bash
# Temiz build
make coremark_clean
make coremark
```

### 5. Linker Hataları

`-lm -lgcc` ile math library ve GCC runtime linklenmeli.

---

## Referanslar

- [CoreMark GitHub](https://github.com/eembc/coremark)
- [CoreMark Barebones Porting Guide](https://github.com/eembc/coremark/blob/main/barebones_porting.md)
- [RISC-V Specifications](https://riscv.org/specifications/)

---

## Değişiklik Geçmişi

| Tarih | Açıklama |
|-------|----------|
| 2025-11-28 | İlk port oluşturuldu |
