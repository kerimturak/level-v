# Peripherals

CERES RISC-V işlemcisinin peripheral modülleri.

## Genel Bakış

```
rtl/periph/
├── uart/       # UART Controller
├── spi/        # SPI Controller
├── i2c/        # I2C Controller
├── gpio/       # GPIO Controller
├── timer/      # Timer Peripheral
├── plic/       # Platform-Level Interrupt Controller
├── pwm/        # PWM Controller
├── dma/        # DMA Controller
├── wdt/        # Watchdog Timer
└── vga/        # VGA Controller
```

## Memory Map

| Peripheral | Base Address | Size | Açıklama |
|------------|--------------|------|----------|
| UART0 | 0x2000_0000 | 4KB | Primary UART |
| UART1 | 0x2000_1000 | 4KB | Secondary UART |
| SPI0 | 0x2000_2000 | 4KB | SPI Controller |
| I2C0 | 0x2000_3000 | 4KB | I2C Controller |
| GPIO | 0x2000_4000 | 4KB | GPIO Controller |
| PWM | 0x2000_5000 | 4KB | PWM Controller |
| Timer | 0x2000_6000 | 4KB | Timer |
| PLIC | 0x2000_7000 | 4KB | Interrupt Controller |
| WDT | 0x2000_8000 | 4KB | Watchdog Timer |
| DMA | 0x2000_9000 | 4KB | DMA Controller |
| VGA | 0x2000_D000 | 4KB | VGA Controller |

## Modül Listesi

| Modül | Dosya | Açıklama |
|-------|-------|----------|
| [UART](uart.md) | `uart/` | Serial communication |
| [SPI](spi.md) | `spi/` | SPI master/slave |
| [I2C](i2c.md) | `i2c/` | I2C master |
| [GPIO](gpio.md) | `gpio/` | General purpose I/O |
| [Timer](timer.md) | `timer/` | Timer/counter |
| [PLIC](plic.md) | `plic/` | Interrupt controller |
| [PWM](pwm.md) | `pwm/` | Pulse width modulation |
| [DMA](dma.md) | `dma/` | Direct memory access |
| [WDT](wdt.md) | `wdt/` | Watchdog timer |
| [VGA](vga.md) | `vga/` | Video output |

## Interrupt Mapping

| IRQ | Peripheral | Açıklama |
|-----|------------|----------|
| 1 | UART0 | UART0 interrupt |
| 2 | UART1 | UART1 interrupt |
| 3 | SPI0 | SPI interrupt |
| 4 | I2C0 | I2C interrupt |
| 5 | GPIO | GPIO interrupt |
| 6 | Timer | Timer interrupt |
| 7 | DMA | DMA completion |
| 8 | WDT | Watchdog timeout |
