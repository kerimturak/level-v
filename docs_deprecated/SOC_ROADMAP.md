# CERES SoC Geliştirme Yol Haritası

Bu doküman, CERES RISC-V işlemcisinin tam bir SoC haline gelmesi için gerekli bileşenleri, mevcut durumu ve gelecek hedefleri tanımlar.

---

## 📊 Mevcut Durum Özeti

### ✅ Tamamlanan Bileşenler

| Bileşen | Konum | Açıklama |
|---------|-------|----------|
| CPU Core | `rtl/core/` | 5-aşamalı pipeline, RV32IMC |
| I-Cache | `rtl/core/mmu/cache.sv` | 32KB, 8-way set-associative |
| D-Cache | `rtl/core/mmu/cache.sv` | 32KB, 8-way set-associative |
| Branch Predictor | `rtl/core/stage01_fetch/` | GShare + BTB + RAS + Loop |
| CLINT | `rtl/wrapper/ceres_soc.sv` | Timer interrupt (mtime/mtimecmp) |
| UART | `rtl/periph/uart/` | TX/RX with FIFO |
| SPI Master | `rtl/periph/spi/` | 8-bit, configurable clock |
| I2C Master | `rtl/periph/i2c/` | Standard/Fast/Fast+ mode |
| PMA | `rtl/core/pmp_pma/pma.sv` | Physical Memory Attributes |
| CSR | `rtl/core/stage03_execute/cs_reg_file.sv` | M-mode CSR set |

---

## 🎯 Hedef Bileşenler

### Öncelik 1: Kritik (Temel SoC İşlevselliği)

#### 1.1 GPIO Controller
```
Konum     : rtl/periph/gpio/gpio.sv
Öncelik   : 🔴 YÜKSEK
Durum     : ❌ Eksik
```

**Açıklama:**
GPIO (General Purpose Input/Output), mikrodenetleyicinin dış dünya ile iletişim kurmasını sağlayan temel birimdir. LED yakma, buton okuma, sensör bağlama gibi tüm temel I/O işlemleri için gereklidir.

**Özellikler:**
| Özellik | Açıklama |
|---------|----------|
| Port Genişliği | 32-bit (parametrik) |
| Direction Control | Her pin için ayrı giriş/çıkış seçimi |
| Output Register | Çıkış değerlerini tutan register |
| Input Register | Giriş değerlerini okuyan register |
| Pull-up/Pull-down | Her pin için dahili pull resistor |
| Interrupt on Change | Pin değişiminde interrupt üretme |
| Edge Detection | Rising/falling/both edge seçimi |
| Atomic Set/Clear | Bit bazında set/clear/toggle |

**Register Map:**
| Offset | İsim | R/W | Açıklama |
|--------|------|-----|----------|
| 0x00 | GPIO_DIR | RW | Direction (0=input, 1=output) |
| 0x04 | GPIO_OUT | RW | Output data register |
| 0x08 | GPIO_IN | R | Input data register |
| 0x0C | GPIO_SET | W | Atomic bit set (write 1 to set) |
| 0x10 | GPIO_CLR | W | Atomic bit clear (write 1 to clear) |
| 0x14 | GPIO_TGL | W | Atomic bit toggle |
| 0x18 | GPIO_PUE | RW | Pull-up enable |
| 0x1C | GPIO_PDE | RW | Pull-down enable |
| 0x20 | GPIO_IE | RW | Interrupt enable |
| 0x24 | GPIO_IS | R/W1C | Interrupt status (write 1 to clear) |
| 0x28 | GPIO_IBE | RW | Interrupt both edges |
| 0x2C | GPIO_IEV | RW | Interrupt event (0=falling, 1=rising) |

---

#### 1.2 PLIC (Platform-Level Interrupt Controller)
```
Konum     : rtl/periph/plic/plic.sv
Öncelik   : 🔴 YÜKSEK
Durum     : ❌ Eksik
```

**Açıklama:**
PLIC, RISC-V spesifikasyonunda tanımlanan harici interrupt yönetim birimidir. Birden fazla interrupt kaynağını önceliklendirerek CPU'ya sunar. Mevcut CLINT sadece timer ve software interrupt sağlar; harici cihazlar (UART RX, GPIO, SPI complete vb.) için PLIC gereklidir.

**Özellikler:**
| Özellik | Açıklama |
|---------|----------|
| Interrupt Kaynakları | 32 (parametrik, max 1024) |
| Priority Levels | 8 seviye (0=disabled, 7=highest) |
| Pending Register | Her kaynak için pending bit |
| Enable Register | Her kaynak için enable bit |
| Threshold | CPU'nun kabul edeceği minimum öncelik |
| Claim/Complete | Interrupt acknowledge mekanizması |

**Register Map (Base: 0x2000_7000):**
| Offset | İsim | R/W | Açıklama |
|--------|------|-----|----------|
| 0x000-0x07C | PRIORITY[0:31] | RW | Interrupt priority (per source) |
| 0x080 | PENDING | R | Pending interrupts bitmap |
| 0x100 | ENABLE | RW | Interrupt enable bitmap |
| 0x200 | THRESHOLD | RW | Priority threshold |
| 0x204 | CLAIM | R | Claim highest pending interrupt |
| 0x204 | COMPLETE | W | Complete interrupt handling |

**Interrupt Bağlantıları:**
```
Source 0  : Reserved (always 0)
Source 1  : UART0 RX (receive complete)
Source 2  : UART0 TX (transmit empty)
Source 3  : UART1 RX
Source 4  : UART1 TX
Source 5  : SPI0 Complete
Source 6  : I2C0 Complete
Source 7  : I2C0 Arbitration Lost
Source 8-15 : GPIO[0-7] interrupts
Source 16-23 : GPIO[8-15] interrupts
Source 24-31 : External interrupts
```

---

#### 1.3 General Purpose Timer
```
Konum     : rtl/periph/timer/gptimer.sv
Öncelik   : 🔴 YÜKSEK
Durum     : ❌ Eksik
```

**Açıklama:**
CLINT'teki mtime sadece sistem timer'ı olarak kullanılır. Kullanıcı uygulamaları için ayrı, yapılandırılabilir timer'lar gereklidir. PWM çıkışı, periyodik interrupt, zaman ölçümü gibi işlevler için kullanılır.

**Özellikler:**
| Özellik | Açıklama |
|---------|----------|
| Timer Sayısı | 4 (parametrik) |
| Counter Genişliği | 32-bit |
| Prescaler | 16-bit (clock bölücü) |
| Modlar | One-shot, Continuous, PWM |
| Compare Channels | Her timer için 2 adet |
| Capture Channels | Her timer için 1 adet |
| Interrupt | Overflow, Compare match, Capture |

**Register Map (per timer, 0x40 spacing):**
| Offset | İsim | R/W | Açıklama |
|--------|------|-----|----------|
| 0x00 | TIMx_CTRL | RW | Control register |
| 0x04 | TIMx_CNT | RW | Counter value |
| 0x08 | TIMx_PSC | RW | Prescaler |
| 0x0C | TIMx_ARR | RW | Auto-reload value |
| 0x10 | TIMx_CCR0 | RW | Compare/Capture 0 |
| 0x14 | TIMx_CCR1 | RW | Compare/Capture 1 |
| 0x18 | TIMx_SR | R/W1C | Status register |
| 0x1C | TIMx_IER | RW | Interrupt enable |

**CTRL Register Bits:**
```
[0]     : EN      - Timer enable
[1]     : DIR     - Count direction (0=up, 1=down)
[2]     : OPM     - One-pulse mode
[4:3]   : CMS     - Center-aligned mode select
[7:5]   : Reserved
[9:8]   : CC0M    - Capture/Compare 0 mode
[11:10] : CC1M    - Capture/Compare 1 mode
[31:12] : Reserved
```

---

### Öncelik 2: Önemli (Gelişmiş Özellikler)

#### 2.1 PWM Controller
```
Konum     : rtl/periph/pwm/pwm.sv
Öncelik   : 🟡 ORTA
Durum     : ❌ Eksik
```

**Açıklama:**
PWM (Pulse Width Modulation), LED parlaklık kontrolü, motor hız kontrolü, servo motor kontrolü gibi analog çıkış gerektiren uygulamalar için kullanılır. GP Timer içinde basit PWM olabilir, ancak ayrı bir PWM modülü daha fazla özellik sunar.

**Özellikler:**
| Özellik | Açıklama |
|---------|----------|
| Kanal Sayısı | 8 (parametrik) |
| Çözünürlük | 16-bit |
| Dead-time | Complementary output için |
| Phase Shift | Kanallar arası faz farkı |
| Sync Mode | Tüm kanalları senkronize başlatma |

**Register Map:**
| Offset | İsim | R/W | Açıklama |
|--------|------|-----|----------|
| 0x00 | PWM_CTRL | RW | Global control |
| 0x04 | PWM_PERIOD | RW | PWM period (all channels) |
| 0x08 | PWM_EN | RW | Channel enable bitmap |
| 0x0C | PWM_POL | RW | Output polarity |
| 0x10-0x2C | PWM_DUTY[0-7] | RW | Duty cycle per channel |
| 0x30 | PWM_DEADTIME | RW | Dead-time configuration |

---

#### 2.2 Watchdog Timer
```
Konum     : rtl/periph/wdt/watchdog.sv
Öncelik   : 🟡 ORTA
Durum     : ❌ Eksik
```

**Açıklama:**
Watchdog Timer, sistemin kilitlenmesi durumunda otomatik reset sağlar. Yazılım periyodik olarak watchdog'u "beslemeli", aksi halde sistem resetlenir.

**Özellikler:**
| Özellik | Açıklama |
|---------|----------|
| Counter | 32-bit |
| Prescaler | 8-bit |
| Window Mode | Erken besleme koruması |
| Lock | Yapılandırma kilitleme |
| Reset/Interrupt | Timeout'ta reset veya interrupt |

**Register Map:**
| Offset | İsim | R/W | Açıklama |
|--------|------|-----|----------|
| 0x00 | WDT_CTRL | RW | Control (enable, mode) |
| 0x04 | WDT_LOAD | RW | Reload value |
| 0x08 | WDT_COUNT | R | Current count |
| 0x0C | WDT_WINDOW | RW | Window start (for window mode) |
| 0x10 | WDT_KICK | W | Kick register (write any value) |
| 0x14 | WDT_LOCK | RW | Lock configuration |

**Güvenlik:**
- `WDT_LOCK` yazıldığında yapılandırma kilitlenir
- Unlock için magic sequence: `0x1ACCE551`

---

#### 2.3 DMA Controller
```
Konum     : rtl/periph/dma/dma_controller.sv
Öncelik   : 🟡 ORTA
Durum     : ❌ Eksik
```

**Açıklama:**
DMA (Direct Memory Access), CPU'yu bypass ederek bellek ve peripheral arasında veri transferi yapar. Büyük veri blokları için CPU yükünü azaltır.

**Özellikler:**
| Özellik | Açıklama |
|---------|----------|
| Kanal Sayısı | 4 (parametrik) |
| Transfer Tipleri | M2M, M2P, P2M |
| Burst Size | 1, 4, 8, 16 words |
| Address Mode | Fixed, Increment, Decrement |
| Circular Mode | Otomatik reload |
| Priority | Kanal öncelikleri |
| Linked List | Scatter-gather desteği |

**Register Map (per channel, 0x20 spacing):**
| Offset | İsim | R/W | Açıklama |
|--------|------|-----|----------|
| 0x00 | DMA_CTRL | RW | Channel control |
| 0x04 | DMA_SRC | RW | Source address |
| 0x08 | DMA_DST | RW | Destination address |
| 0x0C | DMA_CNT | RW | Transfer count |
| 0x10 | DMA_CFG | RW | Configuration |
| 0x14 | DMA_LLI | RW | Linked list item pointer |
| 0x18 | DMA_SR | R | Status |

**Peripheral Bağlantıları:**
```
Request 0 : UART0 TX
Request 1 : UART0 RX
Request 2 : SPI0 TX
Request 3 : SPI0 RX
Request 4 : I2C0 TX
Request 5 : I2C0 RX
Request 6-7 : Reserved
```

---

#### 2.4 System Controller
```
Konum     : rtl/periph/sysctrl/sysctrl.sv
Öncelik   : 🟡 ORTA
Durum     : ❌ Eksik
```

**Açıklama:**
Sistem genelinde clock, reset ve power yönetimi sağlayan birimdir.

**Özellikler:**
| Özellik | Açıklama |
|---------|----------|
| Clock Gating | Peripheral bazında clock açma/kapama |
| Reset Control | Peripheral bazında soft reset |
| Power Domains | Low-power mode yönetimi |
| Chip ID | Unique chip identifier |
| Boot Config | Boot source selection |

**Register Map:**
| Offset | İsim | R/W | Açıklama |
|--------|------|-----|----------|
| 0x00 | SYS_CHIPID | R | Chip ID (read-only) |
| 0x04 | SYS_CLKEN | RW | Clock enable bitmap |
| 0x08 | SYS_SRST | RW | Soft reset (write 1 to reset) |
| 0x0C | SYS_BOOTCFG | R | Boot configuration pins |
| 0x10 | SYS_PWRCTRL | RW | Power control |
| 0x14 | SYS_RSTSTAT | R/W1C | Reset status (reason) |

---

### Öncelik 3: Bonus (Gelişmiş Özellikler)

#### 3.1 Debug Module (JTAG)
```
Konum     : rtl/debug/dm_top.sv
Öncelik   : 🟢 DÜŞÜK
Durum     : ❌ Eksik
```

**Açıklama:**
RISC-V Debug Specification uyumlu debug modülü. JTAG veya cJTAG üzerinden bağlantı, breakpoint, single-step, register okuma/yazma.

---

#### 3.2 RTC (Real-Time Clock)
```
Konum     : rtl/periph/rtc/rtc.sv
Öncelik   : 🟢 DÜŞÜK
Durum     : ❌ Eksik
```

**Açıklama:**
Battery-backed gerçek zamanlı saat. Tarih/saat tutma, alarm fonksiyonu.

---

#### 3.3 CRC Accelerator
```
Konum     : rtl/periph/crc/crc_engine.sv
Öncelik   : 🟢 DÜŞÜK
Durum     : ❌ Eksik
```

**Açıklama:**
Hardware CRC hesaplama. CRC-8, CRC-16, CRC-32 desteği.

---

#### 3.4 External Memory Controller
```
Konum     : rtl/periph/emc/emc.sv
Öncelik   : 🟢 DÜŞÜK
Durum     : ❌ Eksik
```

**Açıklama:**
Harici SRAM, SDRAM veya DDR bellek kontrolcüsü.

---

## 🗺️ Memory Map (Hedef)

```
0x0000_0000 - 0x0FFF_FFFF : Debug Region (256MB)
    0x0000_0000 : Debug Module

0x1000_0000 - 0x1FFF_FFFF : Boot ROM (256MB reserved, 4KB used)
    0x1000_0000 : Boot ROM Start

0x2000_0000 - 0x2FFF_FFFF : Peripheral Region (256MB)
    0x2000_0000 : UART0          (4KB)
    0x2000_1000 : UART1          (4KB)
    0x2000_2000 : SPI0           (4KB)
    0x2000_3000 : I2C0           (4KB)
    0x2000_4000 : GPIO           (4KB)  ← YENİ
    0x2000_5000 : PWM            (4KB)  ← YENİ
    0x2000_6000 : Timer0-3       (4KB)  ← YENİ
    0x2000_7000 : PLIC           (4KB)  ← YENİ
    0x2000_8000 : Watchdog       (4KB)  ← YENİ
    0x2000_9000 : DMA            (4KB)  ← YENİ
    0x2000_A000 : System Ctrl    (4KB)  ← YENİ
    0x2000_B000 : RTC            (4KB)  ← YENİ
    0x2000_C000 : CRC            (4KB)  ← YENİ
    0x2000_D000 - 0x2000_FFFF : Reserved

0x3000_0000 - 0x3FFF_FFFF : CLINT (256MB reserved)
    0x3000_0000 : MSIP
    0x3000_4000 : MTIMECMP
    0x3000_BFF8 : MTIME

0x4000_0000 - 0x7FFF_FFFF : External Memory (1GB)
    0x4000_0000 : QSPI Flash / External RAM

0x8000_0000 - 0xFFFF_FFFF : Main RAM (2GB)
    0x8000_0000 : RAM Start (Reset Vector)
```

---

## 📈 Uygulama Sırası

### Faz 1: Temel I/O (1-2 hafta)
1. ✅ GPIO Controller
2. ✅ PLIC entegrasyonu
3. ✅ Mevcut peripheral'lara interrupt ekleme

### Faz 2: Zamanlama (1 hafta)
4. ✅ General Purpose Timer
5. ✅ PWM (Timer ile birleşik olabilir)
6. ✅ Watchdog Timer

### Faz 3: Sistem (1-2 hafta)
7. ✅ System Controller
8. ✅ DMA Controller

### Faz 4: Gelişmiş (Opsiyonel)
9. Debug Module
10. RTC
11. CRC Accelerator
12. External Memory Controller

---

## 📋 Checklist

- [ ] **GPIO**
  - [ ] Basic I/O (direction, read, write)
  - [ ] Atomic operations (set, clear, toggle)
  - [ ] Pull-up/pull-down
  - [ ] Interrupt on change
  - [ ] PLIC entegrasyonu

- [ ] **PLIC**
  - [ ] Priority registers
  - [ ] Pending/Enable registers
  - [ ] Claim/Complete
  - [ ] Threshold
  - [ ] CPU interrupt output

- [ ] **Timer**
  - [ ] Counter, prescaler
  - [ ] Compare match
  - [ ] PWM output
  - [ ] Input capture
  - [ ] Interrupt generation

- [ ] **Watchdog**
  - [ ] Timeout reset
  - [ ] Window mode
  - [ ] Lock mechanism

- [ ] **DMA**
  - [ ] Basic M2M transfer
  - [ ] Peripheral integration
  - [ ] Circular mode
  - [ ] Linked list

- [ ] **System Controller**
  - [ ] Clock gating
  - [ ] Soft reset
  - [ ] Chip ID

---

## 🔗 Referanslar

1. [RISC-V Privileged Specification](https://riscv.org/specifications/privileged-isa/)
2. [SiFive FE310 Manual](https://sifive.cdn.prismic.io/sifive/4faf3e34-4a42-4c2f-be9e-c77baa4928c7_fe310-g002-manual-v1p5.pdf)
3. [RISC-V PLIC Specification](https://github.com/riscv/riscv-plic-spec)
4. [RISC-V Debug Specification](https://riscv.org/specifications/debug-specification/)

---

*Son Güncelleme: 2025-12-03*
*Versiyon: 1.0*
