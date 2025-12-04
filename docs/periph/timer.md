# General Purpose Timer (GPTimer) - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Register Map](#register-map)
4. [Timer Modları](#timer-modları)
5. [PWM Çıkışı](#pwm-çıkışı)
6. [Interrupt Sistemi](#interrupt-sistemi)

---

## Genel Bakış

### Amaç

`gptimer` modülü, **4 bağımsız 32-bit timer** sağlar. Her timer kendi prescaler, compare/capture kanalları ve PWM output desteğine sahiptir.

### Dosya Konumu

```
rtl/periph/timer/gptimer.sv
```

### Özellikler

- 4 bağımsız 32-bit timer
- Her timer için 16-bit prescaler
- 2 compare/capture kanal per timer
- Up/Down counting modes
- One-pulse mode
- PWM output per channel
- Extensive interrupt support

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module gptimer
  import ceres_param::*;
#(
    parameter int TIMER_COUNT = 4
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Register interface
    input  logic                             stb_i,
    input  logic [$clog2(TIMER_COUNT)+3-1:0] adr_i,
    input  logic [                      3:0] byte_sel_i,
    input  logic                             we_i,
    input  logic [                  XLEN-1:0] dat_i,
    output logic [                  XLEN-1:0] dat_o,

    // Capture inputs
    input  logic [TIMER_COUNT-1:0][1:0] capture_i,

    // PWM outputs
    output logic [TIMER_COUNT-1:0][1:0] pwm_o,

    // Interrupt outputs
    output logic [TIMER_COUNT-1:0] timer_irq_o
);
```

### Address Calculation

```
Timer N register address = N * 0x20 + register_offset

Timer 0: 0x00 - 0x1C
Timer 1: 0x20 - 0x3C
Timer 2: 0x40 - 0x5C
Timer 3: 0x60 - 0x7C
```

---

## Register Map

### Per-Timer Registers (Her Timer İçin)

| Offset | Register | Açıklama |
|--------|----------|----------|
| 0x00 | CTRL | Control register |
| 0x04 | CNT | Counter value |
| 0x08 | PSC | Prescaler (16-bit) |
| 0x0C | ARR | Auto-reload value |
| 0x10 | CCR0 | Compare/Capture 0 |
| 0x14 | CCR1 | Compare/Capture 1 |
| 0x18 | SR | Status register |
| 0x1C | IER | Interrupt enable |

### CTRL Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [7]   │ dir      │ Count direction (0=up, 1=down)                       │
│ [6]   │ opm      │ One-pulse mode                                       │
│ [5:4] │ cms      │ Center-aligned mode (00=edge, 01/10/11=center)       │
│ [3]   │ arpe     │ Auto-reload preload enable                           │
│ [2]   │ urs      │ Update request source                                │
│ [1]   │ udis     │ Update disable                                       │
│ [0]   │ cen      │ Counter enable                                       │
└─────────────────────────────────────────────────────────────────────────┘
```

### Status Register (SR)

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [4] │ cc1if │ Capture/Compare 1 interrupt flag                         │
│ [3] │ cc0if │ Capture/Compare 0 interrupt flag                         │
│ [2] │ trg   │ Trigger interrupt flag                                   │
│ [1] │ dir   │ Direction (read-only, center-aligned mode)               │
│ [0] │ uif   │ Update interrupt flag                                    │
└─────────────────────────────────────────────────────────────────────────┘
```

### Interrupt Enable Register (IER)

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [4] │ cc1ie │ Capture/Compare 1 interrupt enable                       │
│ [3] │ cc0ie │ Capture/Compare 0 interrupt enable                       │
│ [2] │ trgie │ Trigger interrupt enable                                 │
│ [0] │ uie   │ Update interrupt enable                                  │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Timer Modları

### Up Counting Mode

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        UP COUNTING (dir=0)                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   ARR ─────────────────────────────────────────────────────              │
│        │                           │                                     │
│        │     ╱╲                    │     ╱╲                              │
│        │    ╱  ╲                   │    ╱  ╲                             │
│        │   ╱    ╲                  │   ╱    ╲                            │
│   CCR1 │─╱──────╲─────────────────│─╱──────╲───                         │
│        │╱        ╲                 │╱        ╲                           │
│   CCR0 ╱──────────╲───────────────╱──────────╲──                        │
│       ╱            ╲             ╱            ╲                          │
│   0  ╱──────────────╲───────────╱──────────────╲──                      │
│      ▲              ▲UIF        ▲              ▲UIF                      │
│      │              │           │              │                         │
│    start          reload      start          reload                      │
│                                                                          │
│   Counter: 0 → ARR → 0 (overflow generates UIF)                         │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Down Counting Mode

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        DOWN COUNTING (dir=1)                             │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   ARR ─╲                          ╲                                      │
│        │╲                         │╲                                     │
│        │ ╲                        │ ╲                                    │
│   CCR1 │──╲───────────────────────│──╲───                                │
│        │   ╲                      │   ╲                                  │
│   CCR0 │────╲─────────────────────│────╲──                               │
│        │     ╲                    │     ╲                                │
│   0  ──│──────╲───────────────────│──────╲──                            │
│        ▲      ▲UIF                ▲      ▲UIF                            │
│        │      │                   │      │                               │
│      reload underflow           reload underflow                         │
│                                                                          │
│   Counter: ARR → 0 → ARR (underflow generates UIF)                      │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Center-Aligned Mode

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        CENTER-ALIGNED (cms!=0)                           │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   ARR ─────────────╱╲                     ╱╲                             │
│                   ╱  ╲                   ╱  ╲                            │
│   CCR1 ──────────╱────╲─────────────────╱────╲───                        │
│                 ╱      ╲               ╱      ╲                          │
│   CCR0 ────────╱────────╲─────────────╱────────╲──                       │
│               ╱          ╲           ╱          ╲                        │
│   0  ────────╱────────────╲─────────╱────────────╲──                    │
│              ▲UIF         ▲UIF      ▲UIF         ▲UIF                    │
│              │            │         │            │                       │
│            up→down     down→up    up→down     down→up                    │
│                                                                          │
│   Counter: 0 → ARR → 0 (UIF at both boundaries)                         │
│   Symmetric PWM output for motor control                                 │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### One-Pulse Mode

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        ONE-PULSE MODE (opm=1)                            │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Trigger ─────┐                                                        │
│                │                                                        │
│   ┌────────────▼──────────────────────────────────────────────────┐     │
│   │                                                                │     │
│   │  ARR ─────────╱╲                                               │     │
│   │              ╱  ╲                                              │     │
│   │  CCR ───────╱────╲───                                          │     │
│   │            ╱      ╲                                            │     │
│   │  0  ──────╱        ╲─────── (stop, cen=0)                      │     │
│   │           ▲                 ▲                                  │     │
│   │           │ start           │ stop                             │     │
│   │                                                                │     │
│   └────────────────────────────────────────────────────────────────┘     │
│                                                                          │
│   Single cycle, auto-stop. Used for pulse generation.                  │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## PWM Çıkışı

### PWM Timing

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        PWM OUTPUT                                        │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Edge-Aligned PWM (Up counting):                                       │
│   ─────────────────────────────────────                                  │
│                                                                          │
│   CNT      ╱╲      ╱╲      ╱╲                                            │
│       ────╱──╲────╱──╲────╱──╲                                           │
│   CCR ───╱────╲──╱────╲──╱────                                           │
│   ARR ──╱──────╲╱──────╲╱─────                                           │
│                                                                          │
│   PWM  ──┐  ┌──┐  ┌──┐  ┌──                                             │
│          └──┘  └──┘  └──┘                                                │
│          │     │     │                                                   │
│          │ CCR │     │                                                   │
│          ◄─────►                                                         │
│          Duty Cycle = CCR / ARR                                         │
│                                                                          │
│   Center-Aligned PWM (Symmetric):                                       │
│   ─────────────────────────────────────                                  │
│                                                                          │
│   CNT      ╱╲        ╱╲                                                  │
│       ────╱  ╲──────╱  ╲───                                              │
│   CCR ───╱────╲────╱────╲──                                              │
│                                                                          │
│   PWM  ──┐    ┌────┐    ┌──                                             │
│          └────┘    └────┘                                                │
│                                                                          │
│          Symmetric around center (reduced harmonics)                     │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### PWM Configuration

```systemverilog
// PWM frequency = Timer_clk / ((PSC + 1) * (ARR + 1))
// Timer_clk = System_clk

// Example: 1 kHz PWM @ 50 MHz system clock
// PSC = 49, ARR = 999
// PWM_freq = 50M / (50 * 1000) = 1 kHz

// Duty cycle = CCR / ARR
// 50% duty: CCR = ARR / 2
```

---

## Interrupt Sistemi

### Interrupt Sources

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        INTERRUPT SOURCES                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   ┌───────────┐                                                         │
│   │   Timer   │                                                         │
│   │           │                                                         │
│   │ ┌───────┐ │     ┌─────┐                                             │
│   │ │  UIF  │─┼─────┤     │                                             │
│   │ └───────┘ │     │     │     ┌────────────┐                          │
│   │ ┌───────┐ │     │     │     │            │                          │
│   │ │ CC0IF │─┼─────┤ IER ├─────┤ timer_irq  │──► PLIC                  │
│   │ └───────┘ │     │     │     │            │                          │
│   │ ┌───────┐ │     │     │     └────────────┘                          │
│   │ │ CC1IF │─┼─────┤     │                                             │
│   │ └───────┘ │     └─────┘                                             │
│   │ ┌───────┐ │                                                         │
│   │ │  TRG  │─┼─────►                                                   │
│   │ └───────┘ │                                                         │
│   └───────────┘                                                         │
│                                                                          │
│   timer_irq = (SR & IER) != 0                                           │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Flag Clearing

```systemverilog
// Flags are cleared by writing 0 to the corresponding bit
// Writing 1 has no effect

// Clear UIF
write SR, 0xFFFFFFFE  // Clear bit 0

// Clear CC0IF
write SR, 0xFFFFFFF7  // Clear bit 3

// Clear all flags
write SR, 0x00000000
```

---

## Kullanım Örneği

### C Header

```c
#define TIMER_BASE     0x20006000

// Timer 0 registers
#define TIM0_CTRL      (*(volatile uint32_t*)(TIMER_BASE + 0x00))
#define TIM0_CNT       (*(volatile uint32_t*)(TIMER_BASE + 0x04))
#define TIM0_PSC       (*(volatile uint32_t*)(TIMER_BASE + 0x08))
#define TIM0_ARR       (*(volatile uint32_t*)(TIMER_BASE + 0x0C))
#define TIM0_CCR0      (*(volatile uint32_t*)(TIMER_BASE + 0x10))
#define TIM0_CCR1      (*(volatile uint32_t*)(TIMER_BASE + 0x14))
#define TIM0_SR        (*(volatile uint32_t*)(TIMER_BASE + 0x18))
#define TIM0_IER       (*(volatile uint32_t*)(TIMER_BASE + 0x1C))

// Timer N base
#define TIMER(n)       (TIMER_BASE + (n) * 0x20)

// CTRL bits
#define TIM_CEN        (1 << 0)
#define TIM_UDIS       (1 << 1)
#define TIM_URS        (1 << 2)
#define TIM_ARPE       (1 << 3)
#define TIM_DIR        (1 << 7)
#define TIM_OPM        (1 << 6)

// IER bits
#define TIM_UIE        (1 << 0)
#define TIM_CC0IE      (1 << 3)
#define TIM_CC1IE      (1 << 4)

// SR bits
#define TIM_UIF        (1 << 0)
#define TIM_CC0IF      (1 << 3)
#define TIM_CC1IF      (1 << 4)
```

### Basic Timer (1 ms tick)

```c
void timer_init_1ms(void) {
    // 50 MHz clock, 1 ms period
    TIM0_PSC = 49;         // Divide by 50 → 1 MHz
    TIM0_ARR = 999;        // Count 1000 → 1 ms
    TIM0_IER = TIM_UIE;    // Enable update interrupt
    TIM0_CTRL = TIM_CEN;   // Start timer
}

void timer_irq_handler(void) {
    if (TIM0_SR & TIM_UIF) {
        TIM0_SR = ~TIM_UIF;  // Clear flag
        ms_tick++;
    }
}
```

### PWM Output

```c
void pwm_init(uint32_t frequency, uint8_t duty_percent) {
    // Calculate ARR for desired frequency
    uint32_t arr = (50000000 / frequency) - 1;
    
    TIM0_PSC = 0;                             // No prescaler
    TIM0_ARR = arr;                           // Period
    TIM0_CCR0 = (arr * duty_percent) / 100;   // Duty cycle
    TIM0_CTRL = TIM_ARPE | TIM_CEN;           // Preload + enable
}

void pwm_set_duty(uint8_t percent) {
    TIM0_CCR0 = (TIM0_ARR * percent) / 100;
}
```

### One-Shot Pulse

```c
void generate_pulse(uint32_t delay_us, uint32_t width_us) {
    // One-pulse mode for single pulse generation
    TIM0_PSC = 49;                    // 1 MHz tick
    TIM0_ARR = delay_us + width_us;   // Total period
    TIM0_CCR0 = delay_us;             // Pulse start
    TIM0_CTRL = TIM_OPM | TIM_CEN;    // One-pulse + start
    
    // Timer stops automatically after pulse
}
```

### Input Capture

```c
volatile uint32_t capture_value;

void capture_init(void) {
    // Setup for input capture on channel 0
    TIM0_PSC = 0;          // No prescaler for max resolution
    TIM0_ARR = 0xFFFFFFFF; // Maximum period
    TIM0_IER = TIM_CC0IE;  // Capture interrupt
    TIM0_CTRL = TIM_CEN;   // Start
}

void capture_irq_handler(void) {
    if (TIM0_SR & TIM_CC0IF) {
        TIM0_SR = ~TIM_CC0IF;
        capture_value = TIM0_CCR0;  // Read captured value
    }
}
```

---

## Prescaler ve Timing Hesabı

### Frequency Formulas

```
Timer clock = System clock / (PSC + 1)

Update frequency = Timer clock / (ARR + 1)

PWM frequency = System clock / ((PSC + 1) * (ARR + 1))

PWM duty cycle = CCR / (ARR + 1) * 100%
```

### Example Calculations

```
System clock = 50 MHz

1. 1 kHz PWM with 10-bit resolution:
   ARR = 1023 (10-bit)
   PSC = 50000000 / (1000 * 1024) - 1 ≈ 48
   Actual freq = 50M / (49 * 1024) = 996 Hz

2. 1 ms period timer:
   PSC = 49 → 1 MHz timer clock
   ARR = 999 → 1000 ticks = 1 ms

3. 100 Hz with maximum resolution:
   ARR = 65535 (16-bit max usable)
   PSC = 50M / (100 * 65536) - 1 ≈ 6
   Resolution = 1 / 65536 = 0.0015%
```

---

## Özet

`gptimer` modülü:

1. **4 Timer**: Bağımsız çalışan timerlar
2. **Flexible Counting**: Up/down/center-aligned
3. **PWM Support**: Hardware PWM output
4. **One-Pulse**: Single-shot pulse generation
5. **Capture**: External event timestamping
6. **Interrupts**: Update, compare, trigger events
7. **Prescaler**: 16-bit frequency division
