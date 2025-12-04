# PWM Controller - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Register Map](#register-map)
4. [Counter ve Prescaler](#counter-ve-prescaler)
5. [PWM Modları](#pwm-modları)
6. [Dead-Time Generator](#dead-time-generator)
7. [Fault Protection](#fault-protection)

---

## Genel Bakış

### Amaç

`pwm` modülü, **8 bağımsız PWM kanalı** ile motor kontrolü, LED dimming ve güç elektroniği uygulamaları için gelişmiş özellikler sunar.

### Dosya Konumu

```
rtl/periph/pwm/pwm.sv
```

### Özellikler

- 8 bağımsız PWM kanalı
- 16-bit çözünürlük
- Common veya individual period kontrolü
- Dead-time generator (complementary outputs)
- Phase offset per channel
- Center-aligned veya edge-aligned modlar
- Programlanabilir polarity
- Fault input for emergency shutdown
- DMA request capability

---

## Modül Arayüzü

### Parametreler

```systemverilog
module pwm
  import ceres_param::*;
#(
    parameter int NUM_CHANNELS = 8,
    parameter int PWM_WIDTH    = 16
)
```

### Port Tanımları

```systemverilog
(
    input  logic                    clk_i,
    input  logic                    rst_ni,
    
    // Register Interface
    input  logic                    stb_i,
    input  logic [             5:0] adr_i,        // Word address [7:2]
    input  logic [             3:0] byte_sel_i,
    input  logic                    we_i,
    input  logic [            31:0] dat_i,
    output logic [            31:0] dat_o,
    
    // Fault input
    input  logic                    fault_i,
    
    // PWM outputs
    output logic [NUM_CHANNELS-1:0] pwm_o,
    output logic [NUM_CHANNELS-1:0] pwm_n_o,      // Complementary outputs
    
    // Sync output
    output logic                    sync_o,
    
    // DMA request
    output logic                    drq_o,
    
    // Interrupt
    output logic                    irq_o
);
```

---

## Register Map

### Global Registers

| Offset | Register | Açıklama |
|--------|----------|----------|
| 0x00 | GCR | Global Control Register |
| 0x04 | PERIOD | Global period value |
| 0x08 | PSC | Prescaler divider |
| 0x0C | CNT | Counter value (read-only) |
| 0x10 | DEADTIME | Dead-time configuration |
| 0x14 | FAULT | Fault configuration and status |
| 0x18 | IER | Interrupt enable register |
| 0x1C | ISR | Interrupt status register (W1C) |

### Per-Channel Registers (0x10 bytes each, starting at 0x40)

| Offset | Register | Açıklama |
|--------|----------|----------|
| 0x40 + N*0x10 | CCR | Channel Control Register |
| 0x44 + N*0x10 | DUTY | Duty cycle value |
| 0x48 + N*0x10 | PHASE | Phase offset |
| 0x4C + N*0x10 | Reserved | |

### GCR (Global Control) Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [0]    │ EN      │ Global enable                                        │
│ [1]    │ OUTEN   │ Output enable (master gate)                          │
│ [2]    │ CNTMODE │ Counter mode (0=edge, 1=center)                      │
│ [3]    │ ONESHOT │ One-shot mode                                        │
│ [4]    │ COMMODE │ Common period mode                                   │
│ [5]    │ SYNCEN  │ Sync output enable                                   │
│ [6]    │ DRQEN   │ DMA request enable                                   │
│ [15:8] │ SYNCSRC │ Sync source channel mask                             │
└─────────────────────────────────────────────────────────────────────────┘
```

### CCR (Channel Control) Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [0]    │ EN      │ Channel enable                                       │
│ [1]    │ POL     │ Polarity (0=active high, 1=active low)              │
│ [2]    │ COMPEN  │ Complementary output enable                          │
│ [3]    │ DTEN    │ Dead-time enable                                     │
│ [4]    │ FAULTEN │ Fault shutdown enable                                │
│ [15:8] │ FAULTPOL│ Fault output state (0=low, 1=high, 2=hi-z)          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Counter ve Prescaler

### Prescaler

```systemverilog
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        psc_cnt <= 16'h0;
    end else if (pwm_en) begin
        if (psc_cnt >= psc_q) begin
            psc_cnt <= 16'h0;
        end else begin
            psc_cnt <= psc_cnt + 1;
        end
    end
end

assign psc_tick = (psc_cnt == psc_q);
```

### PWM Frequency Calculation

```
PWM_freq = clk_i / ((psc_q + 1) * (period_q + 1))

Example (50 MHz clock):
  1 kHz: psc=0, period=49999  → 50M / (1 * 50000) = 1 kHz
  10 kHz: psc=0, period=4999  → 50M / (1 * 5000) = 10 kHz
  20 kHz: psc=0, period=2499  → 50M / (1 * 2500) = 20 kHz
```

---

## PWM Modları

### Edge-Aligned Mode (CNTMODE=0)

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      EDGE-ALIGNED PWM                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│ CNT     0  1  2  3  4  5  6  7  8  9  10 11 12 13 14 15  0  1  2  ...   │
│         ──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──        │
│                                                                          │
│ PERIOD = 15                                                              │
│ DUTY = 6                                                                 │
│                                                                          │
│ PWM_O   ┌────────────────────┐                    ┌────────────────────┐│
│         │                    │                    │                    ││
│         └────────────────────┴────────────────────┴────────────────────┴│
│         0        6           15         0        6                      │
│                                                                          │
│ Duty Cycle = DUTY / PERIOD = 6/16 = 37.5%                               │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Center-Aligned Mode (CNTMODE=1)

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      CENTER-ALIGNED PWM                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│ CNT     0  1  2  3  4  5  6  7  8  7  6  5  4  3  2  1  0  1  2  ...    │
│         ──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──        │
│           ▲                     ▲                     ▲                  │
│           │       count up      │     count down      │                  │
│                                                                          │
│ PERIOD = 8                                                               │
│ DUTY = 3                                                                 │
│                                                                          │
│ PWM_O      ┌──────────────────────────────────┐      ┌──────────────────│
│            │                                  │      │                   │
│      ──────┘                                  └──────┘                   │
│      0  1  2  3  4  5  6  7  8  7  6  5  4  3  2  1  0                   │
│               ▲              ▲              ▲                            │
│               │  PWM high    │  PWM high    │                            │
│                                                                          │
│ Advantage: Symmetric switching, reduced EMI                              │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Dead-Time Generator

### Dead-Time Concept

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        DEAD-TIME GENERATOR                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│ Without Dead-Time (Shoot-through risk!):                                │
│                                                                          │
│ PWM    ────────┐          ┌──────────────────┐          ┌────           │
│                │          │                  │          │                │
│                └──────────┘                  └──────────┘                │
│                                                                          │
│ PWM_N  ────────┘          ┌──────────────────┘          ┌────           │
│                ▲          ▲                  ▲          ▲                │
│                │          │                  │          │                │
│                └── Both ON! ─┘              └── Both ON! ─┘             │
│                    DANGER!                       DANGER!                 │
│                                                                          │
│ ─────────────────────────────────────────────────────────────────────── │
│                                                                          │
│ With Dead-Time:                                                          │
│                                                                          │
│ PWM    ────────┐              ┌──────────────────┐              ┌────   │
│                │              │                  │              │        │
│                └──────────────┘                  └──────────────┘        │
│                    ├─dt_rise─┤                      ├─dt_rise─┤          │
│                                                                          │
│ PWM_N  ──────────────┘          ┌──────────────────┘          ┌────     │
│                      ├dt_fall─┤                    ├dt_fall─┤            │
│                          │          │                  │                 │
│                          └── Both OFF (safe) ──────────┘                 │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### DEADTIME Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [15:0]  │ RISE │ Dead-time on rising edge (prescaled clocks)           │
│ [31:16] │ FALL │ Dead-time on falling edge                              │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Fault Protection

### FAULT Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [0]    │ FAULTIN  │ Fault input state (read-only)                       │
│ [1]    │ FAULTF   │ Fault occurred flag (sticky, W1C)                   │
│ [2]    │ FAULTPOL │ Fault input polarity                                │
│ [3]    │ FAULTCLR │ Auto-clear when input deasserts                     │
│ [15:8] │ FILTER   │ Fault input debounce cycles                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Fault Response

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         FAULT PROTECTION                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   fault_i   ────────┐                                                   │
│                     │  (debounce filter)                                │
│                     └────────────────────────────────────────           │
│                                                                          │
│   PWM_O     ────────────────┐                                           │
│             (normal)        │ FAULT!                                    │
│                             └────────► Configurable output state:       │
│                                        - FAULTPOL=0: Drive low          │
│                                        - FAULTPOL=1: Drive high         │
│                                        - FAULTPOL=2: Hi-Z               │
│                                                                          │
│   Recovery:                                                              │
│   - FAULTCLR=1: Auto-clear when fault_i deasserts                       │
│   - FAULTCLR=0: Manual clear by writing 1 to FAULTF                     │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Kullanım Örneği

### C Header

```c
#define PWM_BASE       0x20005000

// Global registers
#define PWM_GCR        (*(volatile uint32_t*)(PWM_BASE + 0x00))
#define PWM_PERIOD     (*(volatile uint32_t*)(PWM_BASE + 0x04))
#define PWM_PSC        (*(volatile uint32_t*)(PWM_BASE + 0x08))
#define PWM_CNT        (*(volatile uint32_t*)(PWM_BASE + 0x0C))
#define PWM_DEADTIME   (*(volatile uint32_t*)(PWM_BASE + 0x10))
#define PWM_FAULT      (*(volatile uint32_t*)(PWM_BASE + 0x14))

// Per-channel registers
#define PWM_CCR(n)     (*(volatile uint32_t*)(PWM_BASE + 0x40 + (n)*0x10 + 0x00))
#define PWM_DUTY(n)    (*(volatile uint32_t*)(PWM_BASE + 0x40 + (n)*0x10 + 0x04))
#define PWM_PHASE(n)   (*(volatile uint32_t*)(PWM_BASE + 0x40 + (n)*0x10 + 0x08))

// GCR bits
#define PWM_GCR_EN        (1 << 0)
#define PWM_GCR_OUTEN     (1 << 1)
#define PWM_GCR_CENTER    (1 << 2)
#define PWM_GCR_COMMON    (1 << 4)

// CCR bits
#define PWM_CCR_EN        (1 << 0)
#define PWM_CCR_POL       (1 << 1)
#define PWM_CCR_COMP      (1 << 2)
#define PWM_CCR_DT        (1 << 3)
#define PWM_CCR_FAULT     (1 << 4)
```

### LED Dimming (Edge-Aligned)

```c
void pwm_led_init(void) {
    // 1 kHz PWM, 50 MHz clock
    PWM_PSC = 0;
    PWM_PERIOD = 49999;
    
    // Channel 0: 50% duty
    PWM_DUTY(0) = 25000;
    PWM_CCR(0) = PWM_CCR_EN;
    
    // Enable PWM
    PWM_GCR = PWM_GCR_EN | PWM_GCR_OUTEN | PWM_GCR_COMMON;
}

void pwm_set_brightness(uint8_t channel, uint16_t duty) {
    PWM_DUTY(channel) = duty;
}
```

### Motor Control (Center-Aligned with Dead-Time)

```c
void pwm_motor_init(void) {
    // 20 kHz PWM, center-aligned
    PWM_PSC = 0;
    PWM_PERIOD = 2499;  // 50M / 2500 = 20 kHz (half-period)
    
    // Dead-time: 100ns rise, 100ns fall @ 50MHz = 5 cycles
    PWM_DEADTIME = (5 << 16) | 5;
    
    // Channel 0: Complementary with dead-time and fault
    PWM_CCR(0) = PWM_CCR_EN | PWM_CCR_COMP | PWM_CCR_DT | PWM_CCR_FAULT;
    
    // Center-aligned mode
    PWM_GCR = PWM_GCR_EN | PWM_GCR_OUTEN | PWM_GCR_CENTER | PWM_GCR_COMMON;
}

void pwm_set_motor_duty(int16_t duty) {
    // duty: -1000 to +1000
    if (duty >= 0) {
        PWM_DUTY(0) = duty;
        PWM_DUTY(1) = 0;
    } else {
        PWM_DUTY(0) = 0;
        PWM_DUTY(1) = -duty;
    }
}
```

---

## Özet

`pwm` modülü:

1. **8 Channels**: Independent PWM outputs
2. **16-bit Resolution**: Fine duty control
3. **2 Modes**: Edge-aligned, center-aligned
4. **Dead-Time**: Complementary outputs
5. **Fault Protection**: Emergency shutdown
6. **Phase Offset**: Multi-phase applications
