# GPIO Controller - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Register Map](#register-map)
4. [Atomic İşlemler](#atomic-işlemler)
5. [Interrupt Sistemi](#interrupt-sistemi)
6. [Giriş Senkronizasyonu](#giriş-senkronizasyonu)

---

## Genel Bakış

### Amaç

`gpio` modülü, **32-bit bidirectional GPIO** controller'ı ile pin yönü kontrolü, atomic işlemler ve edge-triggered interrupt desteği sağlar.

### Dosya Konumu

```
rtl/periph/gpio/gpio.sv
```

### Özellikler

- 32-bit bidirectional GPIO
- Per-pin yön kontrolü
- Atomic set/clear/toggle işlemleri
- Pull-up/pull-down konfigürasyonu
- Interrupt on change (rising/falling/both edges)
- 2-stage metastability synchronizer
- Edge detection

---

## Modül Arayüzü

### Parametreler

```systemverilog
module gpio
  import ceres_param::*;
#(
    parameter int GPIO_WIDTH = 32
)
```

### Port Tanımları

```systemverilog
(
    input  logic clk_i,
    input  logic rst_ni,

    // Register interface
    input  logic            stb_i,
    input  logic [     3:0] adr_i,       // 4-bit for 12 registers
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,

    // GPIO pins
    input  logic [GPIO_WIDTH-1:0] gpio_i,      // Input from pads
    output logic [GPIO_WIDTH-1:0] gpio_o,      // Output to pads
    output logic [GPIO_WIDTH-1:0] gpio_oe_o,   // Output enable
    output logic [GPIO_WIDTH-1:0] gpio_pue_o,  // Pull-up enable
    output logic [GPIO_WIDTH-1:0] gpio_pde_o,  // Pull-down enable

    // Interrupt output
    output logic irq_o
);
```

---

## Register Map

| Offset | Register | R/W | Açıklama |
|--------|----------|-----|----------|
| 0x00 | GPIO_DIR | RW | Direction (0=input, 1=output) |
| 0x04 | GPIO_OUT | RW | Output data register |
| 0x08 | GPIO_IN | R | Input data register |
| 0x0C | GPIO_SET | W | Atomic bit set |
| 0x10 | GPIO_CLR | W | Atomic bit clear |
| 0x14 | GPIO_TGL | W | Atomic bit toggle |
| 0x18 | GPIO_PUE | RW | Pull-up enable |
| 0x1C | GPIO_PDE | RW | Pull-down enable |
| 0x20 | GPIO_IE | RW | Interrupt enable |
| 0x24 | GPIO_IS | RW | Interrupt status (W1C) |
| 0x28 | GPIO_IBE | RW | Interrupt both edges |
| 0x2C | GPIO_IEV | RW | Interrupt event (edge select) |

### Register Adresleri

```systemverilog
localparam logic [3:0] ADDR_DIR = 4'h0;
localparam logic [3:0] ADDR_OUT = 4'h1;
localparam logic [3:0] ADDR_IN  = 4'h2;
localparam logic [3:0] ADDR_SET = 4'h3;
localparam logic [3:0] ADDR_CLR = 4'h4;
localparam logic [3:0] ADDR_TGL = 4'h5;
localparam logic [3:0] ADDR_PUE = 4'h6;
localparam logic [3:0] ADDR_PDE = 4'h7;
localparam logic [3:0] ADDR_IE  = 4'h8;
localparam logic [3:0] ADDR_IS  = 4'h9;
localparam logic [3:0] ADDR_IBE = 4'hA;
localparam logic [3:0] ADDR_IEV = 4'hB;
```

---

## Atomic İşlemler

### Atomic Set

```systemverilog
ADDR_SET: begin
    // Write 1 to set bits (OR operation)
    if (byte_sel_i[0]) out_q[7:0]   <= out_q[7:0]   | dat_i[7:0];
    if (byte_sel_i[1]) out_q[15:8]  <= out_q[15:8]  | dat_i[15:8];
    if (byte_sel_i[2]) out_q[23:16] <= out_q[23:16] | dat_i[23:16];
    if (byte_sel_i[3]) out_q[31:24] <= out_q[31:24] | dat_i[31:24];
end
```

### Atomic Clear

```systemverilog
ADDR_CLR: begin
    // Write 1 to clear bits (AND NOT operation)
    if (byte_sel_i[0]) out_q[7:0]   <= out_q[7:0]   & ~dat_i[7:0];
    if (byte_sel_i[1]) out_q[15:8]  <= out_q[15:8]  & ~dat_i[15:8];
    if (byte_sel_i[2]) out_q[23:16] <= out_q[23:16] & ~dat_i[23:16];
    if (byte_sel_i[3]) out_q[31:24] <= out_q[31:24] & ~dat_i[31:24];
end
```

### Atomic Toggle

```systemverilog
ADDR_TGL: begin
    // Write 1 to toggle bits (XOR operation)
    if (byte_sel_i[0]) out_q[7:0]   <= out_q[7:0]   ^ dat_i[7:0];
    if (byte_sel_i[1]) out_q[15:8]  <= out_q[15:8]  ^ dat_i[15:8];
    if (byte_sel_i[2]) out_q[23:16] <= out_q[23:16] ^ dat_i[23:16];
    if (byte_sel_i[3]) out_q[31:24] <= out_q[31:24] ^ dat_i[31:24];
end
```

---

## Interrupt Sistemi

### Edge Detection

```systemverilog
// 2-stage synchronizer sonrası edge detection
assign rising_edge  = gpio_in & ~gpio_prev_q;   // 0→1 geçişi
assign falling_edge = ~gpio_in & gpio_prev_q;   // 1→0 geçişi
assign any_edge     = rising_edge | falling_edge;
```

### Interrupt Trigger Logic

```systemverilog
always_comb begin
    for (int i = 0; i < GPIO_WIDTH; i++) begin
        if (ibe_q[i]) begin
            // Both edges mode
            irq_trigger[i] = any_edge[i];
        end else if (iev_q[i]) begin
            // Rising edge only
            irq_trigger[i] = rising_edge[i];
        end else begin
            // Falling edge only
            irq_trigger[i] = falling_edge[i];
        end
    end
end
```

### Interrupt Output

```systemverilog
// Combined interrupt: any enabled & pending
assign irq_o = |(is_q & ie_q);
```

### Interrupt Status (Write-1-to-Clear)

```systemverilog
ADDR_IS: begin
    // W1C: Writing 1 clears the bit
    if (byte_sel_i[0]) is_q[7:0]   <= is_q[7:0]   & ~dat_i[7:0];
    if (byte_sel_i[1]) is_q[15:8]  <= is_q[15:8]  & ~dat_i[15:8];
    if (byte_sel_i[2]) is_q[23:16] <= is_q[23:16] & ~dat_i[23:16];
    if (byte_sel_i[3]) is_q[31:24] <= is_q[31:24] & ~dat_i[31:24];
end
```

---

## Giriş Senkronizasyonu

### 2-Stage Synchronizer

```systemverilog
// Metastability protection
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        gpio_sync1_q <= '0;
        gpio_sync2_q <= '0;
        gpio_prev_q  <= '0;
    end else begin
        gpio_sync1_q <= gpio_i;         // Stage 1
        gpio_sync2_q <= gpio_sync1_q;   // Stage 2
        gpio_prev_q  <= gpio_sync2_q;   // Previous (for edge detection)
    end
end

// Synchronized input
wire [GPIO_WIDTH-1:0] gpio_in = gpio_sync2_q;
```

### Synchronizer Diagram

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └───

gpio_i     ────┬───────────────
               │ async input

gpio_sync1_q ──────┬───────────
                   │

gpio_sync2_q ──────────┬───────
                       │ stable

gpio_prev_q  ──────────────┬───
                           │
                           
               ├──T1─┼──T2─┤
               sync  sync  edge
               1     2     detect
```

---

## Kullanım Örneği

### C Header

```c
#define GPIO_BASE      0x20004000

#define GPIO_DIR       (*(volatile uint32_t*)(GPIO_BASE + 0x00))
#define GPIO_OUT       (*(volatile uint32_t*)(GPIO_BASE + 0x04))
#define GPIO_IN        (*(volatile uint32_t*)(GPIO_BASE + 0x08))
#define GPIO_SET       (*(volatile uint32_t*)(GPIO_BASE + 0x0C))
#define GPIO_CLR       (*(volatile uint32_t*)(GPIO_BASE + 0x10))
#define GPIO_TGL       (*(volatile uint32_t*)(GPIO_BASE + 0x14))
#define GPIO_PUE       (*(volatile uint32_t*)(GPIO_BASE + 0x18))
#define GPIO_PDE       (*(volatile uint32_t*)(GPIO_BASE + 0x1C))
#define GPIO_IE        (*(volatile uint32_t*)(GPIO_BASE + 0x20))
#define GPIO_IS        (*(volatile uint32_t*)(GPIO_BASE + 0x24))
#define GPIO_IBE       (*(volatile uint32_t*)(GPIO_BASE + 0x28))
#define GPIO_IEV       (*(volatile uint32_t*)(GPIO_BASE + 0x2C))
```

### LED Blink

```c
void led_init(void) {
    GPIO_DIR = 0x0000000F;  // Pin 0-3 output
    GPIO_OUT = 0x00000000;  // All LEDs off
}

void led_toggle(int led) {
    GPIO_TGL = (1 << led);  // Atomic toggle
}
```

### Button Interrupt

```c
void button_irq_init(void) {
    GPIO_DIR &= ~(1 << 4);  // Pin 4 input
    GPIO_PUE |= (1 << 4);   // Enable pull-up
    GPIO_IBE &= ~(1 << 4);  // Single edge
    GPIO_IEV &= ~(1 << 4);  // Falling edge (button press)
    GPIO_IE  |= (1 << 4);   // Enable interrupt
}

void gpio_irq_handler(void) {
    if (GPIO_IS & (1 << 4)) {
        // Button pressed
        led_toggle(0);
        GPIO_IS = (1 << 4);  // Clear interrupt
    }
}
```

---

## Timing Diyagramı

### Edge Detection & Interrupt

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └───

gpio_i[0]  ─────────────┐
                        └───────────────────

gpio_sync2_q ───────────────┐
                            └───────────────

gpio_prev_q  ───────────────────┐
                                └───────────

falling_edge                ┌───┐
           ─────────────────┘   └───────────

is_q[0]                     ┌───────────────
           ─────────────────┘  (latched)

irq_o                       ┌───────────────
(if ie_q[0]=1) ─────────────┘
```

---

## Özet

`gpio` modülü:

1. **32-bit I/O**: Bidirectional GPIO pins
2. **Direction**: Per-pin input/output control
3. **Atomic Ops**: SET/CLR/TGL operations
4. **Pull-up/down**: Configurable resistors
5. **Interrupts**: Rising/falling/both edges
6. **Sync**: 2-stage metastability protection
