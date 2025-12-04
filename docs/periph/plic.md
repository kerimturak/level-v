# PLIC (Platform-Level Interrupt Controller) - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Register Map](#register-map)
4. [Interrupt Akışı](#interrupt-akışı)
5. [Priority Arbitration](#priority-arbitration)
6. [Claim/Complete Mekanizması](#claimcomplete-mekanizması)

---

## Genel Bakış

### Amaç

`plic` modülü, **RISC-V compliant Platform-Level Interrupt Controller** olarak external interrupt'ları yönetir. 32 interrupt source ve 8 priority level destekler.

### Dosya Konumu

```
rtl/periph/plic/plic.sv
```

### Özellikler

- 32 interrupt source (source 0 reserved)
- 8 priority level (0=disabled, 7=highest)
- Priority threshold for masking
- Claim/Complete mechanism
- Edge-triggered capture
- Per-source priority
- Per-source enable

---

## Modül Arayüzü

### Parametreler

```systemverilog
module plic
  import ceres_param::*;
#(
    parameter int NUM_SOURCES  = 32,   // Including reserved 0
    parameter int NUM_PRIORITY = 8     // Priority levels (3 bits)
)
```

### Port Tanımları

```systemverilog
(
    input  logic clk_i,
    input  logic rst_ni,

    // Register interface
    input  logic            stb_i,
    input  logic [     9:0] adr_i,       // 10-bit address space
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,

    // Interrupt sources
    input  logic [NUM_SOURCES-1:0] irq_sources_i,

    // Interrupt output to CPU
    output logic irq_o
);
```

---

## Register Map

### Memory Layout

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        PLIC MEMORY MAP                                   │
├─────────────────────────────────────────────────────────────────────────┤
│ Offset     │ Register                │ Description                      │
├────────────┼─────────────────────────┼──────────────────────────────────┤
│ 0x000      │ Priority[0] (reserved)  │ Source 0 priority (always 0)     │
│ 0x004      │ Priority[1]             │ Source 1 priority (3 bits)       │
│ 0x008      │ Priority[2]             │ Source 2 priority                │
│ ...        │ ...                     │ ...                              │
│ 0x07C      │ Priority[31]            │ Source 31 priority               │
├────────────┼─────────────────────────┼──────────────────────────────────┤
│ 0x080      │ Pending                 │ 32-bit pending register (R/O)    │
├────────────┼─────────────────────────┼──────────────────────────────────┤
│ 0x100      │ Enable                  │ 32-bit enable register           │
├────────────┼─────────────────────────┼──────────────────────────────────┤
│ 0x200      │ Threshold               │ Priority threshold               │
│ 0x204      │ Claim/Complete          │ Claim (read) / Complete (write)  │
└─────────────────────────────────────────────────────────────────────────┘
```

### Register Addresses

```systemverilog
localparam logic [9:0] ADDR_PRIORITY_BASE = 10'h000;  // 0x000-0x07C
localparam logic [9:0] ADDR_PENDING       = 10'h080;  // 0x080
localparam logic [9:0] ADDR_ENABLE        = 10'h100;  // 0x100
localparam logic [9:0] ADDR_THRESHOLD     = 10'h200;  // 0x200
localparam logic [9:0] ADDR_CLAIM         = 10'h204;  // 0x204
```

---

## Interrupt Akışı

### Edge Detection

```systemverilog
// 2-stage synchronizer
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        irq_sync1_q <= '0;
        irq_sync2_q <= '0;
        irq_prev_q  <= '0;
    end else begin
        irq_sync1_q <= irq_sources_i;
        irq_sync2_q <= irq_sync1_q;
        irq_prev_q  <= irq_sync2_q;
    end
end

// Rising edge = new interrupt
assign irq_edge = irq_sync2_q & ~irq_prev_q;
```

### Interrupt Flow Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        PLIC INTERRUPT FLOW                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   irq_sources_i ───► Edge Detection ───► Pending Register               │
│                           │                    │                         │
│                           └────────────────────┼──────────────────┐     │
│                                                ▼                  │     │
│                                          ┌──────────┐            │     │
│                                          │ Enable?  │            │     │
│                                          └────┬─────┘            │     │
│                                               │ yes              │     │
│                                               ▼                  │     │
│                                          ┌──────────┐            │     │
│                                          │Priority >│            │     │
│                                          │Threshold?│            │     │
│                                          └────┬─────┘            │     │
│                                               │ yes              │     │
│                                               ▼                  │     │
│                                          ┌──────────┐            │     │
│                                          │Find Max  │            │     │
│                                          │ Priority │            │     │
│                                          └────┬─────┘            │     │
│                                               │                  │     │
│                                               ▼                  │     │
│                                           irq_o ───► CPU         │     │
│                                               │                  │     │
│   CPU reads CLAIM ◄───────────────────────────┘                  │     │
│         │                                                        │     │
│         ▼                                                        │     │
│   Returns max_id, clears pending ─────────────────────────────────     │
│         │                                                              │
│   CPU handles interrupt                                                │
│         │                                                              │
│   CPU writes COMPLETE(id) ───► Clear claimed ──────────────────────────┘
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Priority Arbitration

### Find Highest Priority

```systemverilog
always_comb begin
    max_priority = '0;
    max_id = '0;
    irq_valid = 1'b0;

    // Source 0 is reserved, start from 1
    for (int i = 1; i < NUM_SOURCES; i++) begin
        if (pending_q[i] && enable_q[i] && !claimed_q[i]) begin
            if (priority_q[i] > max_priority && 
                priority_q[i] > threshold_q) begin
                max_priority = priority_q[i];
                max_id = i;
                irq_valid = 1'b1;
            end
        end
    end
end

assign irq_o = irq_valid;
```

### Priority Example

```
┌───────────────────────────────────────────────────────────────────┐
│                    PRIORITY ARBITRATION                           │
├───────────────────────────────────────────────────────────────────┤
│                                                                    │
│   Source   Pending  Enable  Priority  Threshold=2  Winner         │
│   ─────────────────────────────────────────────────────────       │
│   1        1        1       3         > 2          ✓ (if max)     │
│   2        1        1       1         < 2          ✗              │
│   3        1        0       7         enabled=0    ✗              │
│   4        1        1       5         > 2          ✓ WINNER       │
│   5        0        1       6         pending=0    ✗              │
│                                                                    │
│   Result: Source 4 wins (priority 5 > priority 3)                 │
│   max_id = 4, irq_o = 1                                           │
│                                                                    │
└───────────────────────────────────────────────────────────────────┘
```

---

## Claim/Complete Mekanizması

### Claim (Read)

```systemverilog
// Reading CLAIM atomically claims the interrupt
if (claim_read && irq_valid) begin
    claimed_q[max_id] <= 1'b1;     // Mark as claimed
    pending_q[max_id] <= 1'b0;     // Clear pending
end
```

### Complete (Write)

```systemverilog
// Writing source ID completes the interrupt
if (complete_write) begin
    automatic int complete_id = dat_i[$clog2(NUM_SOURCES)-1:0];
    if (complete_id > 0 && complete_id < NUM_SOURCES) begin
        claimed_q[complete_id] <= 1'b0;
    end
end
```

### Claim/Complete Flow

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      CLAIM/COMPLETE SEQUENCE                             │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   1. Interrupt arrives → pending[n] = 1                                 │
│                                                                          │
│   2. irq_o asserts (priority > threshold, enabled)                      │
│                                                                          │
│   3. CPU reads CLAIM register                                           │
│      → Returns n (highest priority pending)                             │
│      → pending[n] = 0 (cleared atomically)                              │
│      → claimed[n] = 1 (prevent re-interrupt)                            │
│                                                                          │
│   4. CPU handles interrupt for source n                                  │
│                                                                          │
│   5. CPU writes n to COMPLETE register                                   │
│      → claimed[n] = 0 (allow new interrupts)                            │
│                                                                          │
│   6. If new interrupt pending, irq_o asserts again                       │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Kullanım Örneği

### C Header

```c
#define PLIC_BASE           0x20007000

#define PLIC_PRIORITY(n)    (*(volatile uint32_t*)(PLIC_BASE + (n)*4))
#define PLIC_PENDING        (*(volatile uint32_t*)(PLIC_BASE + 0x080))
#define PLIC_ENABLE         (*(volatile uint32_t*)(PLIC_BASE + 0x100))
#define PLIC_THRESHOLD      (*(volatile uint32_t*)(PLIC_BASE + 0x200))
#define PLIC_CLAIM          (*(volatile uint32_t*)(PLIC_BASE + 0x204))
```

### PLIC Initialization

```c
void plic_init(void) {
    // Set all priorities to 1 (lowest enabled)
    for (int i = 1; i < 32; i++) {
        PLIC_PRIORITY(i) = 1;
    }
    
    // Set UART interrupt higher priority
    PLIC_PRIORITY(10) = 5;
    
    // Enable UART and GPIO interrupts
    PLIC_ENABLE = (1 << 10) | (1 << 11);
    
    // Set threshold to 0 (accept all priorities > 0)
    PLIC_THRESHOLD = 0;
}
```

### Interrupt Handler

```c
void external_irq_handler(void) {
    // Claim highest priority interrupt
    uint32_t claim = PLIC_CLAIM;
    
    if (claim == 0) return;  // Spurious
    
    switch (claim) {
        case 10: uart_irq_handler(); break;
        case 11: gpio_irq_handler(); break;
        default: break;
    }
    
    // Complete the interrupt
    PLIC_CLAIM = claim;
}
```

### Priority Threshold Usage

```c
// Disable interrupts below priority 3
void plic_set_threshold(uint32_t threshold) {
    PLIC_THRESHOLD = threshold;
}

// Temporarily mask low priority interrupts
void critical_section_enter(void) {
    plic_set_threshold(4);  // Only priority >= 5 can interrupt
}

void critical_section_exit(void) {
    plic_set_threshold(0);  // All priorities can interrupt
}
```

---

## Timing Diyagramı

### Interrupt Lifecycle

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └───

irq_sources[5]─────┐
                   └───────────────────────────────────

irq_edge[5]            ┌───┐
           ────────────┘   └───────────────────────────

pending[5]             ┌───────────────────┐
           ────────────┘                   └───────────
                                           claim read

irq_o                  ┌───────────────────┐
           ────────────┘                   └───────────

claimed[5]                                 ┌───────────┐
           ────────────────────────────────┘           └─
                                           claim    complete
                                           read     write
```

---

## Özet

`plic` modülü:

1. **32 Sources**: External interrupt inputs
2. **8 Priorities**: 0=disabled, 7=highest
3. **Threshold**: Global priority mask
4. **Claim/Complete**: Atomic interrupt handling
5. **Edge-Triggered**: Rising edge capture
6. **Per-Source**: Priority and enable control
