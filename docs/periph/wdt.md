# Watchdog Timer (WDT) - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Register Map](#register-map)
4. [Window Mode](#window-mode)
5. [Lock Mechanism](#lock-mechanism)
6. [Reset ve Interrupt](#reset-ve-interrupt)

---

## Genel Bakış

### Amaç

`watchdog` modülü, sistem watchdog timer olarak çalışır. Belirli süre içinde refresh yapılmazsa sistem reset veya interrupt üretir.

### Dosya Konumu

```
rtl/periph/wdt/watchdog.sv
```

### Özellikler

- 32-bit down counter
- Window mode (early refresh rejection)
- Lock register protection
- Debug pause support
- Early warning interrupt
- System reset generation

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module watchdog
  import ceres_param::*;
(
    input  logic clk_i,
    input  logic rst_ni,

    // Register interface
    input  logic            stb_i,
    input  logic [     2:0] adr_i,
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,

    // Debug interface
    input  logic debug_halt_i,

    // Outputs
    output logic wdt_reset_o,
    output logic wdt_irq_o
);
```

### Signal Descriptions

| Signal | Yön | Açıklama |
|--------|-----|----------|
| `debug_halt_i` | in | Debug durumunda counter freeze |
| `wdt_reset_o` | out | Watchdog reset signal |
| `wdt_irq_o` | out | Early warning interrupt |

---

## Register Map

| Offset | Register | Açıklama |
|--------|----------|----------|
| 0x00 | CTRL | Control register |
| 0x04 | LOAD | Counter reload value |
| 0x08 | VALUE | Current counter (read-only) |
| 0x0C | KEY | Key register (refresh/lock) |
| 0x10 | WINDOW | Window threshold |
| 0x14 | STATUS | Status/clear register |

### CTRL Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [4]   │ dbg_pause │ Pause counter during debug halt                     │
│ [3]   │ win_en    │ Window mode enable                                  │
│ [2]   │ irq_en    │ Early warning interrupt enable                      │
│ [1]   │ rst_en    │ Reset generation enable                             │
│ [0]   │ wdt_en    │ Watchdog enable                                     │
└─────────────────────────────────────────────────────────────────────────┘
```

### KEY Register Values

```systemverilog
parameter KEY_REFRESH = 32'h5A5A_5A5A;  // Counter refresh
parameter KEY_UNLOCK  = 32'h1234_5678;  // Unlock registers
parameter KEY_LOCK    = 32'hDEAD_BEEF;  // Lock registers
```

### STATUS Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [2] │ window_err │ Early refresh error (window mode)                    │
│ [1] │ early_warn │ Early warning flag (counter < threshold)             │
│ [0] │ timeout    │ Timeout occurred                                     │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Window Mode

### Konsept

Window mode, çok erken refresh yapılmasını engeller. Bu, stuck-in-loop bug'larını yakalamak için kullanışlıdır.

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        WINDOW MODE                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   LOAD ─────────────────────────────────────────────────────────────     │
│        │                                                                 │
│        │  ┌───────────────────────────────────────────────────────┐     │
│        │  │         CLOSED WINDOW (early refresh = error)         │     │
│        │  │                                                       │     │
│   WIN  ───│───────────────────────────────────────────────────────│─    │
│        │  │                                                       │     │
│        │  └───────────────────────────────────────────────────────┘     │
│        │                                                                 │
│        │  ┌───────────────────────────────────────────────────────┐     │
│        │  │           OPEN WINDOW (refresh allowed)                │     │
│   WARN ───│───────────────────────────────────────────────────────│─    │
│        │  │                                                       │     │
│        │  │                                        ▲ IRQ          │     │
│        │  └───────────────────────────────────────────────────────┘     │
│        │                                                                 │
│   0  ──│───────────────────────────────────────────────────────────│─   │
│        │                                           ▲ RESET         │     │
│        ▼                                                            │     │
│      Counter                                                        │     │
│                                                                          │
│   Rules:                                                                │
│   1. Refresh while CNT > WINDOW → window_err → reset                    │
│   2. Refresh while WARN < CNT <= WINDOW → OK, reload                    │
│   3. CNT < WARN → early_warn IRQ                                        │
│   4. CNT == 0 → timeout → reset                                         │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Window Mode Timing

```
              LOAD value
                 │
                 ▼
      ┌──────────────────────────────────────────────────────────┐
      │                                                          │
      │  CLOSED WINDOW (counter > WINDOW)                        │
      │  Refresh here → ERROR                                    │
      │                                                          │
WINDOW├──────────────────────────────────────────────────────────┤
      │                                                          │
      │  OPEN WINDOW (WARN < counter <= WINDOW)                  │
      │  Refresh here → OK, counter reloads                      │
      │                                                          │
 WARN ├──────────────────────────────────────────────────────────┤
      │                                                          │
      │  WARNING ZONE (counter < WARN)                           │
      │  IRQ generated, refresh still allowed                    │
      │                                                          │
   0  └──────────────────────────────────────────────────────────┘
              ▲
              │ TIMEOUT → RESET
```

---

## Lock Mechanism

### Register Koruması

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        LOCK MECHANISM                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   ┌───────────┐                                                         │
│   │           │                                                         │
│   │  LOCKED   │◄────────────────────────────────────────────┐           │
│   │           │                                             │           │
│   └─────┬─────┘                                             │           │
│         │                                                   │           │
│         │ Write KEY_UNLOCK (0x12345678)                     │           │
│         │                                                   │           │
│         ▼                                                   │           │
│   ┌───────────┐                                             │           │
│   │           │                                             │           │
│   │ UNLOCKED  │─────────────────────────────────────────────┘           │
│   │           │     Write KEY_LOCK (0xDEADBEEF)                         │
│   └─────┬─────┘     or timeout (after N cycles)                         │
│         │                                                               │
│         │ Registers writable                                            │
│         ▼                                                               │
│   ┌───────────────────────────────────────────────────────────────┐     │
│   │ CTRL, LOAD, WINDOW registers can be modified                  │     │
│   │ KEY register always writable (for refresh)                    │     │
│   └───────────────────────────────────────────────────────────────┘     │
│                                                                          │
│   Locked state: Only KEY register writable                              │
│   Unlocked state: All registers writable (time-limited)                 │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Key Operations

```systemverilog
// Refresh watchdog
write KEY, 0x5A5A5A5A

// Unlock registers for modification
write KEY, 0x12345678
write LOAD, new_value      // Allowed
write CTRL, new_value      // Allowed
write KEY, 0xDEADBEEF      // Re-lock

// If no re-lock, auto-lock after timeout
```

---

## Reset ve Interrupt

### Output Generation

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        RESET/IRQ GENERATION                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Counter                                                                │
│      │                                                                   │
│      ▼                                                                   │
│   ┌─────────────────┐                                                   │
│   │ CNT < WARN_TH?  │────────┐                                          │
│   └─────────────────┘        │ YES                                      │
│           │ NO               ▼                                          │
│           │           ┌─────────────┐     ┌─────────────┐               │
│           │           │ irq_en set? │────►│  wdt_irq_o  │               │
│           │           └─────────────┘ YES └─────────────┘               │
│           │                                                              │
│           ▼                                                              │
│   ┌─────────────────┐                                                   │
│   │  CNT == 0?      │────────┐                                          │
│   └─────────────────┘        │ YES                                      │
│           │ NO               ▼                                          │
│           │           ┌─────────────┐     ┌──────────────┐              │
│           │           │ rst_en set? │────►│ wdt_reset_o  │              │
│           │           └─────────────┘ YES └──────────────┘              │
│           │                                                              │
│           ▼                                                              │
│   ┌─────────────────┐                                                   │
│   │ Window error?   │────────┐                                          │
│   └─────────────────┘        │ YES                                      │
│           │ NO               ▼                                          │
│           │           ┌──────────────┐                                  │
│           │           │ wdt_reset_o  │ (immediate)                      │
│           │           └──────────────┘                                  │
│           │                                                              │
│           ▼                                                              │
│     Normal operation                                                     │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Debug Pause

```systemverilog
// Counter freezes during debug halt
always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
        counter <= LOAD;
    end else if (wdt_en) begin
        if (dbg_pause && debug_halt_i) begin
            // Counter frozen
        end else begin
            counter <= counter - 1;
        end
    end
end
```

---

## Kullanım Örneği

### C Header

```c
#define WDT_BASE       0x20008000

#define WDT_CTRL       (*(volatile uint32_t*)(WDT_BASE + 0x00))
#define WDT_LOAD       (*(volatile uint32_t*)(WDT_BASE + 0x04))
#define WDT_VALUE      (*(volatile uint32_t*)(WDT_BASE + 0x08))
#define WDT_KEY        (*(volatile uint32_t*)(WDT_BASE + 0x0C))
#define WDT_WINDOW     (*(volatile uint32_t*)(WDT_BASE + 0x10))
#define WDT_STATUS     (*(volatile uint32_t*)(WDT_BASE + 0x14))

// Key values
#define WDT_KEY_REFRESH  0x5A5A5A5A
#define WDT_KEY_UNLOCK   0x12345678
#define WDT_KEY_LOCK     0xDEADBEEF

// CTRL bits
#define WDT_EN         (1 << 0)
#define WDT_RST_EN     (1 << 1)
#define WDT_IRQ_EN     (1 << 2)
#define WDT_WIN_EN     (1 << 3)
#define WDT_DBG_PAUSE  (1 << 4)

// STATUS bits
#define WDT_TIMEOUT    (1 << 0)
#define WDT_EARLY_WARN (1 << 1)
#define WDT_WIN_ERR    (1 << 2)
```

### Basic Initialization

```c
void wdt_init(uint32_t timeout_cycles) {
    // Unlock registers
    WDT_KEY = WDT_KEY_UNLOCK;
    
    // Set timeout
    WDT_LOAD = timeout_cycles;
    
    // Enable with reset generation
    WDT_CTRL = WDT_EN | WDT_RST_EN | WDT_DBG_PAUSE;
    
    // Lock registers
    WDT_KEY = WDT_KEY_LOCK;
}
```

### Refresh (Kick)

```c
void wdt_refresh(void) {
    // Write refresh key
    WDT_KEY = WDT_KEY_REFRESH;
}
```

### Window Mode Setup

```c
void wdt_init_window(uint32_t load, uint32_t window) {
    WDT_KEY = WDT_KEY_UNLOCK;
    
    WDT_LOAD = load;           // Total timeout
    WDT_WINDOW = window;       // Window threshold
    
    // Enable window mode with reset and IRQ
    WDT_CTRL = WDT_EN | WDT_RST_EN | WDT_IRQ_EN | WDT_WIN_EN;
    
    WDT_KEY = WDT_KEY_LOCK;
}

// Main loop with windowed refresh
void main_loop(void) {
    while (1) {
        // Do work...
        process_data();
        
        // Check if in valid window before refresh
        uint32_t cnt = WDT_VALUE;
        uint32_t win = WDT_WINDOW;
        
        if (cnt <= win) {
            wdt_refresh();  // Safe to refresh
        }
        // else: Still in closed window, wait
    }
}
```

### Early Warning Handler

```c
void wdt_irq_handler(void) {
    // Check early warning flag
    if (WDT_STATUS & WDT_EARLY_WARN) {
        // Log warning - timeout approaching
        log_warning("WDT timeout approaching!");
        
        // Try to refresh if possible
        wdt_refresh();
        
        // Clear flag (write 1 to clear)
        WDT_STATUS = WDT_EARLY_WARN;
    }
    
    // Check window error (shouldn't happen in ISR)
    if (WDT_STATUS & WDT_WIN_ERR) {
        log_error("WDT window violation!");
        // System will reset soon...
    }
}
```

### Timeout Calculation

```c
// Calculate timeout in seconds
// Assuming 50 MHz clock
#define SYS_CLK 50000000

uint32_t timeout_to_cycles(float seconds) {
    return (uint32_t)(seconds * SYS_CLK);
}

// 1 second timeout
wdt_init(timeout_to_cycles(1.0));

// 100 ms timeout
wdt_init(timeout_to_cycles(0.1));
```

---

## Timing Örneği

### Normal Operation

```
         ┌──────────────────────────────────────────────────────────────┐
LOAD ────┤                                                              │
         │                                                              │
         │  ╲                                                           │
         │   ╲                                                          │
         │    ╲                                                         │
         │     ╲ refresh                                                │
         │      ╲────────────────────────────────────────────────────── │
         │       │╲                                                     │
         │       │ ╲                                                    │
         │       │  ╲ refresh                                           │
         │       │   ╲─────────────────────────────────────────────────│
         │       │    │╲                                               │
         │       │    │ ╲                                              │
         └───────┴────┴──╲─────────────────────────────────────────────┘
                          No timeout if refreshed periodically
```

### Timeout Event

```
         ┌──────────────────────────────────────────────────────────────┐
LOAD ────┤                                                              │
         │                                                              │
         │  ╲                                                           │
WINDOW ──│───╲──────────────────────────────────────────────────────────│
         │    ╲                                                         │
WARN ────│─────╲────────────────────────────────────────────────────────│
         │      ╲                                             IRQ ▼     │
         │       ╲                                                      │
   0 ────│────────╲─────────────────────────────────────────────────────│
         │         ▲                                                    │
         │         │ TIMEOUT → RESET                                    │
         └─────────┴────────────────────────────────────────────────────┘
                  No refresh → system reset
```

---

## Özet

`watchdog` modülü:

1. **32-bit Counter**: Down-counting timer
2. **Window Mode**: Prevents stuck-in-loop bugs
3. **Lock Protection**: Key-based register access
4. **Debug Support**: Counter pause during halt
5. **Dual Output**: Reset and early warning IRQ
6. **Configurable**: Flexible timeout settings
7. **Safety Critical**: System reliability feature
