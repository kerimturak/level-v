# Wishbone CLINT Slave - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Register Map](#register-map)
4. [Timer Implementasyonu](#timer-implementasyonu)
5. [Wishbone Protokol](#wishbone-protokol)
6. [Interrupt Üretimi](#interrupt-üretimi)

---

## Genel Bakış

### Amaç

`wb_clint_slave` modülü, **RISC-V Core Local Interruptor (CLINT)** fonksiyonalitesini Wishbone bus arayüzüyle sunar. Timer interrupt ve software interrupt yönetimi sağlar.

### Dosya Konumu

```
rtl/wrapper/wb_clint_slave.sv
```

### CLINT Blok Diyagramı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          WB_CLINT_SLAVE                                          │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   Wishbone Bus                           CLINT Registers                         │
│                                                                                  │
│   ┌────────────┐                        ┌─────────────────┐                     │
│   │   cyc/stb  │───────────────────────►│    MSIP[0]      │──────► sw_irq       │
│   │   we       │                        │    (0x0000)     │                     │
│   │   addr     │                        └─────────────────┘                     │
│   │   wdata    │                                                                │
│   │   sel      │                        ┌─────────────────┐                     │
│   └────────────┘                        │   MTIMECMP[0]   │                     │
│                                         │   (0x4000-07)   │                     │
│   ┌────────────┐                        └────────┬────────┘                     │
│   │   ack      │◄───────────────────┐           │                              │
│   │   rdata    │                    │           │ compare                       │
│   │   err      │                    │           ▼                               │
│   └────────────┘                    │   ┌───────────────┐                       │
│                                     │   │   >=          │──────► timer_irq      │
│                                     │   └───────┬───────┘                       │
│                                     │           │                               │
│                                     │   ┌───────┴───────┐                       │
│                                     └───┤    MTIME      │◄────── clk (+1/cyc)   │
│                                         │  (0xBFF8-FF)  │                       │
│                                         └───────────────┘                       │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Parametreler

```systemverilog
module wb_clint_slave
  import ceres_param::*;
#(
    parameter int NUM_HARTS = 1  // Number of harts (cores)
)
```

### Port Tanımları

```systemverilog
(
    input  logic clk_i,
    input  logic rst_ni,

    // Wishbone Slave Interface
    input  wb_master_t wb_m_i,    // Master request
    output wb_slave_t  wb_s_o,    // Slave response

    // Interrupt Outputs
    output logic timer_irq_o,     // Timer interrupt
    output logic sw_irq_o         // Software interrupt
);
```

### Wishbone Struct Detayları

```systemverilog
// wb_master_t (from ceres_param)
typedef struct packed {
    logic        cyc;        // Bus cycle active
    logic        stb;        // Strobe (valid transfer)
    logic        we;         // Write enable
    logic [31:0] adr;        // Address
    logic [31:0] dat;        // Write data
    logic [3:0]  sel;        // Byte select
    logic [2:0]  cti;        // Cycle type identifier
    logic [1:0]  bte;        // Burst type extension
} wb_master_t;

// wb_slave_t (from ceres_param)
typedef struct packed {
    logic        ack;        // Acknowledge
    logic        err;        // Error
    logic        rty;        // Retry
    logic [31:0] dat;        // Read data
} wb_slave_t;
```

---

## Register Map

### CLINT Address Layout (SiFive Spec)

```
┌──────────────────────────────────────────────────────────────────────────┐
│                        CLINT REGISTER MAP                                 │
├────────────────┬──────────┬───────────────────────────────────────────────┤
│ Offset         │ Width    │ Description                                   │
├────────────────┼──────────┼───────────────────────────────────────────────┤
│ 0x0000         │ 4 bytes  │ MSIP[0] - Software interrupt pending          │
│ 0x0004         │ 4 bytes  │ MSIP[1] - (multi-hart only)                   │
│ ...            │          │                                               │
├────────────────┼──────────┼───────────────────────────────────────────────┤
│ 0x4000         │ 8 bytes  │ MTIMECMP[0] - Timer compare value             │
│ 0x4008         │ 8 bytes  │ MTIMECMP[1] - (multi-hart only)               │
│ ...            │          │                                               │
├────────────────┼──────────┼───────────────────────────────────────────────┤
│ 0xBFF8         │ 8 bytes  │ MTIME - Timer counter (shared)                │
└────────────────┴──────────┴───────────────────────────────────────────────┘
```

### Register Definitions

```systemverilog
// Address offsets
localparam logic [15:0] MSIP_OFFSET     = 16'h0000;
localparam logic [15:0] MTIMECMP_OFFSET = 16'h4000;
localparam logic [15:0] MTIME_OFFSET    = 16'hBFF8;

// CLINT Registers
logic [63:0] mtime_q;        // 64-bit free-running counter
logic [63:0] mtimecmp_q;     // 64-bit timer compare
logic        msip_q;         // Software interrupt pending
```

---

## Timer Implementasyonu

### MTIME Counter

```systemverilog
// Free-running 64-bit timer
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        mtime_q <= '0;
    end else begin
        mtime_q <= mtime_q + 1;
    end
end
```

### MTIME Yazma

```systemverilog
// mtime yazılabilir (debugging/test için)
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        mtime_q <= '0;
    end else if (wb_req && wb_we && (addr_offset == MTIME_OFFSET)) begin
        mtime_q[31:0] <= wb_m_i.dat;
    end else if (wb_req && wb_we && (addr_offset == MTIME_OFFSET + 4)) begin
        mtime_q[63:32] <= wb_m_i.dat;
    end else begin
        mtime_q <= mtime_q + 1;
    end
end
```

### MTIMECMP Register

```systemverilog
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        mtimecmp_q <= '1;  // Max value (interrupt disabled at reset)
    end else if (wb_req && wb_we) begin
        case (addr_offset)
            MTIMECMP_OFFSET:     mtimecmp_q[31:0]  <= wb_m_i.dat;
            MTIMECMP_OFFSET + 4: mtimecmp_q[63:32] <= wb_m_i.dat;
        endcase
    end
end
```

---

## Wishbone Protokol

### Request Detection

```systemverilog
wire wb_req = wb_m_i.cyc && wb_m_i.stb;
wire wb_we  = wb_m_i.we;
wire [15:0] addr_offset = wb_m_i.adr[15:0];
```

### Read Logic

```systemverilog
logic [31:0] rdata;

always_comb begin
    rdata = '0;

    case (addr_offset)
        // MSIP
        MSIP_OFFSET: begin
            rdata = {31'b0, msip_q};
        end

        // MTIMECMP (lower 32 bits)
        MTIMECMP_OFFSET: begin
            rdata = mtimecmp_q[31:0];
        end

        // MTIMECMP (upper 32 bits)
        MTIMECMP_OFFSET + 4: begin
            rdata = mtimecmp_q[63:32];
        end

        // MTIME (lower 32 bits)
        MTIME_OFFSET: begin
            rdata = mtime_q[31:0];
        end

        // MTIME (upper 32 bits)
        MTIME_OFFSET + 4: begin
            rdata = mtime_q[63:32];
        end

        default: begin
            rdata = '0;
        end
    endcase
end
```

### Write Logic

```systemverilog
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        msip_q     <= 1'b0;
        mtimecmp_q <= '1;
    end else if (wb_req && wb_we) begin
        case (addr_offset)
            MSIP_OFFSET: begin
                msip_q <= wb_m_i.dat[0];
            end

            MTIMECMP_OFFSET: begin
                mtimecmp_q[31:0] <= wb_m_i.dat;
            end

            MTIMECMP_OFFSET + 4: begin
                mtimecmp_q[63:32] <= wb_m_i.dat;
            end
        endcase
    end
end
```

### Response Generation

```systemverilog
// Single-cycle response
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        wb_s_o.ack <= 1'b0;
        wb_s_o.dat <= '0;
    end else begin
        wb_s_o.ack <= wb_req;
        wb_s_o.dat <= rdata;
    end
end

assign wb_s_o.err = 1'b0;
assign wb_s_o.rty = 1'b0;
```

---

## Interrupt Üretimi

### Timer Interrupt

```systemverilog
// Timer interrupt: mtime >= mtimecmp
assign timer_irq_o = (mtime_q >= mtimecmp_q);
```

### Software Interrupt

```systemverilog
// Software interrupt: msip bit set
assign sw_irq_o = msip_q;
```

### Interrupt Clearing

```systemverilog
// Timer interrupt: mtimecmp'ye mtime'dan büyük değer yazarak
// Software interrupt: msip'e 0 yazarak
```

---

## Timing Diyagramı

### Timer Interrupt Sequence

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └───

mtime_q    ────┬───┬───┬───┬───┬───┬───┬───┬───
               │100│101│102│103│104│105│106│107│

mtimecmp_q ────────────────────────────────────
                            104

timer_irq_o                     ┌──────────────
           ─────────────────────┘
                            mtime >= mtimecmp
```

### MSIP Write Sequence

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └───

wb_m_i.cyc     ┌───────┐           ┌───────┐
           ────┘       └───────────┘       └───

wb_m_i.stb     ┌───────┐           ┌───────┐
           ────┘       └───────────┘       └───

wb_m_i.we      ┌───────┐           ┌───────┐
           ────┘       └───────────┘       └───

wb_m_i.adr ────┤0x0000 ├───────────┤0x0000 ├───

wb_m_i.dat ────┤  0x1  ├───────────┤  0x0  ├───

wb_s_o.ack         ┌───┐               ┌───┐
           ────────┘   └───────────────┘   └───

msip_q             ┌───────────────────┐
           ────────┘                   └───────

sw_irq_o           ┌───────────────────┐
           ────────┘                   └───────
```

---

## Software Usage

### C Header

```c
#ifndef _CLINT_H_
#define _CLINT_H_

#include <stdint.h>

#define CLINT_BASE      0x30000000

#define CLINT_MSIP      (*(volatile uint32_t *)(CLINT_BASE + 0x0000))
#define CLINT_MTIMECMP  (*(volatile uint64_t *)(CLINT_BASE + 0x4000))
#define CLINT_MTIME     (*(volatile uint64_t *)(CLINT_BASE + 0xBFF8))

// Convenience macros for 32-bit access
#define CLINT_MTIMECMP_LO (*(volatile uint32_t *)(CLINT_BASE + 0x4000))
#define CLINT_MTIMECMP_HI (*(volatile uint32_t *)(CLINT_BASE + 0x4004))
#define CLINT_MTIME_LO    (*(volatile uint32_t *)(CLINT_BASE + 0xBFF8))
#define CLINT_MTIME_HI    (*(volatile uint32_t *)(CLINT_BASE + 0xBFFC))

#endif
```

### Timer Interrupt Setup

```c
void timer_init(uint64_t interval) {
    // Read current time
    uint64_t now = CLINT_MTIME;

    // Set compare value
    // Write high word first to avoid spurious interrupt
    CLINT_MTIMECMP_HI = 0xFFFFFFFF;
    CLINT_MTIMECMP_LO = (uint32_t)(now + interval);
    CLINT_MTIMECMP_HI = (uint32_t)((now + interval) >> 32);
}

void timer_handler(void) {
    // Reschedule next interrupt
    uint64_t next = CLINT_MTIMECMP + TIMER_INTERVAL;
    CLINT_MTIMECMP_HI = 0xFFFFFFFF;
    CLINT_MTIMECMP_LO = (uint32_t)next;
    CLINT_MTIMECMP_HI = (uint32_t)(next >> 32);
}
```

### Software Interrupt

```c
void trigger_sw_interrupt(void) {
    CLINT_MSIP = 1;
}

void clear_sw_interrupt(void) {
    CLINT_MSIP = 0;
}
```

---

## Özet

`wb_clint_slave` modülü:

1. **MTIME**: 64-bit free-running timer
2. **MTIMECMP**: 64-bit timer compare
3. **MSIP**: Software interrupt pending
4. **Wishbone**: Single-cycle response
5. **Interrupts**: Timer (mtime >= mtimecmp), SW (msip)

Bu modül, RISC-V standardına uygun CLINT fonksiyonalitesi sağlar.
