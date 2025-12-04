---
title: "Top Module - ceres_wrapper.sv"
description: "Ceres SoC'nin top-level wrapper modülü - sistem entegrasyonu"
date: 2025-12-01
draft: false
weight: 290
---

# Ceres Top Module: ceres_wrapper.sv

`ceres_wrapper.sv` (282 satır), Ceres RISC-V SoC'nin en üst seviye modülüdür. CPU, Memory, Peripherals ve tüm kontrol mantığını birleştirir.

---

## 📁 Dosya Konumu

```
rtl/wrapper/ceres_wrapper.sv
```

---

## 🎯 Amaç

Ceres Top Module'ün ana görevleri:

1. **System Instantiation**: CPU, RAM, UART vb. bileşenleri örnekle
2. **Address Decoding**: Memory map'a göre adresleri ayır
3. **Bus Multiplexing**: Farklı bellek bölgelerine erişimi kontrol et
4. **Peripheral Management**: UART, Timer, Interrupt controller
5. **Clock & Reset**: Sistem saat ve reset yönetimi
6. **Debug Interface**: LED'ler, status sinyalleri

---

## 📊 System Block Diagram

```
┌──────────────────────────────────────────────────────────┐
│              ceres_wrapper.sv (Top Module)               │
├──────────────────────────────────────────────────────────┤
│                                                          │
│  ┌─────────────┐                                        │
│  │   CPU       │─────────────┬─────────────┐           │
│  │ (cpu.sv)    │             │             │           │
│  └─────────────┘             │             │           │
│                              │             │           │
│         Address Decoder      │             │           │
│         ┌──────────────────┐ │             │           │
│         │ sel_ram          │ │             │           │
│         │ sel_clint        │ │             │           │
│         │ sel_pbus         │ │             │           │
│         └──────────────────┘ │             │           │
│                ▲              │             │           │
│         cpu_mem_req           │             │           │
│                              ▼             ▼           │
│  ┌─────────────────────────────────────────────────┐  │
│  │        Memory Bus Multiplexer                   │  │
│  └─────────────────────────────────────────────────┘  │
│    │               │               │                  │
│    ▼               ▼               ▼                  │
│ ┌────────┐  ┌─────────┐  ┌──────────────────┐        │
│ │  RAM   │  │ CLINT   │  │  Peripherals    │        │
│ │(sp_bram│  │(Timer,  │  │(UART, GPIO,etc) │        │
│ │ .sv)   │  │MSIP)    │  │                  │        │
│ └────────┘  └─────────┘  └──────────────────┘        │
│                                                       │
│  ┌──────────────────────────────────────────────┐   │
│  │  Response Multiplexer → CPU                 │   │
│  │  cpu_mem_res = sel_ram ? ram_data :         │   │
│  │                sel_clint ? clint_data : ... │   │
│  └──────────────────────────────────────────────┘   │
│                                                      │
└──────────────────────────────────────────────────────┘
       │             │           │
       ▼             ▼           ▼
    UART_TX      GPIO/LED     External
    UART_RX      SPI/I2C      Interrupts
```

---

## 🏗️ Module Interface

### Parametreler

```systemverilog
module ceres_wrapper #(
    // System Configuration
    parameter int unsigned CLK_FREQ_HZ = CPU_CLK,       // 50 MHz (def)
    parameter int unsigned BAUD_RATE   = 115200,        // UART baud
    
    // Memory Configuration
    parameter int unsigned RAM_SIZE_KB = 1024,           // 1 MB RAM
    parameter int unsigned RAM_LATENCY = 16,             // Latency cycles
    
    // Peripheral Configuration
    parameter bit          NUM_UART = 1,                 // # of UARTs
    parameter bit          SPI_EN   = 1'b0,              // SPI enable
    parameter bit          I2C_EN   = 1'b0,              // I2C enable
    parameter bit          GPIO_EN  = 1'b0,              // GPIO enable
    parameter bit          PWM_EN   = 1'b0,              // PWM enable
    parameter bit          TIMER_EN = 1'b1,              // Timer enable
    parameter bit          PLIC_EN  = 1'b0,              // PLIC enable
    
    // Programming Interface
    parameter string PROG_SEQUENCE = PROGRAM_SEQUENCE    // Boot sequence
)
```

### Girişler (Inputs)

```systemverilog
// Clock & Reset
input logic clk_i;              // System clock
input logic rst_ni;             // Active-low reset

// UART Interface
input logic uart_rx_i;          // UART receive
output logic uart_tx_o;         // UART transmit

// SPI Interface (if SPI_EN=1)
input logic spi0_miso_i;        // SPI master-in
output logic spi0_mosi_o;       // SPI master-out
output logic spi0_sclk_o;       // SPI clock
output logic [3:0] spi0_ss_o;   // SPI chip select

// I2C Interface (if I2C_EN=1)
inout wire i2c0_sda_io;         // I2C data
inout wire i2c0_scl_io;         // I2C clock

// GPIO Interface (if GPIO_EN=1)
input logic [31:0] gpio_i;      // GPIO inputs
output logic [31:0] gpio_o;     // GPIO outputs
output logic [31:0] gpio_oe_o;  // GPIO output enable

// External Interrupts
input logic [7:0] ext_irq_i;    // External interrupt lines

// Programming Interface
input logic program_rx_i;       // Programming receive
output logic prog_mode_led_o;   // Programming LED

// Debug/Status
output logic [3:0] status_led_o; // Status LEDs
```

---

## 💾 Memory Map

```
┌─────────────────────────────────────────────────┐
│           PHYSICAL ADDRESS SPACE                │
│           (32-bit: 4 GB total)                  │
├─────────────────────────────────────────────────┤
│ 0x8000_0000 - 0x800F_FFFF  │  Main RAM          │
│ (128 KB default)            │  256 KB max        │
├─────────────────────────────────────────────────┤
│ 0x3000_0000 - 0x3000_FFFF  │  CLINT             │
│ (Core Local Interrupt Timer)                   │
│   0x3000_0000: MSIP (Machine SWI Pending)      │
│   0x3000_4000: MTIMECMP (Timer Compare)        │
│   0x3000_BFF8: MTIME (Timer Value)             │
├─────────────────────────────────────────────────┤
│ 0x2000_0000 - 0x20FF_FFFF  │  Peripherals       │
│                             │  (16 MB space)    │
│   0x2000_0000: UART0        │                   │
│   0x2000_1000: UART1        │                   │
│   0x2000_2000: SPI0         │                   │
│   0x2000_3000: I2C0         │                   │
│   0x2000_4000: GPIO         │                   │
│   0x2000_5000: PWM          │                   │
│   0x2000_6000: Timer        │                   │
│   0x2000_7000: PLIC         │                   │
├─────────────────────────────────────────────────┤
│ 0x0000_0000 - 0x1FFF_FFFF  │  Reserved/Ext Mem  │
│ (0x2000_0000 - 0x2FFF_FFFF)│  (Future use)      │
│ (0x4000_0000 - 0x7FFF_FFFF)│                    │
├─────────────────────────────────────────────────┤
│ 0xA000_0000 - 0xFFFF_FFFF  │  Debug/External    │
│                             │  (1 GB space)     │
└─────────────────────────────────────────────────┘
```

### Address Region Tanımları

```systemverilog
localparam logic [31:0] RAM_BASE  = 32'h8000_0000;
localparam logic [31:0] RAM_MASK  = 32'h000F_FFFF;   // 1 MB masking

localparam logic [31:0] CLINT_BASE = 32'h3000_0000;
localparam logic [31:0] CLINT_MASK = 32'h0000_FFFF;  // 64 KB masking

localparam logic [31:0] PBUS_BASE = 32'h2000_0000;   // Peripheral Bus
localparam logic [31:0] PBUS_MASK = 32'h00FF_FFFF;   // 16 MB masking
```

---

## 🔀 Address Decoding

### Address Decoder Logic

```systemverilog
always_comb begin
    // Check which region the address belongs to
    sel_ram   = (cpu_mem_req.addr & ~RAM_MASK)   == RAM_BASE;
    sel_clint = (cpu_mem_req.addr & ~CLINT_MASK) == CLINT_BASE;
    sel_pbus  = (cpu_mem_req.addr & ~PBUS_MASK)  == PBUS_BASE;
    
    // Address bus routing
    if (sel_ram) begin
        ram_addr = cpu_mem_req.addr[BYTE_OFFSET + $clog2(RAM_DEPTH)-1 : BYTE_OFFSET];
        ram_rd_en = cpu_mem_req.valid && !cpu_mem_req.we;
    end else if (sel_clint) begin
        clint_off = cpu_mem_req.addr[15:0];
        // CLINT operations
    end else if (sel_pbus) begin
        pbus_addr = cpu_mem_req.addr[23:0];
        // Peripheral operations
    end
end
```

### Hitmap

```
Address:     0x2000_0000 ← sel_pbus = 1
             0x3000_0000 ← sel_clint = 1
             0x8000_0000 ← sel_ram = 1
             0x8000_0004 ← sel_ram = 1
             0x8010_0000 ← (out of range)
```

---

## 💾 Memory (RAM) Controller

### RAM Bileşeni

```systemverilog
// RAM: Single-port Block RAM
// Size: 1 MB (default, parametric)
// Depth: 256K words (32-bit)

sp_bram #(
    .DEPTH(RAM_DEPTH),
    .WIDTH(CACHE_LINE_W)
) i_ram (
    .clk_i(clk_i),
    .rst_ni(sys_rst_n),
    
    // Address & Read
    .addr_i(ram_addr),
    .rd_en_i(ram_rd_en),
    .rd_data_o(ram_rdata),
    
    // Write
    .wr_en_i(ram_wr_en),
    .wr_data_i(cpu_mem_req.wdata),
    .wr_strb_i(ram_wstrb)
);
```

### Write Strobe Handling

```systemverilog
// Convert memory request to write strobes
always_comb begin
    ram_wstrb = '0;
    case (cpu_mem_req.size)
        3'b000: begin  // Byte write
            ram_wstrb[cpu_mem_req.addr[1:0]] = 1'b1;
        end
        3'b001: begin  // Half-word (2 bytes)
            ram_wstrb[cpu_mem_req.addr[1]] +: 2 = 2'b11;
        end
        3'b010: begin  // Word (4 bytes)
            ram_wstrb = 4'b1111;
        end
        default: ram_wstrb = 4'b0;
    endcase
end
```

---

## ⏱️ CLINT (Core Local Interrupt Timer)

### CLINT Registers

```systemverilog
// Machine Software Interrupt Pending
logic msip_q;

// Machine Timer Compare
logic [63:0] mtimecmp_q;

// Machine Timer
logic [63:0] mtime_q;
```

### Timer Operation

```systemverilog
// Increment MTIME every cycle
always_ff @(posedge clk_i) begin
    if (!sys_rst_n) begin
        mtime_q <= 64'b0;
    end else begin
        mtime_q <= mtime_q + 64'b1;  // Increment every cycle
    end
end

// Timer interrupt
assign timer_irq = (mtime_q >= mtimecmp_q);
```

### CLINT Address Map

```
0x3000_0000: MSIP[0]    (R/W)   Machine Software Interrupt Pending
0x3000_4000: MTIMECMP[0](R/W)   Timer Compare Register (64-bit)
0x3000_BFF8: MTIME      (R)     Global Timer (64-bit, read-only)
```

---

## 🔌 Peripheral Bus (PBUS)

### Peripheral Sub-Devices

```systemverilog
// UART Controller
uart #(
    .CLK_FREQ_HZ(CLK_FREQ_HZ),
    .BAUD_RATE(BAUD_RATE)
) i_uart (
    .clk_i(clk_i),
    .rst_ni(sys_rst_n),
    .rx_i(uart_rx_i),
    .tx_o(uart_tx_o),
    
    // Memory interface
    .mem_addr_i(pbus_addr),
    .mem_data_i(cpu_mem_req.wdata),
    .mem_data_o(uart_data),
    .mem_valid_i(sel_pbus && uart_selected),
    .mem_we_i(cpu_mem_req.we)
);

// Conditional instantiation based on parameters
if (SPI_EN) begin
    // SPI controller
    spi i_spi ( ... );
end

if (GPIO_EN) begin
    // GPIO controller
    gpio i_gpio ( ... );
end
```

---

## 🚀 Memory Response Multiplexer

### Response Selection

```systemverilog
always_comb begin
    // Select response based on which device was accessed
    if (sel_ram) begin
        cpu_mem_res.rdata = ram_rdata;
        cpu_mem_res.valid = ram_pending_q;  // Delayed for latency
        cpu_mem_res.err = 1'b0;
    end else if (sel_clint) begin
        cpu_mem_res.rdata = clint_rdata;
        cpu_mem_res.valid = 1'b1;  // Immediate
        cpu_mem_res.err = 1'b0;
    end else if (sel_pbus) begin
        cpu_mem_res.rdata = pbus_rdata;
        cpu_mem_res.valid = pbus_valid;
        cpu_mem_res.err = 1'b0;
    end else begin
        // Invalid address
        cpu_mem_res.rdata = 32'b0;
        cpu_mem_res.valid = 1'b0;
        cpu_mem_res.err = 1'b1;  // Error: unmapped address
    end
end
```

---

## 📶 Reset Management

### Reset Sources

```systemverilog
// Power-on reset
input logic rst_ni;

// Programming interface reset
logic prog_reset;

// Combined system reset
logic sys_rst_n;

`ifdef VERILATOR
    // In simulation, bypass programming reset
    assign sys_rst_n = rst_ni;
`else
    // In hardware, combine all reset sources
    assign sys_rst_n = rst_ni & prog_reset;
`endif
```

---

## 🔗 CPU Instantiation

### CPU Module Connection

```systemverilog
cpu i_cpu (
    // Clock & Reset
    .clk_i(clk_i),
    .rst_ni(sys_rst_n),
    
    // Memory Interface
    .iomem_req_o(cpu_mem_req),
    .iomem_res_i(cpu_mem_res),
    
    // UART
    .uart_tx_o(uart_tx_o),
    .uart_rx_i(uart_rx_i)
);
```

### CPU to Memory Dataflow

```
CPU Request:
    cpu_mem_req.addr   → Address decoder
    cpu_mem_req.data   → Write data
    cpu_mem_req.valid  → Request valid
    cpu_mem_req.we     → Write enable
    
Memory Response:
    cpu_mem_res.data   ← Selected device data
    cpu_mem_res.valid  ← Data ready
    cpu_mem_res.err    ← Error flag
```

---

## 🎛️ Interrupt Handling

### Interrupt Sources

```systemverilog
logic timer_irq;        // From CLINT timer
logic [7:0] ext_irq;    // External interrupts
logic uart_irq;         // From UART

// Interrupt aggregation (can be extended to PLIC)
logic m_eip;            // Machine external interrupt pending

// Simple OR of all interrupt sources
assign cpu_irq = timer_irq | uart_irq | |(ext_irq);
```

---

## 💻 Verilator Simulation

### Verilator-Specific Code

```systemverilog
`ifdef VERILATOR
    // In simulation:
    // - Remove UART floating issues
    // - Bypass complex peripherals
    // - Simplify clock domains
    
    assign sys_rst_n = rst_ni;  // Bypass prog_reset
    
    // Assert reset on startup
    initial begin
        $display("CERES Wrapper initialized");
    end
    
    // Optional: Trace signals
    initial begin
        $dumpfile("ceres_wrapper.vcd");
        $dumpvars(0, ceres_wrapper);
    end
`endif
```

---

## 📊 Signal Summary

| Signal | Width | Direction | Purpose |
|--------|-------|-----------|---------|
| clk_i | 1 | IN | System clock |
| rst_ni | 1 | IN | Active-low reset |
| cpu_mem_req | struct | OUT | Memory request from CPU |
| cpu_mem_res | struct | IN | Memory response to CPU |
| uart_rx_i | 1 | IN | UART receive |
| uart_tx_o | 1 | OUT | UART transmit |
| ram_rdata | CACHE_LINE_W | internal | RAM read data |
| ram_wstrb | 4 | internal | Write strobe |
| mtime_q | 64 | internal | Machine timer counter |
| timer_irq | 1 | internal | Timer interrupt signal |

---

## 🎯 Toplam Sistem Davranışı

### Boot Sequence

```
1. Reset (rst_ni = 0)
   ├─ CPU registers zeroed
   ├─ PC ← RESET_VECTOR (0x8000_0000)
   ├─ RAM cleared
   └─ All peripherals disabled

2. Release Reset (rst_ni = 1)
   ├─ Fetch first instruction from 0x8000_0000
   ├─ CLINT timer starts incrementing
   ├─ Peripherals ready

3. Normal Operation
   ├─ CPU executes instructions
   ├─ Memory requests → Address decoder
   ├─ Responses → CPU
   └─ Interrupts → CPU (timer, UART, etc.)
```

### Example: UART Write

```
CPU executes: sw x3, 0(x4)  ; x4 = 0x2000_0000 (UART TX)

Cycle N:
├─ cpu_mem_req = {addr: 0x2000_0000, data: 0x41, we: 1, valid: 1}
├─ sel_pbus = 1 (peripheral bus selected)
├─ uart_wr_en = 1
├─ uart_data = 0x41 ('A')
├─ UART TX shifts out '0x41'

Cycle N+11 (after 11 cycle latency):
└─ UART TX complete, line ready for next byte
```

---

## 🔧 Configuration Examples

### Minimal Configuration (Learning)

```systemverilog
ceres_wrapper #(
    .CLK_FREQ_HZ(50_000_000),
    .BAUD_RATE(115200),
    .RAM_SIZE_KB(128),         // Minimal RAM
    .NUM_UART(1),
    .SPI_EN(1'b0),
    .GPIO_EN(1'b0),
    .TIMER_EN(1'b1)
) i_ceres ( ... );
```

### Full Configuration (FPGA)

```systemverilog
ceres_wrapper #(
    .CLK_FREQ_HZ(100_000_000),
    .BAUD_RATE(115200),
    .RAM_SIZE_KB(1024),        // Full RAM
    .NUM_UART(2),
    .SPI_EN(1'b1),
    .I2C_EN(1'b1),
    .GPIO_EN(1'b1),
    .PWM_EN(1'b1),
    .TIMER_EN(1'b1),
    .PLIC_EN(1'b1)
) i_ceres ( ... );
```

---

## 🎓 Sonraki Adımlar

- [CPU Top Module](./CPU_TOP_MODULE.md)
- [Memory & Cache](./memory/bram.md)
- [UART Peripheral](./periph/uart.md)

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025

