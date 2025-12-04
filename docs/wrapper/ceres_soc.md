# CERES SoC - Full System-on-Chip Wrapper Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Peripheral Konfigürasyonu](#peripheral-konfigürasyonu)
4. [Address Decoder](#address-decoder)
5. [CLINT Implementasyonu](#clint-implementasyonu)
6. [Peripheral Entegrasyonu](#peripheral-entegrasyonu)
7. [RAM ve Programming](#ram-ve-programming)
8. [Response Multiplexer](#response-multiplexer)

---

## Genel Bakış

### Amaç

`ceres_soc` modülü, **tam özellikli SoC** implementasyonu sunar. CPU, RAM ve tüm peripherals'ı entegre ederek çalışır duruma getirir.

### Dosya Konumu

```
rtl/wrapper/ceres_soc.sv
```

### SoC Topolojisi

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              CERES SOC                                           │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│  ┌────────────────────────────────────────────────────────────────────────────┐ │
│  │                           CPU CORE                                          │ │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐              │ │
│  │  │  Fetch  │→│ Decode  │→│ Execute │→│ Memory  │→│WriteBack│              │ │
│  │  └─────────┘ └─────────┘ └─────────┘ └─────────┘ └─────────┘              │ │
│  └───────────────────────────────┬────────────────────────────────────────────┘ │
│                                  │                                               │
│                                  ▼                                               │
│  ┌───────────────────────────────────────────────────────────────────────────┐  │
│  │                        ADDRESS DECODER                                     │  │
│  │   0x8xxx → RAM    0x3xxx → CLINT    0x2xxx → PERIPHERALS                  │  │
│  └────┬──────────────────────┬────────────────────────┬──────────────────────┘  │
│       │                      │                        │                          │
│       ▼                      ▼                        ▼                          │
│  ┌─────────┐          ┌─────────────┐         ┌─────────────────────────────┐   │
│  │   RAM   │          │    CLINT    │         │      PERIPHERAL BUS         │   │
│  │ 1024KB  │          │ mtime/cmp   │         │                             │   │
│  │(wrapper)│          │   msip      │         │ UART SPI I2C GPIO PWM TIMER │   │
│  └─────────┘          └─────────────┘         │ PLIC WDT DMA VGA            │   │
│                                               └─────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Parametreler

```systemverilog
module ceres_soc
  import ceres_param::*;
#(
    // System Configuration
    parameter int  CPU_CLK_P       = CPU_CLK,         // 50 MHz
    parameter int  BAUD_RATE       = UART_BAUD,       // 115200
    parameter int  ADDR_WIDTH      = 32,
    parameter int  DATA_WIDTH      = 32,
    parameter int  RAM_SIZE_KB     = 1024,            // 1 MB
    parameter int  RAM_LATENCY     = 16,

    // UART Configuration
    parameter int  UART_CLK_FREQ   = CPU_CLK,
    parameter int  UART_BAUD_RATE  = UART_BAUD,

    // Peripheral Enable Flags
    parameter bit  EN_GPIO         = 1'b1,
    parameter bit  EN_PLIC         = 1'b1,
    parameter bit  EN_TIMER        = 1'b1,
    parameter bit  EN_WDT          = 1'b1,
    parameter bit  EN_DMA          = 1'b1,
    parameter bit  EN_PWM          = 1'b1,
    parameter bit  EN_VGA          = 1'b0,

    // Peripheral Configuration
    parameter int  GPIO_WIDTH_P    = GPIO_WIDTH,      // 32
    parameter int  PLIC_SOURCES    = PLIC_NUM_SOURCES,// 32
    parameter int  PLIC_TARGETS    = PLIC_NUM_TARGETS,// 1
    parameter int  TIMER_WIDTH     = 64,
    parameter int  PWM_CHANNELS    = PWM_NUM_CHANNELS,// 4
    parameter int  DMA_CHANNELS    = DMA_NUM_CHANNELS,// 4
    parameter int  VGA_HRES        = 640,
    parameter int  VGA_VRES        = 480,

    // Programming Interface
    parameter string PROGRAM_SEQUENCE_P = PROGRAM_SEQUENCE  // "CERESTEST"
)
```

### Port Tanımları

```systemverilog
(
    // Clock and Reset
    input  logic i_clk,
    input  logic i_rst_n,

    // UART Interface
    output logic o_uart_tx,
    input  logic i_uart_rx,

    // SPI Interface
    output logic       o_spi_sclk,
    output logic       o_spi_mosi,
    input  logic       i_spi_miso,
    output logic [3:0] o_spi_cs_n,

    // I2C Interface
    inout  wire  io_i2c_sda,
    inout  wire  io_i2c_scl,

    // GPIO Interface
    input  logic [GPIO_WIDTH_P-1:0] i_gpio,
    output logic [GPIO_WIDTH_P-1:0] o_gpio,
    output logic [GPIO_WIDTH_P-1:0] o_gpio_oe,

    // PWM Outputs
    output logic [PWM_CHANNELS-1:0] o_pwm,

    // VGA Interface
    output logic [3:0] o_vga_r,
    output logic [3:0] o_vga_g,
    output logic [3:0] o_vga_b,
    output logic       o_vga_hsync,
    output logic       o_vga_vsync,

    // External Interrupts
    input  logic [PLIC_SOURCES-1:0] i_ext_irq,

    // Programming Interface
    input  logic i_prog_rx,
    output logic o_prog_mode_led,

    // Debug Status
    output logic [3:0] o_status_led
);
```

---

## Peripheral Konfigürasyonu

### Generate-based Peripheral Enable

```systemverilog
// GPIO - Enabled by EN_GPIO
generate
    if (EN_GPIO) begin : gen_gpio
        gpio #(
            .WIDTH(GPIO_WIDTH_P)
        ) i_gpio (
            .i_clk    (i_clk),
            .i_rst_n  (sys_rst_n),
            .i_stb    (gpio_sel),
            .i_we     (mem_we),
            .i_addr   (mem_addr[3:2]),
            .i_wdata  (mem_wdata),
            .o_rdata  (gpio_rdata),
            .i_gpio   (i_gpio),
            .o_gpio   (o_gpio),
            .o_gpio_oe(o_gpio_oe)
        );
    end else begin : gen_no_gpio
        assign gpio_rdata = '0;
        assign o_gpio     = '0;
        assign o_gpio_oe  = '0;
    end
endgenerate
```

### Peripheral Enable Summary

| Peripheral | Parameter | Base Offset | Size |
|------------|-----------|-------------|------|
| GPIO | EN_GPIO | 0x4000 | 16B |
| PLIC | EN_PLIC | 0x7000 | 4KB |
| Timer | EN_TIMER | 0x6000 | 64B |
| WDT | EN_WDT | 0x8000 | 16B |
| DMA | EN_DMA | 0x9000 | 256B |
| PWM | EN_PWM | 0x5000 | 64B |
| VGA | EN_VGA | 0xD000 | 4KB |

---

## Address Decoder

### Memory Region Detection

```systemverilog
// Upper nibble decode (addr[31:28])
wire is_ram_region    = (mem_addr[31:28] == 4'h8);  // 0x8xxx_xxxx
wire is_clint_region  = (mem_addr[31:28] == 4'h3);  // 0x3xxx_xxxx
wire is_periph_region = (mem_addr[31:28] == 4'h2);  // 0x2xxx_xxxx
```

### Peripheral Select Decode

```systemverilog
// Peripheral offset decode (addr[15:12])
wire uart_sel  = is_periph_region && (mem_addr[15:12] == 4'h0);  // 0x2000_0xxx
wire spi_sel   = is_periph_region && (mem_addr[15:12] == 4'h2);  // 0x2000_2xxx
wire i2c_sel   = is_periph_region && (mem_addr[15:12] == 4'h3);  // 0x2000_3xxx
wire gpio_sel  = is_periph_region && (mem_addr[15:12] == 4'h4);  // 0x2000_4xxx
wire pwm_sel   = is_periph_region && (mem_addr[15:12] == 4'h5);  // 0x2000_5xxx
wire timer_sel = is_periph_region && (mem_addr[15:12] == 4'h6);  // 0x2000_6xxx
wire plic_sel  = is_periph_region && (mem_addr[15:12] == 4'h7);  // 0x2000_7xxx
wire wdt_sel   = is_periph_region && (mem_addr[15:12] == 4'h8);  // 0x2000_8xxx
wire dma_sel   = is_periph_region && (mem_addr[15:12] == 4'h9);  // 0x2000_9xxx
wire vga_sel   = is_periph_region && (mem_addr[15:12] == 4'hD);  // 0x2000_Dxxx
```

### Complete Address Map

```
┌──────────────────────────────────────────────────────────────┐
│                    ADDRESS MAP                                │
├──────────────┬────────────────┬───────────────────────────────┤
│ Region       │ Address        │ Description                   │
├──────────────┼────────────────┼───────────────────────────────┤
│ RAM          │ 0x8000_0000    │ Main RAM (1MB default)        │
│              │ 0x800F_FFFF    │                               │
├──────────────┼────────────────┼───────────────────────────────┤
│ CLINT        │ 0x3000_0000    │ msip[0]                       │
│              │ 0x3000_4000    │ mtimecmp[0]                   │
│              │ 0x3000_BFF8    │ mtime                         │
├──────────────┼────────────────┼───────────────────────────────┤
│ PERIPH       │ 0x2000_0xxx    │ UART                          │
│              │ 0x2000_2xxx    │ SPI                           │
│              │ 0x2000_3xxx    │ I2C                           │
│              │ 0x2000_4xxx    │ GPIO                          │
│              │ 0x2000_5xxx    │ PWM                           │
│              │ 0x2000_6xxx    │ Timer                         │
│              │ 0x2000_7xxx    │ PLIC                          │
│              │ 0x2000_8xxx    │ WDT                           │
│              │ 0x2000_9xxx    │ DMA                           │
│              │ 0x2000_Dxxx    │ VGA                           │
└──────────────┴────────────────┴───────────────────────────────┘
```

---

## CLINT Implementasyonu

### CLINT Register Map

```systemverilog
// CLINT Register Addresses (SiFive spec)
localparam CLINT_MSIP_OFFSET     = 16'h0000;  // SW interrupt
localparam CLINT_MTIMECMP_OFFSET = 16'h4000;  // Timer compare
localparam CLINT_MTIME_OFFSET    = 16'hBFF8;  // Timer counter
```

### CLINT Implementation

```systemverilog
// CLINT Registers
logic [63:0] mtime_q;           // Free-running timer
logic [63:0] mtimecmp_q;        // Timer compare value
logic        msip_q;            // Software interrupt pending

// Timer Counter (mtime)
always_ff @(posedge i_clk or negedge sys_rst_n) begin
    if (!sys_rst_n) begin
        mtime_q <= '0;
    end else begin
        mtime_q <= mtime_q + 1;
    end
end

// Timer Interrupt Generation
assign timer_irq = (mtime_q >= mtimecmp_q);
assign sw_irq    = msip_q;
```

### CLINT Read Logic

```systemverilog
always_comb begin
    clint_rdata = '0;
    case (mem_addr[15:0])
        CLINT_MSIP_OFFSET:     clint_rdata = {31'b0, msip_q};
        CLINT_MTIMECMP_OFFSET: clint_rdata = mtimecmp_q[31:0];
        CLINT_MTIMECMP_OFFSET + 4: clint_rdata = mtimecmp_q[63:32];
        CLINT_MTIME_OFFSET:    clint_rdata = mtime_q[31:0];
        CLINT_MTIME_OFFSET + 4:clint_rdata = mtime_q[63:32];
        default:               clint_rdata = '0;
    endcase
end
```

### CLINT Write Logic

```systemverilog
always_ff @(posedge i_clk or negedge sys_rst_n) begin
    if (!sys_rst_n) begin
        msip_q     <= '0;
        mtimecmp_q <= '1;  // Max value (interrupt disabled)
    end else if (clint_sel && mem_we) begin
        case (mem_addr[15:0])
            CLINT_MSIP_OFFSET: begin
                msip_q <= mem_wdata[0];
            end
            CLINT_MTIMECMP_OFFSET: begin
                mtimecmp_q[31:0] <= mem_wdata;
            end
            CLINT_MTIMECMP_OFFSET + 4: begin
                mtimecmp_q[63:32] <= mem_wdata;
            end
        endcase
    end
end
```

---

## Peripheral Entegrasyonu

### UART

```systemverilog
uart #(
    .CLK_FREQ (UART_CLK_FREQ),
    .BAUD_RATE(UART_BAUD_RATE)
) i_uart (
    .i_clk     (i_clk),
    .i_rst_n   (sys_rst_n),
    .i_stb     (uart_sel),
    .i_we      (mem_we),
    .i_addr    (mem_addr[3:2]),
    .i_wdata   (mem_wdata),
    .i_wstrb   (mem_wstrb),
    .o_rdata   (uart_rdata),
    .i_uart_rx (i_uart_rx),
    .o_uart_tx (o_uart_tx),
    .o_rx_irq  (uart_rx_irq),
    .o_tx_irq  (uart_tx_irq)
);
```

### PLIC

```systemverilog
generate
    if (EN_PLIC) begin : gen_plic
        plic #(
            .NUM_SOURCES(PLIC_SOURCES),
            .NUM_TARGETS(PLIC_TARGETS)
        ) i_plic (
            .i_clk      (i_clk),
            .i_rst_n    (sys_rst_n),
            .i_stb      (plic_sel),
            .i_we       (mem_we),
            .i_addr     (mem_addr[11:2]),
            .i_wdata    (mem_wdata),
            .o_rdata    (plic_rdata),
            .i_irq_src  (irq_sources),
            .o_irq_tgt  (plic_irq)
        );
    end
endgenerate
```

### Timer (Standalone)

```systemverilog
generate
    if (EN_TIMER) begin : gen_timer
        timer #(
            .WIDTH(TIMER_WIDTH)
        ) i_timer (
            .i_clk    (i_clk),
            .i_rst_n  (sys_rst_n),
            .i_stb    (timer_sel),
            .i_we     (mem_we),
            .i_addr   (mem_addr[5:2]),
            .i_wdata  (mem_wdata),
            .o_rdata  (timer_rdata),
            .o_irq    (timer_periph_irq)
        );
    end
endgenerate
```

### PWM Controller

```systemverilog
generate
    if (EN_PWM) begin : gen_pwm
        pwm #(
            .NUM_CHANNELS(PWM_CHANNELS)
        ) i_pwm (
            .i_clk    (i_clk),
            .i_rst_n  (sys_rst_n),
            .i_stb    (pwm_sel),
            .i_we     (mem_we),
            .i_addr   (mem_addr[5:2]),
            .i_wdata  (mem_wdata),
            .o_rdata  (pwm_rdata),
            .o_pwm    (o_pwm)
        );
    end
endgenerate
```

### DMA Controller

```systemverilog
generate
    if (EN_DMA) begin : gen_dma
        dma #(
            .NUM_CHANNELS(DMA_CHANNELS)
        ) i_dma (
            .i_clk      (i_clk),
            .i_rst_n    (sys_rst_n),
            // Register interface
            .i_stb      (dma_sel),
            .i_we       (mem_we),
            .i_addr     (mem_addr[7:2]),
            .i_wdata    (mem_wdata),
            .o_rdata    (dma_rdata),
            // Memory interface
            .o_dma_req  (dma_req),
            .i_dma_ack  (dma_ack),
            .o_dma_addr (dma_addr),
            .o_dma_we   (dma_we),
            .o_dma_wdata(dma_wdata),
            .i_dma_rdata(dma_rdata_mem),
            .o_irq      (dma_irq)
        );
    end
endgenerate
```

---

## RAM ve Programming

### Wrapper RAM Entegrasyonu

```systemverilog
wrapper_ram #(
    .CPU_CLK         (CPU_CLK_P),
    .PROG_BAUD_RATE  (BAUD_RATE),
    .PROGRAM_SEQUENCE(PROGRAM_SEQUENCE_P),
    .RAM_SIZE_KB     (RAM_SIZE_KB)
) i_main_ram (
    .clk_i           (i_clk),
    .rst_ni          (i_rst_n),
    // CPU interface
    .addr_i          (ram_addr),
    .wdata_i         (ram_wdata),
    .wstrb_i         (ram_wstrb),
    .rdata_o         (ram_rdata),
    .rd_en_i         (ram_rd_en),
    // Programming interface
    .ram_prog_rx_i   (i_prog_rx),
    .system_reset_o  (prog_reset),
    .prog_mode_led_o (o_prog_mode_led)
);
```

---

## Response Multiplexer

### Read Data Selection

```systemverilog
always_comb begin
    case (1'b1)
        is_ram_region:   mem_rdata = ram_rdata;
        is_clint_region: mem_rdata = clint_rdata;
        uart_sel:        mem_rdata = uart_rdata;
        spi_sel:         mem_rdata = spi_rdata;
        i2c_sel:         mem_rdata = i2c_rdata;
        gpio_sel:        mem_rdata = gpio_rdata;
        pwm_sel:         mem_rdata = pwm_rdata;
        timer_sel:       mem_rdata = timer_rdata;
        plic_sel:        mem_rdata = plic_rdata;
        wdt_sel:         mem_rdata = wdt_rdata;
        dma_sel:         mem_rdata = dma_rdata;
        vga_sel:         mem_rdata = vga_rdata;
        default:         mem_rdata = '0;
    endcase
end
```

### Response Valid/Ready

```systemverilog
// RAM: multi-cycle
// Peripherals: single-cycle
always_ff @(posedge i_clk or negedge sys_rst_n) begin
    if (!sys_rst_n) begin
        mem_rvalid <= '0;
    end else begin
        if (is_ram_region) begin
            mem_rvalid <= ram_rvalid;
        end else begin
            mem_rvalid <= mem_valid;  // Single-cycle for peripherals
        end
    end
end
```

---

## Interrupt Routing

### IRQ Source Collection

```systemverilog
// Collect all interrupt sources for PLIC
assign irq_sources = {
    i_ext_irq,           // [31:0]  External sources
    dma_irq,             // [32]    DMA complete
    wdt_irq,             // [33]    Watchdog timeout
    timer_periph_irq,    // [34]    Timer
    i2c_irq,             // [35]    I2C
    spi_irq,             // [36]    SPI
    uart_tx_irq,         // [37]    UART TX
    uart_rx_irq          // [38]    UART RX
};
```

### CPU Interrupt Bağlantısı

```systemverilog
cpu i_cpu (
    // ...
    .timer_irq_i(timer_irq),      // CLINT timer
    .sw_irq_i   (sw_irq),         // CLINT software
    .ext_irq_i  (plic_irq),       // PLIC output
    // ...
);
```

---

## Özet

`ceres_soc` modülü:

1. **CPU Integration**: CERES RV32IMC core
2. **Memory**: 1MB wrapper RAM with programming
3. **CLINT**: mtime/mtimecmp/msip registers
4. **Peripherals**: 10 configurable peripherals
5. **Interrupts**: PLIC + CLINT interrupt routing
6. **Address Decode**: Region + peripheral select
7. **Response Mux**: Multi-source read data selection

Bu modül, tam özellikli bir SoC platformu sunar.
