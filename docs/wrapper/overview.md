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
# CERES SoC Wrapper - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Wishbone Bus Mimarisi](#wishbone-bus-mimarisi)
4. [Memory Map](#memory-map)
5. [Peripheral Entegrasyonu](#peripheral-entegrasyonu)
6. [RAM ve Burst Transfer](#ram-ve-burst-transfer)
7. [CLINT ve Interruptlar](#clint-ve-interruptlar)
8. [Programming Interface](#programming-interface)

---

## Genel Bakış

### Amaç

`ceres_wrapper` modülü, CERES RISC-V işlemcisini **Wishbone B4** bus mimarisi ile SoC'a entegre eden üst düzey wrapper'dır. CPU, bellek, CLINT ve peripherals arasındaki bağlantıları yönetir.

### Dosya Konumu

```
rtl/wrapper/ceres_wrapper.sv
```

### Bus Topolojisi

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          CERES SOC WRAPPER                                       │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌───────────┐     ┌──────────────┐     ┌──────────────────┐                   │
│   │           │     │              │     │                  │                   │
│   │    CPU    │────►│  WB Master   │────►│  WB Interconnect │                   │
│   │  (iomem)  │     │   Bridge     │     │    (1-to-N)      │                   │
│   │           │     │              │     │                  │                   │
│   └───────────┘     └──────────────┘     └────────┬─────────┘                   │
│                                                   │                              │
│                           ┌───────────────────────┼───────────────────┐         │
│                           │                       │                   │         │
│                           ▼                       ▼                   ▼         │
│                    ┌────────────┐          ┌────────────┐      ┌────────────┐   │
│                    │   RAM      │          │   CLINT    │      │   PBUS     │   │
│                    │  Slave     │          │   Slave    │      │   Slave    │   │
│                    │ (0x8xxx)   │          │ (0x3xxx)   │      │ (0x2xxx)   │   │
│                    └─────┬──────┘          └─────┬──────┘      └─────┬──────┘   │
│                          │                       │                   │          │
│                          ▼                       ▼                   ▼          │
│                    ┌────────────┐          ┌────────────┐      ┌────────────┐   │
│                    │  wrapper   │          │   mtime    │      │   UART     │   │
│                    │    RAM     │          │  mtimecmp  │      │   SPI      │   │
│                    │            │          │   msip     │      │   I2C      │   │
│                    └────────────┘          └────────────┘      └────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Parametreler

```systemverilog
module ceres_wrapper
  import ceres_param::*;
#(
    // System Configuration
    parameter int unsigned CLK_FREQ_HZ = CPU_CLK,      // 50 MHz
    parameter int unsigned BAUD_RATE   = 115200,

    // Memory Configuration
    parameter int unsigned RAM_SIZE_KB = 1024,         // 1 MB
    parameter int unsigned RAM_LATENCY = 16,           // cycles

    // Peripheral Configuration
    parameter int unsigned NUM_UART = 1,
    parameter bit          SPI_EN   = 1'b0,
    parameter bit          I2C_EN   = 1'b0,
    parameter bit          GPIO_EN  = 1'b0,
    parameter bit          PWM_EN   = 1'b0,
    parameter bit          TIMER_EN = 1'b1,
    parameter bit          PLIC_EN  = 1'b0,

    // Programming Interface
    parameter string PROG_SEQUENCE = PROGRAM_SEQUENCE
)
```

### Port Tanımları

```systemverilog
(
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    // UART Interface
    output logic uart_tx_o,
    input  logic uart_rx_i,

    // SPI Interface
    output logic       spi0_sclk_o,
    output logic       spi0_mosi_o,
    input  logic       spi0_miso_i,
    output logic [3:0] spi0_ss_o,

    // I2C Interface
    inout wire i2c0_sda_io,
    inout wire i2c0_scl_io,

    // GPIO Interface
    input  logic [31:0] gpio_i,
    output logic [31:0] gpio_o,
    output logic [31:0] gpio_oe_o,

    // External Interrupts
    input logic [7:0] ext_irq_i,

    // Programming Interface
    input  logic program_rx_i,
    output logic prog_mode_led_o,

    // Status
    output logic [3:0] status_led_o
);
```

---

## Wishbone Bus Mimarisi

### Slave Tanımları

```systemverilog
// Wishbone Slave IDs
localparam int SLV_RAM   = 0;  // 0x8000_0000
localparam int SLV_CLINT = 1;  // 0x3000_0000
localparam int SLV_PBUS  = 2;  // 0x2000_0000
localparam int WB_NUM_SLAVES_LOCAL = 3;
```

### Bus Sinyalleri

```systemverilog
// CPU → Wishbone Master Bridge
iomem_req_t cpu_mem_req;
iomem_res_t cpu_mem_res;

// Wishbone Master
wb_master_t wb_cpu_m;
wb_slave_t  wb_cpu_s;

// Wishbone Slave array
wb_master_t wb_slave_m[WB_NUM_SLAVES_LOCAL];
wb_slave_t  wb_slave_s[WB_NUM_SLAVES_LOCAL];
```

### Interconnect

```systemverilog
wb_interconnect #(
    .NUM_SLAVES(WB_NUM_SLAVES_LOCAL)
) i_wb_interconnect (
    .clk_i (clk_i),
    .rst_ni(sys_rst_n),
    .wb_m_i(wb_cpu_m),        // Master input
    .wb_s_o(wb_cpu_s),        // Master response
    .wb_m_o(wb_slave_m),      // Slave requests
    .wb_s_i(wb_slave_s)       // Slave responses
);
```

---

## Memory Map

### Adres Decode

```systemverilog
// Interconnect internal decode
// 0x8xxx_xxxx → SLV_RAM
// 0x3xxx_xxxx → SLV_CLINT
// 0x2xxx_xxxx → SLV_PBUS
```

### Peripheral Bus Decode

```systemverilog
// PBUS internal decode (addr[19:16])
assign uart_sel = (pbus_addr[19:16] == 4'h0);  // 0x2000_0xxx
assign spi_sel  = (pbus_addr[19:16] == 4'h1);  // 0x2001_0xxx
assign i2c_sel  = (pbus_addr[19:16] == 4'h2);  // 0x2002_0xxx
```

---

## Peripheral Entegrasyonu

### UART

```systemverilog
uart i_uart (
    .clk_i     (clk_i),
    .rst_ni    (sys_rst_n),
    .stb_i     (pbus_valid && uart_sel),
    .adr_i     (pbus_addr[3:2]),
    .byte_sel_i(pbus_wstrb),
    .we_i      (pbus_we),
    .dat_i     (pbus_wdata),
    .dat_o     (uart_rdata),
    .uart_rx_i (uart_rx_i),
    .uart_tx_o (uart_tx_o)
);
```

### SPI Master

```systemverilog
spi_master i_spi (
    .clk_i     (clk_i),
    .rst_ni    (sys_rst_n),
    .stb_i     (pbus_valid && spi_sel),
    .adr_i     (pbus_addr[3:2]),
    .byte_sel_i(pbus_wstrb),
    .we_i      (pbus_we),
    .dat_i     (pbus_wdata),
    .dat_o     (spi_rdata),
    .spi_sck_o (spi0_sclk_o),
    .spi_mosi_o(spi0_mosi_o),
    .spi_miso_i(spi0_miso_i),
    .spi_cs_n_o(spi0_ss_o[0])
);
```

### I2C Master

```systemverilog
i2c_master i_i2c (
    .clk_i       (clk_i),
    .rst_ni      (sys_rst_n),
    .stb_i       (pbus_valid && i2c_sel),
    .adr_i       (pbus_addr[4:2]),
    .byte_sel_i  (pbus_wstrb),
    .we_i        (pbus_we),
    .dat_i       (pbus_wdata),
    .dat_o       (i2c_rdata),
    .i2c_scl_o   (i2c_scl_o),
    .i2c_scl_oe_o(i2c_scl_oe),
    .i2c_scl_i   (i2c_scl_i),
    .i2c_sda_o   (i2c_sda_o),
    .i2c_sda_oe_o(i2c_sda_oe),
    .i2c_sda_i   (i2c_sda_i),
    .irq_o       (i2c_irq)
);
```

---

## RAM ve Burst Transfer

### Burst State Machine

RAM modülü cache line burst transfer'ı destekler:

```systemverilog
// Burst detection
wire ram_is_burst = (wb_slave_m[SLV_RAM].cti == WB_CTI_INCR) ||
                    (wb_slave_m[SLV_RAM].cti == WB_CTI_EOB);
wire ram_is_burst_start = ram_wb_req && !ram_wb_we &&
                          (wb_slave_m[SLV_RAM].cti == WB_CTI_INCR) &&
                          !ram_burst_active;
wire ram_is_burst_end = ram_burst_active &&
                        (wb_slave_m[SLV_RAM].cti == WB_CTI_EOB);
```

### Burst Data Capture

```systemverilog
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        ram_burst_data_valid <= 1'b0;
    end else begin
        // First beat: RAM latency sonrası veriyi yakala
        if (ram_delay_q[RAM_LATENCY-1] && !ram_burst_data_valid) begin
            ram_burst_data_q     <= ram_rdata;  // Full cache line
            ram_burst_data_valid <= 1'b1;
            ram_burst_active     <= ram_is_burst;
            ram_burst_cnt        <= '0;
        end
        // Subsequent beats: immediate ACK
        else if (ram_burst_active && ram_wb_req && ram_burst_data_valid) begin
            ram_burst_cnt <= ram_burst_cnt + 1;
            if (ram_is_burst_end) begin
                ram_burst_active     <= 1'b0;
                ram_burst_data_valid <= 1'b0;
            end
        end
    end
end
```

### Word Extraction

```systemverilog
// Cache line'dan doğru word'ü çıkar
always_comb begin
    logic [1:0] word_offset;
    word_offset  = ram_wb_addr[3:2];  // 16-byte line içinde word seçimi
    if (ram_burst_data_valid) begin
        ram_wb_rdata = ram_burst_data_q[word_offset*32+:32];
    end else begin
        ram_wb_rdata = ram_rdata[word_offset*32+:32];
    end
end
```

---

## CLINT ve Interruptlar

### CLINT Slave

```systemverilog
wb_clint_slave i_wb_clint (
    .clk_i      (clk_i),
    .rst_ni     (sys_rst_n),
    .wb_m_i     (wb_slave_m[SLV_CLINT]),
    .wb_s_o     (wb_slave_s[SLV_CLINT]),
    .timer_irq_o(timer_irq),
    .sw_irq_o   (sw_irq)
);
```

### CPU Interrupt Bağlantısı

```systemverilog
cpu i_soc (
    .clk_i      (clk_i),
    .rst_ni     (sys_rst_n),
    .timer_irq_i(timer_irq),    // CLINT timer
    .sw_irq_i   (sw_irq),       // CLINT software
    .ext_irq_i  (|ext_irq_i),   // External
    .iomem_req_o(cpu_mem_req),
    .iomem_res_i(cpu_mem_res)
);
```

---

## Programming Interface

### Reset Yönetimi

```systemverilog
// Verilator'da program reset bypass
`ifdef VERILATOR
    assign sys_rst_n = rst_ni;
`else
    assign sys_rst_n = rst_ni & prog_reset;
`endif
```

### RAM Programmer

```systemverilog
wrapper_ram #(
    .CPU_CLK         (CLK_FREQ_HZ),
    .PROG_BAUD_RATE  (BAUD_RATE),
    .PROGRAM_SEQUENCE(PROG_SEQUENCE)
) i_main_ram (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .addr_i         (ram_addr),
    .wdata_i        (ram_wdata_expanded),
    .wstrb_i        (ram_wstrb),
    .rdata_o        (ram_rdata),
    .rd_en_i        (ram_rd_en),
    .ram_prog_rx_i  (program_rx_i),
    .system_reset_o (prog_reset),
    .prog_mode_led_o(prog_mode_led_o)
);
```

---

## Özet

`ceres_wrapper` modülü:

1. **Wishbone B4 Bus**: CPU ↔ peripherals iletişimi
2. **3 Slave**: RAM, CLINT, PBUS
3. **Burst Support**: Cache line transfer
4. **Peripherals**: UART, SPI, I2C
5. **Interrupts**: Timer, SW, External
6. **Programming**: UART üzerinden RAM programlama

Bu modül, CERES SoC'un ana entegrasyon noktasıdır.
# RAM Programmer - UART-Based RAM Programming Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Programlama Protokolü](#programlama-protokolü)
4. [FSM Detayları](#fsm-detayları)
5. [UART Alıcı](#uart-alıcı)
6. [RAM Yazma](#ram-yazma)
7. [Reset Yönetimi](#reset-yönetimi)

---

## Genel Bakış

### Amaç

`ram_programmer` modülü, **UART üzerinden RAM programlama** işlevselliği sağlar. Magic sequence algıladığında sistemi resetler, program verilerini alır ve RAM'e yazar.

### Dosya Konumu

```
rtl/wrapper/ram_programmer.sv
```

### Programlama Akışı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                        RAM PROGRAMMING FLOW                                      │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────┐    ┌──────────────┐    ┌────────────┐    ┌─────────────┐         │
│   │  IDLE   │───►│ SEQ_RECEIVE  │───►│ LEN_RECEIVE│───►│   PROGRAM   │         │
│   │         │    │              │    │            │    │             │         │
│   └─────────┘    │ "CERESTEST"  │    │ Word Count │    │ Data Words  │         │
│       ▲          └──────────────┘    └────────────┘    └──────┬──────┘         │
│       │                                                       │                 │
│       │          ┌──────────────────────────────────────────┐ │                 │
│       └──────────│              FINISH                      │◄┘                 │
│                  │  Release Reset, Return to IDLE           │                   │
│                  └──────────────────────────────────────────┘                   │
│                                                                                  │
│   UART RX ──────►[FSM]──────► RAM Write ──────► System Reset                   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Parametreler

```systemverilog
module ram_programmer
  import ceres_param::*;
#(
    parameter int CPU_CLK          = 50_000_000,       // Clock frequency
    parameter int PROG_BAUD_RATE   = 115200,           // UART baud rate
    parameter string PROGRAM_SEQUENCE = "CERESTEST"   // 9-char magic sequence
)
```

### Port Tanımları

```systemverilog
(
    input  logic        i_clk,
    input  logic        i_rst_n,

    // UART RX Interface
    input  logic        i_uart_rx,

    // RAM Write Interface
    output logic        o_ram_we,           // RAM write enable
    output logic [31:0] o_ram_addr,         // RAM write address
    output logic [31:0] o_ram_wdata,        // RAM write data

    // System Control
    output logic        o_system_reset,     // Active-low system reset
    output logic        o_prog_mode_led     // Programming mode indicator
);
```

---

## Programlama Protokolü

### Protocol Format

```
┌────────────────────────────────────────────────────────────────────────────┐
│                      PROGRAMMING PROTOCOL                                   │
├────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────┐  ┌───────────────┐  ┌─────────────────────────────────┐  │
│   │ Magic Seq   │  │ Word Count    │  │ Data Words                      │  │
│   │ 9 bytes     │  │ 4 bytes (LE)  │  │ N × 4 bytes (LE)                │  │
│   │ "CERESTEST" │  │ N             │  │ word[0], word[1], ... word[N-1] │  │
│   └─────────────┘  └───────────────┘  └─────────────────────────────────┘  │
│                                                                             │
│   Total bytes = 9 + 4 + (N × 4)                                            │
│                                                                             │
├────────────────────────────────────────────────────────────────────────────┤
│ Example: 256 words (1KB program)                                            │
│                                                                             │
│   "CERESTEST" + 0x00000100 (LE) + 256 × 32-bit words                       │
│   = 9 + 4 + 1024 = 1037 bytes total                                        │
│                                                                             │
└────────────────────────────────────────────────────────────────────────────┘
```

### Little-Endian Format

```systemverilog
// Word Count: N = 0x00001234
// UART byte order: 0x34, 0x12, 0x00, 0x00

// Data Word: 0xDEADBEEF
// UART byte order: 0xEF, 0xBE, 0xAD, 0xDE
```

---

## FSM Detayları

### State Enum

```systemverilog
typedef enum logic [2:0] {
    IDLE,           // Normal operation, monitoring for magic sequence
    SEQ_RECEIVE,    // Receiving magic sequence
    LEN_RECEIVE,    // Receiving word count (4 bytes)
    PROGRAM,        // Receiving and writing data words
    FINISH          // Complete, releasing reset
} prog_state_e;

prog_state_e state_q, state_d;
```

### State Machine

```systemverilog
always_comb begin
    state_d = state_q;

    case (state_q)
        IDLE: begin
            // First byte of magic sequence detected
            if (rx_valid && rx_data == PROGRAM_SEQUENCE[0]) begin
                state_d = SEQ_RECEIVE;
            end
        end

        SEQ_RECEIVE: begin
            if (rx_valid) begin
                if (seq_idx == SEQ_LEN - 1) begin
                    // Full sequence matched
                    state_d = LEN_RECEIVE;
                end else if (rx_data != PROGRAM_SEQUENCE[seq_idx]) begin
                    // Mismatch - abort
                    state_d = IDLE;
                end
            end
        end

        LEN_RECEIVE: begin
            if (rx_valid && byte_idx == 3) begin
                // 4 bytes received
                state_d = PROGRAM;
            end
        end

        PROGRAM: begin
            if (word_cnt == 0) begin
                // All words received
                state_d = FINISH;
            end
        end

        FINISH: begin
            // Wait a few cycles, then return to IDLE
            if (finish_cnt == FINISH_DELAY) begin
                state_d = IDLE;
            end
        end
    endcase
end
```

### State Diagram

```
           rx_valid &&
          rx == SEQ[0]
    ┌─────────────────────►┌─────────────┐
    │                      │ SEQ_RECEIVE │
┌───┴───┐                  │             │
│       │◄─────────────────┤ mismatch    │
│ IDLE  │                  └──────┬──────┘
│       │                         │ seq_complete
└───────┘                         ▼
    ▲                      ┌─────────────┐
    │                      │ LEN_RECEIVE │
    │                      │             │
    │                      └──────┬──────┘
    │                             │ 4 bytes received
    │                             ▼
    │                      ┌─────────────┐
    │                      │   PROGRAM   │
    │                      │             │
    │                      └──────┬──────┘
    │                             │ word_cnt == 0
    │                             ▼
    │  finish_delay        ┌─────────────┐
    └──────────────────────┤   FINISH    │
                           │             │
                           └─────────────┘
```

---

## UART Alıcı

### Baud Rate Generator

```systemverilog
localparam int CLKS_PER_BIT = CPU_CLK / PROG_BAUD_RATE;

logic [15:0] baud_cnt;
logic        baud_tick;

always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        baud_cnt  <= '0;
        baud_tick <= 1'b0;
    end else if (rx_active) begin
        if (baud_cnt == CLKS_PER_BIT - 1) begin
            baud_cnt  <= '0;
            baud_tick <= 1'b1;
        end else begin
            baud_cnt  <= baud_cnt + 1;
            baud_tick <= 1'b0;
        end
    end else begin
        baud_cnt <= CLKS_PER_BIT / 2;  // Sample at bit center
    end
end
```

### UART Receive FSM

```systemverilog
typedef enum logic [1:0] {
    RX_IDLE,
    RX_START,
    RX_DATA,
    RX_STOP
} rx_state_e;

rx_state_e rx_state;
logic [2:0] bit_idx;
logic [7:0] rx_shift;

always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        rx_state <= RX_IDLE;
        rx_valid <= 1'b0;
    end else begin
        rx_valid <= 1'b0;

        case (rx_state)
            RX_IDLE: begin
                if (!i_uart_rx) begin  // Start bit detected
                    rx_state <= RX_START;
                end
            end

            RX_START: begin
                if (baud_tick) begin
                    if (!i_uart_rx) begin  // Confirm start bit
                        rx_state <= RX_DATA;
                        bit_idx  <= '0;
                    end else begin
                        rx_state <= RX_IDLE;  // False start
                    end
                end
            end

            RX_DATA: begin
                if (baud_tick) begin
                    rx_shift <= {i_uart_rx, rx_shift[7:1]};  // LSB first
                    if (bit_idx == 7) begin
                        rx_state <= RX_STOP;
                    end else begin
                        bit_idx <= bit_idx + 1;
                    end
                end
            end

            RX_STOP: begin
                if (baud_tick) begin
                    if (i_uart_rx) begin  // Valid stop bit
                        rx_data  <= rx_shift;
                        rx_valid <= 1'b1;
                    end
                    rx_state <= RX_IDLE;
                end
            end
        endcase
    end
end
```

---

## RAM Yazma

### Address Counter

```systemverilog
// Reset vector aligned address
localparam logic [31:0] RAM_BASE = 32'h8000_0000;

logic [31:0] write_addr;

always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        write_addr <= RAM_BASE;
    end else if (state_q == LEN_RECEIVE && state_d == PROGRAM) begin
        // Reset address at start of programming
        write_addr <= RAM_BASE;
    end else if (word_write_en) begin
        // Increment by 4 (word-aligned)
        write_addr <= write_addr + 4;
    end
end
```

### Word Assembly

```systemverilog
logic [31:0] word_buffer;
logic [1:0]  byte_idx;
logic        word_complete;

always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        byte_idx <= '0;
    end else if (state_q == PROGRAM && rx_valid) begin
        // Little-endian assembly
        case (byte_idx)
            2'b00: word_buffer[7:0]   <= rx_data;
            2'b01: word_buffer[15:8]  <= rx_data;
            2'b10: word_buffer[23:16] <= rx_data;
            2'b11: word_buffer[31:24] <= rx_data;
        endcase
        byte_idx <= byte_idx + 1;
    end
end

assign word_complete = (byte_idx == 2'b11) && rx_valid;
```

### RAM Write Generation

```systemverilog
always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        o_ram_we    <= 1'b0;
        o_ram_addr  <= '0;
        o_ram_wdata <= '0;
    end else begin
        o_ram_we <= 1'b0;

        if (word_complete) begin
            o_ram_we    <= 1'b1;
            o_ram_addr  <= write_addr;
            o_ram_wdata <= {rx_data, word_buffer[23:0]};  // Complete word
        end
    end
end
```

---

## Reset Yönetimi

### System Reset Control

```systemverilog
// Hold CPU in reset during programming
always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        o_system_reset <= 1'b1;  // Active (CPU running)
    end else begin
        case (state_q)
            IDLE: begin
                o_system_reset <= 1'b1;  // Normal operation
            end

            SEQ_RECEIVE, LEN_RECEIVE, PROGRAM: begin
                o_system_reset <= 1'b0;  // Hold CPU in reset
            end

            FINISH: begin
                // Release reset with delay
                if (finish_cnt >= FINISH_DELAY) begin
                    o_system_reset <= 1'b1;
                end
            end
        endcase
    end
end
```

### Programming Mode LED

```systemverilog
// LED indicator during programming
assign o_prog_mode_led = (state_q != IDLE);
```

---

## Timing Diyagramı

### Başarılı Programlama

```
                Magic Seq           Len        Data Words
              ┌───────────┐      ┌─────┐    ┌───────────────────┐
i_uart_rx ────┤CERESTEST  ├──────┤ N   ├────┤ W0  W1  W2 ... Wn ├────────
              └───────────┘      └─────┘    └───────────────────┘

state     ────┬───┬──────────────┬─────────┬────────────────────┬───┬────
          IDLE│SEQ│  SEQ_RECV    │LEN_RECV │     PROGRAM        │FIN│IDLE

o_system_reset ────────┐                                         ┌───────
                       └─────────────────────────────────────────┘

o_prog_mode_led        ┌─────────────────────────────────────────┐
              ─────────┘                                         └───────

o_ram_we                                     ┌─┐ ┌─┐ ┌─┐     ┌─┐
              ───────────────────────────────┘ └─┘ └─┘ └─...─┘ └─────────
```

---

## Kullanım Örneği

### Python Programming Script

```python
#!/usr/bin/env python3
import serial
import struct

MAGIC_SEQUENCE = b"CERESTEST"

def program_ram(port, binary_file, baud=115200):
    """Program CERES RAM via UART"""
    with open(binary_file, 'rb') as f:
        data = f.read()

    # Pad to word alignment
    while len(data) % 4 != 0:
        data += b'\x00'

    word_count = len(data) // 4

    with serial.Serial(port, baud, timeout=5) as ser:
        # Send magic sequence
        ser.write(MAGIC_SEQUENCE)

        # Send word count (little-endian)
        ser.write(struct.pack('<I', word_count))

        # Send data
        ser.write(data)

        print(f"Programmed {word_count} words ({len(data)} bytes)")

if __name__ == "__main__":
    import sys
    program_ram(sys.argv[1], sys.argv[2])
```

---

## Özet

`ram_programmer` modülü:

1. **Magic Sequence**: "CERESTEST" detection
2. **Protocol**: Sequence → Word Count → Data
3. **FSM**: 5-state programming controller
4. **UART**: Built-in 8N1 receiver
5. **RAM Write**: Word-aligned, little-endian
6. **Reset**: CPU held during programming

Bu modül, FPGA üzerinde boot programının yüklenmesini sağlar.
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
# Wishbone Peripheral Bus Slave - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Bus Bridge Mantığı](#bus-bridge-mantığı)
4. [Timing Karakteristikleri](#timing-karakteristikleri)

---

## Genel Bakış

### Amaç

`wb_pbus_slave` modülü, Wishbone bus'tan peripheral modüllere köprü görevi görür. Adres ve kontrol sinyallerini basit memory-mapped arayüze çevirir.

### Dosya Konumu

```
rtl/wrapper/wb_pbus_slave.sv
```

### Bridge Topolojisi

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          WB_PBUS_SLAVE                                           │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│    Wishbone Interface                         Peripheral Interface              │
│                                                                                  │
│    ┌────────────────┐                        ┌────────────────────┐             │
│    │  wb_m_i.cyc    │──────────────────────► │ pbus_valid_o       │             │
│    │  wb_m_i.stb    │                        │                    │             │
│    ├────────────────┤                        ├────────────────────┤             │
│    │  wb_m_i.we     │──────────────────────► │ pbus_we_o          │             │
│    ├────────────────┤                        ├────────────────────┤             │
│    │  wb_m_i.adr    │──────────────────────► │ pbus_addr_o        │             │
│    ├────────────────┤                        ├────────────────────┤             │
│    │  wb_m_i.dat    │──────────────────────► │ pbus_wdata_o       │             │
│    ├────────────────┤                        ├────────────────────┤             │
│    │  wb_m_i.sel    │──────────────────────► │ pbus_wstrb_o       │             │
│    └────────────────┘                        └────────────────────┘             │
│                                                                                  │
│    ┌────────────────┐                        ┌────────────────────┐             │
│    │  wb_s_o.ack    │◄─────────(reg)─────────│ pbus_ready_i       │             │
│    ├────────────────┤                        ├────────────────────┤             │
│    │  wb_s_o.dat    │◄──────────────────────│ pbus_rdata_i       │             │
│    ├────────────────┤                        └────────────────────┘             │
│    │  wb_s_o.err    │◄─────────(0)                                              │
│    └────────────────┘                                                           │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module wb_pbus_slave
  import ceres_param::*;
(
    input  logic clk_i,
    input  logic rst_ni,

    // Wishbone Slave Interface
    input  wb_master_t wb_m_i,    // Master request
    output wb_slave_t  wb_s_o,    // Slave response

    // Peripheral Bus Interface
    output logic        pbus_valid_o,   // Request valid
    output logic        pbus_we_o,      // Write enable
    output logic [31:0] pbus_addr_o,    // Address
    output logic [31:0] pbus_wdata_o,   // Write data
    output logic [3:0]  pbus_wstrb_o,   // Write strobe
    input  logic [31:0] pbus_rdata_i,   // Read data
    input  logic        pbus_ready_i    // Ready/Ack
);
```

---

## Bus Bridge Mantığı

### Request Passthrough

```systemverilog
// Wishbone request → Peripheral bus
wire wb_req = wb_m_i.cyc && wb_m_i.stb;

assign pbus_valid_o = wb_req;
assign pbus_we_o    = wb_m_i.we;
assign pbus_addr_o  = wb_m_i.adr;
assign pbus_wdata_o = wb_m_i.dat;
assign pbus_wstrb_o = wb_m_i.sel;
```

### Response Handling

```systemverilog
// Single-cycle ack (registered)
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        wb_s_o.ack <= 1'b0;
        wb_s_o.dat <= '0;
    end else begin
        wb_s_o.ack <= wb_req && pbus_ready_i;
        wb_s_o.dat <= pbus_rdata_i;
    end
end

assign wb_s_o.err = 1'b0;
assign wb_s_o.rty = 1'b0;
```

### Alternative: Combinational Ack

```systemverilog
// Eğer peripheral single-cycle ise
assign wb_s_o.ack = wb_req;  // Immediate ack
assign wb_s_o.dat = pbus_rdata_i;
assign wb_s_o.err = 1'b0;
assign wb_s_o.rty = 1'b0;
```

---

## Timing Karakteristikleri

### Single-Cycle Access

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └───

wb_m_i.cyc     ┌───────────┐
           ────┘           └───────

wb_m_i.stb     ┌───────────┐
           ────┘           └───────

pbus_valid_o   ┌───────────┐
           ────┘           └───────

pbus_rdata_i ──┤   DATA    ├───────

wb_s_o.ack         ┌───────┐
           ────────┘       └───────

wb_s_o.dat     ────┤  DATA ├───────
```

### Write Operation

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └───

wb_m_i.cyc     ┌───────────┐
           ────┘           └───────

wb_m_i.stb     ┌───────────┐
           ────┘           └───────

wb_m_i.we      ┌───────────┐
           ────┘           └───────

pbus_valid_o   ┌───────────┐
           ────┘           └───────

pbus_we_o      ┌───────────┐
           ────┘           └───────

pbus_wdata_o ──┤  WDATA   ├───────

wb_s_o.ack         ┌───────┐
           ────────┘       └───────
```

---

## Byte Enable Mapping

### Write Strobe

```systemverilog
// Wishbone sel → Peripheral wstrb
// sel[0] = byte 0 (bits 7:0)
// sel[1] = byte 1 (bits 15:8)
// sel[2] = byte 2 (bits 23:16)
// sel[3] = byte 3 (bits 31:24)

// Word write: sel = 4'b1111
// Halfword write (lower): sel = 4'b0011
// Halfword write (upper): sel = 4'b1100
// Byte write: sel = 4'b0001, 4'b0010, 4'b0100, 4'b1000
```

---

## Kullanım Örneği

### SoC Integration

```systemverilog
// Wishbone interconnect → PBUS slave → Peripherals

wb_pbus_slave i_pbus (
    .clk_i       (clk),
    .rst_ni      (rst_n),
    .wb_m_i      (wb_slave_m[SLV_PBUS]),
    .wb_s_o      (wb_slave_s[SLV_PBUS]),
    .pbus_valid_o(pbus_valid),
    .pbus_we_o   (pbus_we),
    .pbus_addr_o (pbus_addr),
    .pbus_wdata_o(pbus_wdata),
    .pbus_wstrb_o(pbus_wstrb),
    .pbus_rdata_i(pbus_rdata),
    .pbus_ready_i(1'b1)  // Single-cycle peripherals
);

// Peripheral address decode
wire uart_sel = (pbus_addr[15:12] == 4'h0);
wire gpio_sel = (pbus_addr[15:12] == 4'h4);

// Read mux
always_comb begin
    case (1'b1)
        uart_sel: pbus_rdata = uart_rdata;
        gpio_sel: pbus_rdata = gpio_rdata;
        default:  pbus_rdata = '0;
    endcase
end
```

---

## Özet

`wb_pbus_slave` modülü:

1. **Transparent Bridge**: Wishbone → Simple peripheral interface
2. **Single-Cycle**: Minimum latency passthrough
3. **Byte Enable**: Full sel/wstrb support
4. **Simple Protocol**: Valid/ready handshake

Bu modül, Wishbone bus'u basit memory-mapped peripherals'a bağlar.
# Wishbone RAM Slave - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Latency Pipeline](#latency-pipeline)
4. [Byte Enable Yazma](#byte-enable-yazma)
5. [Burst Desteği](#burst-desteği)

---

## Genel Bakış

### Amaç

`wb_ram_slave` modülü, Wishbone bus'tan RAM modülüne arayüz sağlar. Konfigüre edilebilir gecikme (latency) ve byte-granular yazma işlemlerini destekler.

### Dosya Konumu

```
rtl/wrapper/wb_ram_slave.sv
```

### RAM Slave Mimarisi

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          WB_RAM_SLAVE                                            │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│    Wishbone Interface              Latency Pipeline         RAM Interface       │
│                                                                                  │
│    ┌────────────┐               ┌─────────────────┐      ┌────────────────┐    │
│    │  cyc/stb   │──────────────►│                 │      │                │    │
│    │  we        │               │   Delay Shift   │─────►│   ram_we_o     │    │
│    │  addr      │──────────────►│   Register      │─────►│   ram_addr_o   │    │
│    │  wdata     │──────────────►│   (LATENCY)     │─────►│   ram_wdata_o  │    │
│    │  sel       │──────────────►│                 │─────►│   ram_wstrb_o  │    │
│    └────────────┘               └────────┬────────┘      └───────┬────────┘    │
│                                          │                       │             │
│    ┌────────────┐                        │                       │             │
│    │  ack       │◄───────────────────────┘                       │             │
│    │  rdata     │◄───────────────────────────────────────────────┘             │
│    │  err       │◄─── (1'b0)             │   ram_rdata_i                       │
│    └────────────┘                        │                                     │
│                                          │                                     │
│                     Latency: LATENCY cycles from req to ack                    │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Parametreler

```systemverilog
module wb_ram_slave
  import ceres_param::*;
#(
    parameter int LATENCY = 1  // RAM access latency (cycles)
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

    // RAM Interface
    output logic        ram_we_o,     // Write enable
    output logic [31:0] ram_addr_o,   // Address
    output logic [31:0] ram_wdata_o,  // Write data
    output logic [3:0]  ram_wstrb_o,  // Byte strobes
    input  logic [31:0] ram_rdata_i   // Read data
);
```

---

## Latency Pipeline

### Delay Shift Register

```systemverilog
// Request tracking için shift register
logic [LATENCY-1:0] req_delay_q;
logic [LATENCY-1:0] we_delay_q;

wire wb_req = wb_m_i.cyc && wb_m_i.stb;

always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        req_delay_q <= '0;
        we_delay_q  <= '0;
    end else begin
        // Shift request through pipeline
        req_delay_q <= {req_delay_q[LATENCY-2:0], wb_req};
        we_delay_q  <= {we_delay_q[LATENCY-2:0], wb_req && wb_m_i.we};
    end
end
```

### ACK Generation

```systemverilog
// ACK arrives LATENCY cycles after request
assign wb_s_o.ack = req_delay_q[LATENCY-1];
```

### Timing Diyagramı (LATENCY=2)

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └───

wb_req         ┌───────┐
           ────┘       └───────────────────

req_delay[0]       ┌───────┐
           ────────┘       └───────────────

req_delay[1]           ┌───────┐
(= ack)    ────────────┘       └───────────

           ├─T0─┼─T1─┼─T2─┤
           req  delay ack
```

---

## Byte Enable Yazma

### Write Strobe Handling

```systemverilog
// Direct passthrough of byte enables
assign ram_we_o    = wb_req && wb_m_i.we;
assign ram_addr_o  = wb_m_i.adr;
assign ram_wdata_o = wb_m_i.dat;
assign ram_wstrb_o = wb_m_i.sel;
```

### RAM Implementation Requirements

```systemverilog
// RAM modülü byte-enable desteklemeli:
always_ff @(posedge clk) begin
    if (we) begin
        if (wstrb[0]) mem[addr][7:0]   <= wdata[7:0];
        if (wstrb[1]) mem[addr][15:8]  <= wdata[15:8];
        if (wstrb[2]) mem[addr][23:16] <= wdata[23:16];
        if (wstrb[3]) mem[addr][31:24] <= wdata[31:24];
    end
end
```

### Store Instructions Mapping

| Instruction | sel | Bytes Written |
|-------------|-----|---------------|
| SW | 4'b1111 | All 4 bytes |
| SH (addr[1:0]=0) | 4'b0011 | Bytes 0,1 |
| SH (addr[1:0]=2) | 4'b1100 | Bytes 2,3 |
| SB (addr[1:0]=0) | 4'b0001 | Byte 0 |
| SB (addr[1:0]=1) | 4'b0010 | Byte 1 |
| SB (addr[1:0]=2) | 4'b0100 | Byte 2 |
| SB (addr[1:0]=3) | 4'b1000 | Byte 3 |

---

## Burst Desteği

### Burst Detection

```systemverilog
wire is_burst = (wb_m_i.cti == WB_CTI_INCR) ||
                (wb_m_i.cti == WB_CTI_EOB);
wire is_burst_end = (wb_m_i.cti == WB_CTI_EOB);
```

### Burst State Machine

```systemverilog
logic burst_active;
logic [1:0] burst_cnt;

always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        burst_active <= 1'b0;
        burst_cnt    <= '0;
    end else begin
        if (wb_req && !burst_active && (wb_m_i.cti == WB_CTI_INCR)) begin
            // Start of burst
            burst_active <= 1'b1;
            burst_cnt    <= '0;
        end else if (burst_active && wb_req) begin
            burst_cnt <= burst_cnt + 1;
            if (is_burst_end) begin
                burst_active <= 1'b0;
            end
        end
    end
end
```

### Burst Timing (4-beat)

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └───

wb_m_i.cyc     ┌───────────────────────────┐
           ────┘                           └───

wb_m_i.stb     ┌───┐   ┌───┐   ┌───┐   ┌───┐
           ────┘   └───┘   └───┘   └───┘   └───

wb_m_i.cti ────┤INCR├───┤INCR├───┤INCR├───┤EOB├───

wb_m_i.adr ────┤ A0 ├───┤ A1 ├───┤ A2 ├───┤ A3 ├───

wb_s_o.ack         ┌───┐   ┌───┐   ┌───┐   ┌───┐
           ────────┘   └───┘   └───┘   └───┘   └───

wb_s_o.dat     ────┤ D0├───┤ D1├───┤ D2├───┤ D3├───
```

---

## Response Sinyalleri

```systemverilog
// Read data from RAM (combinational or pipelined)
assign wb_s_o.dat = ram_rdata_i;

// No error or retry
assign wb_s_o.err = 1'b0;
assign wb_s_o.rty = 1'b0;
```

---

## Konfigürasyon Örnekleri

### Single-Cycle RAM

```systemverilog
wb_ram_slave #(
    .LATENCY(1)
) i_ram_slave (
    .clk_i     (clk),
    .rst_ni    (rst_n),
    .wb_m_i    (wb_m),
    .wb_s_o    (wb_s),
    .ram_we_o  (ram_we),
    .ram_addr_o(ram_addr),
    .ram_wdata_o(ram_wdata),
    .ram_wstrb_o(ram_wstrb),
    .ram_rdata_i(ram_rdata)
);
```

### Multi-Cycle RAM (External Memory)

```systemverilog
wb_ram_slave #(
    .LATENCY(16)  // Slow external memory
) i_ext_ram_slave (
    .clk_i     (clk),
    .rst_ni    (rst_n),
    .wb_m_i    (wb_m),
    .wb_s_o    (wb_s),
    .ram_we_o  (ram_we),
    .ram_addr_o(ram_addr),
    .ram_wdata_o(ram_wdata),
    .ram_wstrb_o(ram_wstrb),
    .ram_rdata_i(ram_rdata)
);
```

---

## Özet

`wb_ram_slave` modülü:

1. **Configurable Latency**: LATENCY parametresi
2. **Byte Enable**: Full sel/wstrb support
3. **Burst Support**: CTI/BTE handling
4. **Simple Interface**: Direct RAM connection

Bu modül, Wishbone bus'u RAM modüllerine bağlar.
# Wrapper RAM - Cache Line Burst Destekli RAM Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Bellek Organizasyonu](#bellek-organizasyonu)
4. [Cache Line Okuma](#cache-line-okuma)
5. [Byte-Granular Yazma](#byte-granular-yazma)
6. [Programming Interface](#programming-interface)

---

## Genel Bakış

### Amaç

`wrapper_ram` modülü, **128-bit cache line** okuma ve **byte-granular yazma** destekleyen RAM modülüdür. Ayrıca UART üzerinden programlama arayüzü içerir.

### Dosya Konumu

```
rtl/wrapper/wrapper_ram.sv
```

### RAM Blok Diyagramı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                            WRAPPER_RAM                                           │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│    ┌──────────────────────────────────────────────────────────────────────────┐ │
│    │                         RAM ARRAY                                         │ │
│    │                                                                           │ │
│    │   ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐                        │ │
│    │   │ Bank 0  │ │ Bank 1  │ │ Bank 2  │ │ Bank 3  │  ← 32-bit banks       │ │
│    │   │(word 0) │ │(word 1) │ │(word 2) │ │(word 3) │                        │ │
│    │   └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘                        │ │
│    │        │           │           │           │                              │ │
│    │        └─────┬─────┴─────┬─────┴─────┬─────┘                              │ │
│    │              │           │           │                                    │ │
│    │              ▼           ▼           ▼                                    │ │
│    │        ┌─────────────────────────────────┐                                │ │
│    │        │   128-bit Cache Line Output     │                                │ │
│    │        │   rdata_o[127:0]                │                                │ │
│    │        └─────────────────────────────────┘                                │ │
│    │                                                                           │ │
│    └──────────────────────────────────────────────────────────────────────────┘ │
│                                                                                  │
│    ┌──────────────┐        ┌──────────────────┐                                 │
│    │  CPU Port    │        │  Programming     │                                 │
│    │  (RW)        │        │  Port (UART)     │                                 │
│    └──────────────┘        └──────────────────┘                                 │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Parametreler

```systemverilog
module wrapper_ram
  import ceres_param::*;
#(
    parameter int CPU_CLK          = 50_000_000,
    parameter int PROG_BAUD_RATE   = 115200,
    parameter string PROGRAM_SEQUENCE = "CERESTEST",
    parameter int RAM_SIZE_KB      = 1024,         // 1 MB default
    parameter int RAM_INIT_FILE    = ""            // Optional hex init
)
```

### Port Tanımları

```systemverilog
(
    input  logic         clk_i,
    input  logic         rst_ni,

    // CPU Memory Interface
    input  logic [31:0]  addr_i,        // Word address
    input  logic [31:0]  wdata_i,       // Write data (32-bit)
    input  logic [3:0]   wstrb_i,       // Byte strobes
    output logic [127:0] rdata_o,       // Read data (128-bit cache line)
    input  logic         rd_en_i,       // Read enable

    // Programming Interface
    input  logic         ram_prog_rx_i, // UART RX for programming
    output logic         system_reset_o,// System reset during programming
    output logic         prog_mode_led_o// Programming mode LED
);
```

---

## Bellek Organizasyonu

### Bank Yapısı

```systemverilog
// 4 x 32-bit banks = 128-bit cache line
localparam int WORDS_PER_LINE = 4;
localparam int RAM_DEPTH = (RAM_SIZE_KB * 1024) / (WORDS_PER_LINE * 4);

// Bank memories
logic [31:0] bank0 [RAM_DEPTH];
logic [31:0] bank1 [RAM_DEPTH];
logic [31:0] bank2 [RAM_DEPTH];
logic [31:0] bank3 [RAM_DEPTH];
```

### Address Mapping

```
┌─────────────────────────────────────────────────────────────────────┐
│                        ADDRESS MAPPING                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   Input Address: addr_i[31:0]                                       │
│                                                                      │
│   ┌──────────────────────────────────────────────────────────────┐  │
│   │31                                        4│3    2│1    0│    │  │
│   │             Line Index                    │ Bank │Unused│    │  │
│   │               (RAM_DEPTH)                 │Select│      │    │  │
│   └──────────────────────────────────────────────────────────────┘  │
│                                                                      │
│   Line Index = addr_i[31:4]   (128-bit line selection)              │
│   Bank Select = addr_i[3:2]   (Word within line: 0,1,2,3)           │
│   Byte Offset = addr_i[1:0]   (Byte within word - ignored)          │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

### Address Decode

```systemverilog
wire [27:0] line_index = addr_i[31:4];
wire [1:0]  word_sel   = addr_i[3:2];
```

---

## Cache Line Okuma

### 128-bit Read

```systemverilog
// Read entire cache line (all 4 banks simultaneously)
always_ff @(posedge clk_i) begin
    if (rd_en_i) begin
        rdata_o <= {bank3[line_index],  // [127:96]
                    bank2[line_index],  // [95:64]
                    bank1[line_index],  // [63:32]
                    bank0[line_index]}; // [31:0]
    end
end
```

### Cache Controller Interface

```
CPU Request: LW addr=0x8000_0010
             line_index = 0x800001
             word_sel = 1

wrapper_ram returns:
  rdata_o[127:0] = {word3, word2, word1, word0}

Cache controller extracts:
  word = rdata_o[word_sel*32 +: 32] = rdata_o[63:32] = word1
```

---

## Byte-Granular Yazma

### Write Logic

```systemverilog
always_ff @(posedge clk_i) begin
    // CPU write veya Programming write
    if (cpu_we || prog_we) begin
        logic [31:0] write_addr;
        logic [31:0] write_data;
        logic [3:0]  write_strb;

        write_addr = prog_active ? prog_addr : addr_i;
        write_data = prog_active ? prog_data : wdata_i;
        write_strb = prog_active ? 4'b1111  : wstrb_i;

        // Bank selection based on word offset
        case (write_addr[3:2])
            2'b00: begin
                if (write_strb[0]) bank0[line_index][7:0]   <= write_data[7:0];
                if (write_strb[1]) bank0[line_index][15:8]  <= write_data[15:8];
                if (write_strb[2]) bank0[line_index][23:16] <= write_data[23:16];
                if (write_strb[3]) bank0[line_index][31:24] <= write_data[31:24];
            end
            2'b01: begin
                if (write_strb[0]) bank1[line_index][7:0]   <= write_data[7:0];
                if (write_strb[1]) bank1[line_index][15:8]  <= write_data[15:8];
                if (write_strb[2]) bank1[line_index][23:16] <= write_data[23:16];
                if (write_strb[3]) bank1[line_index][31:24] <= write_data[31:24];
            end
            2'b10: begin
                if (write_strb[0]) bank2[line_index][7:0]   <= write_data[7:0];
                if (write_strb[1]) bank2[line_index][15:8]  <= write_data[15:8];
                if (write_strb[2]) bank2[line_index][23:16] <= write_data[23:16];
                if (write_strb[3]) bank2[line_index][31:24] <= write_data[31:24];
            end
            2'b11: begin
                if (write_strb[0]) bank3[line_index][7:0]   <= write_data[7:0];
                if (write_strb[1]) bank3[line_index][15:8]  <= write_data[15:8];
                if (write_strb[2]) bank3[line_index][23:16] <= write_data[23:16];
                if (write_strb[3]) bank3[line_index][31:24] <= write_data[31:24];
            end
        endcase
    end
end
```

### Store Instruction Examples

```
SW x1, 0(x2)    // Word store: wstrb=1111, writes to one bank
SH x1, 0(x2)    // Halfword: wstrb=0011 or 1100
SB x1, 0(x2)    // Byte: wstrb=0001, 0010, 0100, or 1000
```

---

## Programming Interface

### RAM Programmer Entegrasyonu

```systemverilog
ram_programmer #(
    .CPU_CLK         (CPU_CLK),
    .PROG_BAUD_RATE  (PROG_BAUD_RATE),
    .PROGRAM_SEQUENCE(PROGRAM_SEQUENCE)
) i_programmer (
    .i_clk         (clk_i),
    .i_rst_n       (rst_ni),
    .i_uart_rx     (ram_prog_rx_i),
    .o_ram_we      (prog_we),
    .o_ram_addr    (prog_addr),
    .o_ram_wdata   (prog_data),
    .o_system_reset(system_reset_o),
    .o_prog_mode_led(prog_mode_led_o)
);
```

### Priority Arbitration

```systemverilog
// Programming port öncelikli
wire prog_active = !system_reset_o;  // During programming
wire cpu_we      = |wstrb_i && !prog_active;
```

---

## Initialization

### Hex File Loading

```systemverilog
initial begin
    if (RAM_INIT_FILE != "") begin
        // 4 bank için ayrı init
        $readmemh({RAM_INIT_FILE, "_b0.hex"}, bank0);
        $readmemh({RAM_INIT_FILE, "_b1.hex"}, bank1);
        $readmemh({RAM_INIT_FILE, "_b2.hex"}, bank2);
        $readmemh({RAM_INIT_FILE, "_b3.hex"}, bank3);
    end
end
```

### Verilator Memory Loading

```systemverilog
`ifdef VERILATOR
    // Load program via DPI
    import "DPI-C" function void load_program(
        input string filename,
        inout logic [31:0] mem0[],
        inout logic [31:0] mem1[],
        inout logic [31:0] mem2[],
        inout logic [31:0] mem3[]
    );

    initial begin
        load_program($test$plusargs("firmware"),
                     bank0, bank1, bank2, bank3);
    end
`endif
```

---

## Timing Diyagramı

### Cache Line Read

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └───

addr_i     ────┤ ADDR  ├───────────

rd_en_i        ┌───────┐
           ────┘       └───────────

rdata_o    ────────────┤128-bit LINE├
                       (registered)
```

### Byte Write

```
              ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
clk_i      ───┘ └─┘ └─┘ └─┘ └─┘ └───

addr_i     ────┤ ADDR  ├───────────

wdata_i    ────┤ DATA  ├───────────

wstrb_i    ────┤ 0001  ├───────────
               (byte 0 only)

bank0[idx]     ────────┤ UPDATED ├─
                       byte 0 only
```

---

## Performance

### Throughput

| Operation | Latency | Bandwidth |
|-----------|---------|-----------|
| Cache Line Read | 1 cycle | 128 bits/cycle |
| Word Write | 1 cycle | 32 bits/cycle |
| Burst Read (4 words) | 1 cycle | 128 bits/cycle |

### Resource Usage (Typical)

| Resource | Usage |
|----------|-------|
| BRAM (1MB) | 256 x 36Kb BRAM |
| LUTs | ~500 (address decode) |
| FFs | ~200 (control logic) |

---

## Özet

`wrapper_ram` modülü:

1. **128-bit Read**: Full cache line single-cycle
2. **Byte-Granular Write**: wstrb-based selective write
3. **4 Banks**: Parallel 32-bit memory banks
4. **Programming**: UART-based boot loading
5. **Priority**: Programming port > CPU port

Bu modül, CERES cache sisteminin backend belleğidir.
