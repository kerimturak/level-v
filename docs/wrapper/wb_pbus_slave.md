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
