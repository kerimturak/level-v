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
