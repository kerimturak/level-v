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
