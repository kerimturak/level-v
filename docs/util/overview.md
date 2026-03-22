# FIFO Modules — Technical Documentation

## Table of Contents

1. [General Overview](#general-overview)
2. [count_fifo](#count_fifo)
3. [le_fifo](#le_fifo)
4. [wbit_fifo](#wbit_fifo)
5. [Comparison](#comparison)
6. [Usage Examples](#usage-examples)

---

## General Overview

### Purpose

The `fifo.sv` file contains **three FIFO modules** with different implementation strategies. Each trades area versus performance differently.

### File Location

```
rtl/util/fifo.sv
```

### FIFO Types

| Module | Full/Empty Detection | Area | Performance |
|--------|----------------------|------|-------------|
| `count_fifo` | Counter-based | Medium | Fast |
| `le_fifo` | Pointer comparison | Low | Medium |
| `wbit_fifo` | Wrap bit | Low | Fast |

---

## count_fifo

### Description

Counter-based FIFO. Uses a separate `fifo_count` counter to track full/empty state.

### Module Interface

```systemverilog
module count_fifo #(
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 4
) (
    input  logic                    clk,
    input  logic                    rst,
    input  logic                    write_en,
    input  logic                    read_en,
    input  logic [DATA_WIDTH-1:0]   write_data,
    output logic [DATA_WIDTH-1:0]   read_data,
    output logic                    full,
    output logic                    empty
);
```

### Operating Principle

```systemverilog
// Track element count with a separate counter
logic [ADDR_WIDTH:0] fifo_count;

always_ff @(posedge clk) begin
    if (rst) begin
        fifo_count <= 0;
    end else begin
        case ({write_en, read_en})
            2'b10:   fifo_count <= fifo_count + 1;  // Write only
            2'b01:   fifo_count <= fifo_count - 1;  // Read only
            default: fifo_count <= fifo_count;       // Both or neither
        endcase
    end
end

assign full  = (fifo_count == FIFO_DEPTH);
assign empty = (fifo_count == 0);
```

### Pros and Cons

| Advantage | Disadvantage |
|-----------|--------------|
| Simple full/empty logic | Extra counter register |
| Element count known | More flip-flops |
| Fast computation | — |

---

## le_fifo

### Description

Pointer-comparison FIFO. Full is detected as `(write_ptr + 1) == read_ptr` (one slot left empty).

### Module Interface

```systemverilog
module le_fifo #(
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 4
) (
    input  logic                    clk,
    input  logic                    rst,
    input  logic                    write_en,
    input  logic                    read_en,
    input  logic [DATA_WIDTH-1:0]   write_data,
    output logic [DATA_WIDTH-1:0]   read_data,
    output logic                    full,
    output logic                    empty
);
```

### Operating Principle

```systemverilog
logic [ADDR_WIDTH-1:0] write_ptr, read_ptr;

// Full: next write position equals read position
assign full  = ((write_ptr + 1'b1) == read_ptr);

// Empty: write and read pointers equal
assign empty = (write_ptr == read_ptr);
```

### Drawback

**Capacity loss**: With FIFO_DEPTH=4 only 3 elements can be stored because one slot is always left empty to distinguish full from empty.

```
   When full:
   ┌───┬───┬───┬───┐
   │ D │ D │ D │   │  ← One slot always empty
   └───┴───┴───┴───┘
     ↑           ↑
   read_ptr   write_ptr
```

---

## wbit_fifo

### Description

Wrap-bit FIFO. An extra MSB (wrap bit) on the pointers separates full from empty. **Uses full capacity**.

### Module Interface

```systemverilog
module wbit_fifo #(
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 4
) (
    input  logic                    clk,
    input  logic                    rst,
    input  logic                    write_en,
    input  logic                    read_en,
    input  logic [DATA_WIDTH-1:0]   write_data,
    output logic [DATA_WIDTH-1:0]   read_data,
    output logic                    full,
    output logic                    empty
);
```

### Operating Principle

```systemverilog
// Pointers are ADDR_WIDTH+1 bits (including wrap bit)
logic [ADDR_WIDTH:0] write_ptr, read_ptr;

// Wrap bit: MSB different?
assign wrap_around = (write_ptr[ADDR_WIDTH] ^ read_ptr[ADDR_WIDTH]);

// Full: wrap bits differ AND lower bits match
assign full = wrap_around & (write_ptr[ADDR_WIDTH-1:0] == read_ptr[ADDR_WIDTH-1:0]);

// Empty: all bits equal
assign empty = (write_ptr == read_ptr);

// Memory addressing: lower bits only
always_ff @(posedge clk) begin
    if (write_en && !full) begin
        fifo_mem[write_ptr[ADDR_WIDTH-1:0]] <= write_data;
        write_ptr <= write_ptr + 1;
    end
end
```

### Wrap Bit Diagram

```
FIFO_DEPTH = 4 (2-bit address)
Pointer = 3-bit [wrap_bit : addr]

Empty:  write_ptr = 000, read_ptr = 000  (same)
        write_ptr = 100, read_ptr = 100  (same)

Full:   write_ptr = 100, read_ptr = 000  (wrap differs, addr same)
        write_ptr = 000, read_ptr = 100  (wrap differs, addr same)

Normal: write_ptr = 010, read_ptr = 000  (2 elements)
        write_ptr = 111, read_ptr = 101  (2 elements, wrapped)
```

### Advantages

| Advantage | Description |
|-----------|-------------|
| Full capacity | All FIFO_DEPTH slots used |
| Simple logic | XOR and comparison only |
| No counter | No extra counter register |

---

## Comparison

### Resource Usage

| Module | Registers | Logic | Capacity |
|--------|-----------|-------|----------|
| `count_fifo` | N+1 bit | Adder | DEPTH |
| `le_fifo` | N bit | Comparator | DEPTH-1 |
| `wbit_fifo` | N+1 bit | XOR+Comparator | DEPTH |

### Full/Empty Timing

| Module | Full Path | Empty Path |
|--------|-----------|------------|
| `count_fifo` | counter → compare | counter → compare |
| `le_fifo` | add → compare | compare |
| `wbit_fifo` | XOR → AND → compare | compare |

### Use Cases

| Scenario | Recommended |
|----------|-------------|
| Element count needed | `count_fifo` |
| Minimum area | `wbit_fifo` |
| Full capacity + low area | `wbit_fifo` |

---

## Usage Examples

### UART TX FIFO

```systemverilog
wbit_fifo #(
    .DATA_WIDTH(8),
    .FIFO_DEPTH(256)
) u_uart_tx_fifo (
    .clk       (clk_i),
    .rst       (!rst_ni),
    .write_en  (tx_write),
    .read_en   (tx_read),
    .write_data(tx_data_in),
    .read_data (tx_data_out),
    .full      (tx_fifo_full),
    .empty     (tx_fifo_empty)
);
```

### Pipeline Buffer

```systemverilog
count_fifo #(
    .DATA_WIDTH(64),
    .FIFO_DEPTH(4)
) u_pipe_buffer (
    .clk       (clk_i),
    .rst       (!rst_ni),
    .write_en  (producer_valid && !full),
    .read_en   (consumer_ready && !empty),
    .write_data(producer_data),
    .read_data (consumer_data),
    .full      (full),
    .empty     (empty)
);
```

---

## Summary

The FIFO modules:

1. **count_fifo**: Element tracking with a counter
2. **le_fifo**: Pointer comparison (one slot lost)
3. **wbit_fifo**: Wrap bit for full capacity

Choose the FIFO that matches application requirements.
