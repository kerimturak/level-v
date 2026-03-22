# Align Buffer Module — Technical Documentation

## Overview

The `align_buffer.sv` module aligns 128-bit lines from the instruction cache into 32-bit RISC-V instructions. It handles misaligned accesses (instructions that cross a cache-line boundary), supports compressed code, and uses an even/odd bank organization over 16-bit parcels.

## Main responsibilities

1. **Instruction alignment:** Extract 32-bit instructions from a 128-bit line  
2. **Misaligned access:** Handle instructions that straddle a line boundary  
3. **Double miss:** When two lines are needed, sequence fetches correctly  
4. **Parcel-based architecture:** Even/odd banks over 16-bit parcels  
5. **Combinational loop prevention:** `split_var` hints for Verilator  

## Architectural parameters

| Parameter | Default (level_param) | Description |
|-----------|----------------------|----------|
| `CACHE_SIZE` | ABUFF_SIZE | Align-buffer cache size (bits) |
| `BLK_SIZE` | BLK_SIZE | Cache line size (bits), typically 128 |
| `XLEN` | 32 | Register width |
| `NUM_WAY` | ABUFF_WAY | Number of ways (for future expansion) |

### Derived parameters

```systemverilog
localparam NUM_SET = (CACHE_SIZE / (BLK_SIZE * NUM_WAY));
localparam IDX_WIDTH = $clog2(NUM_SET);
localparam OFFSET_WIDTH = $clog2(BLK_SIZE / 8);
localparam TAG_SIZE = XLEN - IDX_WIDTH - OFFSET_WIDTH;
localparam NUM_WORDS = BLK_SIZE / 32;  // 128-bit line: 4 words
localparam NUM_PARCELS = NUM_WORDS * 2;  // Each word is 2 parcels (16-bit)
```

**Example (128-bit cache line):**
- `BLK_SIZE = 128 bit`
- `NUM_WORDS = 4` (32-bit words)
- `NUM_PARCELS = 8` (16-bit parcels)
- `OFFSET_WIDTH = 4` (16 byte / 8 = 4 bit)

## Port definitions

### Input ports

| Port | Type | Description |
|------|-----|----------|
| `clk_i` | logic | System clock |
| `rst_ni` | logic | Active-low asynchronous reset |
| `flush_i` | logic | Pipeline flush |
| `buff_req_i` | abuff_req_t | Buffer request from fetch |
| `lowX_res_i` | blowX_res_t | Response from lower cache/memory |

**`abuff_req_t` layout:**
```systemverilog
typedef struct packed {
  logic         valid;     // Request valid?
  logic         ready;     // Buffer ready?
  logic [XLEN-1:0] addr;   // Fetch address
  logic         uncached;  // Uncached access (MMIO)
} abuff_req_t;
```

### Output ports

| Port | Type | Description |
|------|-----|----------|
| `buff_res_o` | abuff_res_t | Buffer response to fetch |
| `lowX_req_o` | blowX_req_t | Request to lower-level cache/memory |

**`abuff_res_t` layout:**
```systemverilog
typedef struct packed {
  logic         valid;          // Response valid?
  logic         ready;          // Buffer ready for next request?
  logic         miss;           // Cache miss occurred?
  logic         waiting_second; // Double miss: second beat pending
  logic [31:0]  blk;            // Aligned 32-bit instruction
} abuff_res_t;
```

## Even/odd bank architecture

### Memory Layout

A 128-bit cache line splits into eight 16-bit parcels:

```
Cache Line (128-bit):
+--------+--------+--------+--------+--------+--------+--------+--------+
| Word 3 | Word 2 | Word 1 | Word 0 |
| O3 E3  | O2 E2  | O1 E1  | O0 E0  |
+--------+--------+--------+--------+--------+--------+--------+--------+
Address:  +E  +C    +A  +8    +6  +4    +2  +0

E (Even): Lower 16-bits of each word
O (Odd):  Upper 16-bits of each word
```

**Bank organization:**
- **Even bank (ebram):** E0–E3 (low 16 bits of each 32-bit word)  
- **Odd bank (obram):** O0–O3 (high 16 bits of each word)  

### Address mapping

```systemverilog
Address:      [TAG | INDEX | OFFSET]
            [31:IDX_WIDTH+OFFSET_WIDTH] [IDX_WIDTH+OFFSET_WIDTH-1:OFFSET_WIDTH] [OFFSET_WIDTH-1:0]

Example (128-bit line, 64 sets):
  TAG:      [31:10]  (22-bit)
  INDEX:    [9:4]    (6-bit, 64 set)
  OFFSET:   [3:0]    (4-bit, 16 byte)
  
OFFSET breakdown:
  [3:2] -> word_sel  (one of four words in the line)
  [1]   -> half_sel  (half within word: 0=lower, 1=upper)
  [0]   -> byte_sel  (unused here)
```

## Operation flow

### 1. Address Parsing

```systemverilog
half_sel = buff_req_i.addr[1];        // Half within 32-bit word
word_sel = buff_req_i.addr[OFFSET_WIDTH-1:2];  // Word within cache line
unalign  = &{word_sel, half_sel};     // Cache line boundary cross?

odd.rd_idx = buff_req_i.addr[IDX_WIDTH+OFFSET_WIDTH-1:OFFSET_WIDTH];
{overflow, even.rd_idx} = odd.rd_idx + {{(IDX_WIDTH-1){1'b0}}, unalign};
```

**Unaligned access detection:**
- `unalign = 1` when the 32-bit instruction spans an I-cache line boundary  
- Example: `addr[3:1] = 3'b111` → `word_sel=3`, `half_sel=1` (last halfword in line) → `unalign=1`  
- On index overflow, the even bank’s index points at the *next* line  

### 2. Tag Comparison & Hit/Miss Detection

```systemverilog
odd.wr_tag = {1'b1, buff_req_i.addr[XLEN-1:IDX_WIDTH+OFFSET_WIDTH]};
even.wr_tag = overflow ? {1'b1, tag_plus1} : odd.wr_tag;

even.rd_tag = tag_ram[even.rd_idx];
odd.rd_tag  = tag_ram[odd.rd_idx];

even.valid = even.rd_tag[TAG_SIZE];  // MSB: valid bit
odd.valid  = odd.rd_tag[TAG_SIZE];

even.match = (even.rd_tag[TAG_SIZE-1:0] == even.wr_tag[TAG_SIZE-1:0]);
odd.match  = (odd.rd_tag[TAG_SIZE-1:0] == odd.wr_tag[TAG_SIZE-1:0]);

even.miss = buff_req_i.valid && !(even.valid && even.match);
odd.miss  = buff_req_i.valid && !(odd.valid && odd.match);
```

**Miss State:**
```
miss_state = {odd.miss, even.miss}
2'b00 -> Both banks HIT
2'b01 -> Even miss, Odd hit
2'b10 -> Odd miss, Even hit
2'b11 -> Both banks MISS (double miss possible)
```

### 3. Parcel Selection

**Cache Hit Path:**
```systemverilog
// Even bank: lower 16-bits of word
case (parcel_idx[WORD_SEL_WIDTH-1:0])
  2'd0: even.parcel = even.rd_parcel[0];
  2'd1: even.parcel = even.rd_parcel[1];
  2'd2: even.parcel = even.rd_parcel[2];
  2'd3: even.parcel = even.rd_parcel[3];
endcase

// Odd bank: upper 16-bits of word
case (word_sel)
  2'd0: odd.parcel = odd.rd_parcel[0];
  2'd1: odd.parcel = odd.rd_parcel[1];
  2'd2: odd.parcel = odd.rd_parcel[2];
  2'd3: odd.parcel = odd.rd_parcel[3];
endcase
```

**Memory Response Path (Miss):**
```systemverilog
// Odd bank: upper 16-bit of selected word from memory
case (word_sel)
  2'd0: odd.deviceX_parcel = lowX_res_i.blk[31:16];
  2'd1: odd.deviceX_parcel = lowX_res_i.blk[63:48];
  2'd2: odd.deviceX_parcel = lowX_res_i.blk[95:80];
  2'd3: odd.deviceX_parcel = lowX_res_i.blk[127:112];
endcase

// Even bank: first parcel on split-line case, else same as odd halfword
even.deviceX_parcel = unalign ? lowX_res_i.blk[15:0] : odd.deviceX_parcel;
```

### 4. Instruction Assembly

**Case Analysis:**

#### Case 1: Word-Aligned (half_sel=0, addr[1]=0)
```
Instruction: [addr: lower16] [addr+2: upper16]
Output: {odd.parcel, even.parcel}

Example: `addr=0x80000000`
  even.parcel = E0 (cache[0x0:0x1])
  odd.parcel  = O0 (cache[0x2:0x3])
  inst = {O0, E0} = cache[0x0:0x3]
```

#### Case 2: Half-Word Offset (half_sel=1, addr[1]=1)
```
Instruction: [addr: lower16] [addr+2: upper16 from next word]
Output: {even.parcel, odd.parcel}

Example: `addr=0x80000002`
  odd.parcel  = O0 (cache[0x2:0x3])
  even.parcel = E1 (cache[0x4:0x5])
  inst = {E1, O0} = cache[0x2:0x5]
```

#### Case 3: Unaligned (cache line boundary cross, addr[3:1]=111)
```
Instruction spans two cache lines
Output: {even.parcel(next_line), odd.parcel(current_line)}

Example: `addr=0x8000000E`
  odd.parcel  = O3 (current line[0xE:0xF])
  even.parcel = E0 (next line[0x0:0x1])
  inst = {E0_next, O3_current}
```

### 5. Double Miss State Machine

**Problem:**  
A split-line instruction needs two lines. If both miss, two refill responses are required. Do **not** assert `buff_res_o.valid` after only the first response—the 32-bit instruction is not complete yet.

**Solution:**
```systemverilog
// Ignore valid for one cycle after first response
always_ff @(posedge clk_i) begin
  if ((miss_state == 2'b11) && lowX_res_i.valid && unalign)
    ignore_valid_q <= 1'b1;
  else
    ignore_valid_q <= 1'b0;
end

// Track that we're waiting for second response
always_ff @(posedge clk_i) begin
  if ((miss_state == 2'b11) && masked_valid && unalign)
    waiting_second_q <= 1'b1;
  else if (waiting_second_q && masked_valid)
    waiting_second_q <= 1'b0;
end

masked_valid = lowX_res_i.valid && !ignore_valid_q;
```

**Timeline:**
```
Cycle N:   First request (odd bank line)
Cycle N+X: First response → ignore_valid_q=1, waiting_second_q=1
Cycle N+X+1: Second request (even bank line)
Cycle N+Y: Second response → instruction valid!
```

### 6. Output Valid Generation

```systemverilog
buff_res_o.valid = 
  &hit_state ||  // Both banks hit (same cycle)
  (|miss_state && !half_sel && masked_valid) ||  // Word-aligned single miss
  (!(&miss_state) && half_sel && masked_valid) ||  // Half-word partial hit
  (waiting_second_q && masked_valid);  // Double miss second response
```

**When `buff_res_o.valid` is asserted:**
1. **Dual hit:** both banks hit → instruction ready same cycle  
2. **Single miss (word-aligned):** one refill completes the instruction  
3. **Single miss (halfword straddle, partial hit):** one bank hit, one miss → one refill  
4. **Double miss:** two refills; valid only after the second completes  

## Request Generation Logic

```systemverilog
if (waiting_second_q && !masked_valid)
  lowX_req_o.valid = !buff_req_i.uncached;  // Second request
else if (&miss_state)
  lowX_req_o.valid = !masked_valid && !buff_req_i.uncached;  // First request
else if (|miss_state)
  lowX_req_o.valid = !masked_valid && !waiting_second_q && !buff_req_i.uncached;  // Single miss
else
  lowX_req_o.valid = 1'b0;  // Both hit
```

### Address Calculation

```systemverilog
base_addr = buff_req_i.addr & ~(BLOCK_BYTES - 1);  // Cache line aligned

if (waiting_second_q)
  lowX_req_o.addr = base_addr + BLOCK_BYTES;  // Even bank line
else
  case ({unalign, odd.miss, even.miss})
    3'b101:  lowX_req_o.addr = base_addr + BLOCK_BYTES;  // Even miss only
    3'b111:  lowX_req_o.addr = base_addr;  // Double miss: odd first
    default: lowX_req_o.addr = base_addr;  // Same line
  endcase
```

## Verilator Optimizations

### Split_Var Directive

```systemverilog
bank_t even /*verilator split_var*/, odd /*verilator split_var*/;
logic miss_state /*verilator split_var*/;
logic word_sel /*verilator split_var*/;
```

**Purpose:**
- Improve combinational-loop detection in Verilator’s 2-state simulation  
- Break apparent circular dependencies between even/odd `bank_t` structs  
- Reduce `UNOPTFLAT` noise  

**Details:**
- See `docs/verilator/bugs/002_combinational_loop_instruction_corruption.md`  
- Without `split_var`, Verilator can mis-order evaluation and report false combinational loops  
- `split_var` treats each struct field more like an independent variable for scheduling  

## Timing Analysis

### Critical Paths

1. **Tag Comparison Path:**
   ```
   buff_req_i.addr → tag_ram read → tag compare → hit/miss detection → output mux
   ```
   - Combinational path, single cycle
   - Tag RAM is usually a combinational read of a registered address (watch BRAM inference)  

2. **Parcel Selection Path:**
   ```
   word_sel/half_sel → bank select → parcel mux → instruction assembly
   ```
   - Mux tree can be timing-critical  
   - Large `case` trees map cleanly in synthesis  

3. **Double Miss FSM Path:**
   ```
   lowX_res_i.valid → ignore_valid_q → masked_valid → FSM transition
   ```
   - Sequential logic, register to register
   - Timing constraint: single cycle state transition

### Performance Metrics

| Case | Latency | Throughput |
|-------|---------|------------|
| **Dual Hit** | 1 cycle | 1 inst/cycle |
| **Single Miss (aligned)** | N+1 cycles | 1 inst/N cycles |
| **Single Miss (half-word)** | N+1 cycles | 1 inst/N cycles |
| **Double Miss (unalign)** | 2N+2 cycles | 1 inst/2N cycles |

*N = Memory access latency (cache line fetch)*

## Exception Handling

The align buffer does not originate exceptions; it passes through faults raised by fetch:

- **Instruction access fault:** PMA `grand_o=0` (execute not granted) — handled in fetch  
- **Instruction misaligned:** PC alignment rules — handled in fetch  
- **Uncached access:** `buff_req_i.uncached=1` bypasses the cache data array  

## Debug Support

### Signal Monitoring

```systemverilog
// Signals to monitor in simulation:
- miss_state        // {odd.miss, even.miss} encoding
- unalign           // Cache line boundary cross
- waiting_second_q  // Double miss FSM state
- masked_valid      // Effective valid signal
- buff_res_o.valid  // Final instruction valid
- buff_res_o.blk    // Assembled instruction
```

### Waveform Analysis

```
Signal Flow for Double Miss:
  1. buff_req_i.valid = 1, unalign = 1, miss_state = 2'b11
  2. lowX_req_o.valid = 1 (first request, odd bank line)
  3. lowX_res_i.valid = 1 (first response)
  4. ignore_valid_q = 1 (suppress first valid)
  5. waiting_second_q = 1 (FSM transition)
  6. lowX_req_o.valid = 1 (second request, even bank line)
  7. lowX_res_i.valid = 1 (second response)
  8. buff_res_o.valid = 1 (final instruction ready)
```

## Suggested assertions

```systemverilog
// Double miss: issue second refill while waiting
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (waiting_second_q && !masked_valid) |-> lowX_req_o.valid);

// Valid output must not be all-zero except legal NOP encoding
assert property (@(posedge clk_i) disable iff (!rst_ni)
  buff_res_o.valid |-> (buff_res_o.blk inside {32'h00000013, [32'h1:32'hFFFFFFFF]}));

// Both banks cannot miss unless the access crosses a line
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (miss_state == 2'b11) |-> unalign);

// Flush must clear split-line wait state
assert property (@(posedge clk_i) disable iff (!rst_ni)
  flush_i |=> !waiting_second_q);
```

## Future improvements

1. **Way-Associative Support**: Currently single-way, future set-associative expansion
2. **Prefetching:** proactive line fetch on sequential streams  
3. **Streaming buffer:** burst refill on back-to-back misses  
4. **Tag RAM:** retime or map to BRAM macros where helpful  
5. **Adaptive banking:** repartition banks for compressed-heavy code  

---

## 🚀 Prefetcher implementation plan

### Prefetcher types and comparison

| # | Prefetcher type | Complexity | Area | Expected gain | Best for |
|---|----------------|-------------|------|------------------|----------------|
| 1 | **Next-Line** | ⭐ Low | ~50 FF | %5-10 hit rate gain | Baseline, sequential access |
| 2 | **Stride** | ⭐⭐ Medium | ~1-2KB | %10-20 hit rate gain | Array / strided loops |
| 3 | **Stream** | ⭐⭐ Medium | ~512B-1KB | %15-25 hit rate gain | Sequential I-fetch |
| 4 | **Markov** | ⭐⭐⭐ Medium-High | ~4-8KB | %15-30 hit rate gain | Irregular patterns |
| 5 | **Neural/Perceptron** | ⭐⭐⭐⭐ High | ~2-4KB | %20-35 hit rate gain | Complex patterns |
| 6 | **Hybrid** | ⭐⭐⭐ Medium-High | ~2-4KB | %20-30 hit rate gain | Mixed workloads |

### Phased implementation plan

| Phase | Prefetcher | Goal | Estimated time | Status |
|-------|-----------|-------|--------------|-------|
| 1 | Next-Line (I-Cache) | Baseline bring-up | 1-2 day | ⏳ Planned |
| 2 | Stride (D-Cache) | Array / loop streams | 3-5 day | 📋 Pending |
| 3 | Stream (I-Cache) | Sequential fetch | 3-5 day | 📋 Pending |
| 4 | Hybrid/Neural | Maximum coverage | 1-2 week | 📋 Pending |

---

### 1️⃣ Next-line prefetcher (phase 1 — starting point)

**Operating principle:**
- On a demand miss, also prefetch the following line  
- Strong fit for sequential code  
- Smallest area/complexity prefetch baseline  

```systemverilog
module next_line_prefetcher #(
    parameter XLEN     = 32,
    parameter BLK_SIZE = 128  // Cache line size in bits
)(
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             cache_miss_i,
    input  logic [XLEN-1:0]  miss_addr_i,
    input  logic             prefetch_ack_i,  // Prefetch accepted
    output logic             prefetch_valid_o,
    output logic [XLEN-1:0]  prefetch_addr_o
);

    localparam LINE_BYTES = BLK_SIZE / 8;  // 16 bytes for 128-bit line
    localparam OFFSET_BITS = $clog2(LINE_BYTES);

    // Prefetch state
    logic prefetch_pending_q;
    logic [XLEN-1:0] prefetch_addr_q;

    // Next line address calculation (cache line aligned)
    logic [XLEN-1:0] next_line_addr;
    assign next_line_addr = {miss_addr_i[XLEN-1:OFFSET_BITS], {OFFSET_BITS{1'b0}}} + LINE_BYTES;

    // Prefetch output
    assign prefetch_valid_o = prefetch_pending_q;
    assign prefetch_addr_o = prefetch_addr_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            prefetch_pending_q <= 1'b0;
            prefetch_addr_q <= '0;
        end else begin
            if (cache_miss_i && !prefetch_pending_q) begin
                // New miss — prefetch next line
                prefetch_pending_q <= 1'b1;
                prefetch_addr_q <= next_line_addr;
            end else if (prefetch_ack_i) begin
                // Prefetch accepted
                prefetch_pending_q <= 1'b0;
            end
        end
    end

endmodule
```

**Integration:** trigger from the I-cache miss path in `align_buffer.sv` or `cache.sv`.

---

### 2️⃣ Stride prefetcher (phase 2)

**Operating principle:**
- Track recent address history per PC (or PC bucket)  
- When the same stride repeats, prefetch `addr + stride`  
- Strong for array walks and regular stride kernels  

```systemverilog
module stride_prefetcher #(
    parameter XLEN        = 32,
    parameter TABLE_SIZE  = 64,
    parameter STRIDE_BITS = 12,
    parameter BLK_SIZE    = 128
)(
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             access_valid_i,
    input  logic [XLEN-1:0]  access_pc_i,
    input  logic [XLEN-1:0]  access_addr_i,
    input  logic             cache_hit_i,
    input  logic             prefetch_ack_i,
    output logic             prefetch_valid_o,
    output logic [XLEN-1:0]  prefetch_addr_o,
    output logic [1:0]       prefetch_confidence_o
);

    typedef struct packed {
        logic [XLEN-1:0]        last_addr;
        logic signed [STRIDE_BITS-1:0] stride;
        logic [1:0]             state;  // 0: initial, 1: transient, 2: steady, 3: no-pred
        logic                   valid;
    } stride_entry_t;

    stride_entry_t table [TABLE_SIZE];

    // PC-indexed lookup
    logic [$clog2(TABLE_SIZE)-1:0] idx;
    assign idx = access_pc_i[$clog2(TABLE_SIZE)+1:2];

    // Current stride calculation
    logic signed [STRIDE_BITS-1:0] current_stride;
    assign current_stride = access_addr_i - table[idx].last_addr;

    // Prefetch decision: steady state (confidence >= 2)
    assign prefetch_valid_o = access_valid_i && 
                              table[idx].valid && 
                              (table[idx].state >= 2'd2);
    assign prefetch_addr_o = access_addr_i + 
                             {{(XLEN-STRIDE_BITS){table[idx].stride[STRIDE_BITS-1]}}, 
                              table[idx].stride};
    assign prefetch_confidence_o = table[idx].state;

    // State machine update
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            for (int i = 0; i < TABLE_SIZE; i++) begin
                table[i] <= '0;
            end
        end else if (access_valid_i) begin
            if (!table[idx].valid) begin
                // First access — create entry
                table[idx].last_addr <= access_addr_i;
                table[idx].stride <= '0;
                table[idx].state <= 2'd0;
                table[idx].valid <= 1'b1;
            end else begin
                // Update existing entry
                table[idx].last_addr <= access_addr_i;
                
                if (current_stride == table[idx].stride) begin
                    // Stride match — increase confidence
                    if (table[idx].state < 2'd3)
                        table[idx].state <= table[idx].state + 1;
                end else begin
                    // Stride mismatch — record new stride, reset confidence
                    table[idx].stride <= current_stride;
                    table[idx].state <= 2'd1;
                end
            end
        end
    end

endmodule
```

---

### 3️⃣ Stream prefetcher (phase 3 — great for I-cache)

**Operating principle:**
- After *N* consecutive misses along a line, declare a streaming region  
- Prefetch several lines ahead in the stream direction  
- Excellent for long sequential instruction runs  

```systemverilog
module stream_prefetcher #(
    parameter XLEN           = 32,
    parameter NUM_STREAMS    = 4,
    parameter PREFETCH_DEGREE = 4,  // Lines to prefetch ahead
    parameter BLK_SIZE       = 128
)(
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             cache_miss_i,
    input  logic [XLEN-1:0]  miss_addr_i,
    input  logic             prefetch_ack_i,
    output logic             prefetch_valid_o,
    output logic [XLEN-1:0]  prefetch_addr_o
);

    localparam LINE_BYTES = BLK_SIZE / 8;
    localparam OFFSET_BITS = $clog2(LINE_BYTES);

    typedef struct packed {
        logic [XLEN-1:0] start_addr;
        logic [XLEN-1:0] current_addr;
        logic            direction;  // 0: ascending, 1: descending
        logic [2:0]      confidence;
        logic [2:0]      prefetch_count;
        logic            valid;
    } stream_t;

    stream_t streams [NUM_STREAMS];
    logic [$clog2(NUM_STREAMS)-1:0] alloc_ptr;
    logic [$clog2(NUM_STREAMS)-1:0] active_stream;
    logic stream_found;

    // Stream matching logic
    always_comb begin
        stream_found = 1'b0;
        active_stream = '0;
        
        for (int i = 0; i < NUM_STREAMS; i++) begin
            if (streams[i].valid) begin
                // Check if miss is in this stream's range
                logic [XLEN-1:0] expected_addr;
                expected_addr = streams[i].direction ? 
                               streams[i].current_addr - LINE_BYTES :
                               streams[i].current_addr + LINE_BYTES;
                
                if (miss_addr_i[XLEN-1:OFFSET_BITS] == expected_addr[XLEN-1:OFFSET_BITS]) begin
                    stream_found = 1'b1;
                    active_stream = i[$clog2(NUM_STREAMS)-1:0];
                end
            end
        end
    end

    // Prefetch output from active stream
    assign prefetch_valid_o = stream_found && 
                              (streams[active_stream].confidence >= 3'd2) &&
                              (streams[active_stream].prefetch_count < PREFETCH_DEGREE);
    assign prefetch_addr_o = streams[active_stream].direction ?
                             streams[active_stream].current_addr - (LINE_BYTES * (streams[active_stream].prefetch_count + 1)) :
                             streams[active_stream].current_addr + (LINE_BYTES * (streams[active_stream].prefetch_count + 1));

    // Stream management state machine
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            for (int i = 0; i < NUM_STREAMS; i++) begin
                streams[i] <= '0;
            end
            alloc_ptr <= '0;
        end else if (cache_miss_i) begin
            if (stream_found) begin
                // Update existing stream
                streams[active_stream].current_addr <= miss_addr_i;
                if (streams[active_stream].confidence < 3'd7)
                    streams[active_stream].confidence <= streams[active_stream].confidence + 1;
            end else begin
                // Allocate new stream
                streams[alloc_ptr].start_addr <= miss_addr_i;
                streams[alloc_ptr].current_addr <= miss_addr_i;
                streams[alloc_ptr].direction <= 1'b0;  // Default ascending
                streams[alloc_ptr].confidence <= 3'd1;
                streams[alloc_ptr].prefetch_count <= '0;
                streams[alloc_ptr].valid <= 1'b1;
                alloc_ptr <= alloc_ptr + 1;
            end
        end
        
        if (prefetch_ack_i && stream_found) begin
            streams[active_stream].prefetch_count <= streams[active_stream].prefetch_count + 1;
        end
    end

endmodule
```

---

### 📐 Parametric prefetcher wrapper (compile-time selection)

Wrapper to pick one prefetch algorithm via parameters:

```systemverilog
module prefetcher_wrapper #(
    parameter XLEN           = 32,
    parameter BLK_SIZE       = 128,
    parameter PREFETCH_TYPE  = 0,  // 0: None, 1: NextLine, 2: Stride, 3: Stream, 4: Hybrid
    // Stride parameters
    parameter STRIDE_TABLE   = 64,
    parameter STRIDE_BITS    = 12,
    // Stream parameters
    parameter NUM_STREAMS    = 4,
    parameter PREFETCH_DEGREE = 4
)(
    input  logic             clk_i,
    input  logic             rst_ni,
    // Cache interface
    input  logic             cache_miss_i,
    input  logic             cache_hit_i,
    input  logic [XLEN-1:0]  access_addr_i,
    input  logic [XLEN-1:0]  access_pc_i,
    input  logic             access_valid_i,
    // Prefetch interface
    input  logic             prefetch_ack_i,
    output logic             prefetch_valid_o,
    output logic [XLEN-1:0]  prefetch_addr_o
);

    generate
        if (PREFETCH_TYPE == 0) begin : gen_no_prefetch
            // No prefetching
            assign prefetch_valid_o = 1'b0;
            assign prefetch_addr_o = '0;
            
        end else if (PREFETCH_TYPE == 1) begin : gen_next_line
            // Next-Line Prefetcher
            next_line_prefetcher #(
                .XLEN(XLEN),
                .BLK_SIZE(BLK_SIZE)
            ) u_next_line (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .cache_miss_i(cache_miss_i),
                .miss_addr_i(access_addr_i),
                .prefetch_ack_i(prefetch_ack_i),
                .prefetch_valid_o(prefetch_valid_o),
                .prefetch_addr_o(prefetch_addr_o)
            );
            
        end else if (PREFETCH_TYPE == 2) begin : gen_stride
            // Stride Prefetcher
            stride_prefetcher #(
                .XLEN(XLEN),
                .TABLE_SIZE(STRIDE_TABLE),
                .STRIDE_BITS(STRIDE_BITS),
                .BLK_SIZE(BLK_SIZE)
            ) u_stride (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .access_valid_i(access_valid_i),
                .access_pc_i(access_pc_i),
                .access_addr_i(access_addr_i),
                .cache_hit_i(cache_hit_i),
                .prefetch_ack_i(prefetch_ack_i),
                .prefetch_valid_o(prefetch_valid_o),
                .prefetch_addr_o(prefetch_addr_o),
                .prefetch_confidence_o()  // Optional
            );
            
        end else if (PREFETCH_TYPE == 3) begin : gen_stream
            // Stream Prefetcher
            stream_prefetcher #(
                .XLEN(XLEN),
                .NUM_STREAMS(NUM_STREAMS),
                .PREFETCH_DEGREE(PREFETCH_DEGREE),
                .BLK_SIZE(BLK_SIZE)
            ) u_stream (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .cache_miss_i(cache_miss_i),
                .miss_addr_i(access_addr_i),
                .prefetch_ack_i(prefetch_ack_i),
                .prefetch_valid_o(prefetch_valid_o),
                .prefetch_addr_o(prefetch_addr_o)
            );
            
        end else if (PREFETCH_TYPE == 4) begin : gen_hybrid
            // Hybrid: Stride + Stream with arbiter
            logic stride_valid, stream_valid;
            logic [XLEN-1:0] stride_addr, stream_addr;
            
            stride_prefetcher #(.XLEN(XLEN), .TABLE_SIZE(STRIDE_TABLE)) u_stride (
                .clk_i(clk_i), .rst_ni(rst_ni),
                .access_valid_i(access_valid_i),
                .access_pc_i(access_pc_i),
                .access_addr_i(access_addr_i),
                .cache_hit_i(cache_hit_i),
                .prefetch_ack_i(prefetch_ack_i && stride_valid),
                .prefetch_valid_o(stride_valid),
                .prefetch_addr_o(stride_addr),
                .prefetch_confidence_o()
            );
            
            stream_prefetcher #(.XLEN(XLEN), .NUM_STREAMS(NUM_STREAMS)) u_stream (
                .clk_i(clk_i), .rst_ni(rst_ni),
                .cache_miss_i(cache_miss_i),
                .miss_addr_i(access_addr_i),
                .prefetch_ack_i(prefetch_ack_i && stream_valid && !stride_valid),
                .prefetch_valid_o(stream_valid),
                .prefetch_addr_o(stream_addr)
            );
            
            // Stride has priority
            assign prefetch_valid_o = stride_valid | stream_valid;
            assign prefetch_addr_o = stride_valid ? stride_addr : stream_addr;
        end
    endgenerate

endmodule
```

---

### 🔧 Integration architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         CPU Core                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────┐     ┌──────────────────┐    ┌─────────────────┐   │
│  │  Fetch   │────►│   Align Buffer   │───►│  Prefetcher     │   │
│  │  Stage   │     │   (align_buffer) │    │  (PREFETCH_TYPE)│   │
│  └──────────┘     └────────┬─────────┘    └────────┬────────┘   │
│                            │                       │             │
│                            ▼                       ▼             │
│                   ┌──────────────────────────────────────┐      │
│                   │           I-Cache                     │      │
│                   │   cache_req: demand + prefetch        │      │
│                   └──────────────────────────────────────┘      │
│                            │                                     │
│                            ▼                                     │
│                   ┌──────────────────────────────────────┐      │
│                   │        Memory Arbiter                 │      │
│                   │   Priority: Demand > Prefetch         │      │
│                   └──────────────────────────────────────┘      │
│                                                                  │
│  ┌──────────┐     ┌──────────────────┐    ┌─────────────────┐   │
│  │ Memory   │────►│     D-Cache      │───►│  Stride         │   │
│  │  Stage   │     │                  │    │  Prefetcher     │   │
│  └──────────┘     └──────────────────┘    └─────────────────┘   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Parameters to add to level_param.sv

```systemverilog
// ============================================================================
// PREFETCHER PARAMETERS
// ============================================================================
localparam int PREFETCH_TYPE = 1;        // 0:None, 1:NextLine, 2:Stride, 3:Stream, 4:Hybrid
localparam int STRIDE_TABLE_SIZE = 64;   // Stride prefetcher table entries
localparam int STRIDE_BITS = 12;         // Stride bit width
localparam int NUM_STREAMS = 4;          // Stream prefetcher stream count
localparam int PREFETCH_DEGREE = 4;      // How many lines ahead to prefetch
```

## Related modules

1. **fetch.sv:** top-level fetch; instantiates the align buffer  
2. **cache.sv:** I-cache refill path into the align buffer  
3. **compressed_decoder.sv:** expands 16-bit parcels after fetch  

## References

1. RISC-V Unprivileged ISA Specification - Instruction Fetch
2. "Cache and Memory Hierarchy Design: A Performance-Directed Approach" - Steven A. Przybylski
3. "Computer Architecture: A Quantitative Approach" - Hennessy & Patterson, Chapter 2 (Memory Hierarchy)
4. Verilator Manual - Split_Var Directive

---

**Last updated:** 4 December 2025  
**Author:** Kerim TURAK  
**License:** MIT License
