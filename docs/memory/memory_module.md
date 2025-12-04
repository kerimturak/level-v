# MEMORY Modülü - Teknik Döküman

## Genel Bakış

`memory.sv` modülü, RISC-V işlemcisinin **Memory Access Stage** (MEM) implementasyonudur. Load/Store instruction'ları için data cache (D-Cache) interface'ini yönetir, memory transaction tracking yapar ve load data alignment/sign-extension işlemlerini gerçekleştirir.

## Sorumluluklar

1. **Data Cache Interface**: D-Cache'e read/write request'leri gönderir
2. **Memory Transaction Tracking**: Aktif memory operation'ları takip eder
3. **Load Data Alignment**: Byte/halfword/word alignment ve extraction
4. **Sign/Zero Extension**: Load data sign/zero extension (LB/LBU, LH/LHU)
5. **Uncached Access**: PMA (Physical Memory Attributes) ile uncached region detection
6. **Cache Miss Handling**: D-Cache miss stall generation
7. **FENCE.I Support**: Cache flush coordination

## Port Tanımları

### Clock & Control

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `stall_i` | stall_e | Pipeline stall sinyali |
| `fe_flush_cache_i` | logic | Cache flush sinyali (FENCE.I) |

### Lower-Level Memory Interface (Wishbone)

| Port | Tip | Açıklama |
|------|-----|----------|
| `lx_dres_i` | dlowX_res_t | Wishbone bus response (from memory) |
| `lx_dreq_o` | dlowX_req_t | Wishbone bus request (to memory) |

### Pipeline Interface

| Port | Tip | Açıklama |
|------|-----|----------|
| `me_data_req_i` | data_req_t | Memory stage data request (pipe3) |
| `ex_data_req_i` | data_req_t | Execute stage data request (pipe2) |
| `me_data_o` | [XLEN-1:0] | Load data output (to writeback) |

### Stall Outputs

| Port | Tip | Açıklama |
|------|-----|----------|
| `dmiss_stall_o` | logic | D-Cache miss stall |
| `fencei_stall_o` | logic | FENCE.I dirty writeback stall |

## Data Structures

### data_req_t (Data Request)

```systemverilog
typedef struct packed {
  logic             valid;        // Request valid
  logic [XLEN-1:0]  addr;         // Memory address
  logic             rw;           // 0=read (load), 1=write (store)
  logic [1:0]       rw_size;      // 01=byte, 10=half, 11=word
  logic             ld_op_sign;   // Load sign extension (1=signed, 0=unsigned)
  logic [XLEN-1:0]  data;         // Store data
} data_req_t;
```

**Fields:**
- **valid**: Request enable (1 = active load/store)
- **addr**: Target memory address (byte-addressed)
- **rw**: Direction (0 = load, 1 = store)
- **rw_size**: Transfer size
  - `2'b01`: Byte (LB, LBU, SB)
  - `2'b10`: Halfword (LH, LHU, SH)
  - `2'b11`: Word (LW, SW)
- **ld_op_sign**: Sign extension for loads
  - `1`: Signed (LB, LH)
  - `0`: Unsigned (LBU, LHU)
- **data**: Store data (for SW, SH, SB)

### dcache_req_t (D-Cache Request)

```systemverilog
typedef struct packed {
  logic             valid;        // Request valid
  logic [XLEN-1:0]  addr;         // Address
  logic             ready;        // Request ready
  logic             rw;           // 0=read, 1=write
  logic [1:0]       rw_size;      // Size
  logic [XLEN-1:0]  data;         // Write data
  logic             uncached;     // Bypass cache (uncached region)
} dcache_req_t;
```

### dcache_res_t (D-Cache Response)

```systemverilog
typedef struct packed {
  logic             valid;        // Response valid (cache hit or refill complete)
  logic [XLEN-1:0]  data;         // Read data
} dcache_res_t;
```

## Memory Transaction Management

### Request Change Detection

```systemverilog
logic req_changed;
logic ex_valid_q;
logic [XLEN-1:0] ex_addr_q;
logic ex_rw_q;
logic [1:0] ex_rw_size_q;

always_ff @(posedge clk_i) begin
  if (!rst_ni || fe_flush_cache_i) begin
    ex_valid_q <= 1'b0;
    ex_addr_q <= '0;
    ex_rw_q <= 1'b0;
    ex_rw_size_q <= '0;
  end else begin
    ex_valid_q <= ex_data_req_i.valid;
    ex_addr_q <= ex_data_req_i.addr;
    ex_rw_q <= ex_data_req_i.rw;
    ex_rw_size_q <= ex_data_req_i.rw_size;
  end
end

assign req_changed = (ex_data_req_i.addr != ex_addr_q) || 
                     (ex_data_req_i.rw != ex_rw_q) || 
                     (ex_data_req_i.rw_size != ex_rw_size_q) || 
                     (ex_data_req_i.valid && !ex_valid_q);
```

**Purpose:** Detect new/changed memory requests

**Why Register Comparison?**
- `ex_data_req_i` may remain valid for multiple cycles (consecutive accesses)
- Need to distinguish new request from held request
- Compare with previous cycle's values

**Excluded from Comparison:**
- `.data` field excluded to break combinational loop
- `data` depends on forwarding → forwarding depends on stall → stall depends on `mem_req_fire`

### Memory Request Fire Logic

```systemverilog
logic mem_txn_active;
logic mem_req_fire;

assign mem_req_fire = ex_data_req_i.valid && req_changed && !mem_txn_active;
```

**Conditions for New Request:**
1. `ex_data_req_i.valid = 1`: Request active
2. `req_changed = 1`: New/different request
3. `mem_txn_active = 0`: No active transaction

**Purpose:** Start exactly one cache transaction per memory operation

### Transaction Tracking

```systemverilog
always_ff @(posedge clk_i) begin
  if (!rst_ni || fe_flush_cache_i) begin
    mem_txn_active <= 1'b0;
  end else begin
    if (dcache_res.valid) begin
      mem_txn_active <= 1'b0;  // Transaction complete
    end
    if (mem_req_fire) begin
      mem_txn_active <= 1'b1;  // Transaction started
    end
  end
end
```

**State Machine:**
```
IDLE --[mem_req_fire]--> ACTIVE --[dcache_res.valid]--> IDLE
```

**Purpose:**
- Prevent multiple cache requests for same operation
- Track pending memory operations

## D-Cache Interface

### Cache Request Generation

```systemverilog
always_comb begin
  dcache_req.valid = mem_req_fire;
  dcache_req.addr = ex_data_req_i.addr;
  dcache_req.ready = 1'b1;
  dcache_req.rw = ex_data_req_i.rw;
  dcache_req.rw_size = ex_data_req_i.rw_size;
  dcache_req.data = ex_data_req_i.data;
  dcache_req.uncached = uncached;
end
```

**Key Points:**
- `valid`: Asserted only when new request fires
- `addr`: Byte-addressed (not word-aligned)
- `uncached`: Set by PMA for uncached regions

### Cache Response Handling

```systemverilog
dcache_res_t dcache_res;  // From D-Cache

// Cache miss detection
dmiss_stall_o = mem_req_fire || (mem_txn_active && !dcache_res.valid);
```

**Stall Conditions:**
1. **New request starting**: `mem_req_fire = 1` (stall for 1 cycle minimum)
2. **Active transaction pending**: `mem_txn_active && !dcache_res.valid` (cache miss)

**No Stall:**
- Cache hit: `dcache_res.valid = 1` same cycle as `mem_req_fire`
- IDLE: No active transaction

## PMA (Physical Memory Attributes)

### Uncached Region Detection

```systemverilog
pma i_dpma (
  .addr_i(ex_data_req_i.addr),
  .uncached_o(uncached),
  .memregion_o(),  // Not used
  .grand_o()       // Not used
);
```

**Purpose:** Determine if address is in uncached memory region

**Typical Memory Map:**
| Region | Base | Size | Cached? |
|--------|------|------|---------|
| RAM | 0x80000000 | 128 MB | Yes |
| Peripherals | 0x20000000 | 256 KB | No |
| Boot ROM | 0x10000000 | 64 KB | No |

**Uncached Access:**
- Peripheral registers (UART, GPIO, etc.)
- Memory-mapped I/O
- Bypass cache, direct to Wishbone bus

## Load Data Alignment & Extension

### Byte/Halfword Selection

```systemverilog
logic [7:0] selected_byte;
logic [15:0] selected_halfword;

selected_byte = rd_data[(ex_data_req_i.addr[1:0]*8)+:8];
selected_halfword = rd_data[(ex_data_req_i.addr[1]*16)+:16];
```

**Byte Selection (addr[1:0]):**
```
addr[1:0] = 00 → Byte 0 (bits 7:0)
addr[1:0] = 01 → Byte 1 (bits 15:8)
addr[1:0] = 10 → Byte 2 (bits 23:16)
addr[1:0] = 11 → Byte 3 (bits 31:24)
```

**Halfword Selection (addr[1]):**
```
addr[1] = 0 → Halfword 0 (bits 15:0)
addr[1] = 1 → Halfword 1 (bits 31:16)
```

### Sign/Zero Extension

```systemverilog
always_comb begin
  rd_data = dcache_res.data;
  me_data_o = '0;
  
  selected_byte = rd_data[(ex_data_req_i.addr[1:0]*8)+:8];
  selected_halfword = rd_data[(ex_data_req_i.addr[1]*16)+:16];
  
  unique case (ex_data_req_i.rw_size)
    2'b01: me_data_o = ex_data_req_i.ld_op_sign ? 
                       {{24{selected_byte[7]}}, selected_byte} :  // LB (signed)
                       {24'b0, selected_byte};                    // LBU (unsigned)
    
    2'b10: me_data_o = ex_data_req_i.ld_op_sign ? 
                       {{16{selected_halfword[15]}}, selected_halfword} :  // LH (signed)
                       {16'b0, selected_halfword};                         // LHU (unsigned)
    
    2'b11: me_data_o = rd_data;  // LW (word, no extension)
    
    default: me_data_o = '0;
  endcase
end
```

**Load Instruction Handling:**

1. **LB (Load Byte, Signed):**
```
Memory: 0x80001000 = 0x12345678
lbu x1, 2(x2)  # x2 = 0x80001000, offset = 2
→ addr = 0x80001002
→ selected_byte = 0x78 (byte 2)
→ me_data_o = {{24{1'b0}}, 0x78} = 0x00000078
```

2. **LBU (Load Byte, Unsigned):**
```
Memory: 0x80001000 = 0x123456F8
lb x1, 3(x2)  # x2 = 0x80001000, offset = 3
→ addr = 0x80001003
→ selected_byte = 0xF8 (byte 3)
→ me_data_o = {{24{1'b1}}, 0xF8} = 0xFFFFFFF8 (-8 signed)
```

3. **LH (Load Halfword, Signed):**
```
Memory: 0x80001000 = 0x1234F678
lh x1, 2(x2)  # x2 = 0x80001000, offset = 2
→ addr = 0x80001002
→ selected_halfword = 0xF678
→ me_data_o = {{16{1'b1}}, 0xF678} = 0xFFFFF678
```

4. **LHU (Load Halfword, Unsigned):**
```
Memory: 0x80001000 = 0x1234F678
lhu x1, 2(x2)  # x2 = 0x80001000, offset = 2
→ addr = 0x80001002
→ selected_halfword = 0xF678
→ me_data_o = {{16{1'b0}}, 0xF678} = 0x0000F678
```

5. **LW (Load Word):**
```
Memory: 0x80001000 = 0x12345678
lw x1, 0(x2)  # x2 = 0x80001000
→ addr = 0x80001000
→ me_data_o = 0x12345678 (no extension)
```

## Store Data Handling

**Store data alignment:** Handled by D-Cache

**Store instruction flow:**
```
1. EX stage: Generate store address, prepare store data
2. MEM stage: Send request to D-Cache
3. D-Cache: Align data, perform byte-enable write
```

**Example (SB - Store Byte):**
```assembly
sb x1, 2(x2)  # x2 = 0x80001000, x1 = 0xAB
```

**D-Cache receives:**
- `addr = 0x80001002`
- `rw_size = 2'b01` (byte)
- `data = 0x000000AB`

**D-Cache action:**
- Byte lane select: addr[1:0] = 10 → Lane 2
- Byte enable: 4'b0100
- Write byte 2 of cache line/memory word

## Timing Diagram

### Cache Hit (Load)

```
Cycle:      N       N+1     N+2
            ___     ___     ___
clk:       |   |___|   |___|   |___

EX:        LW      next    next

ex_data_req.valid:  ‾‾‾‾‾‾‾\________

mem_req_fire:       ‾‾‾\___________

dcache_req.valid:   ‾‾‾\___________

dcache_res.valid:   ____/‾‾‾\______  (cache hit, same cycle)

mem_txn_active:     ____/‾‾‾\______

dmiss_stall_o:      ‾‾‾\___________  (1 cycle stall)

me_data_o:          XXXX|DATA|XXXX
```

**Latency:** 1 cycle (cache hit)

### Cache Miss (Load)

```
Cycle:      N       N+1     N+2 ... N+10    N+11
            ___     ___     ___     ___     ___
clk:       |   |___|   |___|   |...|   |___|   |___

EX:        LW      next    next ... stall   next

mem_req_fire:       ‾‾‾\___________________________

dcache_res.valid:   _____________...____/‾‾‾\______  (refill complete)

mem_txn_active:     ____/‾‾‾‾‾‾‾‾‾...‾‾‾‾\__________

dmiss_stall_o:      ‾‾‾‾‾‾‾‾‾‾‾‾‾...‾‾‾\___________  (~10 cycles)

me_data_o:          XXXXXXXXXXXX...|DATA|XXXX
```

**Latency:** ~10 cycles (cache miss + Wishbone refill)

### Store Instruction

```
Cycle:      N       N+1     N+2
            ___     ___     ___
clk:       |   |___|   |___|   |___

EX:        SW      next    next

mem_req_fire:       ‾‾‾\___________

dcache_req.valid:   ‾‾‾\___________
dcache_req.rw:      ‾‾‾\___________  (write)

dcache_res.valid:   ____/‾‾‾\______  (write ack)

dmiss_stall_o:      ‾‾‾\___________  (1 cycle stall)
```

**Latency:** 1 cycle (write-through or write-back hit)

## FENCE.I Handling

### Cache Flush Coordination

```systemverilog
input logic fe_flush_cache_i;      // From fetch stage (FENCE.I)
output logic fencei_stall_o;       // To hazard unit

// Forwarded from D-Cache
cache i_dcache (
  .flush_i(fe_flush_cache_i),
  .fencei_stall_o(fencei_stall_o)
);
```

**FENCE.I Flow:**
1. FENCE.I instruction detected (decode stage)
2. `fe_flush_cache_i = 1` → Flush I-Cache and D-Cache
3. D-Cache writes back dirty lines → `fencei_stall_o = 1`
4. After writeback complete → `fencei_stall_o = 0`
5. Pipeline resumes

**Purpose:** Ensure memory consistency after self-modifying code

## Cache Miss Stall

### Stall Logic

```systemverilog
dmiss_stall_o = mem_req_fire || (mem_txn_active && !dcache_res.valid);
```

**Stall Scenarios:**
1. **New Request (1 cycle minimum):**
   - `mem_req_fire = 1`
   - Even cache hit requires 1 cycle for address decode

2. **Cache Miss (variable latency):**
   - `mem_txn_active = 1` and `dcache_res.valid = 0`
   - Stall until refill completes

**No Stall:**
- No active request
- Cache hit: `dcache_res.valid = 1` on second cycle

## Memory Region Examples

### Cached Access (RAM)

```assembly
lui x2, 0x80000      # x2 = 0x80000000 (RAM base)
lw x1, 0(x2)         # Load from cached RAM
```

**Behavior:**
- `uncached = 0`
- Cache lookup
- On hit: 1 cycle latency
- On miss: ~10 cycles (refill from memory)

### Uncached Access (Peripheral)

```assembly
lui x2, 0x20000      # x2 = 0x20000000 (Peripheral base)
lw x1, 0x1000(x2)    # Load from UART (0x20001000)
```

**Behavior:**
- `uncached = 1`
- Bypass cache
- Direct Wishbone transaction
- Latency depends on peripheral response time

## Performance Considerations

### Cache Hit Rate

**Typical Workload:**
- **I-Cache**: 95-99% hit rate
- **D-Cache**: 85-95% hit rate

**Impact:**
- 1 cycle per hit
- ~10 cycles per miss

**Example:**
```
100 loads:
- 90 hits → 90 cycles
- 10 misses → 100 cycles
Total: 190 cycles (avg 1.9 cycles/load)

vs. No cache: 1000 cycles (avg 10 cycles/load)
```

### Critical Paths

**Address Path:**
```
ex_data_req_i.addr → PMA → dcache_req.addr → Cache tag compare
```

**Data Path (Load):**
```
Cache data array → Mux (way select) → Alignment → Sign extension → me_data_o
```

**Delay:** ~5-8 ns (FPGA)

## Verification

### Test Cases

1. **Aligned Loads:**
```assembly
lw x1, 0(x2)     # Word-aligned
lh x1, 0(x2)     # Halfword-aligned
lb x1, 0(x2)     # Byte (any alignment)
```

2. **Unaligned Loads:**
```assembly
lb x1, 1(x2)     # Byte offset 1
lh x1, 2(x2)     # Halfword offset 2
lbu x1, 3(x2)    # Byte offset 3
```

3. **Sign Extension:**
```assembly
lb x1, 0(x2)     # Signed byte (negative)
lbu x1, 0(x2)    # Unsigned byte (same address)
# Compare: x1 (lb) should be sign-extended
```

4. **Cache Miss:**
```assembly
lw x1, 0(x2)     # First access (miss)
lw x1, 0(x2)     # Second access (hit)
```

5. **Uncached Access:**
```assembly
lui x2, 0x20000  # Peripheral base
lw x1, 0(x2)     # Uncached load
```

### Assertions

```systemverilog
// Only one active transaction at a time
assert property (@(posedge clk_i) disable iff (!rst_ni)
  mem_req_fire |-> !mem_txn_active);

// Transaction cleared on cache response
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (mem_txn_active && dcache_res.valid) |=> !mem_txn_active);

// Load data valid when cache responds
assert property (@(posedge clk_i) disable iff (!rst_ni)
  dcache_res.valid |-> (me_data_o !== 'x));

// No new request while transaction active
assert property (@(posedge clk_i) disable iff (!rst_ni)
  mem_txn_active |-> !mem_req_fire);
```

## İlgili Modüller

1. **cache.sv**: Data cache implementation (8-way set associative)
2. **pma.sv**: Physical memory attributes (cached/uncached detection)
3. **execution.sv**: Provides load/store address and data
4. **writeback.sv**: Receives load data

## Gelecek İyileştirmeler

1. **Store Buffer**: Decouple stores from pipeline (reduce stall)
2. **Hardware Prefetcher**: Predict and prefetch cache lines
3. **Non-Blocking Cache**: Multiple outstanding misses
4. **Write Coalescing**: Merge multiple stores to same cache line

## Referanslar

1. RISC-V Unprivileged ISA Specification v20191213 - Chapter 2 (Load/Store)
2. "Computer Architecture: A Quantitative Approach" - Hennessy & Patterson, Appendix B (Memory Hierarchy)
3. ARM AMBA Wishbone B4 Specification

---

**Son Güncelleme:** 5 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
