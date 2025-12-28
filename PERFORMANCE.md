# CoreMark Performance Optimization Guide

**Current CoreMark Score: 2.16**

---

## Current System Architecture

### Pipeline Configuration
- **5-stage in-order pipeline**: Fetch → Decode → Execute → Memory → Writeback
- **Hazard detection**: Data forwarding (EX→EX, MEM→EX, WB→EX, WB→DE)
- **Load-use hazard**: 1-cycle stall on load-to-use dependency
- **Branch resolution**: Execute stage (2-cycle penalty on misprediction)

### Branch Prediction Unit
- **Algorithm**: Tournament predictor (GShare + Bimodal hybrid)
  - **GShare Predictor**:
    - Pattern History Table (PHT): 512 entries × 2-bit saturating counters
    - Global History Register (GHR): 24 bits
    - XOR-based indexing: `index = PC[11:2] ^ GHR[9:0]`
  - **Bimodal Predictor**: 512 entries × 2-bit counters (PC-indexed)
  - **Choice/Meta Predictor**: 512 entries × 2-bit selector
- **Branch Target Buffer (BTB)**: 256 entries
- **Indirect Branch Target Cache (IBTC)**: 32 entries (for JALR)
- **Return Address Stack (RAS)**: 16-entry depth
- **Loop Predictor**: 8 entries with iteration count tracking

### Cache Hierarchy
- **Instruction Cache (I-Cache)**:
  - Size: 8 KB (65,536 bits)
  - Associativity: 4-way set associative
  - Line size: 128 bits (16 bytes)
  - Number of sets: 128
  - Replacement: Pseudo-LRU (tree-based)

- **Data Cache (D-Cache)**:
  - Size: 8 KB (65,536 bits)
  - Associativity: 4-way set associative
  - Line size: 128 bits (16 bytes)
  - Number of sets: 128
  - Write policy: Write-back with dirty bits
  - Replacement: Pseudo-LRU (tree-based)

- **Align Buffer**: 1-way (instruction alignment for compressed/uncompressed mixing)

### Prefetching
- **I-Cache Prefetcher**: **DISABLED** (PREFETCH_TYPE = 0)
  - Next-line prefetcher implemented but not active
  - Can be enabled by setting `PREFETCH_TYPE = 1` in ceres_param.sv
- **D-Cache Prefetcher**: **NOT IMPLEMENTED**
  - No hardware prefetching for data cache

### Execution Units
- **ALU**: Single-cycle for most integer operations
- **Multiplier**: Sequential (32 cycles for 32×32 multiplication using shift-and-add)
- **Divider**: Sequential (32+ cycles for division)
- **No FPU**: Floating-point not implemented

### ISA Support
- **RV32I**: Base integer instruction set
- **RV32M**: Integer multiplication and division
- **RV32C**: Compressed instructions (16-bit)
- **Zicsr**: Control and Status Register instructions
- **Machine mode only**: No user/supervisor mode

---

## Performance Improvement Recommendations

### In-Order Pipeline Optimizations

#### 1. Enhanced Branch Prediction
**Potential Gain**: 15-25% for control-flow intensive code

- **Increase BTB size**: 256 → 512 or 1024 entries
  - More branch targets cached = fewer BTB misses
  - Minimal area cost, significant performance gain for large programs

- **Deeper RAS**: 16 → 32 entries
  - Better function call/return prediction
  - Critical for deeply nested function calls

- **Larger GHR**: 24 → 32 or 48 bits
  - Capture longer branch correlation patterns
  - Useful for complex control flow

- **Perceptron predictor** (advanced):
  - Replace 2-bit counters with small neural network
  - Better accuracy on complex patterns
  - Higher area cost but superior performance

#### 2. Cache Optimizations
**Potential Gain**: 10-20% for memory-intensive workloads

- **Critical word first + Early restart**:
  - Return requested word before full cache line arrives
  - Reduces effective miss latency
  - Medium implementation complexity

- **Non-blocking cache (D-Cache)**:
  - Allow cache hits while miss is pending
  - Requires Miss Status Holding Registers (MSHRs)
  - Significant performance gain for memory-bound code

- **Victim cache**:
  - Small fully-associative cache (4-8 entries) for recently evicted lines
  - Reduces conflict misses
  - Low area cost, good performance benefit

- **Write buffer/coalescing**:
  - Buffer multiple stores and merge consecutive writes
  - Reduces memory traffic
  - Already in your list (#3)

#### 3. Advanced Prefetching
**Potential Gain**: 10-15% for regular memory access patterns

- **Stride prefetcher** (data cache):
  - Detect strided access patterns (array traversals)
  - Better than next-line for non-sequential data
  - Already in your list (#5)

- **Stream buffer**:
  - Dedicated buffer for prefetched data
  - Prevents cache pollution
  - Already in your list (#4)

- **Tagged prefetch**:
  - Track prefetch accuracy per PC
  - Disable prefetch for low-accuracy PCs
  - Reduces memory bandwidth waste

#### 4. Pipeline Enhancements
**Potential Gain**: 5-15% by reducing stalls

- **Zero-cycle ALU forwarding**:
  - Forward ALU result in same cycle (EX→EX)
  - Requires careful timing, may impact clock frequency
  - Eliminates 1-cycle dependency stalls

- **Speculative memory access**:
  - Start address calculation in Decode stage
  - Issue memory request earlier
  - Complex hazard handling required

- **Load bypass/fast forward**:
  - Dedicated path for load data forwarding
  - Reduce load-use penalty from 1 cycle to 0
  - Moderate complexity

- **Branch resolution in Decode**:
  - Move branch condition check to Decode (from Execute)
  - Reduces misprediction penalty: 2 cycles → 1 cycle
  - Requires early register file read

#### 5. Execution Unit Improvements
**Potential Gain**: Variable, depends on workload multiplication intensity

- **Fast multiplier**:
  - Replace 32-cycle sequential with Booth/Wallace tree
  - 1-3 cycle latency (pipelined)
  - Significant area increase
  - CoreMark uses multiplication moderately

- **Fast divider**:
  - Replace sequential with radix-4 or SRT algorithm
  - 8-16 cycle latency
  - Less critical for CoreMark than multiplier

#### 6. Instruction Fusion
**Potential Gain**: 5-10% for common instruction sequences

- **Macro-op fusion**:
  - Detect and fuse common pairs: `lui + addi`, `auipc + jalr`, `compare + branch`
  - Execute as single operation
  - Reduces instruction count and improves IPC

#### 7. Loop Optimization Hardware
**Potential Gain**: 5-10% for loop-heavy code (CoreMark has tight loops)

- **Loop buffer/stream**:
  - Cache decoded instructions for small loops
  - Bypass fetch/decode stages
  - Low area cost, good performance for tight loops

- **Zero-overhead loop support**:
  - Hardware loop counter and branch elimination
  - Requires ISA extension or custom implementation

#### 8. Memory Hierarchy Improvements
**Potential Gain**: 5-10%

- **Banked cache design**:
  - Split cache into multiple banks
  - Allows parallel access to different banks
  - Already in your list (#2)

- **Larger cache sizes**:
  - 8 KB → 16 KB or 32 KB
  - Reduces capacity misses
  - Area/power cost consideration

- **Higher associativity**:
  - 4-way → 8-way
  - Reduces conflict misses
  - Diminishing returns, increased latency

#### 9. Compiler Optimizations
**Potential Gain**: 10-20% (no hardware change required)

- **Aggressive optimization flags**:
  - `-O3 -march=rv32imc -mabi=ilp32`
  - `-funroll-loops` for loop-intensive code
  - `-finline-functions` for small functions

- **Link-time optimization (LTO)**:
  - Whole-program optimization
  - Better inlining and dead code elimination

- **Profile-guided optimization (PGO)**:
  - Optimize based on profiling data
  - Better code layout and branch hints

- Already in your list (#6)

#### 10. Trace Cache
**Potential Gain**: 10-15% for control-flow intensive code

- **Store decoded instruction traces**:
  - Cache post-decode instruction sequences
  - Bypass fetch and decode stages entirely
  - Effective for code with branches

- Already in your list (#1)

---

## Quick Wins (Easiest Implementation)

1. **Enable I-Cache prefetcher** (set `PREFETCH_TYPE = 1`, zero code change)
2. **Increase BTB/RAS size** (parameter change only)
3. **Tune GHR size** (parameter change + minor logic)
4. **Compiler optimization flags** (no hardware change)
5. **Critical word first** (cache modification, moderate complexity)

---

## High-Impact Optimizations (Best ROI)

### Immediate Priorities (Recommended Implementation Order)

1. **Enable I-Cache prefetcher** (PREFETCH_TYPE = 1)
   - **Effort**: Trivial (parameter change)
   - **Gain**: 5-10% for instruction-fetch bound code
   - **Risk**: None (already implemented and tested)

2. **Store Buffer Implementation**
   - **Effort**: Medium (new module + integration)
   - **Gain**: 10-15% for store-heavy workloads
   - **Design**:
     - 4-8 entry FIFO buffer for pending stores
     - Coalesce consecutive/overlapping writes
     - Allow loads to bypass pending stores (with address matching)
     - Drain to D-Cache when buffer full or fence instruction
   - **Benefits**:
     - Reduces store-induced pipeline stalls
     - Merges multiple stores to same cache line
     - Improves memory bandwidth utilization

3. **Non-blocking L2 Cache**
   - **Effort**: High (new cache level + arbiter)
   - **Gain**: 15-25% for working sets >16 KB
   - **Design**:
     - Size: 64 KB - 128 KB (unified I/D)
     - Associativity: 8-way or 16-way
     - Non-blocking: 2-4 MSHRs (Miss Status Holding Registers)
     - Write-back policy with victim buffer
     - Inclusive with L1 caches
   - **Benefits**:
     - Absorbs L1 misses with lower latency than main memory
     - Non-blocking allows cache hits during miss handling
     - Larger capacity improves working set coverage

4. **Branch predictor improvements** (BTB/RAS/GHR sizing)
   - **Effort**: Low (parameter tuning)
   - **Gain**: 10-20%

5. **Fast multiplier** (Wallace tree or Booth encoding)
   - **Effort**: Medium-High
   - **Gain**: Variable (depends on multiplication intensity)

6. **Stride prefetcher for data cache**
   - **Effort**: Medium (new prefetcher module)
   - **Gain**: 10-15% for array-heavy code

7. **Compiler aggressive optimization + LTO**
   - **Effort**: Low (compiler flags)
   - **Gain**: 10-20%

---

## Advanced Techniques (Higher Complexity)

1. **Trace cache**
2. **Instruction fusion**
3. **Zero-cycle ALU forwarding**
4. **Loop buffer**
5. **Speculative memory access**

---

## Measurement and Profiling

Before optimization, measure:
- **Branch misprediction rate**: Target <5% for CoreMark
- **Cache miss rate**:
  - I-Cache: Target <1%
  - D-Cache: Target <3-5%
- **CPI (Cycles Per Instruction)**: Target <1.5 for in-order pipeline
- **Stall cycles breakdown**:
  - Load-use hazards
  - Cache misses
  - Branch mispredictions

Use hardware performance counters or simulation to identify bottlenecks.

---

## Notes

- **Area vs. Performance tradeoff**: Some optimizations (e.g., larger caches, faster multipliers) significantly increase area
- **Power consideration**: Aggressive prefetching and larger structures consume more power
- **Clock frequency impact**: Zero-cycle forwarding may increase critical path
- **CoreMark characteristics**:
  - Moderate branch density
  - Small working set (fits in 8 KB cache)
  - Tight loops with predictable branches
  - Moderate use of multiplication

---

## Original Suggestions

1. Trace cache can improve our performance
2. Non-blocking banked cache can improve performance
3. Use write buffer for data cache
4. Prefetching and stream buffer
5. Data prefetch
6. Compiler optimizations
