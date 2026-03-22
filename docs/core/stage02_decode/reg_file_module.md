# Register File Module — Technical Documentation

## Overview

The `reg_file.sv` module is the core’s 32×32-bit general-purpose register file (GPRs). It provides dual-port asynchronous reads and a single synchronous write port. `x0` is hardwired to zero.

## RISC-V Register Conventions

### Register Set (x0-x31)

| Register | ABI Name | Description | Saver |
|----------|----------|-------------|-------|
| x0 | zero | Hardwired zero | - |
| x1 | ra | Return address | Caller |
| x2 | sp | Stack pointer | Callee |
| x3 | gp | Global pointer | - |
| x4 | tp | Thread pointer | - |
| x5-x7 | t0-t2 | Temporaries | Caller |
| x8 | s0/fp | Saved register / Frame pointer | Callee |
| x9 | s1 | Saved register | Callee |
| x10-x11 | a0-a1 | Function args / return values | Caller |
| x12-x17 | a2-a7 | Function arguments | Caller |
| x18-x27 | s2-s11 | Saved registers | Callee |
| x28-x31 | t3-t6 | Temporaries | Caller |

**Note:** ABI names are for software; hardware only sees indices `x0`–`x31`.

## Port definitions

### Input ports

| Port | Type | Description |
|------|-----|----------|
| `clk_i` | logic | System clock (synchronous writes) |
| `rst_ni` | logic | Active-low asynchronous reset |
| `rw_en_i` | logic | Write enable (from writeback) |
| `r1_addr_i` | [4:0] | Source register 1 address (rs1) |
| `r2_addr_i` | [4:0] | Source register 2 address (rs2) |
| `waddr_i` | [4:0] | Destination register (`rd`, from writeback) |
| `wdata_i` | [XLEN-1:0] | Write data (from writeback) |

### Output ports

| Port | Type | Description |
|------|-----|----------|
| `r1_data_o` | [XLEN-1:0] | Source register 1 data |
| `r2_data_o` | [XLEN-1:0] | Source register 2 data |

## Implementation

### Register Array

```systemverilog
logic [XLEN-1:0] registers[31:0];  // 32 registers, x0-x31
```

**Size:**
- 32 registers × 32 bits = 1024 bits = 128 bytes

**FPGA mapping:**
- Distributed RAM: implemented from LUTs  
- Block RAM: BRAM primitives (common for larger register files)  

### Asynchronous read logic

```systemverilog
always_comb begin : register_read
  r1_data_o = registers[r1_addr_i];
  r2_data_o = registers[r2_addr_i];
end
```

**Properties:**
- **Combinational read:** address valid in cycle *N* → data valid in cycle *N*  
- **Dual read ports:** `rs1` and `rs2` in parallel  
- **No read latency:** data is a pure combinational function of address  

**`x0` special case:**
- Reads always see 0 (array slot 0 is kept at zero)  
- After reset all entries are cleared, including `x0`  

### Synchronous write logic

```systemverilog
always_ff @(posedge clk_i) begin : register_write
  if (!rst_ni) begin
    registers <= '{default: 0};  // Reset: clear all GPRs
  end else if (rw_en_i == 1'b1 && waddr_i != 5'b0) begin
    registers[waddr_i] <= wdata_i;
  end
end
```

**Properties:**
- **Synchronous write:** updates on the clock rising edge  
- **`x0` write protection:** writes are suppressed when `waddr_i == 0`  
- **Single write port:** one register per cycle  

**Timing:**
```
Cycle N:   waddr_i=5, wdata_i=100, rw_en_i=1
Cycle N+1: registers[5] = 100 (write committed)
           r1_addr_i=5 → r1_data_o=100 (combinational read in same cycle)
```

## Register File Access Patterns

### Pattern 1: Dual Read, Single Write

```assembly
Cycle N:   add x5, x3, x4    # WB: Write x5
Cycle N+1: sub x6, x5, x7    # DE: Read x5, x7
```

**Cycle N+1 Register File Activity:**
- **Write Port**: x5 ← add result (from Cycle N writeback)
- **Read Port 1**: x5 (rs1 for sub)
- **Read Port 2**: x7 (rs2 for sub)

**Hazard:** read-after-write (RAW)  
- `x5` is not updated until the write clock edge (end of WB in the prior instruction)  
- Decode’s read is combinational (start of cycle)  
- **Fix:** bypass / forwarding in `decode`  

### Pattern 2: Independent Operations

```assembly
Cycle N:   add x5, x3, x4    # WB: Write x5
Cycle N+1: or x6, x10, x11   # DE: read x10, x11 (not x5)
```

**No Hazard:**
- Write x5, read x10/x11 → No conflict
- No forwarding required  

### Pattern 3: x0 Read

```assembly
Cycle N: add x5, x0, x4     # x0 + x4 → x5
```

**Register File:**
- `r1_addr_i = 0` → `r1_data_o = registers[0] = 0`
- `x0` always reads as 0  

### Pattern 4: x0 Write (Ignored)

```assembly
Cycle N: add x0, x3, x4     # x3 + x4 → x0 (NOP equivalent)
```

**Register File:**
- `waddr_i = 0`, `rw_en_i = 1`
- `waddr_i != 5'b0` is false → write dropped  
- `x0` stays 0  

## Timing Characteristics

### Read Timing

```
Address Valid → [Combinational Delay] → Data Valid
  t = 0           t = 1-2 ns (FPGA)       t = 1-2 ns
```

**Read Delay:**
- Distributed RAM: ~1-2 ns (LUT delay)
- Block RAM: ~2-3 ns (BRAM access time)

**Critical Path:**
```
r1_addr_i → LUT[r1_addr_i] → Mux (forwarding) → r1_data_o
```

### Write Timing

```
Clock Edge → [Setup Time] → Register Update → [Hold Time]
  t = 0        t = -0.5 ns     t = 0.5 ns       t = 0.5 ns
```

**Write Constraints:**
- Setup time: waddr_i, wdata_i, rw_en_i must be stable before clk edge
- Hold time: Must remain stable after clk edge
- Propagation: New data available next cycle

## RAW Hazard Example

### Scenario: Back-to-Back Dependent Instructions

```assembly
Cycle N:   add x5, x3, x4    # x5 = x3 + x4 (Cycle N+3 WB)
Cycle N+1: sub x6, x5, x7    # x6 = x5 - x7 (Cycle N+1 DE)
```

**Problem:**
- Cycle N+1 Decode: `r1_addr_i = 5` → Read x5 (old value)
- Cycle N+3 Writeback: `waddr_i = 5`, `wdata_i = new_value` → Write x5

**Timeline:**
```
Cycle N:   FE: add     DE: -      EX: -      MEM: -     WB: -
Cycle N+1: FE: sub     DE: add    EX: -      MEM: -     WB: -
Cycle N+2: FE: next    DE: sub    EX: add    MEM: -     WB: -
Cycle N+3: FE: next    DE: next   EX: sub    MEM: add   WB: -
Cycle N+4: FE: next    DE: next   EX: next   MEM: sub   WB: add (x5 written)
```

**Cycle N+2 (sub in Decode):**
- `r1_addr_i = 5` → `r1_data_o = registers[5]` (old value!)
- `add` has not reached writeback yet  

**Solution: Data Forwarding (decode.sv)**
```systemverilog
// decode.sv
r1_data_o = fwd_a_i ? wb_data_i : r1_data;
```

- Hazard unit: `(WB.rd == DE.rs1) && WB.rf_rw_en` → `fwd_a_i = 1`
- `r1_data_o = wb_data_i` (the `add` result)  

## Reset Behavior

```systemverilog
if (!rst_ni) begin
  registers <= '{default: 0};  // All registers = 0
end
```

**On reset:**
- All 32 architectural registers are cleared  
- `x0` = 0 (hardwired)  
- `x1`–`x31` = 0 (typical power-on choice)  

**RISC-V note:**
- Only the boot PC is mandated (`RESET_VECTOR`); GPR reset values are **implementation-defined**  
- All-zero is common for deterministic bring-up  

## Synthesis Considerations

### Distributed RAM vs Block RAM

**Distributed RAM (LUT-based):**
- **Pros:** asynchronous read, lowest latency  
- **Cons:** burns LUTs (32×32 ≈ 1024 LUT bits of storage)  
- **Typical:** Xilinx LUTRAM, Intel MLAB  

**Block RAM (BRAM):**
- **Pros:** dedicated macro, frees LUTs  
- **Cons:** usually synchronous read → +1 cycle read latency unless you pipeline around it  
- **Typical:** wide or deep register files (e.g. RV64, 64 regs)  

**For RV32I:** prefer distributed/async style if decode must read combinationally in one cycle.  

### FPGA Optimization

```systemverilog
(* ram_style = "distributed" *) logic [XLEN-1:0] registers[31:0];
```

**Or:**
```systemverilog
(* ram_style = "block" *) logic [XLEN-1:0] registers[31:0];
```

**Xilinx Vivado:**
- `distributed`: LUT RAM
- `block`: BRAM
- `auto`: let the tool choose  

## Debugging & Verification

### Waveform Analysis

```
Signal Monitoring:
- r1_addr_i, r2_addr_i   : Read addresses
- r1_data_o, r2_data_o   : Read data
- waddr_i, wdata_i       : Write address/data
- rw_en_i                : Write enable
- registers[0:31]        : All register contents
```

### Common Issues

1. **x0 Not Zero:**
   - **Symptom:** x0 reads non-zero value
   - **Cause:** Write protection logic missing (`waddr_i != 5'b0`)
   - **Fix:** Check condition in write logic

2. **RAW Hazard:**
   - **Symptom:** Incorrect operand read after write
   - **Cause:** No forwarding, old value read
   - **Fix:** Implement data forwarding in decode

3. **Write Not Happening:**
   - **Symptom:** Register value doesn't update
   - **Cause:** `rw_en_i = 0` or clock issue
   - **Fix:** Verify writeback stage control

### Assertions

```systemverilog
// x0 must remain zero in the array
assert property (@(posedge clk_i) disable iff (!rst_ni)
  registers[0] == 32'h0);

// Registers must be stable when writes are disabled
assert property (@(posedge clk_i) disable iff (!rst_ni)
  !rw_en_i |=> $stable(registers));

// Writes to x0 must be dropped (x0 stays 0)
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (rw_en_i && (waddr_i == 5'b0)) |=> (registers[0] == 32'h0));

// Read data must track address (combinational read model)
assert property (@(posedge clk_i) disable iff (!rst_ni)
  r1_data_o == registers[r1_addr_i]);
```

## Performance Impact

### Register File Access Latency

**Typical Pipeline:**
```
Cycle N:   Fetch
Cycle N+1: Decode + Register Read (combinational)
Cycle N+2: Execute
Cycle N+3: Memory
Cycle N+4: Writeback + Register Write
```

**Register File Contribution:**
- **Read:** 0 cycles (combinational, part of decode)
- **Write:** 0 cycles (parallel with other operations)

**No Performance Penalty:** Register file access doesn't stall pipeline

### Register File Size Impact

**32x32-bit = 1 KB:**
- Negligible area for modern FPGAs/ASICs
- Critical path: ~1-2 ns (well within 100-500 MHz)

**Larger Designs (RV64, 64 registers):**
- 64x64-bit = 4 KB
- May benefit from BRAM (but adds read latency)

## Test Bench Example

```systemverilog
initial begin
  // Reset
  rst_ni = 0; #10;
  rst_ni = 1; #10;
  
  // Test 1: Write to x5, read back
  waddr_i = 5;
  wdata_i = 32'h12345678;
  rw_en_i = 1;
  @(posedge clk_i);
  rw_en_i = 0;
  #1;  // Wait for combinational read
  r1_addr_i = 5;
  #1;
  assert(r1_data_o == 32'h12345678) else $error("Read mismatch!");
  
  // Test 2: Write to x0 (should be ignored)
  waddr_i = 0;
  wdata_i = 32'hDEADBEEF;
  rw_en_i = 1;
  @(posedge clk_i);
  rw_en_i = 0;
  #1;
  r1_addr_i = 0;
  #1;
  assert(r1_data_o == 32'h0) else $error("x0 not zero!");
  
  // Test 3: Dual read
  waddr_i = 10; wdata_i = 32'hAAAAAAAA; rw_en_i = 1; @(posedge clk_i);
  waddr_i = 11; wdata_i = 32'hBBBBBBBB; rw_en_i = 1; @(posedge clk_i);
  rw_en_i = 0;
  #1;
  r1_addr_i = 10;
  r2_addr_i = 11;
  #1;
  assert(r1_data_o == 32'hAAAAAAAA && r2_data_o == 32'hBBBBBBBB) 
    else $error("Dual read failed!");
end
```

## Related modules

1. **decode.sv:** drives read ports  
2. **writeback.sv:** drives the write port  
3. **hazard_unit.sv:** RAW detection and forward mux selects  

## Future improvements

1. **Register renaming:** enable out-of-order execution  
2. **More read/write ports:** superscalar issue width > 1  
3. **ECC:** soft-error protection on the array  
4. **Power gating:** clock-gate unused banks  

## References

1. RISC-V Unprivileged ISA Specification v20191213 - Chapter 2 (RV32I Base Integer Instruction Set)
2. RISC-V Calling Convention - ABI Specification
3. "Computer Organization and Design: RISC-V Edition" - Patterson & Hennessy, Chapter 4 (Register File)

---

**Last updated:** 5 December 2025  
**Author:** Kerim TURAK  
**License:** MIT License
