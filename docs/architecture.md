---
title: "Architecture"
description: "Detailed architectural design documentation for the Level RISC-V processor"
date: 2025-12-01
draft: false
weight: 100
---

# Level RISC-V Processor — Architecture

This documentation describes the detailed architectural design of the Level RISC-V processor. Each major block is covered in its own subsection.

---

## 1. High-Level Architecture Summary

Level RISC-V is a lightweight, modular 32-bit RISC-V processor core. It implements RV32IMC and supports CSR (Control and Status Register) and FENCE operations.

### Key Features

- **ISA**: RV32IMC (integer base + multiply/divide + compressed)
- **Register file**: 32 × 32-bit
- **Memory model**: Von Neumann (unified memory)
- **Pipeline**: 5-stage
- **Exception handling**: Parametric exception priority
- **Performance**: ~1 DMIPS/MHz

### Content Map

```
┌─────────────────────────────────────────────┐
│         Fetch Stage (IF)                    │
│  Instruction Memory → PC Management        │
└────────────────┬────────────────────────────┘
                 │
┌────────────────▼────────────────────────────┐
│      Decode Stage (ID)                      │
│  Instruction Decoding → Register Read       │
└────────────────┬────────────────────────────┘
                 │
┌────────────────▼────────────────────────────┐
│     Execute Stage (EX)                      │
│  ALU, Multiplier, Branch Logic              │
└────────────────┬────────────────────────────┘
                 │
┌────────────────▼────────────────────────────┐
│      Memory Stage (MEM)                     │
│  Data Cache Access, Load/Store              │
└────────────────┬────────────────────────────┘
                 │
┌────────────────▼────────────────────────────┐
│     Write-Back Stage (WB)                   │
│  Register File Update                       │
└─────────────────────────────────────────────┘
```

---

## 2. Fetch Stage (IF - Instruction Fetch)

### 2.1 Overview

The fetch stage owns Program Counter (PC) management and brings instructions from instruction memory.

**Path**: `rtl/core/stage01_fetch/`

### 2.2 Main Blocks

#### Program Counter (PC) Management

```systemverilog
// PC update
always_comb begin
    if (rst) begin
        next_pc = PC_RESET_VALUE;  // Default: 0x8000_0000
    end else if (is_branch_taken) begin
        next_pc = branch_target;
    end else if (is_jump) begin
        next_pc = jump_target;
    end else if (exception_occurred) begin
        next_pc = exception_vector;
    end else begin
        next_pc = pc + increment;  // increment = 2 (RV32C) or 4 (RV32I)
    end
end
```

**PC constants**:
- `PC_RESET_VALUE`: 0x8000_0000 (boot address)
- `PC_ALIGN`: 2-byte alignment for RV32C, 4-byte for RV32I

#### Instruction Buffer (I-Buffer)

The fetch stage includes an instruction buffer that:
- Buffers compressed (16-bit) and normal (32-bit) instructions
- Holds instructions across pipeline stalls
- Waits on cache miss

```systemverilog
typedef struct {
    logic [31:0] instr;      // 32-bit instruction (aligned)
    logic valid;             // Valid bit
    logic [31:0] pc;         // Program Counter
    logic [4:0] exc_type;    // Exception type
} instr_buffer_t;
```

#### Exception Detection @ Fetch

Exceptions detected in fetch:

| Exception | Cause | Code |
|-----------|-------|------|
| Debug Breakpoint | `tdata1[2] == 1'b1 && PC == tdata2` | 1 |
| Instruction Misaligned | PC[0]!=0 for RV32C or PC[1:0]!=0 for RV32I | 0 |
| Instruction Access Fault | Memory access error (grant signal) | 1 |
| Illegal Instruction | Undefined opcode | 2 |

### 2.3 Parametric Exception Priority

Level uses a parametric exception priority scheme aligned with the RISC-V Privileged Specification.

```systemverilog
// Exception priority definitions (level_param.sv)
typedef enum logic [4:0] {
    PRIORITY_1,           // Highest (checked first)
    PRIORITY_2,
    PRIORITY_3,
    PRIORITY_4,
    PRIORITY_5,
    PRIORITY_6,
    PRIORITY_7,           // Lowest (checked last)
    PRIORITY_DISABLED     // Exception disabled
} exc_priority_t;

// Default RISC-V spec-aligned priorities:
localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_1;
localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_2;
localparam exc_priority_t EXC_PRIORITY_INSTR_ACCESS_FAULT = PRIORITY_3;
localparam exc_priority_t EXC_PRIORITY_ILLEGAL = PRIORITY_4;
localparam exc_priority_t EXC_PRIORITY_EBREAK = PRIORITY_5;
localparam exc_priority_t EXC_PRIORITY_ECALL = PRIORITY_6;
```

**Configuration file**: `rtl/include/exception_priority.svh`

Alternative configurations:
- `EXCEPTION_PRIORITY_DEBUG_FIRST` (default — RISC-V spec aligned)
- `EXCEPTION_PRIORITY_MISALIGNED_FIRST` (testing)
- `EXCEPTION_PRIORITY_ILLEGAL_FIRST` (testing)
- `EXCEPTION_PRIORITY_DISABLED_DEBUG` (debug disabled)

### 2.4 Priority Check Function

```systemverilog
function automatic logic check_exc_priority(
    input exc_priority_t exc_pri,
    input exc_priority_t min_pri
);
    // TRUE if exc_pri is higher than or equal to min_pri and not disabled
    return (exc_pri <= min_pri) && (exc_pri != PRIORITY_DISABLED);
endfunction
```

### 2.5 Exception Priority Selection Logic

```systemverilog
// All exceptions are detected
has_debug_breakpoint = fetch_valid && tdata1[2] && (pc == tdata2);
has_instr_misaligned = fetch_valid && (misa_c ? pc[0] : (pc[1:0] != 2'b00));
has_instr_access_fault = fetch_valid && !grand;
has_illegal_instr = fetch_valid && illegal_instr && buff_res.valid;

// Parametric priority-based selection
if (has_debug_breakpoint && check_exc_priority(
    EXC_PRIORITY_DEBUG_BREAKPOINT, PRIORITY_7)) begin
    exc_type = BREAKPOINT;
end else if (has_instr_misaligned && check_exc_priority(
    EXC_PRIORITY_INSTR_MISALIGNED, PRIORITY_7)) begin
    exc_type = INSTR_MISALIGNED;
end else if (has_instr_access_fault && check_exc_priority(
    EXC_PRIORITY_INSTR_ACCESS_FAULT, PRIORITY_7)) begin
    exc_type = INSTR_ACCESS_FAULT;
// ... other exceptions
end
```

---

## 3. Decode Stage (ID - Instruction Decode)

### 3.1 Overview

The decode stage decodes the instruction from the instruction buffer and reads the register file.

**Path**: `rtl/core/stage02_decode/`

### 3.2 Instruction Decoder

The decoder splits a 32-bit (or compressed 16-bit) instruction into the following fields:

```systemverilog
typedef struct {
    logic [6:0] opcode;      // 7-bit opcode
    logic [4:0] rd;          // Destination register
    logic [4:0] rs1;         // Source register 1
    logic [4:0] rs2;         // Source register 2
    logic [11:0] imm12;      // 12-bit immediate
    logic [31:0] imm32;      // 32-bit immediate (sign-extended)
    instr_type_t instr_type; // Instruction type (add, sub, ld, sd, etc.)
    logic valid;             // Valid bit
} decoded_instr_t;
```

### 3.3 Instruction Categories

Instruction families supported by Level RISC-V:

#### Integer arithmetic (RV32I)
- **ADD/SUB**: Add/subtract
- **AND/OR/XOR**: Bitwise ops
- **SLL/SRL/SRA**: Shifts
- **SLT/SLTU**: Compare

#### Multiply/divide (RV32M)
- **MUL/MULH/MULHSU/MULHU**: Multiply
- **DIV/DIVU**: Divide
- **REM/REMU**: Remainder

#### Load/store (memory)
- **LW/LH/LB/LHU/LBU**: Loads
- **SW/SH/SB**: Stores

#### Branch and jump
- **BEQ/BNE/BLT/BGE/BLTU/BGEU**: Conditional branches
- **JAL/JALR**: Unconditional jumps (with link)

#### System
- **ECALL/EBREAK**: System traps
- **FENCE/FENCE.I**: Memory barriers
- **CSR***: CSR access

### 3.4 Register File

Thirty-two 32-bit registers:
- `x0`–`x31`: General-purpose
- `x0 (zero)`: Hard-wired zero (writes ignored)
- `x1 (ra)`: Return Address
- `x2 (sp)`: Stack Pointer

```systemverilog
// Register file
logic [31:0] reg_file [0:31];

// Dual-port read (two reads same cycle)
always @(*) begin
    read_data1 = (rs1 == 5'b0) ? 32'b0 : reg_file[rs1];
    read_data2 = (rs2 == 5'b0) ? 32'b0 : reg_file[rs2];
end

// Write (from WB stage)
always @(posedge clk) begin
    if (wr_en && (wr_addr != 5'b0)) begin
        reg_file[wr_addr] <= wr_data;
    end
end
```

### 3.5 Hazard Detection

The decode stage detects data hazards and asserts stalls.

```systemverilog
// Data hazard: previous instruction will write rd and
// this instruction uses rs1 or rs2
logic data_hazard;
assign data_hazard = (prev_rd_wr_en && 
                      ((prev_rd == rs1 && rs1 != 5'b0) ||
                       (prev_rd == rs2 && rs2 != 5'b0)));

// Pipeline stall when needed
assign stall = data_hazard || memory_stall;
```

---

## 4. Execute Stage (EX - Execution)

### 4.1 Overview

The execute stage contains the ALU (arithmetic logic unit), multiplier, and branch logic.

**Path**: `rtl/core/stage03_execute/`

### 4.2 ALU (Arithmetic Logic Unit)

The ALU performs basic arithmetic and logical operations.

```systemverilog
// ALU operations
typedef enum logic [3:0] {
    ALU_ADD,      // Add
    ALU_SUB,      // Subtract
    ALU_AND,      // AND
    ALU_OR,       // OR
    ALU_XOR,      // XOR
    ALU_SLL,      // Logical Left Shift
    ALU_SRL,      // Logical Right Shift
    ALU_SRA,      // Arithmetic Right Shift
    ALU_SLT,      // Set if Less Than
    ALU_SLTU,     // Set if Less Than Unsigned
    ALU_NOOP      // No Operation
} alu_op_t;

// ALU Implementation
always_comb begin
    case (alu_op)
        ALU_ADD:  alu_result = operand1 + operand2;
        ALU_SUB:  alu_result = operand1 - operand2;
        ALU_AND:  alu_result = operand1 & operand2;
        ALU_OR:   alu_result = operand1 | operand2;
        ALU_XOR:  alu_result = operand1 ^ operand2;
        ALU_SLL:  alu_result = operand1 << operand2[4:0];
        ALU_SRL:  alu_result = operand1 >> operand2[4:0];
        ALU_SRA:  alu_result = $signed(operand1) >>> operand2[4:0];
        ALU_SLT:  alu_result = ($signed(operand1) < $signed(operand2)) ? 1 : 0;
        ALU_SLTU: alu_result = (operand1 < operand2) ? 1 : 0;
        default:  alu_result = 32'b0;
    endcase
end
```

**ALU characteristics**:
- 32-bit operands
- Combinational (1 cycle)
- Flags: zero, carry, overflow, sign

### 4.3 Multiplier (RV32M)

Level implements the M extension (multiply/divide).

#### Multiplier design

```systemverilog
// Radix-4 multiplier
// 32×32 → 64 bit
// 2 cycles

module multiplier_radix4 (
    input clk, rst,
    input logic [31:0] multiplicand,
    input logic [31:0] multiplier,
    input logic start,
    
    output logic [63:0] product,
    output logic valid
);

// Internal: 16 steps (32 bits / 2)
// 2 bits processed per step
```

**Multiplier characteristics**:
- Radix-4 algorithm
- 2-cycle latency
- Signed and unsigned

#### Divider design

```systemverilog
// Non-restoring division
// 32 ÷ 32 → Q + R
// 34 cycles (iterative)

module divider (
    input clk, rst,
    input logic [31:0] dividend,
    input logic [31:0] divisor,
    input logic start,
    
    output logic [31:0] quotient,
    output logic [31:0] remainder,
    output logic valid,
    output logic div_by_zero
);
```

**Divider characteristics**:
- Non-restoring division
- 34-cycle latency (32 bits + overhead)
- Divide-by-zero detection
- Signed and unsigned

### 4.4 Branch Logic

```systemverilog
// Branch conditions
logic branch_taken;

always_comb begin
    case (branch_type)
        BEQ:  branch_taken = (operand1 == operand2);
        BNE:  branch_taken = (operand1 != operand2);
        BLT:  branch_taken = ($signed(operand1) < $signed(operand2));
        BGE:  branch_taken = ($signed(operand1) >= $signed(operand2));
        BLTU: branch_taken = (operand1 < operand2);
        BGEU: branch_taken = (operand1 >= operand2);
        default: branch_taken = 1'b0;
    endcase
end

// Branch target
assign branch_target = pc + imm;
```

### 4.5 Jump Logic

```systemverilog
// JAL (Jump and Link)
logic jal_taken;
logic [31:0] jal_target;

assign jal_taken = (instr_type == JAL);
assign jal_target = pc + imm;
assign link_address = pc + 4;  // Return address

// JALR (Jump and Link Register)
logic jalr_taken;
logic [31:0] jalr_target;

assign jalr_taken = (instr_type == JALR);
assign jalr_target = (reg_data[rs1] + imm) & ~32'h1;  // LSB = 0
```

---

## 5. Memory Stage (MEM - Memory Access)

### 5.1 Overview

The memory stage handles data memory access for loads and stores.

**Path**: `rtl/core/stage04_memory/`

### 5.2 Data Cache Architecture

```
┌─────────────────────────────────────┐
│      Data Cache (DC)                │
│  - Cache Line: 128 bits (16 bytes)  │
│  - Associativity: 2-way             │
│  - Sets: 128                         │
│  - Total Size: 4 KB                 │
└─────────────────────────────────────┘
         │                │
         ▼                ▼
┌──────────────────────────────────────┐
│      Physical Memory Interface       │
│  - AXI4 Protocol (32-bit)            │
│  - Master Port to Main Memory        │
└──────────────────────────────────────┘
```

**Cache parameters**:

| Parameter | Value | Description |
|-----------|-------|-------------|
| CACHE_LINE_SIZE | 16B (128b) | Cache line size |
| CACHE_SETS | 128 | Number of sets |
| CACHE_WAYS | 2 | 2-way associative |
| CACHE_SIZE | 4KB | Total cache size |
| CACHE_POLICY | LRU | Replacement: least recently used |

### 5.3 Load Operations

```systemverilog
// Load opcodes
typedef enum logic [2:0] {
    LOAD_BYTE,           // LB (8-bit signed)
    LOAD_BYTE_UNSIGNED,  // LBU (8-bit unsigned)
    LOAD_HALF,           // LH (16-bit signed)
    LOAD_HALF_UNSIGNED,  // LHU (16-bit unsigned)
    LOAD_WORD            // LW (32-bit)
} load_type_t;

// Load flow
always @(posedge clk) begin
    // 1. Address: addr = rs1 + imm
    mem_addr = reg_data[rs1] + sign_extend(imm);
    
    // 2. Cache lookup
    if (cache_hit) begin
        load_data = cache_data;
    end else begin
        // Miss: fetch from main memory
        mem_req_valid = 1'b1;
        wait_memory = 1'b1;
    end
    
    // 3. Sign extension or zero padding
    case (load_type)
        LOAD_BYTE: rd_data = sign_extend_8(load_data[7:0]);
        LOAD_HALF: rd_data = sign_extend_16(load_data[15:0]);
        LOAD_WORD: rd_data = load_data[31:0];
    endcase
end
```

### 5.4 Store Operations

```systemverilog
// Store opcodes
typedef enum logic [1:0] {
    STORE_BYTE,  // SB (8-bit)
    STORE_HALF,  // SH (16-bit)
    STORE_WORD   // SW (32-bit)
} store_type_t;

// Store flow
always @(posedge clk) begin
    // 1. Address calculation
    mem_addr = rs1 + sign_extend(imm);
    
    // 2. Data preparation (alignment)
    case (store_type)
        STORE_BYTE: begin
            write_enable = 4'b0001 << mem_addr[1:0];
            write_data = {4{rs2_data[7:0]}};
        end
        STORE_HALF: begin
            write_enable = 4'b0011 << {mem_addr[1], 1'b0};
            write_data = {2{rs2_data[15:0]}};
        end
        STORE_WORD: begin
            write_enable = 4'b1111;
            write_data = rs2_data;
        end
    endcase
    
    // 3. Cache update
    if (cache_hit) begin
        cache_write(mem_addr, write_data, write_enable);
    end else begin
        // Write-through to main memory
        mem_write_req = 1'b1;
    end
end
```

### 5.5 Memory Alignment

```systemverilog
// Misalignment Detection
logic misaligned;

always_comb begin
    case (load_type)
        LOAD_HALF: misaligned = mem_addr[0];
        LOAD_WORD: misaligned = (mem_addr[1:0] != 2'b00);
        default:   misaligned = 1'b0;
    endcase
end

// Misaligned Exception
assign exc_data_misaligned = misaligned && mem_valid;
```

### 5.6 Cache Control

```systemverilog
// Cache write-through policy
typedef enum logic [1:0] {
    CACHE_DIRTY,     // Written but not in memory
    CACHE_CLEAN,     // Coherent with memory
    CACHE_INVALID    // Invalid
} cache_state_t;

// LRU Replacement
logic [CACHE_WAYS-1:0] lru;  // Least recently used way

// Cache Hit/Miss
assign cache_hit = (cache_tag == mem_addr[31:7]) && cache_valid;
assign cache_miss = ~cache_hit && mem_req_valid;
```

---

## 6. Write-Back Stage (WB - Write-Back)

### 6.1 Overview

The write-back stage writes computed results back to the register file.

**Path**: `rtl/core/stage05_writeback/`

### 6.2 Write-Back Control

```systemverilog
// Write-back sources
typedef enum logic [1:0] {
    WB_ALU,       // ALU result
    WB_MEMORY,    // Load result
    WB_PC_NEXT,   // PC+4 (JAL/JALR)
    WB_CSR        // CSR read data
} wb_source_t;

// Write-back multiplexer
always_comb begin
    case (wb_source)
        WB_ALU:     wb_data = alu_result;
        WB_MEMORY:  wb_data = memory_read_data;
        WB_PC_NEXT: wb_data = pc + 4;
        WB_CSR:     wb_data = csr_data;
        default:    wb_data = 32'b0;
    endcase
end

// Register Write
always @(posedge clk) begin
    if (wb_enable && (wb_rd != 5'b0)) begin
        reg_file[wb_rd] <= wb_data;
    end
end
```

### 6.3 Forward Detection

Forwarding (bypass) reduces data hazards:

```systemverilog
// EX forward: execute → decode
logic ex_forward_valid;
assign ex_forward_valid = (ex_rd_wr_en && 
                           ((ex_rd == id_rs1 && id_rs1 != 5'b0) ||
                            (ex_rd == id_rs2 && id_rs2 != 5'b0)));

// MEM forward: memory → decode
logic mem_forward_valid;
assign mem_forward_valid = (mem_rd_wr_en && 
                            ((mem_rd == id_rs1 && id_rs1 != 5'b0) ||
                             (mem_rd == id_rs2 && id_rs2 != 5'b0)));

// WB forward: write-back → decode (less common)
logic wb_forward_valid;
assign wb_forward_valid = (wb_enable && 
                           ((wb_rd == id_rs1 && id_rs1 != 5'b0) ||
                            (wb_rd == id_rs2 && id_rs2 != 5'b0)));
```

---

## 7. Control & Status Registers (CSR)

### 7.1 Supported CSRs

Level supports the following CSRs (representative set):

#### User-level CSRs
| CSR | Address | Description |
|---------|-------|----------|
| FCSR | 0x001 | Floating-Point Control |
| FFLAGS | 0x004 | FP Exception Flags |
| FRM | 0x005 | FP Rounding Mode |
| UTIME | 0xC00 | User Timer (Read-only) |

#### Supervisor-level CSRs
| CSR | Address | Description |
|---------|-------|----------|
| SSTATUS | 0x100 | Supervisor Status |
| SIE | 0x104 | Supervisor Interrupt Enable |
| STVEC | 0x105 | Supervisor Trap Vector |
| SCAUSE | 0x142 | Supervisor Cause |
| STVAL | 0x143 | Supervisor Trap Value |

#### Machine-level CSRs
| CSR | Address | Description |
|---------|-------|----------|
| MSTATUS | 0x300 | Machine Status |
| MISA | 0x301 | Machine ISA |
| MIE | 0x304 | Machine Interrupt Enable |
| MTVEC | 0x305 | Machine Trap Vector |
| MCAUSE | 0x342 | Machine Cause |
| MTVAL | 0x343 | Machine Trap Value |
| MCYCLE | 0xB00 | Cycle Counter |
| MINSTRET | 0xB02 | Instruction Counter |

### 7.2 CSR Read/Write

```systemverilog
// CSR operations
typedef enum logic [2:0] {
    CSR_RW,      // Read-Write
    CSR_RS,      // Read-Set
    CSR_RC,      // Read-Clear
    CSR_RWI,     // Read-Write Immediate
    CSR_RSI,     // Read-Set Immediate
    CSR_RCI      // Read-Clear Immediate
} csr_op_t;

// CSR access
always @(posedge clk) begin
    case (csr_op)
        CSR_RW: begin
            read_val = csr_file[csr_addr];
            csr_file[csr_addr] = write_val;
        end
        CSR_RS: begin
            read_val = csr_file[csr_addr];
            csr_file[csr_addr] = csr_file[csr_addr] | write_val;
        end
        CSR_RC: begin
            read_val = csr_file[csr_addr];
            csr_file[csr_addr] = csr_file[csr_addr] & ~write_val;
        end
    endcase
end
```

---

## 8. Exception and Interrupt Handling

### 8.1 Exception Types

```systemverilog
typedef enum logic [3:0] {
    // Synchronous Exceptions
    INSTR_MISALIGNED = 4'h0,      // Instruction address misaligned
    INSTR_ACCESS_FAULT = 4'h1,    // Instruction access fault
    ILLEGAL_INSTR = 4'h2,          // Illegal instruction
    BREAKPOINT = 4'h3,             // Breakpoint (ebreak)
    LOAD_MISALIGNED = 4'h4,        // Load address misaligned
    LOAD_ACCESS_FAULT = 4'h5,      // Load access fault
    STORE_MISALIGNED = 4'h6,       // Store address misaligned
    STORE_ACCESS_FAULT = 4'h7,     // Store access fault
    ECALL_U = 4'h8,                // Environment call (User)
    ECALL_S = 4'h9,                // Environment call (Supervisor)
    ECALL_M = 4'hB,                // Environment call (Machine)
    INSTR_PAGE_FAULT = 4'hC,       // Instruction page fault
    LOAD_PAGE_FAULT = 4'hD,        // Load page fault
    STORE_PAGE_FAULT = 4'hF        // Store page fault
} exception_code_t;
```

### 8.2 Exception Handling Flow

```
    ┌─────────────────────┐
    │ Exception detect    │
    │ (any stage)         │
    └──────────┬──────────┘
               │
    ┌──────────▼──────────┐
    │ Exception priority  │
    │ (parametric)        │
    └──────────┬──────────┘
               │
    ┌──────────▼──────────┐
    │ Pipeline flush      │
    │ (younger stages)    │
    └──────────┬──────────┘
               │
    ┌──────────▼──────────┐
    │ CSR updates         │
    │ - MCAUSE            │
    │ - MTVAL             │
    │ - MEPC              │
    └──────────┬──────────┘
               │
    ┌──────────▼──────────┐
    │ Handler fetched     │
    │ (from MTVEC)        │
    └──────────┬──────────┘
               │
    ┌──────────▼──────────┐
    │ PC ← handler        │
    │ Pipeline restarted  │
    └─────────────────────┘
```

### 8.3 Exception Priority Example

**Scenario**: Three exceptions at once

```
State:
- Debug Breakpoint (EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_1)
- Instruction Misaligned (EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_2)
- Illegal Instruction (EXC_PRIORITY_ILLEGAL = PRIORITY_4)

Priority check order:
1. Debug breakpoint: check_exc_priority(PRIORITY_1, PRIORITY_7) → TRUE ✓
   → Debug breakpoint wins

**Result**: Debug breakpoint is taken (highest priority)
```

---

## 9. Memory System

### 9.1 Memory Map

```
┌──────────────────────────────────┐
│   Physical Address Space         │
│   (32-bit: 0x0 - 0xFFFFFFFF)     │
├──────────────────────────────────┤
│ 0x0000_0000 - 0x0000_FFFF        │ 64 KB RAM (On-Chip)
├──────────────────────────────────┤
│ 0x1000_0000 - 0x1000_FFFF        │ Peripherals (UART, etc)
├──────────────────────────────────┤
│ 0x2000_0000 - 0x7FFF_FFFF        │ External Memory
├──────────────────────────────────┤
│ 0x8000_0000 - 0xFFFF_FFFF        │ ROM / Boot Region
└──────────────────────────────────┘
```

### 9.2 Memory Access Latency

| Memory | Latency | Cache | Notes |
|-------------|---------|-------|-------|
| L1 I-Cache | 1 cycle | Hit | On-chip, fast |
| L1 D-Cache | 1 cycle | Hit | On-chip, fast |
| L2 cache (none) | — | — | Not in this design |
| Main Memory | 10+ cycle | Miss | AXI4 via fabric |
| Peripherals | Variable | None | UART vs real devices |

### 9.3 Memory Ordering (FENCE)

```systemverilog
// FENCE handling
typedef struct {
    logic predecessor_read;    // PI (Predecessor Instruction)
    logic predecessor_write;   // PW
    logic successor_read;      // SI (Successor Instruction)
    logic successor_write;     // SW
} fence_bits_t;

// FENCE pipeline stall
always @(posedge clk) begin
    if (fence_instruction) begin
        pipeline_stall = 1'b1;
        // Wait until all prior instructions complete
        wait_for_completion = 1'b1;
    end
end
```

---

## 10. Debug and Trace

### 10.1 Trace Port

Level can emit trace information for simulation and debug:

```systemverilog
// Trace Signals
typedef struct {
    logic clk;
    logic rst;
    logic [31:0] pc;
    logic [31:0] instr;
    logic instr_valid;
    logic [4:0] rd;
    logic [31:0] rd_data;
    logic rd_wr_en;
    logic [31:0] mem_addr;
    logic [31:0] mem_data;
    logic mem_valid;
    logic mem_wr_en;
    logic [31:0] csr_addr;
    logic [31:0] csr_data;
    logic csr_wr_en;
    logic [4:0] exc_type;
    logic exc_valid;
} trace_t;
```

### 10.2 Debug Triggers (Trigger Module)

```systemverilog
// Debug trigger control (tdata1)
typedef struct {
    logic type_select;     // Trigger type
    logic dmode;           // Debug mode
    logic [3:0] match_type; // Match criteria
    logic execute;         // Execute trigger
    logic store;           // Store trigger
    logic load;            // Load trigger
} trigger_control_t;

// Debug Trigger Data (tdata2)
logic [31:0] tdata2;  // Breakpoint address

// Breakpoint detect
logic breakpoint = tdata1[2] && (pc == tdata2);
```

---

## 11. Performance

### 11.1 Pipeline Throughput

```
Ideal case (no stalls):
    1 instruction per cycle (1 IPC)
    
With Hazards:
    - Load-use: +1 cycle stall
    - Branch misprediction: +3 cycle penalty
    - DIV: +34 cycle latency
    - MUL: +2 cycle latency
```

### 11.2 Operation Latency

| Operation | Latency | Notes |
|-------|---------|-------|
| ADD/SUB/AND/OR/XOR/SLL/SRL/SRA | 2 | 1 EX + 1 WB |
| SLT/SLTU | 2 | 1 EX + 1 WB |
| LW/LH/LB | 4 | 1 MEM hit + 1 extra + 2 WB |
| SW/SH/SB | 1 | 1 MEM |
| BEQ/BNE/etc | 3 | 1 EX + 2 fetch delay |
| JAL/JALR | 1 | Direct address computation |
| MUL/MULH/etc | 4 | 2 MUL + 2 WB |
| DIV/DIVU | 36 | 34 DIV + 2 WB |
| CSR Operations | 2 | 1 EX + 1 WB |

### 11.3 DMIPS

```
Level RISC-V @ 1 MHz:
    ~1 DMIPS/MHz
    
Example:
    @ 100 MHz: ~100 DMIPS
    @ 200 MHz: ~200 DMIPS
```

---

## 12. Parametric Design

### 12.1 Key Parameters

**File**: `rtl/pkg/level_param.sv`

```systemverilog
// Instruction Set Extensions
localparam bit ENABLE_RV32M = 1'b1;  // Multiply/Divide
localparam bit ENABLE_RV32C = 1'b1;  // Compressed

// Memory Parameters
localparam int INSTR_MEM_SIZE = 32'h10000;   // 64 KB
localparam int DATA_MEM_SIZE = 32'h4000;     // 16 KB

// Cache Parameters
localparam int CACHE_LINE_SIZE = 16;         // bytes
localparam int CACHE_SETS = 128;
localparam int CACHE_WAYS = 2;

// Exception Priority (Configurable)
localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_1;
localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_2;
// ... more
```

### 12.2 Customization

Alternative configurations are defined in `rtl/include/exception_priority.svh`:

```systemverilog
// Example: alternative priority configuration
`ifdef EXCEPTION_PRIORITY_MISALIGNED_FIRST
    localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_1;  // Swap
    localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_2;
`else
    // Default RISC-V spec aligned
    localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_1;
    localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_2;
`endif
```

---

## 13. Testability

### 13.1 DPI-C Interface

Level exposes a DPI-C interface for test harnesses written in C.

```systemverilog
// DPI-C Export Functions
export "DPI-C" function get_register_value;
export "DPI-C" function set_register_value;
export "DPI-C" function get_memory_value;
export "DPI-C" function set_memory_value;
export "DPI-C" function get_csr_value;
```

### 13.2 VCD Dump

```bash
# Generate VCD (waveform.vcd)
make wave

# Open VCD in GTKWave
gtkwave build/work/waveform.vcd &
```

### 13.3 Test Coverage

```bash
# Generate coverage report
make coverage

# Open HTML report
firefox build/logs/coverage/index.html &
```

---

## 14. Debugging

### 14.1 Breakpoint Setup

```
Machine debug interface registers:
1. tdata1 ← breakpoint control
2. tdata2 ← breakpoint address
3. Debugger takes trap at this address
```

### 14.2 Trace Analysis

```bash
# Capture trace from simulation
make trace

# Trace file: build/logs/trace.txt
# One line per instruction (PC, opcode, rd, rd_data, etc.)
```

### 14.3 Post-Simulation Analysis

```python
# Python script: analyze_trace.py
import pandas as pd
df = pd.read_csv('build/logs/trace.txt')
# Filter exceptions
exceptions = df[df['exc_type'] != 'NONE']
print(exceptions)
```

---

## 15. Suggested Reading Order

1. **Beginners**: Section 1 (summary) → Sections 2–3 (fetch/decode)
2. **Advanced**: Sections 4–6 (EX/MEM/WB) → Section 8 (exceptions)
3. **RTL designers**: Section 7 (CSR) → Section 12 (parametric design)
4. **Verification**: Sections 13–14 (testability/debugging)

---

## 16. Resources and References

### RISC-V Specifications
- [RISC-V User-Level ISA Spec](https://riscv.org/specifications/)
- [RISC-V Privileged Spec](https://riscv.org/specifications/privileged-isa/)

### In-repo resources
- `rtl/core/` — Verilog/SystemVerilog RTL
- `rtl/pkg/level_param.sv` — Parametric definitions
- `rtl/include/` — Include files
- `script/` — Python and shell scripts
- `docs/` — Documentation

### Related documents
- [PARAMETRIC_EXCEPTION_PRIORITY.md](parametric-exception-priority.md)
- [IMPLEMENTATION_SUMMARY.md](#implementation)
- [riscv-test.md](#riscv-tests)

---

**Last updated**: 1 December 2025  
**Version**: 1.0  
**Author**: Level Development Team

