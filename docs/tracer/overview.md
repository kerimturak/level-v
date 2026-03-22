# Konata Logger Module — Technical Documentation

## Table of Contents

1. [General Overview](#general-overview)
2. [Konata Format](#konata-format)
3. [Pipeline Stage Tracking](#pipeline-stage-tracking)
4. [Log Commands](#log-commands)
5. [Stall and Flush Handling](#stall-and-flush-handling)
6. [Metadata Logging](#metadata-logging)
7. [Usage](#usage)

---

## General Overview

### Purpose

The `konata_logger` module logs the Level RISC-V processor pipeline behavior in **Konata pipeline visualizer** format. It records each instruction’s progress through pipeline stages, stalls, and flushes.

### File Location

```
rtl/tracer/konata_logger.sv
```

### Activation

```bash
# Via Makefile
make run T=test KONATA_TRACER=1 LOG_PIPELINE=1

# Verilator define
+define+KONATA_TRACER
```

### Key Features

| Feature | Description |
|---------|-------------|
| **Format** | Konata v0004 |
| **Stages** | F, D, X, M, Wb |
| **Metadata** | grp, stall, stall_cycles, mem_latency |
| **Output** | `results/logs/rtl/level.KONATA` |

---

## Konata Format

### File Header

```
KONATA	0004
```

### Command Types

| Command | Format | Description |
|---------|--------|-------------|
| `C=` | `C=\t<cycle>` | First cycle (absolute) |
| `C` | `C\t1` | Cycle increment |
| `I` | `I\t<id>\t<id>\t0` | Instruction issue |
| `S` | `S\t<id>\t0\t<stage>` | Stage start |
| `E` | `E\t<id>\t0\t<stage>` | Stage end |
| `L` | `L\t<id>\t<lane>\t<text>` | Label (metadata) |
| `R` | `R\t<id>\t<id>\t<flush>` | Retire (0=commit, 1=flush) |

### Sample Log

```
KONATA	0004
C=	0
I	0	0	0
L	0	0	80000000: 00000297
L	0	1	grp=ALU
S	0	0	F
C	1
E	0	0	F
S	0	0	D
I	1	1	0
L	1	0	80000004: 02028293
L	1	1	grp=ALU
S	1	0	F
C	1
E	0	0	D
S	0	0	X
E	1	0	F
S	1	0	D
C	1
...
```

---

## Pipeline Stage Tracking

### Stage Structure

```systemverilog
typedef struct {
    integer      id;              // Unique instruction ID
    logic [31:0] pc;              // Program counter
    logic [31:0] inst;            // Instruction word
    logic        valid;           // Valid instruction in this stage
    logic        started_f;       // F stage started
    logic        started_d;       // D stage started
    logic        started_x;       // X stage started
    logic        started_m;       // M stage started
    logic        started_wb;      // Wb stage started

    // Metadata
    instr_type_e instr_type;      // Instruction type
    integer      stall_cycles;    // Total stall cycle count
    integer      mem_stall_cycles;// Memory stall cycle count
    stall_e      first_stall;     // First stall reason
    logic        retired;         // Retired
} pipe_entry_t;
```

### Stage Registers

```systemverilog
pipe_entry_t fetch_s, decode_s, execute_s, memory_s, writeback_s;
pipe_entry_t prev_fetch, prev_decode, prev_execute, prev_memory, prev_writeback;
```

### Pipeline Advance Signals

```systemverilog
// Front-end (F + D): advances only when NO_STALL
logic adv_front;
assign adv_front = (stall_cause == NO_STALL);

// Back-end (X + M + Wb): stalls on IMISS/DMISS/ALU/FENCE.I
logic adv_back;
assign adv_back = !(stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL});
```

---

## Log Commands

### Helper Functions

```systemverilog
function void log_stage_start(input integer id, input string stg);
    if (fd) $fwrite(fd, "S\t%0d\t0\t%s\n", id, stg);
endfunction

function void log_stage_end(input integer id, input string stg);
    if (fd) $fwrite(fd, "E\t%0d\t0\t%s\n", id, stg);
endfunction

function void log_issue(input integer id);
    if (fd) $fwrite(fd, "I\t%0d\t%0d\t0\n", id, id);
endfunction

function void log_line_pc_inst(input integer id, input logic [31:0] pc, input logic [31:0] inst);
    if (fd) $fwrite(fd, "L\t%0d\t0\t%08h: %08h\n", id, pc, inst);
endfunction

function void log_retire(input integer id);
    if (fd) $fwrite(fd, "R\t%0d\t%0d\t0\n", id, id);
endfunction

function void log_retire_flush(input integer id);
    if (fd) $fwrite(fd, "R\t%0d\t%0d\t1\n", id, id);
endfunction
```

### Instruction Group Classification

```systemverilog
function string instr_group(input instr_type_e t);
    case (t)
        i_lb, i_lh, i_lw, i_lbu, i_lhu: return "LOAD";
        s_sb, s_sh, s_sw:               return "STORE";
        b_beq, b_bne, b_blt, b_bge, b_bltu, b_bgeu: return "BRANCH";
        u_jal, i_jalr:                  return "JUMP";
        CSR_RW, CSR_RS, CSR_RC, CSR_RWI, CSR_RSI, CSR_RCI: return "CSR";
        ecall, ebreak:                  return "SYSCALL";
        mret, wfi:                      return "PRIV";
        fence_i:                        return "FENCE";
        default:                        return "ALU";
    endcase
endfunction
```

### Stall Reason String

```systemverilog
function string stall_to_str(input stall_e s);
    case (s)
        NO_STALL:       return "NONE";
        IMISS_STALL:    return "IMISS";
        DMISS_STALL:    return "DMISS";
        LOAD_RAW_STALL: return "RAW";
        ALU_STALL:      return "ALU";
        default:        return "OTHER";
    endcase
endfunction
```

---

## Stall and Flush Handling

### Stall Counter

```systemverilog
// Do not count on flush cycle
if (!flush_fe) begin
    // Front (F + D) stall
    if (!adv_front) begin
        if (fetch_s.valid) fetch_s.stall_cycles++;
        if (decode_s.valid) decode_s.stall_cycles++;
    end

    // Back (X + M + Wb) stall
    if (!adv_back) begin
        if (execute_s.valid) execute_s.stall_cycles++;
        if (memory_s.valid) memory_s.stall_cycles++;
        if (writeback_s.valid) writeback_s.stall_cycles++;

        // LOAD/STORE memory latency tracking
        if (memory_s.valid && is_mem_instr(memory_s.instr_type))
            memory_s.mem_stall_cycles++;
    end
end
```

### Flush Handling

```systemverilog
if (flush_fe) begin
    // All in-flight instructions are flushed
    if (prev_fetch.valid) log_retire_flush(prev_fetch.id);
    if (prev_decode.valid) log_retire_flush(prev_decode.id);
    if (prev_execute.valid) log_retire_flush(prev_execute.id);
    if (prev_memory.valid) log_retire_flush(prev_memory.id);
    if (prev_writeback.valid) log_retire_flush(prev_writeback.id);

    // Clear pipeline
    fetch_s     <= '{default: 0};
    decode_s    <= '{default: 0};
    execute_s   <= '{default: 0};
    memory_s    <= '{default: 0};
    writeback_s <= '{default: 0};
end
```

---

## Metadata Logging

### Retire Metadata

At writeback stage, metadata is written for each instruction:

```systemverilog
if (prev_writeback.valid && prev_writeback.started_wb && !prev_writeback.retired) begin
    string g_str, st_str;
    int mem_lat;

    g_str   = instr_group(prev_writeback.instr_type);
    st_str  = stall_to_str(prev_writeback.first_stall);
    mem_lat = prev_writeback.mem_stall_cycles;

    // Metadata: grp=..., stall=..., stall_cycles=N [mem_latency=M]
    $fwrite(fd, "L\t%0d\t1\tgrp=%s stall=%s stall_cycles=%0d",
            prev_writeback.id, g_str, st_str, prev_writeback.stall_cycles);
    
    if (mem_lat > 0)
        $fwrite(fd, " mem_latency=%0d", mem_lat);
    
    $fwrite(fd, "\n");

    log_stage_end(prev_writeback.id, "Wb");
    log_retire(prev_writeback.id);
end
```

### Sample Metadata

```
L	42	1	grp=LOAD stall=DMISS stall_cycles=12 mem_latency=10
L	43	1	grp=ALU stall=RAW stall_cycles=1
L	44	1	grp=BRANCH stall=NONE stall_cycles=0
```

---

## Usage

### Makefile

```bash
# Pipeline trace enabled
make run T=rv32ui-p-add KONATA_TRACER=1

# Specify log file path
make run T=test KONATA_TRACER=1 +log_path=/path/to/trace.log
```

### Log File

Default output: `results/logs/rtl/level.KONATA`

### Opening in Konata Viewer

1. Start the Konata application
2. File → Open → select `level.KONATA`
3. Inspect the pipeline visualization

### Visualizer View

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  Cycle    0    1    2    3    4    5    6    7    8    9   10   11   12        │
│ ────────────────────────────────────────────────────────────────────────────── │
│  I0      [F   ][D   ][X   ][M   ][Wb  ]                                        │
│  I1           [F   ][D   ][X   ][M   ][Wb  ]                                   │
│  I2                [F   ][D   ][X   ][M   ][Wb  ]                              │
│  I3                     [F   ][D   ][X   ][M   ][Wb  ]                         │
│  I4 (LOAD)              [F   ][D   ][X   ][M        ][Wb  ]  ← DMISS stall     │
│  I5                          [F   ][D   ][D   ][X   ][M   ][Wb  ] ← RAW stall  │
│  I6 (BRANCH)                      [F   ][D   ][X   ] ← FLUSH                   │
│  I7                                    [F   ] ← FLUSH                          │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Summary

The `konata_logger` module:

1. **Konata v0004**: Standard pipeline visualizer format
2. **5-Stage Tracking**: F, D, X, M, Wb stages
3. **Stall Analysis**: stall_cycles, mem_latency
4. **Flush Detection**: Misprediction and exception flushes
5. **Rich Metadata**: grp, stall reason, cycle counts

This module is a critical tool for pipeline performance analysis and debug.
