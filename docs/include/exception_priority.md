# Exception Priority - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [RISC-V Exception Modeli](#risc-v-exception-modeli)
3. [Priority Konfigürasyonu](#priority-konfigürasyonu)
4. [Exception Türleri](#exception-türleri)
5. [Trap Handling](#trap-handling)
6. [Pipeline Entegrasyonu](#pipeline-entegrasyonu)
7. [Kullanım Örnekleri](#kullanım-örnekleri)

---

## Genel Bakış

### Amaç

`exception_priority.svh` dosyası, RISC-V exception'larının **öncelik sırasını** tanımlar. Aynı cycle'da birden fazla exception oluştuğunda hangi exception'ın işleneceğini belirler.

### Dosya Konumu

```
rtl/include/exception_priority.svh
```

### Temel Konsept

```
Aynı anda birden fazla exception oluşabilir:
- Instruction page fault (fetch)
- Illegal instruction (decode)
- Load/Store fault (memory)

Priority sayısı düşük olan exception önce işlenir.
```

---

## RISC-V Exception Modeli

### Exception vs Interrupt

| Tip | Özellik | Örnek |
|-----|---------|-------|
| **Exception** | Senkron, instruction kaynaklı | Illegal instruction |
| **Interrupt** | Asenkron, dış kaynaklı | Timer interrupt |

### Exception Sınıfları

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                         EXCEPTION CLASSIFICATION                                 │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                          INSTRUCTION EXCEPTIONS                          │   │
│   │                                                                          │   │
│   │   • Instruction Address Misaligned                                       │   │
│   │   • Instruction Access Fault                                             │   │
│   │   • Illegal Instruction                                                  │   │
│   │   • Breakpoint                                                           │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                            LOAD EXCEPTIONS                               │   │
│   │                                                                          │   │
│   │   • Load Address Misaligned                                              │   │
│   │   • Load Access Fault                                                    │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                           STORE EXCEPTIONS                               │   │
│   │                                                                          │   │
│   │   • Store/AMO Address Misaligned                                         │   │
│   │   • Store/AMO Access Fault                                               │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                         ENVIRONMENT CALLS                                │   │
│   │                                                                          │   │
│   │   • Environment Call from U-mode                                         │   │
│   │   • Environment Call from S-mode                                         │   │
│   │   • Environment Call from M-mode                                         │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Priority Konfigürasyonu

### RISC-V Standart Priority

RISC-V spesifikasyonu exception önceliklerini belirler:

```systemverilog
// exception_priority.svh

`ifndef EXCEPTION_PRIORITY_SVH
`define EXCEPTION_PRIORITY_SVH

//------------------------------------------------------------------------------
// EXCEPTION PRIORITY CONFIGURATION
// Lower number = Higher priority
// Based on RISC-V Privileged Specification
//------------------------------------------------------------------------------

// Instruction Exceptions (highest priority for same instruction)
localparam int PRIORITY_INSTR_ADDR_MISALIGNED = 0;
localparam int PRIORITY_INSTR_ACCESS_FAULT    = 1;
localparam int PRIORITY_ILLEGAL_INSTR         = 2;
localparam int PRIORITY_BREAKPOINT            = 3;

// Load Exceptions
localparam int PRIORITY_LOAD_ADDR_MISALIGNED  = 4;
localparam int PRIORITY_LOAD_ACCESS_FAULT     = 5;

// Store Exceptions
localparam int PRIORITY_STORE_ADDR_MISALIGNED = 6;
localparam int PRIORITY_STORE_ACCESS_FAULT    = 7;

// Environment Calls (lowest priority)
localparam int PRIORITY_ECALL_U               = 8;
localparam int PRIORITY_ECALL_S               = 9;
localparam int PRIORITY_ECALL_M               = 10;

`endif // EXCEPTION_PRIORITY_SVH
```

### Priority Tablosu

| Priority | Exception | Code | Açıklama |
|----------|-----------|------|----------|
| 0 | Instruction Address Misaligned | 0 | En yüksek öncelik |
| 1 | Instruction Access Fault | 1 | I-Cache/Bus fault |
| 2 | Illegal Instruction | 2 | Geçersiz opcode |
| 3 | Breakpoint | 3 | EBREAK instruction |
| 4 | Load Address Misaligned | 4 | Unaligned load |
| 5 | Load Access Fault | 5 | D-Cache/Bus fault |
| 6 | Store Address Misaligned | 6 | Unaligned store |
| 7 | Store Access Fault | 7 | D-Cache/Bus fault |
| 8 | Environment Call U-mode | 8 | ECALL from User |
| 9 | Environment Call S-mode | 9 | ECALL from Supervisor |
| 10 | Environment Call M-mode | 11 | ECALL from Machine |

---

## Exception Türleri

### Instruction Address Misaligned

```systemverilog
// Fetch stage'de kontrol
// Compressed (RV32C) ile 2-byte aligned olabilir
// Standard instructions 4-byte aligned olmalı

logic instr_addr_misaligned;

`ifdef RV32C_ENABLED
    assign instr_addr_misaligned = pc[0];  // Bit 0 must be 0
`else
    assign instr_addr_misaligned = |pc[1:0];  // Bits 1:0 must be 0
`endif
```

### Instruction Access Fault

```systemverilog
// I-Cache miss + bus error
// PMA non-executable region
// PMP execute violation

logic instr_access_fault;

assign instr_access_fault = icache_error || 
                            pma_exec_fault || 
                            pmp_exec_fault;
```

### Illegal Instruction

```systemverilog
// Decode stage'de kontrol
// - Invalid opcode
// - Invalid funct3/funct7
// - CSR access violation

logic illegal_instr;

assign illegal_instr = !valid_opcode || 
                       invalid_funct || 
                       csr_access_fault;
```

### Load/Store Misaligned

```systemverilog
// Memory stage'de kontrol
// LW/SW: 4-byte aligned
// LH/SH: 2-byte aligned
// LB/SB: no alignment requirement

logic addr_misaligned;

always_comb begin
    case (mem_size)
        MEM_SIZE_WORD: addr_misaligned = |addr[1:0];
        MEM_SIZE_HALF: addr_misaligned = addr[0];
        MEM_SIZE_BYTE: addr_misaligned = 1'b0;
        default:       addr_misaligned = 1'b1;
    endcase
end
```

### Load/Store Access Fault

```systemverilog
// D-Cache miss + bus error
// PMA read/write violation
// PMP read/write violation

logic load_access_fault;
logic store_access_fault;

assign load_access_fault  = dcache_error && is_load;
assign store_access_fault = dcache_error && is_store;
```

---

## Trap Handling

### Exception Priority Resolver

```systemverilog
// Aynı cycle'da birden fazla exception varsa
// En yüksek öncelikli olanı seç

function automatic logic [3:0] resolve_exception_priority(
    input logic instr_addr_mis,
    input logic instr_access,
    input logic illegal,
    input logic breakpoint,
    input logic load_mis,
    input logic load_access,
    input logic store_mis,
    input logic store_access,
    input logic ecall
);
    // Priority order (low number = high priority)
    if (instr_addr_mis) return 4'd0;  // Instruction address misaligned
    if (instr_access)   return 4'd1;  // Instruction access fault
    if (illegal)        return 4'd2;  // Illegal instruction
    if (breakpoint)     return 4'd3;  // Breakpoint
    if (load_mis)       return 4'd4;  // Load address misaligned
    if (load_access)    return 4'd5;  // Load access fault
    if (store_mis)      return 4'd6;  // Store address misaligned
    if (store_access)   return 4'd7;  // Store access fault
    if (ecall)          return 4'd11; // Environment call M-mode
    return 4'd15;                     // No exception
endfunction
```

### Trap Entry

```systemverilog
// Exception oluştuğunda
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        mepc   <= '0;
        mcause <= '0;
        mtval  <= '0;
    end else if (exception_valid) begin
        // Save PC
        mepc <= exception_pc;

        // Save cause (exception code)
        mcause <= {1'b0, 27'b0, exception_code};

        // Save trap value
        case (exception_code)
            EXC_INSTR_ADDR_MIS:  mtval <= exception_pc;
            EXC_INSTR_ACC_FAULT: mtval <= exception_pc;
            EXC_ILLEGAL_INSTR:   mtval <= exception_instr;
            EXC_LOAD_ADDR_MIS:   mtval <= exception_addr;
            EXC_LOAD_ACC_FAULT:  mtval <= exception_addr;
            EXC_STORE_ADDR_MIS:  mtval <= exception_addr;
            EXC_STORE_ACC_FAULT: mtval <= exception_addr;
            default:             mtval <= '0;
        endcase
    end
end
```

---

## Pipeline Entegrasyonu

### Exception Propagation

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                        EXCEPTION FLOW IN PIPELINE                                │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   FETCH ─────► DECODE ─────► EXECUTE ─────► MEMORY ─────► WRITEBACK             │
│     │            │              │             │              │                   │
│     │            │              │             │              │                   │
│     ▼            ▼              ▼             ▼              ▼                   │
│  ┌──────┐    ┌──────┐      ┌──────┐      ┌──────┐      ┌──────┐                 │
│  │Instr │    │Illegal│     │ (none│      │Load/ │      │      │                 │
│  │Addr  │    │Instr │      │ usually)    │Store │      │Commit│                 │
│  │Fault │    │Break │      │      │      │Fault │      │      │                 │
│  └──────┘    └──────┘      └──────┘      └──────┘      └──────┘                 │
│     │            │              │             │              │                   │
│     │            │              │             │              │                   │
│     └────────────┴──────────────┴─────────────┴──────────────┘                   │
│                                  │                                               │
│                                  ▼                                               │
│                          ┌─────────────┐                                        │
│                          │  EXCEPTION  │                                        │
│                          │  RESOLVER   │                                        │
│                          └──────┬──────┘                                        │
│                                 │                                               │
│                                 ▼                                               │
│                          ┌─────────────┐                                        │
│                          │ TRAP ENTRY  │                                        │
│                          │ (CSR write) │                                        │
│                          └──────┬──────┘                                        │
│                                 │                                               │
│                                 ▼                                               │
│                          ┌─────────────┐                                        │
│                          │ FLUSH PIPE  │                                        │
│                          │ Jump mtvec  │                                        │
│                          └─────────────┘                                        │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Exception Register

Pipeline stage'ler arasında exception bilgisi taşınır:

```systemverilog
typedef struct packed {
    logic        valid;       // Exception aktif
    logic [3:0]  cause;       // Exception code
    logic [31:0] pc;          // Exception PC
    logic [31:0] tval;        // Trap value
} exception_t;

// Pipeline register
exception_t ex_exception_q, mem_exception_q;
```

### Precise Exception

RISC-V precise exception gerektirir:

```systemverilog
// Exception olan instruction'dan önceki tüm instruction'lar
// commit edilmiş olmalı
// Sonrakiler flush edilmeli

always_comb begin
    if (exception_valid) begin
        // Flush younger instructions
        flush_if = 1'b1;
        flush_id = 1'b1;
        flush_ex = 1'b1;

        // Exception instruction commit edilmez
        mem_commit = 1'b0;
    end
end
```

---

## Kullanım Örnekleri

### Exception Handler

```systemverilog
module exception_handler
  import ceres_param::*;
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // Exception inputs from pipeline
    input  logic        i_fetch_fault,
    input  logic        i_illegal_instr,
    input  logic        i_load_fault,
    input  logic        i_store_fault,
    input  logic [31:0] i_pc,
    input  logic [31:0] i_addr,
    input  logic [31:0] i_instr,

    // Exception output
    output logic        o_exception,
    output logic [3:0]  o_cause,
    output logic [31:0] o_tval
);

`include "exception_priority.svh"

    // Priority-based exception selection
    always_comb begin
        o_exception = 1'b0;
        o_cause     = '0;
        o_tval      = '0;

        if (i_fetch_fault) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_INSTR_ACCESS_FAULT[3:0];
            o_tval      = i_pc;
        end else if (i_illegal_instr) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_ILLEGAL_INSTR[3:0];
            o_tval      = i_instr;
        end else if (i_load_fault) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_LOAD_ACCESS_FAULT[3:0];
            o_tval      = i_addr;
        end else if (i_store_fault) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_STORE_ACCESS_FAULT[3:0];
            o_tval      = i_addr;
        end
    end

endmodule
```

### Test Code

```c
// Exception test (C code)

void test_illegal_instruction() {
    // Illegal instruction - should trap
    asm volatile(".word 0x00000000");
}

void test_load_misaligned() {
    volatile int* ptr = (int*)0x80000001;  // Misaligned
    int val = *ptr;  // Should trap
}

void test_store_access_fault() {
    volatile int* ptr = (int*)0x00000000;  // Invalid region
    *ptr = 0xDEADBEEF;  // Should trap
}
```

---

## Özet

`exception_priority.svh` dosyası:

1. **Priority Definition**: RISC-V exception öncelikleri
2. **Exception Types**: 11 farklı exception tipi
3. **Trap Handling**: CSR kayıtları (mepc, mcause, mtval)
4. **Precise Exception**: Pipeline flush ve recovery
5. **Configurable**: Parametre ile özelleştirilebilir

Bu dosya, CERES RISC-V işlemcisinin exception handling mekanizmasının temelini oluşturur.
