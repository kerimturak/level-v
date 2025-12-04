# CERES Parameter Package - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Core Parameters](#core-parameters)
3. [Cache Parameters](#cache-parameters)
4. [Branch Predictor Parameters](#branch-predictor-parameters)
5. [Peripheral Parameters](#peripheral-parameters)
6. [Wishbone Bus Parameters](#wishbone-bus-parameters)
7. [Memory Map](#memory-map)
8. [RISC-V Opcodes](#risc-v-opcodes)
9. [Enumerations](#enumerations)
10. [Structures](#structures)
11. [Functions](#functions)

---

## Genel Bakış

### Amaç

`ceres_param.sv` dosyası, CERES RISC-V işlemcisinin **merkezi konfigürasyon paketi**dir. Tüm RTL modülleri bu paketi import ederek parametrelere, tiplere ve fonksiyonlara erişir.

### Dosya Konumu

```
rtl/pkg/ceres_param.sv
```

### Kullanım

```systemverilog
import ceres_param::*;
```

### Organizasyon

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                        CERES_PARAM PACKAGE STRUCTURE                             │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │ 1. CORE PARAMETERS                                                       │   │
│   │    CPU_CLK, XLEN, RESET_VECTOR                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │ 2. CACHE PARAMETERS                                                      │   │
│   │    BLK_SIZE, IC_*, DC_*, ABUFF_*                                        │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │ 3. BRANCH PREDICTOR PARAMETERS                                           │   │
│   │    PHT_SIZE, BTB_SIZE, GHR_SIZE, RAS_SIZE                               │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │ 4. PERIPHERAL PARAMETERS                                                 │   │
│   │    UART, GPIO, Timer register offsets                                   │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │ 5. WISHBONE BUS PARAMETERS                                               │   │
│   │    WB_DATA_WIDTH, WB_ADDR_WIDTH, WB_BURST_LEN                           │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │ 6. MEMORY MAP                                                            │   │
│   │    MMAP_*, PERIPH_*, CLINT_* addresses                                  │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │ 7. RISC-V OPCODES                                                        │   │
│   │    R-type, I-type, S-type, B-type, U-type, J-type                       │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │ 8. ENUMERATIONS                                                          │   │
│   │    instr_type_e, exc_type_e, alu_op_e, pc_sel_e, stall_e, etc.         │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │ 9. STRUCTURES                                                            │   │
│   │    pipe1_t, pipe2_t, pipe3_t, pipe4_t, wb_master_t, wb_slave_t         │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │ 10. FUNCTIONS                                                            │   │
│   │    resolved_instr_type(), is_branch(), trap_cause_decode(), etc.        │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Core Parameters

### Temel CPU Ayarları

```systemverilog
localparam int CPU_CLK = 50_000_000;           // 50 MHz
localparam int XLEN = 32;                       // 32-bit architecture
localparam logic [31:0] RESET_VECTOR = 32'h8000_0000;  // Boot address
```

| Parametre | Değer | Açıklama |
|-----------|-------|----------|
| `CPU_CLK` | 50 MHz | Sistem saat frekansı |
| `XLEN` | 32 | Register genişliği (RV32) |
| `RESET_VECTOR` | 0x8000_0000 | Reset sonrası PC değeri |

---

## Cache Parameters

### Cache Boyutları

```systemverilog
// Block size
localparam int BLK_SIZE = 128;  // 128-bit cache line (16 bytes)

// Instruction Cache
localparam int IC_WAY = 8;                      // 8-way set associative
localparam int IC_CAPACITY = 8 * 1024 * 8;      // 8KB (bits)
localparam int IC_SIZE = IC_CAPACITY / IC_WAY;  // Per-way size

// Data Cache
localparam int DC_WAY = 8;                      // 8-way set associative
localparam int DC_CAPACITY = 8 * 1024 * 8;      // 8KB (bits)
localparam int DC_SIZE = DC_CAPACITY / DC_WAY;  // Per-way size

// Align Buffer
localparam int ABUFF_SIZE = 512;
localparam int ABUFF_WAY = 1;
```

### Cache Özet Tablosu

| Cache | Kapasite | Way | Block Size | Sets |
|-------|----------|-----|------------|------|
| I-Cache | 8 KB | 8 | 128-bit | 64 |
| D-Cache | 8 KB | 8 | 128-bit | 64 |
| Align Buffer | 512 B | 1 | - | - |

---

## Branch Predictor Parameters

### Predictor Boyutları

```systemverilog
localparam int PHT_SIZE = 512;    // Pattern History Table entries
localparam int BTB_SIZE = 256;    // Branch Target Buffer entries
localparam int GHR_SIZE = 24;     // Global History Register bits
localparam int IBTC_SIZE = 32;    // Indirect Branch Target Cache
localparam int RAS_SIZE = 16;     // Return Address Stack depth
localparam int LOOP_SIZE = 8;     // Loop predictor entries
localparam int BP_LOG_INTERVAL = 10000;  // Stats log interval
```

### Predictor Yapısı

```
┌─────────────────────────────────────────────────────────────────┐
│                    BRANCH PREDICTOR                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   GHR (24-bit) ───┬──► PHT (512 entries, 2-bit saturating)      │
│                   │                                              │
│   PC ─────────────┴──► BTB (256 entries, target + type)         │
│                                                                  │
│   PC ────────────────► RAS (16-deep, CALL/RET stack)            │
│                                                                  │
│   PC ────────────────► IBTC (32 entries, indirect targets)      │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Peripheral Parameters

### UART Parametreleri

```systemverilog
localparam int PROG_BAUD_RATE = 115200;
localparam PROGRAM_SEQUENCE = "CERESTEST";
localparam int UART_DATA_WIDTH = 8;
localparam int UART_TX_FIFO_DEPTH = 256;
localparam int UART_RX_FIFO_DEPTH = 32;
```

### GPIO Parametreleri

```systemverilog
localparam int GPIO_WIDTH = 32;
localparam int NUM_EXT_IRQ = 16;
```

### Multiplier/Divider

```systemverilog
localparam int MUL_WIDTH = 32;
localparam int DIV_WIDTH = 32;
localparam int Mul_Type = 0;  // 0: Wallace, 1: Dadda
```

### Prefetcher (Şu an devre dışı)

```systemverilog
localparam int PREFETCH_TYPE = 0;      // 0=Disabled
localparam int STRIDE_TABLE_SIZE = 64;
localparam int STRIDE_BITS = 12;
localparam int NUM_STREAMS = 4;
localparam int PREFETCH_DEGREE = 4;
```

---

## Wishbone Bus Parameters

### Bus Genişlikleri

```systemverilog
localparam int WB_DATA_WIDTH = 32;
localparam int WB_ADDR_WIDTH = 32;
localparam int WB_SEL_WIDTH = WB_DATA_WIDTH / 8;  // 4
localparam int WB_NUM_SLAVES = 4;
localparam int WB_BURST_LEN = BLK_SIZE / WB_DATA_WIDTH;  // 4
```

---

## Memory Map

### Base Adresler

```systemverilog
localparam logic [31:0] MMAP_DEBUG_BASE   = 32'h0000_0000;
localparam logic [31:0] MMAP_BOOTROM_BASE = 32'h1000_0000;
localparam logic [31:0] MMAP_PERIPH_BASE  = 32'h2000_0000;
localparam logic [31:0] MMAP_CLINT_BASE   = 32'h3000_0000;
localparam logic [31:0] MMAP_EXTMEM_BASE  = 32'h4000_0000;
localparam logic [31:0] MMAP_RAM_BASE     = 32'h8000_0000;
```

### Peripheral Offset'leri

```systemverilog
localparam logic [15:0] PERIPH_UART0_OFF = 16'h0000;  // 0x2000_0xxx
localparam logic [15:0] PERIPH_UART1_OFF = 16'h1000;  // 0x2000_1xxx
localparam logic [15:0] PERIPH_SPI0_OFF  = 16'h2000;  // 0x2000_2xxx
localparam logic [15:0] PERIPH_I2C0_OFF  = 16'h3000;  // 0x2000_3xxx
localparam logic [15:0] PERIPH_GPIO_OFF  = 16'h4000;  // 0x2000_4xxx
localparam logic [15:0] PERIPH_PWM_OFF   = 16'h5000;  // 0x2000_5xxx
localparam logic [15:0] PERIPH_TIMER_OFF = 16'h6000;  // 0x2000_6xxx
localparam logic [15:0] PERIPH_PLIC_OFF  = 16'h7000;  // 0x2000_7xxx
localparam logic [15:0] PERIPH_WDT_OFF   = 16'h8000;  // 0x2000_8xxx
localparam logic [15:0] PERIPH_DMA_OFF   = 16'h9000;  // 0x2000_9xxx
localparam logic [15:0] PERIPH_VGA_OFF   = 16'hD000;  // 0x200D_xxxx
```

### CLINT Register Offset'leri

```systemverilog
localparam logic [15:0] CLINT_MSIP_OFF     = 16'h0000;  // Software interrupt
localparam logic [15:0] CLINT_MTIMECMP_OFF = 16'h4000;  // Timer compare
localparam logic [15:0] CLINT_MTIME_OFF    = 16'hBFF8;  // Timer counter
```

### Memory Map Diyagramı

```
0xFFFF_FFFF ┬─────────────────────────────────────────────────────
            │                    RAM                              
            │               (Cacheable)                           
            │              (Executable)                           
            │                 (2 GB)                              
0x8000_0000 ┼─────────────────────────────────────────────────────
            │               Reserved                              
0x4000_0000 ┼─────────────────────────────────────────────────────
            │               Reserved                              
0x3001_0000 ┼─────────────────────────────────────────────────────
            │                 CLINT                               
            │     mtime, mtimecmp, msip (64 KB)                  
0x3000_0000 ┼─────────────────────────────────────────────────────
            │               Reserved                              
0x2010_0000 ┼───── VGA Framebuffer (256 KB) ──────────────────────
0x200D_0000 ┼───── VGA Control ───────────────────────────────────
0x2009_0000 ┼───── DMA ───────────────────────────────────────────
0x2008_0000 ┼───── WDT ───────────────────────────────────────────
0x2007_0000 ┼───── PLIC ──────────────────────────────────────────
0x2006_0000 ┼───── Timer ─────────────────────────────────────────
0x2005_0000 ┼───── PWM ───────────────────────────────────────────
0x2004_0000 ┼───── GPIO ──────────────────────────────────────────
0x2003_0000 ┼───── I2C0 ──────────────────────────────────────────
0x2002_0000 ┼───── SPI0 ──────────────────────────────────────────
0x2001_0000 ┼───── UART1 ─────────────────────────────────────────
0x2000_0000 ┼───── UART0 ─────────────────────────────────────────
            │               Reserved                              
0x1000_0000 ┼───── Boot ROM ──────────────────────────────────────
0x0000_0000 ┴───── Debug ─────────────────────────────────────────
```

---

## RISC-V Opcodes

### Opcode Tanımları

```systemverilog
localparam logic [6:0] system        = 7'b11100_11;  // SYSTEM (ECALL, CSR)
localparam logic [6:0] op_fence_i    = 7'b00011_11;  // FENCE, FENCE.I
localparam logic [6:0] op_r_type     = 7'b01100_11;  // R-type (ADD, SUB, ...)
localparam logic [6:0] op_i_type_load= 7'b00000_11;  // Load (LB, LH, LW)
localparam logic [6:0] op_i_type     = 7'b00100_11;  // I-type (ADDI, ANDI, ...)
localparam logic [6:0] op_s_type     = 7'b01000_11;  // Store (SB, SH, SW)
localparam logic [6:0] op_b_type     = 7'b11000_11;  // Branch (BEQ, BNE, ...)
localparam logic [6:0] op_i_type_jump= 7'b11001_11;  // JALR
localparam logic [6:0] op_u_type_load= 7'b01101_11;  // LUI
localparam logic [6:0] op_u_type_jump= 7'b11011_11;  // JAL
localparam logic [6:0] op_u_type_auipc=7'b00101_11;  // AUIPC
```

---

## Enumerations

### Instruction Types (`instr_type_e`)

```systemverilog
typedef enum logic [5:0] {
    Null_Instr_Type,
    instr_invalid,
    // R-type
    r_add, r_sub, r_sll, r_slt, r_sltu, r_xor, r_srl, r_sra, r_or, r_and,
    // I-type
    i_addi, i_slti, i_sltiu, i_xori, i_ori, i_andi, i_slli, i_srli, i_srai,
    // M-extension
    r_mul, r_mulh, r_mulhsu, r_mulhu, r_rem, r_remu, r_div, r_divu,
    // Load
    i_lb, i_lh, i_lw, i_lbu, i_lhu,
    // Store
    s_sb, s_sh, s_sw,
    // Branch
    b_beq, b_bne, b_blt, b_bge, b_bltu, b_bgeu,
    // Upper immediate
    u_lui, u_auipc,
    // Jump
    u_jal, i_jalr,
    // CSR
    CSR_RW, CSR_RS, CSR_RC, CSR_RWI, CSR_RSI, CSR_RCI,
    // System
    ecall, ebreak, mret, wfi, fence_i, fence
} instr_type_e;
```

### Exception Types (`exc_type_e`)

```systemverilog
typedef enum logic [3:0] {
    INSTR_MISALIGNED,
    INSTR_ACCESS_FAULT,
    ILLEGAL_INSTRUCTION,
    EBREAK,
    BREAKPOINT,
    LOAD_MISALIGNED,
    LOAD_ACCESS_FAULT,
    STORE_MISALIGNED,
    STORE_ACCESS_FAULT,
    ECALL,
    NO_EXCEPTION
} exc_type_e;
```

### ALU Operations (`alu_op_e`)

```systemverilog
typedef enum logic [4:0] {
    OP_ADD, OP_SUB, OP_SLL, OP_SLT, OP_SLTU, OP_XOR, OP_SRL, OP_SRA, OP_OR, OP_AND,
    OP_MUL, OP_MULH, OP_MULHSU, OP_MULHU, OP_DIV, OP_DIVU, OP_REM, OP_REMU,
    OP_LUI,
    OP_CSRRW, OP_CSRRS, OP_CSRRC, OP_CSRRWI, OP_CSRRSI, OP_CSRRCI
} alu_op_e;
```

### Stall Reasons (`stall_e`)

```systemverilog
typedef enum logic [2:0] {
    NO_STALL       = 0,
    LOAD_RAW_STALL = 1,  // Load-use hazard
    IMISS_STALL    = 2,  // I-Cache miss
    DMISS_STALL    = 3,  // D-Cache miss
    ALU_STALL      = 4,  // Multi-cycle ALU (MUL/DIV)
    FENCEI_STALL   = 5   // FENCE.I processing
} stall_e;
```

### Wishbone CTI/BTE

```systemverilog
typedef enum logic [2:0] {
    WB_CTI_CLASSIC = 3'b000,  // Single transfer
    WB_CTI_CONST   = 3'b001,  // Constant address burst
    WB_CTI_INCR    = 3'b010,  // Incrementing burst
    WB_CTI_EOB     = 3'b111   // End of burst
} wb_cti_e;

typedef enum logic [1:0] {
    WB_BTE_LINEAR = 2'b00,
    WB_BTE_WRAP4  = 2'b01,
    WB_BTE_WRAP8  = 2'b10,
    WB_BTE_WRAP16 = 2'b11
} wb_bte_e;
```

---

## Structures

### Pipeline Register Structures

```systemverilog
// Fetch -> Decode
typedef struct packed {
    logic [XLEN-1:0] pc;
    logic [XLEN-1:0] pc_incr;
    inst_t           inst;
    exc_type_e       exc_type;
    instr_type_e     instr_type;
    predict_info_t   spec;
    // Tracer info (conditional)
} pipe1_t;

// Decode -> Execute
typedef struct packed {
    logic [XLEN-1:0] pc, pc_incr;
    logic            rf_rw_en, wr_en;
    logic [1:0]      rw_size, result_src, alu_in1_sel;
    alu_op_e         alu_ctrl;
    pc_sel_e         pc_sel;
    logic            alu_in2_sel, ld_op_sign;
    logic [XLEN-1:0] r1_data, r2_data, imm;
    logic [4:0]      r1_addr, r2_addr, rd_addr;
    // CSR fields
    logic            rd_csr, wr_csr;
    logic [11:0]     csr_idx;
    // ...
} pipe2_t;

// Execute -> Memory
typedef struct packed {
    logic [XLEN-1:0] pc_incr, pc;
    logic            rf_rw_en, wr_en;
    logic [1:0]      rw_size, result_src;
    logic            ld_op_sign;
    logic [4:0]      rd_addr;
    logic [XLEN-1:0] alu_result, write_data;
    logic            dcache_valid;
    logic [XLEN-1:0] read_data;
    // ...
} pipe3_t;

// Memory -> Writeback
typedef struct packed {
    logic [XLEN-1:0] pc_incr, pc;
    logic            rf_rw_en;
    logic [1:0]      result_src;
    logic [4:0]      rd_addr;
    logic [XLEN-1:0] alu_result, read_data;
    // ...
} pipe4_t;
```

### Wishbone Structures

```systemverilog
typedef struct packed {
    logic [WB_ADDR_WIDTH-1:0] adr;
    logic [WB_DATA_WIDTH-1:0] dat;
    logic [WB_SEL_WIDTH-1:0]  sel;
    logic                     we;
    logic                     stb;
    logic                     cyc;
    wb_cti_e                  cti;
    wb_bte_e                  bte;
} wb_master_t;

typedef struct packed {
    logic [WB_DATA_WIDTH-1:0] dat;
    logic                     ack;
    logic                     err;
    logic                     rty;
    logic                     stall;
} wb_slave_t;
```

### Cache Interfaces

```systemverilog
// I-Cache Request
typedef struct packed {
    logic            valid;
    logic            ready;
    logic [XLEN-1:0] addr;
    logic            uncached;
} icache_req_t;

// D-Cache Request
typedef struct packed {
    logic            valid, ready;
    logic [XLEN-1:0] addr;
    logic            uncached, rw;
    logic [1:0]      rw_size;
    logic [31:0]     data;
} dcache_req_t;
```

---

## Functions

### Instruction Type Resolver

```systemverilog
function instr_type_e resolved_instr_type(input inst_t inst_i);
    case (inst_i.opcode)
        op_r_type: begin
            if (inst_i.funct7[0]) begin  // M-extension
                case (inst_i.funct3)
                    3'd0: resolved_instr_type = r_mul;
                    3'd1: resolved_instr_type = r_mulh;
                    // ...
                endcase
            end else begin
                case (inst_i.funct3)
                    3'd0: resolved_instr_type = (inst_i.funct7[5]) ? r_sub : r_add;
                    // ...
                endcase
            end
        end
        // ... other opcodes
    endcase
endfunction
```

### Branch Type Detector

```systemverilog
function pc_sel_e is_branch(instr_type_e instr);
    case (instr)
        b_beq:  return BEQ;
        b_bne:  return BNE;
        b_blt:  return BLT;
        b_bge:  return BGE;
        b_bltu: return BLTU;
        b_bgeu: return BGEU;
        i_jalr: return JALR;
        u_jal:  return JAL;
        default: return NO_BJ;
    endcase
endfunction
```

### Trap Cause Decoder

```systemverilog
function automatic logic [XLEN-1:0] trap_cause_decode(input exc_type_e exc);
    case (exc)
        INSTR_ACCESS_FAULT:  return 1;
        ILLEGAL_INSTRUCTION: return 2;
        EBREAK:              return 3;
        LOAD_MISALIGNED:     return 4;
        LOAD_ACCESS_FAULT:   return 5;
        STORE_MISALIGNED:    return 6;
        STORE_ACCESS_FAULT:  return 7;
        ECALL:               return 11;
        default:             return '1;
    endcase
endfunction
```

### CSR Name Decoder

```systemverilog
function string csr_name(input logic [11:0] idx);
    case (idx)
        12'h300: return "mstatus";
        12'h301: return "misa";
        12'h304: return "mie";
        12'h305: return "mtvec";
        12'h341: return "mepc";
        12'h342: return "mcause";
        12'h343: return "mtval";
        12'h344: return "mip";
        // ... more CSRs
        default: return $sformatf("csr_%03h", idx);
    endcase
endfunction
```

---

## Özet

`ceres_param.sv` paketi:

1. **1000+ Satır**: Tüm RTL konfigürasyonu
2. **Merkezi Tanımlar**: Tüm modüller bu paketi import eder
3. **Type Safety**: Enum ve struct ile tip güvenliği
4. **Functions**: Decode ve utility fonksiyonları
5. **Memory Map**: Tam SoC adres haritası

Bu paket, CERES RISC-V işlemcisinin **single source of truth**'udur.
