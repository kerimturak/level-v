---
title: "Mimari Tasarım"
description: "Ceres RISC-V Procesöründen Detaylı Mimari Tasarım Dökümantasyonu"
date: 2025-12-01
draft: false
weight: 100
---

# Ceres RISC-V Processor - Mimari Tasarım

Bu dökümantasyon, Ceres RISC-V procesörün detaylı mimari tasarımını açıklamaktadır. Her bileşen kendi alt bölümünde ayrıntılı bir şekilde ele alınmıştır.

---

## 1. Genel Mimari Özet

Ceres RISC-V, 32-bit hafif ve modüler bir RISC-V processor çekirdeğidir. RV32IMC komut setini destekler ve CSR (Control and Status Register) ile FENCE komutları için destek sunmaktadır.

### Temel Özellikler

- **Komut Seti**: RV32IMC (Integer Base + Multiply/Divide + Compressed)
- **Register Seti**: 32 x 32-bit
- **Bellek Mimarisi**: Von Neumann (Unified Memory)
- **Pipeline Yapısı**: 5-aşamalı (5-stage)
- **Hata Yönetimi**: Parametrik Exception Priority sistemi
- **Performans**: 1 DMIPS/MHz

### İçerik Haritası

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

### 2.1 Genel Açıklama

Fetch aşaması, Program Counter (PC) yönetiminden sorumludur ve talimatları instruction memory'den almaktadır.

**Dosya Konumu**: `rtl/core/stage01_fetch/`

### 2.2 Ana Bileşenler

#### Program Counter (PC) Management

```systemverilog
// PC güncellemesi
always_comb begin
    if (rst) begin
        next_pc = PC_RESET_VALUE;  // Varsayılan: 0x8000_0000
    end else if (is_branch_taken) begin
        next_pc = branch_target;
    end else if (is_jump) begin
        next_pc = jump_target;
    end else if (exception_occurred) begin
        next_pc = exception_vector;
    end else begin
        next_pc = pc + increment;  // increment = 2 (RV32C) veya 4 (RV32I)
    end
end
```

**PC Sabitler**:
- `PC_RESET_VALUE`: 0x8000_0000 (Önyükleme adresi)
- `PC_ALIGN`: RV32C için 2 byte, RV32I için 4 byte hizalama

#### Instruction Buffer (I-Buffer)

Fetch aşamasında bir instruction buffer bulunur. Bu buffer:
- Sıkıştırılmış (16-bit) ve normal (32-bit) komutları tamponlar
- Pipeline stall durumunda talimatları geciktirir
- Cache miss sırasında bekleme yapar

```systemverilog
typedef struct {
    logic [31:0] instr;      // 32-bit talimat (aligned)
    logic valid;             // Geçerli bit
    logic [31:0] pc;         // Program Counter
    logic [4:0] exc_type;    // Exception tipi
} instr_buffer_t;
```

#### Exception Detection @ Fetch

Fetch aşamasında tespit edilen istisnalar:

| İstisna | Sebep | Kod |
|---------|-------|-----|
| Debug Breakpoint | `tdata1[2] == 1'b1 && PC == tdata2` | 1 |
| Instruction Misaligned | RV32C için PC[0]!=0 veya RV32I için PC[1:0]!=0 | 0 |
| Instruction Access Fault | Bellek erişim hatası (grand signal) | 1 |
| Illegal Instruction | Tanımlanmamış komut | 2 |

### 2.3 Parametrik Exception Priority

Ceres, RISC-V Privileged Specification'a uygun olarak parametrik exception priority sistemi kullanmaktadır.

```systemverilog
// Exception Priority Tanımları (ceres_param.sv)
typedef enum logic [4:0] {
    PRIORITY_1,           // En yüksek (ilk kontrol edilir)
    PRIORITY_2,
    PRIORITY_3,
    PRIORITY_4,
    PRIORITY_5,
    PRIORITY_6,
    PRIORITY_7,           // En düşük (son kontrol edilir)
    PRIORITY_DISABLED     // İstisna devre dışı
} exc_priority_t;

// Varsayılan RISC-V Spec-uyumlu Priority:
localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_1;
localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_2;
localparam exc_priority_t EXC_PRIORITY_INSTR_ACCESS_FAULT = PRIORITY_3;
localparam exc_priority_t EXC_PRIORITY_ILLEGAL = PRIORITY_4;
localparam exc_priority_t EXC_PRIORITY_EBREAK = PRIORITY_5;
localparam exc_priority_t EXC_PRIORITY_ECALL = PRIORITY_6;
```

**Konfigürasyon Dosyası**: `rtl/include/exception_priority.svh`

Alternatif konfigürasyonlar:
- `EXCEPTION_PRIORITY_DEBUG_FIRST` (Varsayılan - RISC-V Spec uyumlu)
- `EXCEPTION_PRIORITY_MISALIGNED_FIRST` (Test amaçlı)
- `EXCEPTION_PRIORITY_ILLEGAL_FIRST` (Test amaçlı)
- `EXCEPTION_PRIORITY_DISABLED_DEBUG` (Debug devre dışı)

### 2.4 Priority Check Fonksiyonu

```systemverilog
function automatic logic check_exc_priority(
    input exc_priority_t exc_pri,
    input exc_priority_t min_pri
);
    // exc_pri, min_pri'den daha yüksekse (ya da eşitse) ve 
    // devre dışı değilse TRUE döner
    return (exc_pri <= min_pri) && (exc_pri != PRIORITY_DISABLED);
endfunction
```

### 2.5 Exception Priority Seçim Mantığı

```systemverilog
// Tüm istisnalar tespit edilir
has_debug_breakpoint = fetch_valid && tdata1[2] && (pc == tdata2);
has_instr_misaligned = fetch_valid && (misa_c ? pc[0] : (pc[1:0] != 2'b00));
has_instr_access_fault = fetch_valid && !grand;
has_illegal_instr = fetch_valid && illegal_instr && buff_res.valid;

// Parametrik priority-tabanlı seçim
if (has_debug_breakpoint && check_exc_priority(
    EXC_PRIORITY_DEBUG_BREAKPOINT, PRIORITY_7)) begin
    exc_type = BREAKPOINT;
end else if (has_instr_misaligned && check_exc_priority(
    EXC_PRIORITY_INSTR_MISALIGNED, PRIORITY_7)) begin
    exc_type = INSTR_MISALIGNED;
end else if (has_instr_access_fault && check_exc_priority(
    EXC_PRIORITY_INSTR_ACCESS_FAULT, PRIORITY_7)) begin
    exc_type = INSTR_ACCESS_FAULT;
// ... diğer istisnalar
end
```

---

## 3. Decode Stage (ID - Instruction Decode)

### 3.1 Genel Açıklama

Decode aşaması, instruction buffer'dan gelen talimatı çözer (decode eder) ve register dosyasından değerleri okur.

**Dosya Konumu**: `rtl/core/stage02_decode/`

### 3.2 Instruction Decoder

Decoder modülü, 32-bit (veya sıkıştırılmış 16-bit) talimatı aşağıdaki alanlara ayırır:

```systemverilog
typedef struct {
    logic [6:0] opcode;      // 7-bit opcode
    logic [4:0] rd;          // Destination register
    logic [4:0] rs1;         // Source register 1
    logic [4:0] rs2;         // Source register 2
    logic [11:0] imm12;      // 12-bit immediate
    logic [31:0] imm32;      // 32-bit immediate (sign-extended)
    instr_type_t instr_type; // Komut tipi (add, sub, ld, sd, vb)
    logic valid;             // Geçerli bit
} decoded_instr_t;
```

### 3.3 Komut Tipleri

Ceres RISC-V desteklediği komut tipleri:

#### Integer Aritmetik (RV32I)
- **ADD/SUB**: Toplama/Çıkarma
- **AND/OR/XOR**: Bit işlemleri
- **SLL/SRL/SRA**: Kaydırma işlemleri
- **SLT/SLTU**: Karşılaştırma

#### Multiply/Divide (RV32M)
- **MUL/MULH/MULHSU/MULHU**: Çarpma
- **DIV/DIVU**: Bölüm
- **REM/REMU**: Kalan

#### Load/Store (Memory)
- **LW/LH/LB/LHU/LBU**: Load (Yükleme)
- **SW/SH/SB**: Store (Saklama)

#### Branch & Jump
- **BEQ/BNE/BLT/BGE/BLTU/BGEU**: Şartlı atlama
- **JAL/JALR**: Koşulsuz atlama (link ile)

#### System
- **ECALL/EBREAK**: Sistem çağrıları
- **FENCE/FENCE.I**: Bellek bariyerleri
- **CSR***: Control & Status Register işlemleri

### 3.4 Register File

32 adet 32-bit registerden oluşur:
- `x0-x31`: Genel amaçlı registerler
- `x0 (zero)`: Her zaman 0 (yazma yoksayılır)
- `x1 (ra)`: Return Address
- `x2 (sp)`: Stack Pointer

```systemverilog
// Register File yapısı
logic [31:0] reg_file [0:31];

// Dual-port read (aynı cycle'da 2 okuma)
always @(*) begin
    read_data1 = (rs1 == 5'b0) ? 32'b0 : reg_file[rs1];
    read_data2 = (rs2 == 5'b0) ? 32'b0 : reg_file[rs2];
end

// Write (WB aşamasından)
always @(posedge clk) begin
    if (wr_en && (wr_addr != 5'b0)) begin
        reg_file[wr_addr] <= wr_data;
    end
end
```

### 3.5 Hazard Detection

Decode aşamasında data hazards tespit edilir ve stall işlemi gerçekleştirilir.

```systemverilog
// Data Hazard: Önceki komut rd'yi yazacaksa ve
// bu komut rs1 veya rs2 olarak kullanıyor
logic data_hazard;
assign data_hazard = (prev_rd_wr_en && 
                      ((prev_rd == rs1 && rs1 != 5'b0) ||
                       (prev_rd == rs2 && rs2 != 5'b0)));

// Pipeline stall gerekiyorsa
assign stall = data_hazard || memory_stall;
```

---

## 4. Execute Stage (EX - Execution)

### 4.1 Genel Açıklama

Execute aşaması, ALU (Arithmetic Logic Unit), Multiplier ve Branch Logic'i içerir.

**Dosya Konumu**: `rtl/core/stage03_execute/`

### 4.2 ALU (Arithmetic Logic Unit)

ALU, temel aritmetik ve mantıksal işlemleri gerçekleştirir.

```systemverilog
// ALU Operasyonları
typedef enum logic [3:0] {
    ALU_ADD,      // Toplama
    ALU_SUB,      // Çıkarma
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

**ALU Özellikleri**:
- 32-bit işlenenler
- Kombinasyonel tasarım (1 cycle)
- Flags: Zero, Carry, Overflow, Sign

### 4.3 Multiplier (RV32M)

Ceres, Multiply/Divide opsiyonunu destekler.

#### Multiplier Tasarımı

```systemverilog
// Yaramaz Multiplier (Radix-4)
// 32x32 → 64 bit
// 2 cycle sürer

module multiplier_radix4 (
    input clk, rst,
    input logic [31:0] multiplicand,
    input logic [31:0] multiplier,
    input logic start,
    
    output logic [63:0] product,
    output logic valid
);

// İç işlem: 16 aşama (32 bit / 2)
// Adım başına: 2 bit işlenir
```

**Multiplier Özellikleri**:
- Radix-4 algoritması
- 2 cycle latency
- Signed ve unsigned destekler

#### Divider Tasarımı

```systemverilog
// Bölüm Algoritması (Non-restoring Division)
// 32 ÷ 32 → Q + R
// 34 cycle sürer (iteratif)

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

**Divider Özellikleri**:
- Non-restoring division
- 34 cycle latency (32 bit + overhead)
- Zero divisor detection
- Signed ve unsigned destekler

### 4.4 Branch Logic

```systemverilog
// Şart Kontrolleri
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

// Branch Hedgehog (Branch Target)
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

### 5.1 Genel Açıklama

Memory aşaması, Load/Store işlemleri için veri belleğine erişimden sorumludur.

**Dosya Konumu**: `rtl/core/stage04_memory/`

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

**Cache Parametreleri**:

| Parametre | Değer | Açıklama |
|-----------|-------|----------|
| CACHE_LINE_SIZE | 16B (128b) | Minimal cache satırı |
| CACHE_SETS | 128 | Toplam cache set sayısı |
| CACHE_WAYS | 2 | 2-way associative |
| CACHE_SIZE | 4KB | Toplam cache boyutu |
| CACHE_POLICY | LRU | Replacement: Least Recently Used |

### 5.3 Load İşlemleri

```systemverilog
// Load Komutları
typedef enum logic [2:0] {
    LOAD_BYTE,           // LB (8-bit signed)
    LOAD_BYTE_UNSIGNED,  // LBU (8-bit unsigned)
    LOAD_HALF,           // LH (16-bit signed)
    LOAD_HALF_UNSIGNED,  // LHU (16-bit unsigned)
    LOAD_WORD            // LW (32-bit)
} load_type_t;

// Load İşlem Akışı
always @(posedge clk) begin
    // 1. Address hesaplama: addr = rs1 + imm
    mem_addr = reg_data[rs1] + sign_extend(imm);
    
    // 2. Cache lookup
    if (cache_hit) begin
        load_data = cache_data;
    end else begin
        // Miss: Main memory'den getir
        mem_req_valid = 1'b1;
        wait_memory = 1'b1;
    end
    
    // 3. Sign extension veya zero padding
    case (load_type)
        LOAD_BYTE: rd_data = sign_extend_8(load_data[7:0]);
        LOAD_HALF: rd_data = sign_extend_16(load_data[15:0]);
        LOAD_WORD: rd_data = load_data[31:0];
    endcase
end
```

### 5.4 Store İşlemleri

```systemverilog
// Store Komutları
typedef enum logic [1:0] {
    STORE_BYTE,  // SB (8-bit)
    STORE_HALF,  // SH (16-bit)
    STORE_WORD   // SW (32-bit)
} store_type_t;

// Store İşlem Akışı
always @(posedge clk) begin
    // 1. Address hesaplama
    mem_addr = rs1 + sign_extend(imm);
    
    // 2. Data hazırlama (alignment)
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
        // Write-through: Main memory'ye yaz
        mem_write_req = 1'b1;
    end
end
```

### 5.5 Bellek Hizalama

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

### 5.6 Cache Kontrol

```systemverilog
// Cache Write-through Policy
typedef enum logic [1:0] {
    CACHE_DIRTY,     // Yazılmış ama bellekte değil
    CACHE_CLEAN,     // Bellekte güncel
    CACHE_INVALID    // Geçersiz
} cache_state_t;

// LRU Replacement
logic [CACHE_WAYS-1:0] lru;  // Least recently used way

// Cache Hit/Miss
assign cache_hit = (cache_tag == mem_addr[31:7]) && cache_valid;
assign cache_miss = ~cache_hit && mem_req_valid;
```

---

## 6. Write-Back Stage (WB - Write-Back)

### 6.1 Genel Açıklama

Write-Back aşaması, compute sonuçlarını register dosyasına geri yazar.

**Dosya Konumu**: `rtl/core/stage05_writeback/`

### 6.2 Write-Back Kontrol

```systemverilog
// Write-back Sources
typedef enum logic [1:0] {
    WB_ALU,       // ALU sonucu
    WB_MEMORY,    // Load sonucu
    WB_PC_NEXT,   // PC+4 (JAL/JALR)
    WB_CSR        // CSR değeri
} wb_source_t;

// Write-back Multiplexer
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

Forwarding (data bypass) kümesi, data hazards'ı minimize eder:

```systemverilog
// EX Forward: Execute'dan Decode'a
logic ex_forward_valid;
assign ex_forward_valid = (ex_rd_wr_en && 
                           ((ex_rd == id_rs1 && id_rs1 != 5'b0) ||
                            (ex_rd == id_rs2 && id_rs2 != 5'b0)));

// MEM Forward: Memory'den Decode'a
logic mem_forward_valid;
assign mem_forward_valid = (mem_rd_wr_en && 
                            ((mem_rd == id_rs1 && id_rs1 != 5'b0) ||
                             (mem_rd == id_rs2 && id_rs2 != 5'b0)));

// WB Forward: Write-Back'ten Decode'a (nadir)
logic wb_forward_valid;
assign wb_forward_valid = (wb_enable && 
                           ((wb_rd == id_rs1 && id_rs1 != 5'b0) ||
                            (wb_rd == id_rs2 && id_rs2 != 5'b0)));
```

---

## 7. Control & Status Registers (CSR)

### 7.1 Desteklenen CSR'ler

Ceres, aşağıdaki CSR'leri destekler:

#### User-Level CSR'ler
| CSR Adı | Adres | Açıklama |
|---------|-------|----------|
| FCSR | 0x001 | Floating-Point Control |
| FFLAGS | 0x004 | FP Exception Flags |
| FRM | 0x005 | FP Rounding Mode |
| UTIME | 0xC00 | User Timer (Read-only) |

#### Supervisor-Level CSR'ler
| CSR Adı | Adres | Açıklama |
|---------|-------|----------|
| SSTATUS | 0x100 | Supervisor Status |
| SIE | 0x104 | Supervisor Interrupt Enable |
| STVEC | 0x105 | Supervisor Trap Vector |
| SCAUSE | 0x142 | Supervisor Cause |
| STVAL | 0x143 | Supervisor Trap Value |

#### Machine-Level CSR'ler
| CSR Adı | Adres | Açıklama |
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
// CSR Komutları
typedef enum logic [2:0] {
    CSR_RW,      // Read-Write
    CSR_RS,      // Read-Set
    CSR_RC,      // Read-Clear
    CSR_RWI,     // Read-Write Immediate
    CSR_RSI,     // Read-Set Immediate
    CSR_RCI      // Read-Clear Immediate
} csr_op_t;

// CSR İşlemleri
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

## 8. İstisna ve Interrupt Yönetimi

### 8.1 İstisna Türleri

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

### 8.2 İstisna İşleme Akışı

```
    ┌─────────────────────┐
    │  İstisna Tespit     │
    │  (Herhangi aşamada) │
    └──────────┬──────────┘
               │
    ┌──────────▼──────────┐
    │ Exception Priority  │
    │ Seç (Parametrik)    │
    └──────────┬──────────┘
               │
    ┌──────────▼──────────┐
    │ Pipeline Flush      │
    │ (Önceki aşamalar)   │
    └──────────┬──────────┘
               │
    ┌──────────▼──────────┐
    │ CSR Güncellemeleri  │
    │ - MCAUSE            │
    │ - MTVAL             │
    │ - MEPC              │
    └──────────┬──────────┘
               │
    ┌──────────▼──────────┐
    │ Handler Çıkartılır  │
    │ (MTVEC adresinden)  │
    └──────────┬──────────┘
               │
    ┌──────────▼──────────┐
    │ PC ← Handler Adres  │
    │ Pipeline Yeniden    │
    │ Başlatılır          │
    └─────────────────────┘
```

### 8.3 Exception Priority Örneği

**Senaryo**: Aynı anda 3 istisna var

```
Durumu:
- Debug Breakpoint (EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_1)
- Instruction Misaligned (EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_2)
- Illegal Instruction (EXC_PRIORITY_ILLEGAL = PRIORITY_4)

Priority Check Sırası:
1. Debug Breakpoint: check_exc_priority(PRIORITY_1, PRIORITY_7) → TRUE ✓
   → Debug Breakpoint seçilir

Sonuç: Debug Breakpoint işlenir (en yüksek priority)
```

---

## 9. Bellek Sistemi

### 9.1 Bellek Mimarisi

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

### 9.2 Bellek Erişim Latency

| Bellek Türü | Latency | Cache | Notes |
|-------------|---------|-------|-------|
| L1 I-Cache | 1 cycle | Hit | On-chip, fast |
| L1 D-Cache | 1 cycle | Hit | On-chip, fast |
| L2 Cache (None) | — | — | Tasarımda yok |
| Main Memory | 10+ cycle | Miss | AXI4 via fabric |
| Peripherals | Variable | None | UART vs real devices |

### 9.3 Memory Ordering (FENCE)

```systemverilog
// FENCE Komut İşlemi
typedef struct {
    logic predecessor_read;    // PI (Predecessor Instruction)
    logic predecessor_write;   // PW
    logic successor_read;      // SI (Successor Instruction)
    logic successor_write;     // SW
} fence_bits_t;

// FENCE Pipeline Stall
always @(posedge clk) begin
    if (fence_instruction) begin
        pipeline_stall = 1'b1;
        // Tüm önceki instruction'lar tamamlanana kadar
        wait_for_completion = 1'b1;
    end
end
```

---

## 10. Debug ve Trace Sistemi

### 10.1 Trace Port

Ceres, simulation ve debug amaçlı trace çıkışı sağlar:

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
// Debug Trigger Kontrol (tdata1)
typedef struct {
    logic type_select;     // Trigger tipi
    logic dmode;           // Debug mode
    logic [3:0] match_type; // Match kriteri
    logic execute;         // Execute trigger
    logic store;           // Store trigger
    logic load;            // Load trigger
} trigger_control_t;

// Debug Trigger Data (tdata2)
logic [31:0] tdata2;  // Breakpoint adresi

// Breakpoint Tespit
logic breakpoint = tdata1[2] && (pc == tdata2);
```

---

## 11. Performans Özellikleri

### 11.1 Pipeline Throughput

```
Ideal Durum (Stall yok):
    1 instruction per cycle (1 IPC)
    
With Hazards:
    - Load-use: +1 cycle stall
    - Branch misprediction: +3 cycle penalty
    - DIV: +34 cycle latency
    - MUL: +2 cycle latency
```

### 11.2 Çevirme Gecikmesi (latency)

| İşlem | Latency | Notes |
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

### 11.3 DMIPS Skor

```
Ceres RISC-V @ 1 MHz:
    ~1 DMIPS/MHz
    
Örnek:
    @ 100 MHz: ~100 DMIPS
    @ 200 MHz: ~200 DMIPS
```

---

## 12. Parametrik Tasarım

### 12.1 Önemli Parametreler

**Dosya**: `rtl/pkg/ceres_param.sv`

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
// ... (daha fazla)
```

### 12.2 Kustomizasyon

Alternatif yapılandırmalar `rtl/include/exception_priority.svh`'de tanımlanmıştır:

```systemverilog
// Örnek: Alternative Priority Configuration
`ifdef EXCEPTION_PRIORITY_MISALIGNED_FIRST
    localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_1;  // Swap
    localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_2;
`else
    // Default RISC-V spec-uyumlu
    localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_1;
    localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_2;
`endif
```

---

## 13. Testlenebilirlik

### 13.1 DPI-C İnterface

Ceres, C ile yazılmış test harness'leri desteklemek için DPI-C arayüzü sağlar.

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
# VCD oluştur (waveform.vcd)
make wave

# VCD'yi GTKWave ile aç
gtkwave build/work/waveform.vcd &
```

### 13.3 Test Coverage

```bash
# Coverage raporu oluştur
make coverage

# HTML raporu aç
firefox build/logs/coverage/index.html &
```

---

## 14. Hata Ayıklama (Debugging)

### 14.1 Breakpoint Ayarı

```
Machine Debug Interface (MDI) yazmaç:
1. tdata1 ← breakpoint kontrol
2. tdata2 ← breakpoint adresi
3. Debugger bu adreste trap alır
```

### 14.2 Trace Analiz

```bash
# Simülasyondan trace almak
make trace

# Trace dosyası: build/logs/trace.txt
# Her instruction bir satır (PC, opcode, rd, rd_data, vb)
```

### 14.3 Post-Sim Analiz

```python
# Python script: analyze_trace.py
import pandas as pd
df = pd.read_csv('build/logs/trace.txt')
# Exception'lar filtrele
exceptions = df[df['exc_type'] != 'NONE']
print(exceptions)
```

---

## 15. Önerilen Okuma Sırası

1. **Başlayanlar için**: Bölüm 1 (Genel Özet) → Bölüm 2-3 (Fetch/Decode)
2. **İleri seviye**: Bölüm 4-6 (EX/MEM/WB) → Bölüm 8 (İstisna Yönetimi)
3. **Tasarımcılar**: Bölüm 7 (CSR) → Bölüm 12 (Parametrik Tasarım)
4. **Test Yazanları**: Bölüm 13-14 (Testlenebilirlik/Debugging)

---

## 16. Kaynaklar ve Referanslar

### RISC-V Specifications
- [RISC-V User-Level ISA Spec](https://riscv.org/specifications/)
- [RISC-V Privileged Spec](https://riscv.org/specifications/privileged-isa/)

### Ceres İçsel Kaynaklar
- `rtl/core/` - Verilog Tasarım dosyaları
- `rtl/pkg/ceres_param.sv` - Parametrik tanımlar
- `rtl/include/` - Header dosyaları
- `script/` - Python ve Shell scriptler
- `docs/` - Dökümantasyon

### İlgili Belgeler
- [PARAMETRIC_EXCEPTION_PRIORITY.md](./PARAMETRIC_EXCEPTION_PRIORITY.md)
- [IMPLEMENTATION_SUMMARY.md](./IMPLEMENTATION_SUMMARY.md)
- [riscv-test.md](./riscv-test.md)

---

**Son Güncelleme**: 1 Aralık 2025  
**Versiyon**: 1.0  
**Yazar**: Ceres Development Team

