# CPU Modülü - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Pipeline Mimarisi](#pipeline-mimarisi)
4. [Pipeline Register Yapıları](#pipeline-register-yapıları)
5. [Stall ve Flush Mekanizmaları](#stall-ve-flush-mekanizmaları)
6. [Exception Yönetimi](#exception-yönetimi)
7. [Branch Prediction Geri Bildirimi](#branch-prediction-geri-bildirimi)
8. [Bellek Arbiter](#bellek-arbiter)
9. [Donanım Kesmeleri](#donanım-kesmeleri)
10. [Zamanlama Diyagramları](#zamanlama-diyagramları)
11. [Performans Analizi](#performans-analizi)
12. [Doğrulama ve Test](#doğrulama-ve-test)

---

## Genel Bakış

### Amaç

`cpu` modülü, CERES RISC-V işlemcisinin **üst seviye (top-level)** modülüdür. Bu modül, 5-aşamalı pipeline mimarisini bir araya getirir ve tüm alt modüller arasındaki veri akışını koordine eder.

### Temel Özellikler

| Özellik | Değer |
|---------|-------|
| **ISA** | RV32IMC (Base Integer + Multiply + Compressed) |
| **Pipeline Derinliği** | 5 aşama (Fetch, Decode, Execute, Memory, Writeback) |
| **Adresleme** | 32-bit |
| **Bellek Mimarisi** | Von Neumann (Unified Memory) |
| **Branch Prediction** | GSHARE + BTB + RAS |
| **Önbellek** | I-Cache + D-Cache (8-way, 8KB) |
| **İstisna Desteği** | Tam M-mode exception handling |
| **CSR Desteği** | Machine-mode CSR'ler |
| **Kesme Desteği** | Timer, Software, External (PLIC) |

### Mimari Blok Diyagramı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                                    CPU TOP                                       │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────────┐   │
│  │  FETCH  │───▶│  DECODE │───▶│ EXECUTE │───▶│  MEMORY │───▶│  WRITEBACK  │   │
│  │ Stage 1 │    │ Stage 2 │    │ Stage 3 │    │ Stage 4 │    │   Stage 5   │   │
│  └────┬────┘    └────┬────┘    └────┬────┘    └────┬────┘    └──────┬──────┘   │
│       │              │              │              │                 │          │
│       │    pipe1     │    pipe2     │    pipe3     │      pipe4      │          │
│       └──────────────┴──────────────┴──────────────┴─────────────────┘          │
│                                                                                  │
│  ┌─────────────────────────────────────────────────────────────────────────┐   │
│  │                          HAZARD UNIT                                     │   │
│  │   • Data Forwarding (EX→EX, MEM→EX, WB→EX, WB→DE)                       │   │
│  │   • Load-Use Stall Detection                                             │   │
│  │   • Branch Flush Control                                                 │   │
│  └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│  ┌─────────────────────────────────────────────────────────────────────────┐   │
│  │                        MEMORY ARBITER                                    │   │
│  │   • I-Cache ↔ D-Cache Arbitration                                        │   │
│  │   • Wishbone Bus Interface                                               │   │
│  └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module cpu
  import ceres_param::*;
(
    // Saat ve Reset
    input  logic       clk_i,        // Sistem saati
    input  logic       rst_ni,       // Aktif-düşük asenkron reset
    
    // Donanım Kesmeleri
    input  logic       timer_irq_i,  // CLINT timer interrupt (MTIP)
    input  logic       sw_irq_i,     // CLINT software interrupt (MSIP)
    input  logic       ext_irq_i,    // PLIC external interrupt (MEIP)
    
    // Bellek Arayüzü
    output iomem_req_t iomem_req_o,  // Bellek istek bus'ı
    input  iomem_res_t iomem_res_i   // Bellek yanıt bus'ı
);
```

### Port Açıklamaları

#### Saat ve Reset

| Port | Yön | Genişlik | Açıklama |
|------|-----|----------|----------|
| `clk_i` | Giriş | 1 bit | Pozitif kenar tetiklemeli sistem saati |
| `rst_ni` | Giriş | 1 bit | Aktif-düşük asenkron reset (0 = reset aktif) |

#### Donanım Kesmeleri

| Port | Yön | Genişlik | Açıklama |
|------|-----|----------|----------|
| `timer_irq_i` | Giriş | 1 bit | CLINT timer kesmesi (MTIP - Machine Timer Interrupt Pending) |
| `sw_irq_i` | Giriş | 1 bit | CLINT yazılım kesmesi (MSIP - Machine Software Interrupt Pending) |
| `ext_irq_i` | Giriş | 1 bit | PLIC harici kesme (MEIP - Machine External Interrupt Pending) |

#### Bellek Arayüzü

| Port | Yön | Tip | Açıklama |
|------|-----|-----|----------|
| `iomem_req_o` | Çıkış | `iomem_req_t` | Wishbone-uyumlu bellek istek yapısı |
| `iomem_res_i` | Giriş | `iomem_res_t` | Wishbone-uyumlu bellek yanıt yapısı |

### Bellek Arayüz Yapıları

```systemverilog
// Bellek İstek Yapısı (iomem_req_t)
typedef struct packed {
    logic [XLEN-1:0]       addr;     // Bellek adresi
    logic [XLEN-1:0]       wdata;    // Yazılacak veri
    logic [WB_SEL_WIDTH-1:0] sel;    // Byte seçim sinyalleri
    logic                  we;       // Yazma enable (1=write, 0=read)
    logic                  valid;    // İstek geçerlilik
    logic [2:0]            burst;    // Burst tipi
} iomem_req_t;

// Bellek Yanıt Yapısı (iomem_res_t)
typedef struct packed {
    logic [XLEN-1:0]       rdata;    // Okunan veri
    logic                  ready;    // Yanıt hazır
    logic                  error;    // Hata durumu
} iomem_res_t;
```

---

## Pipeline Mimarisi

### 5-Aşamalı Pipeline Genel Yapısı

```
Cycle:    1     2     3     4     5     6     7     8
        ┌─────┬─────┬─────┬─────┬─────┐
Instr 1 │ IF  │ DE  │ EX  │ MEM │ WB  │
        └─────┴─────┴─────┴─────┴─────┘
              ┌─────┬─────┬─────┬─────┬─────┐
Instr 2       │ IF  │ DE  │ EX  │ MEM │ WB  │
              └─────┴─────┴─────┴─────┴─────┘
                    ┌─────┬─────┬─────┬─────┬─────┐
Instr 3             │ IF  │ DE  │ EX  │ MEM │ WB  │
                    └─────┴─────┴─────┴─────┴─────┘
                          ┌─────┬─────┬─────┬─────┬─────┐
Instr 4                   │ IF  │ DE  │ EX  │ MEM │ WB  │
                          └─────┴─────┴─────┴─────┴─────┘
```

### Pipeline Aşamaları

#### Stage 1: Instruction Fetch (IF)

```systemverilog
fetch #(
    .RESET_VECTOR(RESET_VECTOR)
) i_fetch (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .flush_i      (fencei_flush),      // FENCE.I cache flush
    .flush_pc_i   (flush_pc),          // Flush sonrası PC
    .stall_i      (stall_cause),       // Stall nedeni
    .lx_ires_i    (fe_lx_ires),        // I-Cache yanıtı
    .pc_target_i  (ex_pc_target_last), // Branch hedef adresi
    .spec_hit_i   (ex_spec_hit),       // Speculation doğru mu?
    .ex_mtvec_i   (ex_mtvec),          // Trap vektör adresi
    .trap_active_i(fe_trap_active),    // Trap aktif mi?
    .misa_c_i     (ex_misa_c),         // C-extension aktif mi?
    .tdata1_i     (ex_tdata1),         // Trigger data 1
    .tdata2_i     (ex_tdata2),         // Trigger data 2
    .tcontrol_i   (ex_tcontrol),       // Trigger control
    .spec_o       (fe_spec),           // Branch prediction bilgisi
    .lx_ireq_o    (lx_ireq),           // I-Cache isteği
    .pc_o         (fe_pc),             // Mevcut PC
    .pc_incr_o    (fe_pc_incr),        // Sonraki PC (PC+2/4)
    .inst_o       (fe_inst),           // Fetch edilen instruction
    .imiss_stall_o(fe_imiss_stall),    // I-Cache miss stall
    .exc_type_o   (fe_exc_type),       // Exception tipi
    .instr_type_o (fe_instr_type),     // Instruction tipi
    .de_info_i    (de_info),           // Decode geri bildirimi
    .ex_info_i    (ex_info)            // Execute geri bildirimi
);
```

**Fetch Aşaması Görevleri:**
- Program Counter (PC) yönetimi
- Instruction cache erişimi
- Compressed instruction (RV32C) decode
- Branch prediction (GSHARE, BTB, RAS)
- Instruction alignment (32-bit boundary)
- Exception detection (INSTR_ACCESS_FAULT, ILLEGAL_INSTRUCTION)

#### Stage 2: Instruction Decode (DE)

```systemverilog
decode i_decode (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),
    .fwd_a_i     (de_fwd_a),        // Rs1 forwarding from WB
    .fwd_b_i     (de_fwd_b),        // Rs2 forwarding from WB
    .wb_data_i   (wb_data),         // Writeback data
    .inst_i      (pipe1.inst),      // Instruction from fetch
    .instr_type_i(pipe1.instr_type),// Instruction type
    .rd_addr_i   (pipe4.rd_addr),   // WB destination register
    .rf_rw_en_i  (wb_rf_rw),        // WB register write enable
    .r1_data_o   (de_r1_data),      // Rs1 data
    .r2_data_o   (de_r2_data),      // Rs2 data
    .ctrl_o      (de_ctrl),         // Control signals
    .imm_o       (de_imm),          // Immediate value
    .exc_type_o  (de_exc_type)      // Exception type
);
```

**Decode Aşaması Görevleri:**
- Instruction çözümleme (opcode, funct3, funct7)
- Register file okuma (rs1, rs2)
- Immediate değer genişletme
- Control signal üretimi
- Hazard detection için bilgi sağlama

#### Stage 3: Execute (EX)

```systemverilog
execution i_execution (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .stall_i      (stall_cause),
    .fwd_a_i      (ex_fwd_a),         // Rs1 forwarding select
    .fwd_b_i      (ex_fwd_b),         // Rs2 forwarding select
    .alu_result_i (pipe3.alu_result), // MEM stage ALU result
    .wb_data_i    (wb_data),          // WB stage data
    .r1_data_i    (pipe2.r1_data),    // Rs1 from decode
    .r2_data_i    (pipe2.r2_data),    // Rs2 from decode
    .alu_in1_sel_i(pipe2.alu_in1_sel),// ALU input 1 select
    .alu_in2_sel_i(pipe2.alu_in2_sel),// ALU input 2 select
    .instr_type_i (pipe2.instr_type), // Instruction type
    .trap_active_i(trap_active),      // Trap active flag
    .trap_tval_i  (trap_tval),        // Trap value
    .trap_cause_i (ex_trap_cause),    // Trap cause
    .trap_mepc_i  (ex_trap_mepc),     // Trap return address
    .timer_irq_i  (timer_irq_i),      // Timer interrupt
    .sw_irq_i     (sw_irq_i),         // Software interrupt
    .ext_irq_i    (ext_irq_i),        // External interrupt
    .rd_csr_i     (ex_rd_csr),        // CSR read enable
    .wr_csr_i     (ex_wr_csr),        // CSR write enable
    .csr_idx_i    (pipe2.csr_idx),    // CSR index
    .csr_or_data_i(pipe2.csr_or_data),// CSR operation or data
    .pc_i         (pipe2.pc),         // Current PC
    .pc_incr_i    (pipe2.pc_incr),    // Next PC
    .imm_i        (pipe2.imm),        // Immediate
    .pc_sel_i     (pipe2.pc_sel),     // Branch type
    .alu_ctrl_i   (pipe2.alu_ctrl),   // ALU operation
    .write_data_o (ex_wdata),         // Store data
    .pc_target_o  (ex_pc_target),     // Branch target
    .alu_result_o (ex_alu_result),    // ALU result
    .pc_sel_o     (ex_pc_sel),        // Branch taken
    .alu_stall_o  (ex_alu_stall),     // MUL/DIV stall
    .exc_type_o   (ex_alu_exc_type),  // Exception type
    .mtvec_o      (ex_mtvec),         // Trap vector
    .misa_c_o     (ex_misa_c),        // C-extension enable
    .tdata1_o     (ex_tdata1),        // Trigger data 1
    .tdata2_o     (ex_tdata2),        // Trigger data 2
    .tcontrol_o   (ex_tcontrol)       // Trigger control
);
```

**Execute Aşaması Görevleri:**
- ALU işlemleri (aritmetik, mantıksal, karşılaştırma)
- Branch/Jump koşul hesaplama
- Multiply/Divide işlemleri
- CSR okuma/yazma
- Exception detection ve handling
- Data forwarding uygulama

#### Stage 4: Memory Access (MEM)

```systemverilog
memory i_memory (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),
    .stall_i          (stall_cause),
    .fe_flush_cache_i (fencei_flush),   // FENCE.I cache flush
    .me_data_req_i    (me_data_req),    // Memory request (from pipe3)
    .ex_data_req_i    (ex_data_req),    // Memory request (from EX)
    .lx_dres_i        (lx_dres),        // D-Cache response
    .lx_dreq_o        (lx_dreq),        // D-Cache request
    .me_data_o        (me_rdata),       // Load data
    .dmiss_stall_o    (me_dmiss_stall), // D-Cache miss stall
    .fencei_stall_o   (me_fencei_stall) // FENCE.I stall
);
```

**Memory Aşaması Görevleri:**
- Data cache erişimi
- Load/Store işlemleri
- Byte/Halfword/Word hizalama
- Cache miss yönetimi
- FENCE.I cache flush

#### Stage 5: Write-Back (WB)

```systemverilog
writeback i_writeback (
    .clk_i           (clk_i),
    .rst_ni          (rst_ni),
    .data_sel_i      (pipe4.result_src), // Data source select
    .pc_incr_i       (pipe4.pc_incr),    // PC+2/4
    .pc_i            (pipe4.pc),         // Current PC
    .alu_result_i    (pipe4.alu_result), // ALU result
    .read_data_i     (pipe4.read_data),  // Memory data
    .stall_i         (stall_cause),      // Stall cause
    .rf_rw_en_i      (pipe4.rf_rw_en),   // Register write enable
    .rf_rw_en_o      (wb_rf_rw),         // Actual write enable
    .wb_data_o       (wb_data)           // Write-back data
);
```

**Write-Back Aşaması Görevleri:**
- Result source seçimi (ALU, Memory, PC+4)
- Register file yazma
- Instruction commit

---

## Pipeline Register Yapıları

### pipe1: Fetch → Decode

```systemverilog
typedef struct packed {
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;    // Trace bilgisi
`endif
    logic [XLEN-1:0] pc;           // Program counter
    logic [XLEN-1:0] pc_incr;      // PC + 2 veya PC + 4
    logic [XLEN-1:0] inst;         // 32-bit instruction
    exc_type_e       exc_type;     // Exception tipi
    instr_type_e     instr_type;   // Instruction tipi
    predict_info_t   spec;         // Branch prediction bilgisi
} pipe1_t;
```

**Pipeline Register Kontrolü:**

```systemverilog
always_ff @(posedge clk_i) begin
    if (!rst_ni || de_flush_en || |priority_flush || fencei_flush) begin
        // Reset veya flush durumunda NOP yükle
        pipe1 <= '{exc_type: NO_EXCEPTION, instr_type: instr_invalid, default: 0};
    end else if (de_enable) begin
        // Normal işlem: fetch'ten gelen verileri yükle
        pipe1 <= '{
            pc       : fe_pc,
            pc_incr  : fe_pc_incr,
            inst     : fe_inst,
            exc_type : fe_active_exc_type,
            instr_type: fe_instr_type,
            spec     : fe_spec
            // ... tracer fields
        };
    end
end
```

### pipe2: Decode → Execute

```systemverilog
typedef struct packed {
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;
`endif
    logic [XLEN-1:0] pc;           // Program counter
    logic [XLEN-1:0] pc_incr;      // Sonraki PC
    logic            rf_rw_en;     // Register yazma enable
    logic            wr_en;        // Memory yazma enable
    logic [1:0]      rw_size;      // Load/Store boyutu
    logic [1:0]      result_src;   // Result kaynağı
    alu_op_e         alu_ctrl;     // ALU işlem tipi
    pc_sel_e         pc_sel;       // Branch/Jump tipi
    logic            alu_in1_sel;  // ALU input 1 seçimi
    logic            alu_in2_sel;  // ALU input 2 seçimi
    logic            ld_op_sign;   // Load sign extension
    logic            rd_csr;       // CSR okuma enable
    logic            wr_csr;       // CSR yazma enable
    logic [11:0]     csr_idx;      // CSR adresi
    logic            csr_or_data;  // CSR op veya immediate
    logic            dcache_valid; // D-Cache geçerli
    logic [XLEN-1:0] r1_data;      // Rs1 değeri
    logic [XLEN-1:0] r2_data;      // Rs2 değeri
    logic [4:0]      r1_addr;      // Rs1 adresi
    logic [4:0]      r2_addr;      // Rs2 adresi
    logic [4:0]      rd_addr;      // Rd adresi
    logic [XLEN-1:0] imm;          // Immediate değeri
    instr_type_e     instr_type;   // Instruction tipi
    predict_info_t   spec;         // Branch prediction bilgisi
} pipe2_t;
```

### pipe3: Execute → Memory

```systemverilog
typedef struct packed {
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;
    logic            rd_en_csr;    // CSR okundu mu
    logic            wr_en_csr;    // CSR yazıldı mı
    logic [11:0]     csr_idx;      // CSR adresi
    instr_type_e     instr_type;   // Instruction tipi
    logic [XLEN-1:0] csr_wr_data;  // CSR yazma verisi
`endif
    logic [XLEN-1:0] pc_incr;      // Sonraki PC
    logic [XLEN-1:0] pc;           // Program counter
    logic            rf_rw_en;     // Register yazma enable
    logic            wr_en;        // Memory yazma enable
    logic [1:0]      rw_size;      // Load/Store boyutu
    logic [1:0]      result_src;   // Result kaynağı
    logic            ld_op_sign;   // Load sign extension
    logic [4:0]      rd_addr;      // Rd adresi
    logic [XLEN-1:0] alu_result;   // ALU sonucu
    logic [XLEN-1:0] write_data;   // Store verisi
    logic            dcache_valid; // D-Cache geçerli
    logic [XLEN-1:0] read_data;    // Load verisi
} pipe3_t;
```

### pipe4: Memory → Write-Back

```systemverilog
typedef struct packed {
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;
    logic            wr_en;
    logic [1:0]      rw_size;
    logic [XLEN-1:0] write_data;
    logic            rd_en_csr;
    logic            wr_en_csr;
    logic [11:0]     csr_idx;
    instr_type_e     instr_type;
    logic [XLEN-1:0] csr_wr_data;
    logic            dcache_valid;
`endif
    logic [XLEN-1:0] pc_incr;      // Sonraki PC
    logic [XLEN-1:0] pc;           // Program counter
    logic            rf_rw_en;     // Register yazma enable
    logic [1:0]      result_src;   // Result kaynağı
    logic [4:0]      rd_addr;      // Rd adresi
    logic [XLEN-1:0] alu_result;   // ALU sonucu
    logic [XLEN-1:0] read_data;    // Load verisi
} pipe4_t;
```

---

## Stall ve Flush Mekanizmaları

### Stall Nedenleri

```systemverilog
typedef enum logic [2:0] {
    NO_STALL       = 3'b000,  // Stall yok
    IMISS_STALL    = 3'b001,  // I-Cache miss
    DMISS_STALL    = 3'b010,  // D-Cache miss
    LOAD_RAW_STALL = 3'b011,  // Load-use hazard
    ALU_STALL      = 3'b100,  // MUL/DIV beklemesi
    FENCEI_STALL   = 3'b101   // FENCE.I cache flush
} stall_e;
```

### Stall Öncelik Sıralaması

```systemverilog
always_comb begin
    stall_cause = NO_STALL;
    
    if (me_fencei_stall) begin
        // En yüksek öncelik: FENCE.I dirty writeback
        stall_cause = FENCEI_STALL;
    end else if (fe_imiss_stall) begin
        // I-Cache miss
        stall_cause = IMISS_STALL;
    end else if (me_dmiss_stall) begin
        // D-Cache miss
        stall_cause = DMISS_STALL;
    end else if (fe_stall || de_stall) begin
        // Load-use hazard
        stall_cause = LOAD_RAW_STALL;
    end else if (ex_alu_stall) begin
        // MUL/DIV işlemi devam ediyor
        stall_cause = ALU_STALL;
    end
end
```

### Stall Davranışları

| Stall Tipi | Etkilenen Aşamalar | Açıklama |
|------------|-------------------|----------|
| `FENCEI_STALL` | Tüm pipeline | D-Cache dirty line writeback beklemesi |
| `IMISS_STALL` | Fetch, Decode | I-Cache miss, bellek erişimi bekleniyor |
| `DMISS_STALL` | Tüm pipeline | D-Cache miss, bellek erişimi bekleniyor |
| `LOAD_RAW_STALL` | Fetch, Decode | Load-use data hazard |
| `ALU_STALL` | Tüm pipeline | MUL/DIV işlemi tamamlanmadı |

### Flush Mekanizmaları

#### Priority Flush (Exception Tabanlı)

```systemverilog
// Exception önceliğine göre flush kararı
priority_flush = ex_exc_type != NO_EXCEPTION ? 3:          // EX exception
                 de_active_exc_type != NO_EXCEPTION ? 2 :  // DE exception
                 0;                                        // Flush yok
```

| priority_flush | Flush Alanı | Açıklama |
|---------------|-------------|----------|
| 3 | pipe1, pipe2 | Execute exception (en yüksek öncelik) |
| 2 | pipe1 | Decode exception |
| 0 | Yok | Flush gerekmez |

#### FENCE.I Flush

```systemverilog
// FENCE.I veya MISA yazması durumunda cache flush
fencei_flush = (pipe2.instr_type == fence_i) || 
               (ex_wr_csr && pipe2.csr_idx == 12'h301);  // misa write

// Flush sonrası dönülecek PC
flush_pc = pipe2.pc_incr;
```

#### Branch Misprediction Flush

```systemverilog
// Branch prediction doğruluğu kontrolü
if (ex_pc_sel) 
    ex_spec_hit = pipe2.spec.taken && (ex_pc_target == pipe2.spec.pc);
else 
    ex_spec_hit = !pipe2.spec.taken;

// Misprediction durumunda hedef PC
if (!ex_spec_hit) begin
    if (ex_pc_sel) 
        ex_pc_target_last = ex_pc_target;  // Branch alındı, hedef adrese git
    else 
        ex_pc_target_last = pipe2.pc_incr; // Branch alınmadı, sıradaki instr
end
```

### Flush ve Stall Etkileşimi

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        STALL/FLUSH İNTERAKSİYONU                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Stall Aktif İken Flush:                                                    │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ de_flush_en = stall_cause inside {IMISS, DMISS, ALU, FENCEI} ?      │   │
│  │               1'b0 : de_flush;                                       │   │
│  │                                                                      │   │
│  │ ex_flush_en = stall_cause inside {IMISS, DMISS, ALU, FENCEI} ?      │   │
│  │               1'b0 : ex_flush;                                       │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  Mantık: Stall durumunda flush ertelenir, stall çözüldüğünde flush         │
│          uygulanır. Bu, bellek erişimi sırasında veri kaybını önler.       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Exception Yönetimi

### Exception Tipleri

```systemverilog
typedef enum logic [4:0] {
    NO_EXCEPTION         = 5'd0,
    INSTR_MISALIGNED     = 5'd1,   // Instruction hizalama hatası
    INSTR_ACCESS_FAULT   = 5'd2,   // Instruction erişim hatası
    ILLEGAL_INSTRUCTION  = 5'd3,   // Geçersiz instruction
    BREAKPOINT           = 5'd4,   // EBREAK
    LOAD_MISALIGNED      = 5'd5,   // Load hizalama hatası
    LOAD_ACCESS_FAULT    = 5'd6,   // Load erişim hatası
    STORE_MISALIGNED     = 5'd7,   // Store hizalama hatası
    STORE_ACCESS_FAULT   = 5'd8,   // Store erişim hatası
    ECALL_M              = 5'd11   // Machine mode ECALL
} exc_type_e;
```

### Aşama Bazlı Exception Kaynakları

| Aşama | Exception Tipleri | Tespit Yöntemi |
|-------|------------------|----------------|
| **Fetch** | INSTR_ACCESS_FAULT, ILLEGAL_INSTRUCTION | PMA grant yok, C-extension decode hatası |
| **Decode** | ILLEGAL_INSTRUCTION | Tanınmayan opcode, geçersiz CSR |
| **Execute** | INSTR_MISALIGNED, LOAD_MISALIGNED, STORE_MISALIGNED | Adres hizalama kontrolü |
| **Memory** | LOAD_ACCESS_FAULT, STORE_ACCESS_FAULT | PMA ihlali |

### Exception Öncelik Sistemi

```systemverilog
// Exception mask: hangi aşamada exception var?
excp_mask = {1'b0, 
             ex_exc_type != NO_EXCEPTION,        // [2] Execute
             de_active_exc_type != NO_EXCEPTION, // [1] Decode
             fe_active_exc_type != NO_EXCEPTION  // [0] Fetch
            };

// Trap aktif sinyali
trap_active = |excp_mask[3:1];
fe_trap_active = |{excp_mask[3:1], de_active_exc_type != NO_EXCEPTION};
de_trap_active = de_active_exc_type != NO_EXCEPTION;
```

### Trap Cause ve Trap Value Hesaplama

```systemverilog
// Trap cause: en yüksek öncelikli exception'ın kodu
ex_trap_cause = ex_exc_type != NO_EXCEPTION ? trap_cause_decode(ex_exc_type) :
                de_active_exc_type != NO_EXCEPTION ? trap_cause_decode(de_active_exc_type) :
                fe_active_exc_type != NO_EXCEPTION ? trap_cause_decode(fe_active_exc_type) : 
                trap_cause_decode(ex_exc_type);

// Trap mepc: exception oluşan instruction'ın PC'si
ex_trap_mepc = ex_exc_type != NO_EXCEPTION ? pipe2.pc :
               de_active_exc_type != NO_EXCEPTION ? pipe1.pc :
               fe_active_exc_type != NO_EXCEPTION ? fe_pc : 
               pipe2.pc;
```

### Trap Value (mtval) Hesaplama

```systemverilog
always_comb begin
    // Execute stage exceptions
    if (ex_exc_type != NO_EXCEPTION) begin
        unique case (ex_exc_type)
            ILLEGAL_INSTRUCTION: trap_tval = '0;  // Spike uyumu: 0
            LOAD_MISALIGNED,
            STORE_MISALIGNED:    trap_tval = ex_alu_result;  // Faulting address
            default:             trap_tval = '0;
        endcase
    end
    // Decode stage exceptions
    else if (de_active_exc_type != NO_EXCEPTION) begin
        unique case (de_active_exc_type)
            ILLEGAL_INSTRUCTION: trap_tval = '0;
            INSTR_MISALIGNED:    trap_tval = pipe1.pc;  // Faulting PC
            default:             trap_tval = '0;
        endcase
    end
    // Fetch stage exceptions
    else if (fe_active_exc_type != NO_EXCEPTION) begin
        unique case (fe_active_exc_type)
            INSTR_MISALIGNED:    trap_tval = fe_pc;
            ILLEGAL_INSTRUCTION: trap_tval = '0;
            default:             trap_tval = '0;
        endcase
    end
end
```

### Exception Akış Diyagramı

```
┌────────────────────────────────────────────────────────────────────────────────┐
│                          EXCEPTION AKIŞ DİYAGRAMI                              │
├────────────────────────────────────────────────────────────────────────────────┤
│                                                                                │
│     Fetch          Decode         Execute        Memory         Writeback     │
│       │               │               │             │               │         │
│       ▼               ▼               ▼             ▼               ▼         │
│   ┌───────┐       ┌───────┐       ┌───────┐     ┌───────┐       ┌───────┐    │
│   │ fe_exc│──────▶│de_exc │──────▶│ex_exc │     │       │       │       │    │
│   │ _type │       │_type  │       │_type  │     │       │       │       │    │
│   └───────┘       └───────┘       └───────┘     └───────┘       └───────┘    │
│       │               │               │                                       │
│       └───────────────┴───────────────┘                                       │
│                       │                                                        │
│                       ▼                                                        │
│               ┌───────────────┐                                                │
│               │ Priority Mux  │                                                │
│               │ EX > DE > FE  │                                                │
│               └───────┬───────┘                                                │
│                       │                                                        │
│                       ▼                                                        │
│               ┌───────────────┐                                                │
│               │  CSR Update   │                                                │
│               │ mcause, mepc  │                                                │
│               │ mtval, mstatus│                                                │
│               └───────┬───────┘                                                │
│                       │                                                        │
│                       ▼                                                        │
│               ┌───────────────┐                                                │
│               │  PC ← mtvec   │                                                │
│               │  Flush pipe   │                                                │
│               └───────────────┘                                                │
│                                                                                │
└────────────────────────────────────────────────────────────────────────────────┘
```

---

## Branch Prediction Geri Bildirimi

### Speculation Hit/Miss Tespiti

```systemverilog
always_comb begin
    // Branch alındı mı kontrolü
    if (ex_pc_sel) begin
        // Branch/Jump alındı: tahmin doğru mu ve hedef doğru mu?
        ex_spec_hit = pipe2.spec.taken && (ex_pc_target == pipe2.spec.pc);
    end else begin
        // Branch alınmadı: not-taken tahmini doğru mu?
        ex_spec_hit = !pipe2.spec.taken;
    end
end
```

### Misprediction Kurtarma

```systemverilog
always_comb begin
    if (!ex_spec_hit) begin
        // Misprediction: doğru hedefi belirle
        if (ex_pc_sel)
            ex_pc_target_last = ex_pc_target;    // Aslında alınmalıydı
        else
            ex_pc_target_last = pipe2.pc_incr;   // Aslında alınmamalıydı
    end else begin
        ex_pc_target_last = ex_pc_target;
    end
end
```

### Pipeline Feedback Yapıları

```systemverilog
// Decode → Fetch geri bildirimi
typedef struct packed {
    predict_info_t spec;    // Branch prediction bilgisi
    logic          bjtype;  // Branch/Jump instruction mı?
    logic [XLEN-1:0] pc;    // Instruction PC
} pipe_info_t;

// Execute → Fetch geri bildirimi
always_comb begin
    ex_info.spec   = pipe2.spec;
    ex_info.bjtype = is_branch(pipe2.instr_type);
    ex_info.pc     = pipe2.pc;
end
```

### Branch Resolution Zamanlama

```
Cycle:     1      2      3      4      5      6
         ┌──────┬──────┬──────┬──────┐
Branch:  │  IF  │  DE  │  EX  │  MEM │
         │      │      │(resolve)    │
         └──────┴──────┴──────┴──────┘
                        │
                        ▼
         ┌──────────────────────┐
         │ spec_hit hesaplama   │
         │ Mispred: flush IF/DE │
         │ Correct: devam et    │
         └──────────────────────┘

Misprediction Cezası: 2 cycle (IF + DE flush)
```

---

## Bellek Arbiter

### Memory Arbiter Bağlantıları

```systemverilog
memory_arbiter i_memory_arbiter (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),
    .icache_req_i(lx_ireq),     // I-Cache isteği
    .dcache_req_i(lx_dreq),     // D-Cache isteği
    .icache_res_o(fe_lx_ires),  // I-Cache yanıtı
    .dcache_res_o(lx_dres),     // D-Cache yanıtı
    .iomem_res_i (iomem_res_i), // Harici bellek yanıtı
    .iomem_req_o (iomem_req_o)  // Harici bellek isteği
);
```

### Arbitrasyon Mantığı

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                           BELLEK ARBİTER                                      │
├──────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│   ┌─────────────┐                                    ┌─────────────┐        │
│   │  I-Cache    │──────┐                      ┌──────│   I-Cache   │        │
│   │  Request    │      │                      │      │   Response  │        │
│   └─────────────┘      │                      │      └─────────────┘        │
│                        │    ┌───────────┐     │                              │
│                        ├───▶│  ARBITER  │─────┤                              │
│                        │    │           │     │                              │
│   ┌─────────────┐      │    │  D > I    │     │      ┌─────────────┐        │
│   │  D-Cache    │──────┘    │ Priority  │     └──────│   D-Cache   │        │
│   │  Request    │           └─────┬─────┘            │   Response  │        │
│   └─────────────┘                 │                  └─────────────┘        │
│                                   │                                          │
│                                   ▼                                          │
│                          ┌───────────────┐                                   │
│                          │   Wishbone    │                                   │
│                          │     Bus       │                                   │
│                          └───────────────┘                                   │
│                                                                              │
│   Öncelik: D-Cache > I-Cache (data hazard'ları minimize etmek için)         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## Donanım Kesmeleri

### Kesme Tipleri

| Kesme | Kaynak | CSR Bit | Açıklama |
|-------|--------|---------|----------|
| Timer (MTIP) | CLINT | mip[7] | Zamanlayıcı kesmesi |
| Software (MSIP) | CLINT | mip[3] | Yazılım kesmesi |
| External (MEIP) | PLIC | mip[11] | Harici cihaz kesmesi |

### Kesme İşleme Akışı

```systemverilog
// Kesmeler execution aşamasına iletilir
execution i_execution (
    // ...
    .timer_irq_i  (timer_irq_i),   // CLINT timer
    .sw_irq_i     (sw_irq_i),      // CLINT software
    .ext_irq_i    (ext_irq_i),     // PLIC external
    // ...
);
```

### Kesme Öncelikleri

```
Kesme Öncelik Sırası (yüksekten düşüğe):
1. External Interrupt (MEIP) - PLIC
2. Timer Interrupt (MTIP)    - CLINT
3. Software Interrupt (MSIP) - CLINT
4. Synchronous Exceptions

Not: Kesmeler mie (machine interrupt enable) ve 
     mstatus.MIE bitlerine bağlıdır.
```

---

## Zamanlama Diyagramları

### Normal İşlem Akışı

```
clk_i    ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

         ┌─────────────────────────────────────────────────────
pipe1    │ I1        │ I2        │ I3        │ I4        │ I5
         └─────────────────────────────────────────────────────

         ┌─────────────────────────────────────────────────────
pipe2    │ --        │ I1        │ I2        │ I3        │ I4
         └─────────────────────────────────────────────────────

         ┌─────────────────────────────────────────────────────
pipe3    │ --        │ --        │ I1        │ I2        │ I3
         └─────────────────────────────────────────────────────

         ┌─────────────────────────────────────────────────────
pipe4    │ --        │ --        │ --        │ I1        │ I2
         └─────────────────────────────────────────────────────
```

### I-Cache Miss Stall

```
clk_i    ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

stall    ________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\__________
cause             IMISS_STALL (10 cycles)

         ┌─────────────────────────────────────────────────────
pipe1    │ I1    │ I1 (stall)│ I1 (stall)│ ...        │ I2
         └─────────────────────────────────────────────────────

         ┌─────────────────────────────────────────────────────
pipe2    │ --    │ nop       │ nop       │ ...        │ I1
         └─────────────────────────────────────────────────────
```

### Branch Misprediction Flush

```
clk_i    ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

Branch   ──────────────────────/‾‾‾‾\______________________________
Taken                           │EX  │

spec_hit ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\____/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

         ┌─────────────────────────────────────────────────────
pipe1    │ Br     │ X (wrong)│ Y (wrong)│ T1        │ T2
         └─────────────────────────────────────────────────────
                               ↑ flush    ↑ correct path

         ┌─────────────────────────────────────────────────────
pipe2    │ --     │ Br       │ nop      │ nop       │ T1
         └─────────────────────────────────────────────────────
                    ↑ resolve  ↑ flush

Misprediction Cezası: 2 cycle
```

### Load-Use Hazard Stall

```
clk_i    ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

LW x1    │ IF     │ DE       │ EX       │ MEM      │ WB
ADD x2,x1│        │ IF       │ IF(stall)│ DE       │ EX

stall    __________________/‾‾‾‾\______________________________
cause                       LOAD_RAW

         ┌─────────────────────────────────────────────────────
pipe1    │ LW     │ ADD      │ ADD(hold)│ I3       │ I4
         └─────────────────────────────────────────────────────

         ┌─────────────────────────────────────────────────────
pipe2    │ --     │ LW       │ bubble   │ ADD      │ I3
         └─────────────────────────────────────────────────────

Load-Use Cezası: 1 cycle (forwarding ile minimize edilmiş)
```

### Exception Handling

```
clk_i    ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

Illegal  │ IF     │ DE       │ EX       │
Instr                        │(exc det) │

trap     ______________________________/‾‾‾‾\____________________
active

         ┌─────────────────────────────────────────────────────
pipe1    │ ILL    │ I2       │ I3       │ nop      │ handler
         └─────────────────────────────────────────────────────
                               ↑ flush    ↑ PC=mtvec

         ┌─────────────────────────────────────────────────────
pipe2    │ --     │ ILL      │ nop      │ nop      │ nop
         └─────────────────────────────────────────────────────
                    ↑ exc      ↑ flush

CSR Updates:
- mcause ← exception_code
- mepc   ← faulting_pc
- mtval  ← exception_info
- PC     ← mtvec
```

---

## Performans Analizi

### IPC (Instructions Per Cycle) Hesabı

| Durum | IPC | Açıklama |
|-------|-----|----------|
| İdeal | 1.0 | Stall veya flush yok |
| Ortalama | 0.7-0.8 | Normal çalışma |
| Cache Miss | 0.1-0.2 | Bellek erişim gecikmesi |

### Stall Cezaları

| Stall Tipi | Tipik Süre | Etkisi |
|------------|------------|--------|
| I-Cache Miss | ~10 cycle | IPC düşüşü |
| D-Cache Miss | ~10 cycle | Pipeline durdurma |
| Load-Use Hazard | 1 cycle | Minimal etki |
| MUL/DIV | 1-32 cycle | İşlem bağımlı |
| Branch Mispred | 2 cycle | Pipeline flush |

### Optimizasyon Stratejileri

1. **Branch Prediction Doğruluğu**
   - GSHARE + BTB + RAS kombinasyonu
   - Hedef: >90% doğruluk

2. **Cache Hit Rate**
   - 8-way set associative
   - 8KB kapasite
   - Hedef: >95% hit rate

3. **Data Forwarding**
   - MEM→EX forwarding
   - WB→EX forwarding
   - WB→DE forwarding

4. **Instruction Fetch Bandwidth**
   - Compressed instruction desteği
   - Alignment buffer

---

## Doğrulama ve Test

### Assertion'lar

```systemverilog
// Pipeline tutarlılık kontrolü
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (stall_cause == NO_STALL) |-> 
    (pipe1 != $past(pipe1) || de_flush_en)
) else $error("Pipeline should advance when not stalled");

// Exception öncelik kontrolü
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (ex_exc_type != NO_EXCEPTION && de_active_exc_type != NO_EXCEPTION) |->
    (priority_flush == 3)
) else $error("EX exception should have highest priority");

// Stall/Flush mutual exclusion
assert property (@(posedge clk_i) disable iff (!rst_ni)
    (stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL}) |->
    (!de_flush_en && !ex_flush_en)
) else $error("Flush should be suppressed during cache stalls");
```

### Test Senaryoları

1. **Basic Pipeline Flow**
   - Ardışık NOP'lar
   - Basit aritmetik işlemler
   - Register file R/W

2. **Hazard Tests**
   - RAW hazard (data forwarding)
   - Load-use hazard (stall)
   - WAW hazard (in-order)

3. **Branch Tests**
   - Koşullu branch (taken/not-taken)
   - JAL/JALR
   - Misprediction recovery

4. **Exception Tests**
   - Illegal instruction
   - Misaligned access
   - ECALL/EBREAK

5. **Interrupt Tests**
   - Timer interrupt
   - External interrupt
   - Interrupt masking

6. **Cache Tests**
   - I-Cache miss/hit
   - D-Cache miss/hit
   - FENCE.I

### Konata Pipeline Visualizer

```systemverilog
`ifdef KONATA_TRACER
    konata_logger i_konata_logger ();
`endif
```

Konata trace formatı pipeline durumunu görselleştirmek için kullanılır:
- Instruction fetch, decode, execute, memory, writeback aşamaları
- Stall ve flush olayları
- Branch resolution

---

## Özet

`cpu` modülü, CERES RISC-V işlemcisinin merkezi koordinasyon birimidir. Bu modül:

1. **5-aşamalı pipeline**'ı yönetir (IF, DE, EX, MEM, WB)
2. **Pipeline register**'ları (pipe1-4) aracılığıyla veri akışını sağlar
3. **Hazard unit** ile data hazard'ları çözer
4. **Stall mekanizması** ile cache miss ve diğer gecikmeleri yönetir
5. **Flush mekanizması** ile branch misprediction ve exception'ları işler
6. **Exception handling** ile hata durumlarını yakalar ve işler
7. **Memory arbiter** ile I-Cache ve D-Cache arasında arbitrasyon yapar
8. **Kesme desteği** ile timer, software ve external interrupt'ları işler

Bu tasarım, basitlik ve performans arasında denge kurarak, eğitim ve gerçek dünya uygulamaları için uygun bir RISC-V işlemci çekirdeği sunar.
