---
title: "RTL Documentation Index"
description: "Tüm RTL modül belgeleri - hızlı navigasyon"
date: 2025-12-01
draft: false
weight: 300
---

# RTL Documentation Index

Ceres RISC-V RTL kodlaması için kapsamlı belgeler.

---

## 📚 Hızlı Başlangıç

**İlk defa mı RTL'ı inceliyorsunuz?**

1. [RTL Overview](./RTL_OVERVIEW.md) - Proje yapısı ve modül haritası
2. [Top Wrapper Module](./CERES_WRAPPER.md) - SoC entegrasyonu
3. [CPU Top Module](./CPU_TOP_MODULE.md) - Pipeline orchestration

**Pipeline detaylı öğrenmek isterseniz:**

4. [Fetch Stage](./stages/FETCH_STAGE.md) - İlk stage (IF)
5. [Decode Stage](./stages/DECODE_STAGE.md) - İkinci stage (ID)
6. [Execute Stage](./stages/EXECUTE_STAGE.md) - Üçüncü stage (EX)
7. [Memory & WriteBack](./stages/MEMORY_WRITEBACK_STAGES.md) - Dördüncü & beşinci stage (MEM, WB)

**Pipeline desteği:**

8. [Hazard Unit](./HAZARD_UNIT.md) - Veri hazard tespiti ve çözümü

---

## 📂 Dokumentasyon Yapısı

```
docs/rtl/
├── RTL_OVERVIEW.md              ← Başlayın buradan
├── CERES_WRAPPER.md             ← SoC top module
├── CPU_TOP_MODULE.md            ← CPU orchestrator
├── HAZARD_UNIT.md               ← Hazard detection
│
├── stages/
│   ├── FETCH_STAGE.md           ← IF stage
│   ├── DECODE_STAGE.md          ← ID stage
│   ├── EXECUTE_STAGE.md         ← EX stage
│   └── MEMORY_WRITEBACK_STAGES.md ← MEM & WB
│
├── periph/                       (Gelecek)
│   ├── uart.md
│   ├── gpio.md
│   └── clint.md
│
├── cache/                        (Gelecek)
│   ├── icache.md
│   └── dcache.md
│
└── mul_div/                      (Gelecek)
    ├── multiplier.md
    └── divider.md
```

---

## 🎯 Modüllere Göre Navigasyon

### Top Level

| Modül | Dosya | Satır | Görev |
|-------|-------|-------|-------|
| **ceres_wrapper** | `rtl/wrapper/ceres_wrapper.sv` | 282 | SoC entegrasyonu, bellek haritası |
| **cpu** | `rtl/core/cpu.sv` | 698 | CPU orchestration, pipeline kontrol |

### Pipeline Stages

| Stage | Modüller | Belge | Görev |
|-------|----------|--------|-------|
| **IF (Fetch)** | `fetch.sv` (344 L) | [FETCH_STAGE.md](./stages/FETCH_STAGE.md) | PC yönetimi, instruction fetch |
| **ID (Decode)** | `decode.sv`, `control_unit.sv`, `reg_file.sv`, `extend.sv` | [DECODE_STAGE.md](./stages/DECODE_STAGE.md) | Instruction decode, register read |
| **EX (Execute)** | `execution.sv`, `alu.sv`, `cs_reg_file.sv`, `mul_div/` | [EXECUTE_STAGE.md](./stages/EXECUTE_STAGE.md) | ALU işlemleri, CSR, MUL/DIV |
| **MEM (Memory)** | `memory.sv` | [MEMORY_WRITEBACK_STAGES.md](./stages/MEMORY_WRITEBACK_STAGES.md) | Load/Store, Data cache |
| **WB (WriteBack)** | `writeback.sv` | [MEMORY_WRITEBACK_STAGES.md](./stages/MEMORY_WRITEBACK_STAGES.md) | Register file yazma |

### Support Modules

| Modül | Dosya | Belge | Görev |
|-------|-------|-------|-------|
| **Hazard Unit** | `core/hazard_unit.sv` | [HAZARD_UNIT.md](./HAZARD_UNIT.md) | Veri hazard tespiti, forwarding |
| **Branch Predictor** | `core/fetch_unit/branch_predictor.sv` | (Gelecek) | Gshare algorithm |
| **Return Address Stack** | `core/fetch_unit/ras.sv` | (Gelecek) | RAS (8 entry) |
| **I-Cache** | `core/mmu/cache.sv` | (Gelecek) | L1-I cache |
| **D-Cache** | `core/mmu/cache.sv` | (Gelecek) | L1-D cache |

### Peripherals

| Cihaz | Dosya | Satır | Belge | Görev |
|-------|-------|-------|--------|-------|
| **UART** | `periph/uart*.sv` | 400+ | (Gelecek) | Serial communication |
| **CLINT** | `wrapper/` | - | [CERES_WRAPPER.md](./CERES_WRAPPER.md#-clint-core-local-interrupt-timer) | Timer, interrupts |

### Compute Units

| Unit | Dosya | Satır | Belge | Görev |
|------|-------|-------|--------|-------|
| **ALU** | `stage03_execute/alu.sv` | 376 | [EXECUTE_STAGE.md](./stages/EXECUTE_STAGE.md#-alu-module---alusvv) | +, -, AND, OR, XOR, SLL, SRL, SRA |
| **Multiplier** | `stage03_execute/mul_div/mul_int.sv` | 200+ | (Gelecek) | 32×32 multiply |
| **Wallace Tree** | `stage03_execute/mul_div/wallace32x32/` | - | (Gelecek) | Wallace tree multiply |
| **Divider** | `stage03_execute/mul_div/divu_int.sv` | 200+ | (Gelecek) | Non-restoring divide |

### Memory & CSR

| Modül | Dosya | Satır | Belge | Görev |
|-------|-------|-------|--------|-------|
| **CSR File** | `stage03_execute/cs_reg_file.sv` | 425 | [EXECUTE_STAGE.md](./stages/EXECUTE_STAGE.md#-csr-module---cs_reg_filesvv) | 20+ CSR registers |
| **Register File** | `stage02_decode/reg_file.sv` | 40 | [DECODE_STAGE.md](./stages/DECODE_STAGE.md#-register-file---reg_filesvv) | 32×32 register |
| **RAM (BRAM)** | `ram/sp_bram.sv` | 100+ | (Gelecek) | Single-port block RAM |
| **Instruction Cache** | `core/mmu/cache.sv` | 500+ | (Gelecek) | Parametric cache |
| **Data Cache** | `core/mmu/cache.sv` | 500+ | (Gelecek) | Parametric cache |

---

## 🔄 Pipeline Data Flow

```
Instruction Journey Through Pipeline:
────────────────────────────────────────

Memory (RAM/Cache)
       ↓
IF (Fetch)                    → instruction
       ↓
pipe1_t (register)
       ↓
ID (Decode)                   → control signals, operands
       ↓
pipe2_t (register)
       ↓
EX (Execute)                  → ALU result, branch decision
       ↓
pipe3_t (register)
       ↓
MEM (Memory)                  → load data (if load/store)
       ↓
pipe4_t (register)
       ↓
WB (WriteBack)                → register file write
       ↓
x0-x31 (Registers)
```

---

## 🎓 Learning Paths

### Path 1: Sequential Read (Recommended)

Best for understanding the complete pipeline:

1. [RTL Overview](./RTL_OVERVIEW.md) - Get the big picture (30 min)
2. [CERES_WRAPPER.md](./CERES_WRAPPER.md) - System integration (45 min)
3. [CPU_TOP_MODULE.md](./CPU_TOP_MODULE.md) - Pipeline orchestration (45 min)
4. [FETCH_STAGE.md](./stages/FETCH_STAGE.md) - First stage details (45 min)
5. [DECODE_STAGE.md](./stages/DECODE_STAGE.md) - Second stage details (45 min)
6. [EXECUTE_STAGE.md](./stages/EXECUTE_STAGE.md) - Third stage details (60 min)
7. [MEMORY_WRITEBACK_STAGES.md](./stages/MEMORY_WRITEBACK_STAGES.md) - Final stages (45 min)
8. [HAZARD_UNIT.md](./HAZARD_UNIT.md) - Pipeline safety (45 min)

**Total**: ~6 hours for complete understanding

### Path 2: Module-Focused (For specific work)

For fixing bugs or adding features in specific modules:

1. [RTL Overview](./RTL_OVERVIEW.md) - Orientation
2. Go directly to relevant stage or module
3. Use [HAZARD_UNIT.md](./HAZARD_UNIT.md) for side effects

### Path 3: Problem-Based (For troubleshooting)

"Why is my instruction taking too long?"
- → [CPU_TOP_MODULE.md](./CPU_TOP_MODULE.md) (pipeline timing)
- → [HAZARD_UNIT.md](./HAZARD_UNIT.md) (stalling)
- → Relevant stage document

"Why is my load not getting the right value?"
- → [MEMORY_WRITEBACK_STAGES.md](./stages/MEMORY_WRITEBACK_STAGES.md) (memory operations)
- → [HAZARD_UNIT.md](./HAZARD_UNIT.md) (forwarding)
- → [DECODE_STAGE.md](./stages/DECODE_STAGE.md) (register file)

"Why is my branch going to wrong address?"
- → [FETCH_STAGE.md](./stages/FETCH_STAGE.md) (branch prediction)
- → [EXECUTE_STAGE.md](./stages/EXECUTE_STAGE.md) (branch resolution)
- → [HAZARD_UNIT.md](./HAZARD_UNIT.md) (pipeline flush)

---

## 📊 Key Metrics

### Pipeline Characteristics

| Aspect | Value |
|--------|-------|
| **Pipeline Depth** | 5 stages |
| **Instruction Window** | 4 instructions (pipe1-4) |
| **ALU Latency** | 1 cycle |
| **Multiply Latency** | 3-4 cycles |
| **Divide Latency** | 30-40 cycles |
| **Load Latency** | 3 cycles (1 Miss), 4+ cycles (cache miss) |
| **Branch Latency** | 3 cycles |
| **Max Clock Frequency** | Depends on implementation |

### Code Statistics

| Category | Count | File Count | Lines |
|----------|-------|-----------|-------|
| **Pipeline Stages** | 5 | 13 | ~1,100 |
| **Support Modules** | 5+ | 10+ | ~2,500 |
| **Peripherals** | 3+ | 10+ | ~1,500 |
| **Memory System** | 2 | 5+ | ~1,000 |
| **Total Core** | - | 41 | ~6,100 |

---

## 🔗 Cross-References

### Pipeline Register Structures

```
pipe1_t (IF→ID):
  ├─ instruction (32-bit)
  ├─ pc
  ├─ instr_type
  └─ exception

pipe2_t (ID→EX):
  ├─ r1_data, r2_data
  ├─ immediate
  ├─ control signals
  └─ rd_addr

pipe3_t (EX→MEM):
  ├─ alu_result
  ├─ write_data (for stores)
  └─ exception

pipe4_t (MEM→WB):
  ├─ load_data
  ├─ alu_result
  └─ register write info
```

### Signal Naming Conventions

```
_i   = input
_o   = output
_q   = qualified (registered)
_n   = active-low
_en  = enable
_sel = select
_req = request
_res = response
```

---

## 🛠️ Development Guide

### Adding a New Instruction

1. **Decode**: [DECODE_STAGE.md](./stages/DECODE_STAGE.md) - Add to `instr_type_e` enum, `control_unit.sv`
2. **Execute**: [EXECUTE_STAGE.md](./stages/EXECUTE_STAGE.md) - Add ALU operation, `alu.sv`
3. **Test**: Create test case, verify with hazard unit

### Fixing a Pipeline Bug

1. Identify stage: [CPU_TOP_MODULE.md](./CPU_TOP_MODULE.md)
2. Check hazards: [HAZARD_UNIT.md](./HAZARD_UNIT.md)
3. Stage-specific: Relevant stage document
4. Test: Verify with CoreMark or RISC-V tests

### Performance Analysis

1. [CPU_TOP_MODULE.md](./CPU_TOP_MODULE.md) - Pipeline timing
2. Specific stage - Check latency table
3. [HAZARD_UNIT.md](./HAZARD_UNIT.md) - Stall analysis
4. Simulation trace - Verify predictions

---

## 📝 Documentation Metadata

| Document | Lines | Last Updated | Coverage |
|----------|-------|--------------|----------|
| RTL_OVERVIEW.md | 500+ | Dec 1, 2025 | Complete |
| CERES_WRAPPER.md | 450+ | Dec 1, 2025 | ~90% |
| CPU_TOP_MODULE.md | 550+ | Dec 1, 2025 | ~85% |
| FETCH_STAGE.md | 600+ | Dec 1, 2025 | ~80% |
| DECODE_STAGE.md | 650+ | Dec 1, 2025 | ~85% |
| EXECUTE_STAGE.md | 700+ | Dec 1, 2025 | ~85% |
| MEMORY_WRITEBACK_STAGES.md | 550+ | Dec 1, 2025 | ~80% |
| HAZARD_UNIT.md | 550+ | Dec 1, 2025 | 95% |

**Planned**: ALU details, Multiplier, Divider, Cache, UART, Branch Predictor, RAS

---

## 🎯 Quick Reference

### Finding Code

**Q: Where is the ALU?**
- A: `rtl/core/stage03_execute/alu.sv` - See [EXECUTE_STAGE.md](./stages/EXECUTE_STAGE.md#-alu-module---alusvv)

**Q: Where are the registers (x0-x31)?**
- A: `rtl/core/stage02_decode/reg_file.sv` - See [DECODE_STAGE.md](./stages/DECODE_STAGE.md#-register-file---reg_filesvv)

**Q: How does branching work?**
- A: PC calculation in [EXECUTE_STAGE.md](./stages/EXECUTE_STAGE.md#branch-resolution), flush in [HAZARD_UNIT.md](./HAZARD_UNIT.md#-pipeline-flushing)

**Q: What is data forwarding?**
- A: RAW hazard solution in [HAZARD_UNIT.md](./HAZARD_UNIT.md#-data-forwarding)

**Q: Why does my code stall?**
- A: Load-use hazard explanation in [HAZARD_UNIT.md](./HAZARD_UNIT.md#-load-use-hazard-stalling)

---

## 📞 Contributing

Found an error or missing documentation?
- Check existing docs first
- Create clear, concise additions
- Include code examples and diagrams
- Update this index

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025  
**Beklenen**: 50+ sayfaya ulaşmak

