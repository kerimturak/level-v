# RISC-V Test Ortamı CSR Konfigürasyon Rehberi

## Giriş
Bu rehber, RV32IMC işlemciniz için `riscv-tests` ortamını yapılandırmayı ve CSR (Control and Status Register) işlemlerini devre dışı bırakmayı açıklamaktadır.

---

## 1. CSR'lar Nelerdir ve Neden Kapatıyoruz?

### CSR'ların Görevleri

| CSR Grubu | İşlevi | Neden Kapatıyoruz |
|-----------|--------|-------------------|
| **mstatus** | Makine modu durum kaydı (privilege seviyesi, kesme, FP/Vector enable) | Basit bir RV32IMC çekirdeği için privilege modu gerektirmez |
| **mtvec** | Trap vektör adresi (exception/interrupt handler) | Exception handling olmadan basit test yapacaksak gereksiz |
| **mepc** | Exception'dan dönüş adresi | Exception handling olmadan gereksiz |
| **mcause** | Exception/interrupt sebebi | Exception handling olmadan gereksiz |
| **mhartid** | Hart (hardware thread) ID'si | Tek çekirdek için her zaman 0 |
| **pmpaddr/pmpcfg** | Physical Memory Protection | Basit sistem için bellek koruması gerektirmez |
| **medeleg/mideleg** | Exception/interrupt delegasyonu | Supervisor modu olmadan gereksiz |
| **satp** | Adres çevirisi | MMU olmadan gereksiz |
| **fcsr** | Floating-point CSR | RV32IMC'de F extension yok |
| **vcsr** | Vector CSR | RV32IMC'de V extension yok |

---

## 2. Dosya Yapısı

```
riscv-tests/
├── env/
│   ├── p/              # Orijinal physical single-core
│   └── ceres/          # Sizin yeni ortamınız
│       └── link.ld     # Linker script
```

---

## 3. Minimal RV32IMC Konfigürasyonu

### 3.1 Başlangıç Makroları - Temizleme

Orijinal kodda **kaldırılacak** kısımlar:

```asm
# ❌ KALDIRILACAK - Privilege mode ayarları
#define RVTEST_RV32M                                                    \
  .macro init;                                                          \
  RVTEST_ENABLE_MACHINE;                                                \
  .endm

#define RVTEST_RV32S                                                    \
  .macro init;                                                          \
  RVTEST_ENABLE_SUPERVISOR;                                             \
  .endm

# ❌ KALDIRILACAK - Floating-point enabler
#define RVTEST_RV32UF
#define RVTEST_FP_ENABLE

# ❌ KALDIRILACAK - Vector enabler  
#define RVTEST_RV32UV
#define RVTEST_VECTOR_ENABLE
```

### 3.2 Yeni Minimal Makro

```asm
# ✅ YENİ - Sadece RV32I için minimal başlatma
#define RVTEST_RV32I                                                    \
  .macro init;                                                          \
  .endm
```

**Açıklama:** Boş bir `.endm` makrosu bile yeterli - hiçbir CSR konfigürasyonu yapmıyoruz.

---

## 4. Reset Vector - Minimal Versiyon

### 4.1 Orijinal Kodda Kaldırılacaklar

```asm
# ❌ KALDIRILACAK bloklarını işaretleyelim:

reset_vector:
    # INIT_XREG;              # ✅ TUTULACAK - Registerleri sıfırla
    # RISCV_MULTICORE_DISABLE; # ❌ KALDIR - mhartid CSR kullanıyor
    # INIT_RNMI;              # ❌ KALDIR - mtvec ve mnstatus CSR
    # INIT_SATP;              # ❌ KALDIR - satp CSR (MMU)
    # INIT_PMP;               # ❌ KALDIR - pmpaddr/pmpcfg CSR
    # DELEGATE_NO_TRAPS;      # ❌ KALDIR - medeleg/mideleg CSR
    # li TESTNUM, 0;          # ✅ TUTULACAK - Test numarası
    # la t0, trap_vector;     # ❌ KALDIR - mtvec CSR
    # csrw mtvec, t0;         # ❌ KALDIR
    # CHECK_XLEN;             # ✅ TUTULACAK (opsiyonel) - xlen kontrolü
    # ... stvec delegation    # ❌ KALDIR - stvec/medeleg CSR
    # csrwi mstatus, 0;       # ❌ KALDIR - mstatus CSR
    # init;                   # ✅ TUTULACAK - Boş makro
    # EXTRA_INIT;             # ✅ TUTULACAK - Boş makro
    # la t0, 1f;              # ❌ KALDIR - mepc CSR
    # csrw mepc, t0;          # ❌ KALDIR
    # mret;                   # ❌ KALDIR - Privilege instruction
```

### 4.2 Minimal Reset Vector

```asm
reset_vector:
    INIT_XREG;                  # Tüm registerleri sıfırla
    li TESTNUM, 0;              # Test numarasını başlat
    CHECK_XLEN;                 # XLEN kontrolü (opsiyonel)
    init;                       # Boş makro (ileride genişletilebilir)
    EXTRA_INIT;                 # Boş makro (ileride genişletilebilir)
    j 1f;                       # Test koduna dallan
1:
```

**Açıklama:**
- `INIT_XREG`: Tüm x1-x31 registerlerini sıfırlar (önemli)
- `CHECK_XLEN`: RV32 olduğunu doğrular (opsiyonel ama önerilir)
- `j 1f`: Doğrudan test koduna atlar (privilege değişimi yok)

---

## 5. Trap Handler - Basitleştirme

### 5.1 Orijinal Trap Vector

```asm
trap_vector:
    csrr t5, mcause;           # ❌ CSR okuma
    li t6, CAUSE_USER_ECALL;
    beq t5, t6, write_tohost;
    # ... daha fazla exception kontrolü
```

### 5.2 Minimal Trap Vector (Opsiyonel)

Eğer **hiç exception handling** istemiyorsanız:

```asm
# Option 1: Trap vector'ü tamamen kaldırın
# RVTEST_CODE_BEGIN makrosundan trap_vector etiketini çıkarın

# Option 2: Sadece fail durumunu yakalayın
trap_vector:
    li TESTNUM, 0xBAD;         # Trap = test başarısız
    j write_tohost;
```

**Önemli:** `write_tohost` etiketini **tutun** - testlerin sonuç bildirmesi için gerekli.

---

## 6. RVTEST_PASS ve RVTEST_FAIL

### 6.1 Orijinal PASS/FAIL (CSR kullanıyor)

```asm
#define RVTEST_PASS                                                     \
        fence;                                                          \
        li TESTNUM, 1;                                                  \
        li a7, 93;              # ❌ ecall için syscall number          \
        li a0, 0;                                                       \
        ecall                   # ❌ CSR gerektirir (mcause, mepc)
```

### 6.2 Minimal PASS/FAIL (Sadece tohost)

```asm
#define RVTEST_PASS                                                     \
        fence;                                                          \
        li TESTNUM, 1;                                                  \
        la t5, tohost;                                                  \
        sw TESTNUM, 0(t5);                                              \
        sw zero, 4(t5);                                                 \
1:      j 1b;                   # Sonsuz döngü (simülatör tohost'u okur)

#define RVTEST_FAIL                                                     \
        fence;                                                          \
1:      beqz TESTNUM, 1b;       # TESTNUM sıfırsa bekle                \
        sll TESTNUM, TESTNUM, 1;                                        \
        or TESTNUM, TESTNUM, 1; # Fail biti ekle                       \
        la t5, tohost;                                                  \
        sw TESTNUM, 0(t5);                                              \
        sw zero, 4(t5);                                                 \
2:      j 2b;
```

**Açıklama:**
- `ecall` kullanmıyoruz (CSR gerektirir)
- Doğrudan `tohost` bellek adresine yazıyoruz
- Simülatör/testbench bu adresi izleyerek sonucu öğrenir

---

## 7. CHECK_XLEN Makrosu

### 7.1 Orijinal (RVTEST_PASS kullanıyor)

```asm
#define CHECK_XLEN li a0, 1; slli a0, a0, 31; bltz a0, 1f; RVTEST_PASS; 1:
```

### 7.2 Düzeltilmiş Versiyon

```asm
#define CHECK_XLEN                                                      \
        li a0, 1;                                                       \
        slli a0, a0, 31;        # RV32'de negatif, RV64'te pozitif     \
        bltz a0, 1f;            # RV32 ise devam et                    \
        li TESTNUM, 0xBAD;      # RV64 tespit edildi = fail            \
        j write_tohost;                                                 \
1:
```

---

## 8. Tam Minimal Header Dosyası

```c
// ceres/env_physical_single_core.h

#ifndef _ENV_CERES_PHYSICAL_SINGLE_CORE_H
#define _ENV_CERES_PHYSICAL_SINGLE_CORE_H

#include "../encoding.h"

//-----------------------------------------------------------------------
// Minimal RV32IMC Init Macro
//-----------------------------------------------------------------------

#define RVTEST_RV32I                                                    \
  .macro init;                                                          \
  .endm

//-----------------------------------------------------------------------
// Register Initialization (Mandatory)
//-----------------------------------------------------------------------

#define INIT_XREG                                                       \
  li x1, 0;  li x2, 0;  li x3, 0;  li x4, 0;                            \
  li x5, 0;  li x6, 0;  li x7, 0;  li x8, 0;                            \
  li x9, 0;  li x10, 0; li x11, 0; li x12, 0;                           \
  li x13, 0; li x14, 0; li x15, 0; li x16, 0;                           \
  li x17, 0; li x18, 0; li x19, 0; li x20, 0;                           \
  li x21, 0; li x22, 0; li x23, 0; li x24, 0;                           \
  li x25, 0; li x26, 0; li x27, 0; li x28, 0;                           \
  li x29, 0; li x30, 0; li x31, 0;

//-----------------------------------------------------------------------
// XLEN Check (Optional but Recommended)
//-----------------------------------------------------------------------

#define CHECK_XLEN                                                      \
        li a0, 1;                                                       \
        slli a0, a0, 31;                                                \
        bltz a0, 1f;                                                    \
        li TESTNUM, 0xBAD;                                              \
        j write_tohost;                                                 \
1:

//-----------------------------------------------------------------------
// Empty Placeholders
//-----------------------------------------------------------------------

#define EXTRA_INIT
#define EXTRA_INIT_TIMER
#define EXTRA_DATA

//-----------------------------------------------------------------------
// Code Section
//-----------------------------------------------------------------------

#define RVTEST_CODE_BEGIN                                               \
        .section .text.init;                                            \
        .align  6;                                                      \
        .globl _start;                                                  \
_start:                                                                 \
        j reset_vector;                                                 \
        .align 2;                                                       \
trap_vector:                                                            \
        li TESTNUM, 0xBAD;                                              \
        j write_tohost;                                                 \
reset_vector:                                                           \
        INIT_XREG;                                                      \
        li TESTNUM, 0;                                                  \
        CHECK_XLEN;                                                     \
        init;                                                           \
        EXTRA_INIT;                                                     \
        EXTRA_INIT_TIMER;                                               \
        j 1f;                                                           \
1:

#define RVTEST_CODE_END                                                 \
        unimp

//-----------------------------------------------------------------------
// Pass/Fail Macros (No CSR)
//-----------------------------------------------------------------------

#define TESTNUM gp

#define RVTEST_PASS                                                     \
        fence;                                                          \
        li TESTNUM, 1;                                                  \
        la t5, tohost;                                                  \
        sw TESTNUM, 0(t5);                                              \
        sw zero, 4(t5);                                                 \
1:      j 1b;

#define RVTEST_FAIL                                                     \
        fence;                                                          \
1:      beqz TESTNUM, 1b;                                               \
        sll TESTNUM, TESTNUM, 1;                                        \
        or TESTNUM, TESTNUM, 1;                                         \
        la t5, tohost;                                                  \
        sw TESTNUM, 0(t5);                                              \
        sw zero, 4(t5);                                                 \
2:      j 2b;

//-----------------------------------------------------------------------
// Data Section (tohost/fromhost for communication)
//-----------------------------------------------------------------------

#define RVTEST_DATA_BEGIN                                               \
        EXTRA_DATA                                                      \
        .pushsection .tohost,"aw",@progbits;                            \
        .align 6; .global tohost; tohost: .dword 0; .size tohost, 8;    \
        .align 6; .global fromhost; fromhost: .dword 0; .size fromhost, 8;\
        .popsection;                                                    \
        .align 4; .global begin_signature; begin_signature:

#define RVTEST_DATA_END .align 4; .global end_signature; end_signature:

#endif
```

---

## 9. Neden Bu Değişiklikler?

### CSR Gereksinimleri

| Özellik | CSR Gerektirir mi? | RV32IMC'de Var mı? |
|---------|-------------------|--------------------|
| Privilege modes (M/S/U) | ✅ Evet | ❌ Opsiyonel |
| Interrupts/Exceptions | ✅ Evet | ❌ Minimal impl. için gereksiz |
| MMU (Virtual Memory) | ✅ Evet | ❌ RV32I'de yok |
| Floating-point | ✅ Evet (fcsr) | ❌ F extension yok |
| Vector operations | ✅ Evet (vcsr) | ❌ V extension yok |
| Multi-hart | ✅ Evet (mhartid) | ❌ Tek çekirdek |

### Basit RV32IMC Çekirdeği İçin Yeterli

✅ **Integer registers** (x0-x31)  
✅ **Basic instructions** (ADD, SUB, LW, SW, BEQ, JAL, etc.)  
✅ **Multiply/Divide** (M extension)  
✅ **Compressed** (C extension - 16-bit instructions)  
❌ CSR instructions gereksiz (CSRRW, CSRRS, etc.)

---

## 10. Test Etme

### 10.1 Basit Test Örneği

```asm
#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32I
RVTEST_CODE_BEGIN

  # Test 1: Basit toplama
  TEST_RR_OP(2, add, 5, 2, 3);
  
  # Test 2: Load/Store
  la t0, tdat;
  li t1, 0xDEADBEEF;
  sw t1, 0(t0);
  lw t2, 0(t0);
  li TESTNUM, 3;
  bne t1, t2, fail;

  RVTEST_PASS

fail:
  RVTEST_FAIL

RVTEST_CODE_END

RVTEST_DATA_BEGIN
  TEST_DATA
tdat:
  .word 0
RVTEST_DATA_END
```

### 10.2 Derleme

```bash
riscv32-unknown-elf-gcc -march=rv32imc -mabi=ilp32 \
  -static -mcmodel=medany -fvisibility=hidden \
  -nostdlib -nostartfiles \
  -I./env/ceres -I./isa/macros/scalar \
  -T./env/ceres/link.ld \
  test.S -o test.elf
```

---

## 11. Özet

### ❌ Kaldırılan CSR'lar

- `mstatus`, `mtvec`, `mepc`, `mcause` (privilege/exception handling)
- `mhartid` (multi-core)
- `pmpaddr`, `pmpcfg` (memory protection)
- `medeleg`, `mideleg` (delegation)
- `satp` (MMU)
- `fcsr`, `vcsr` (FP/Vector)

### ✅ Tutulan Özellikler

- Register başlatma (`INIT_XREG`)
- XLEN kontrolü (`CHECK_XLEN`)
- Test sonuç bildirimi (`tohost`)
- Temel test makroları

### 🎯 Sonuç

Bu minimal konfigürasyon, **RV32IMC** çekirdeğiniz için CSR desteği gerektirmeyen saf integer testleri çalıştırmanıza olanak tanır. İleride interrupt veya privilege mode desteği eklerseniz, CSR makrolarını kademeli olarak geri ekleyebilirsiniz.