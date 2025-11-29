// RISC-V Architecture Test Model Header File for Ceres Processor
// Copyright (c) 2024, Ceres-V Project
// See LICENSE for license details.
//
// Description: Target-specific macros for riscv-arch-test framework
// Ceres-V RV32IMC_Zicsr Processor

#ifndef _MODEL_TEST_H
#define _MODEL_TEST_H

//=============================================================================
// Configuration
//=============================================================================

#define XLEN 32
#define ALIGNMENT 2

// PMP Configuration (if supported)
#ifndef RVMODEL_PMP_GRAIN
  #define RVMODEL_PMP_GRAIN   0
#endif

#ifndef RVMODEL_NUM_PMPS
  #define RVMODEL_NUM_PMPS    0  // Ceres doesn't have PMP yet
#endif

// Vectored trap handler alignment
#ifndef MTVEC_ALIGN
  #define MTVEC_ALIGN   6
#endif

//=============================================================================
// Boot and Halt Macros
//=============================================================================

// Boot sequence - setup trap handler for Ceres
// Jump over the handler, set mtvec, then continue
#define RVMODEL_BOOT                                                    \
    j _rvtest_boot_continue;                                            \
    .align 4;                                                           \
    .global rvtest_trap_handler;                                        \
rvtest_trap_handler:                                                    \
    csrr t0, mcause;                                                    \
    csrr t1, mepc;                                                      \
    li t2, 3;                   /* EBREAK mcause */                     \
    bne t0, t2, 1f;                                                     \
    lhu t3, 0(t1);              /* Load instruction */                  \
    andi t3, t3, 0x3;           /* Check if compressed */               \
    li t4, 0x3;                                                         \
    beq t3, t4, 2f;             /* If 0x3, it's 32-bit */               \
    addi t1, t1, 2;             /* Compressed: PC += 2 */               \
    j 3f;                                                               \
2:  addi t1, t1, 4;             /* 32-bit: PC += 4 */                   \
3:  csrw mepc, t1;                                                      \
    mret;                                                               \
1:  li t2, 11;                  /* ECALL mcause */                      \
    bne t0, t2, 4f;                                                     \
    j halt_loop;                /* ECALL = halt */                      \
4:  addi t1, t1, 4;             /* Unknown: skip 4 bytes */             \
    csrw mepc, t1;                                                      \
    mret;                                                               \
_rvtest_boot_continue:                                                  \
    .option push;                                                       \
    .option norelax;                                                    \
    la t0, rvtest_trap_handler;                                         \
    csrw mtvec, t0;                                                     \
    .option pop;

// Halt sequence - signal test completion via ecall
#define RVMODEL_HALT                                                    \
    fence;                                                              \
    li a7, 93;                /* exit syscall number */                 \
    li a0, 0;                 /* exit code 0 = pass */                  \
    ecall;                                                              \
halt_loop:                                                              \
    j halt_loop;

//=============================================================================
// Data Section Macros
//=============================================================================

// Additional data section for tohost/fromhost (simulation interface)
#define RVMODEL_DATA_SECTION                                            \
    .pushsection .tohost,"aw",@progbits;                                \
    .align 8; .global tohost; tohost: .dword 0;                         \
    .align 8; .global fromhost; fromhost: .dword 0;                     \
    .popsection;                                                        \
    .align 8; .global begin_regstate; begin_regstate:                   \
    .word 128;                                                          \
    .align 8; .global end_regstate; end_regstate:                       \
    .word 4;

// Begin signature area
#define RVMODEL_DATA_BEGIN                                              \
    RVMODEL_DATA_SECTION                                                \
    .align ALIGNMENT;                                                   \
    .global begin_signature; begin_signature:

// End signature area
#define RVMODEL_DATA_END                                                \
    .align ALIGNMENT;                                                   \
    .global end_signature; end_signature:

//=============================================================================
// I/O Macros (non-functional for RTL simulation)
//=============================================================================

#define RVMODEL_IO_INIT
#define RVMODEL_IO_WRITE_STR(_R, _STR)
#define RVMODEL_IO_CHECK()
#define RVMODEL_IO_ASSERT_GPR_EQ(_S, _R, _I)
#define RVMODEL_IO_ASSERT_SFPR_EQ(_F, _R, _I)
#define RVMODEL_IO_ASSERT_DFPR_EQ(_D, _R, _I)

//=============================================================================
// Interrupt Clearing Macros (stubs - Ceres minimal interrupt support)
//=============================================================================

#define RVMODEL_SET_MSW_INT
#define RVMODEL_CLEAR_MSW_INT
#define RVMODEL_CLEAR_MTIMER_INT
#define RVMODEL_CLEAR_MEXT_INT

// S-mode interrupt macros (stubs if S-mode not supported)
#define RVMODEL_CLR_SSW_INT
#define RVMODEL_CLR_STIMER_INT
#define RVMODEL_CLR_SEXT_INT

// VS-mode interrupt macros (stubs)
#define RVMODEL_CLR_VSW_INT
#define RVMODEL_CLR_VTIMER_INT
#define RVMODEL_CLR_VEXT_INT

// M-mode interrupt macros
#define RVMODEL_CLR_MSW_INT
#define RVMODEL_CLR_MTIMER_INT
#define RVMODEL_CLR_MEXT_INT

#endif // _MODEL_TEST_H
