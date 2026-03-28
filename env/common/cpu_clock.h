/* =====================================================================
 * Level-V — single source for CPU clock in C (env benchmarks / syscalls)
 * =====================================================================
 * Build flags: makefile passes -DCPU_CLK_HZ=... via LEVELV_CPU_CLK_CPPFLAGS.
 * RTL: keep numeric match with rtl/pkg/level_param.sv localparam CPU_CLK.
 * ===================================================================== */
#ifndef LEVELV_CPU_CLOCK_H
#define LEVELV_CPU_CLOCK_H

#include <stdint.h>

#ifndef CPU_CLK_HZ
#define CPU_CLK_HZ 25000000UL
#endif

/* Whole MHz (UART baud divisor); use a clock divisible by 1e6 for exact baud. */
#ifndef CPU_MHZ
#define CPU_MHZ ((uint32_t)((CPU_CLK_HZ) / 1000000UL))
#endif

#endif /* LEVELV_CPU_CLOCK_H */
