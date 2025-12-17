/*
Copyright 2018 Embedded Microprocessor Benchmark Consortium (EEMBC)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Original Author: Shay Gal-on
Modified for minimal RISC-V (no UART, CSR-based timing)
*/

#include "coremark.h"
#include "core_portme.h"

#if VALIDATION_RUN
volatile ee_s32 seed1_volatile = 0x3415;
volatile ee_s32 seed2_volatile = 0x3415;
volatile ee_s32 seed3_volatile = 0x66;
#endif
#if PERFORMANCE_RUN
volatile ee_s32 seed1_volatile = 0x0;
volatile ee_s32 seed2_volatile = 0x0;
volatile ee_s32 seed3_volatile = 0x66;
#endif
#if PROFILE_RUN
volatile ee_s32 seed1_volatile = 0x8;
volatile ee_s32 seed2_volatile = 0x8;
volatile ee_s32 seed3_volatile = 0x8;
#endif
volatile ee_s32 seed4_volatile = ITERATIONS;
volatile ee_s32 seed5_volatile = 0;

/************************/
/* Standard C Functions */
/************************/

/* memset - needed because we use -nostdlib */
void *memset(void *s, int c, size_t n)
{
    unsigned char *p = s;
    while (n--) {
        *p++ = (unsigned char)c;
    }
    return s;
}

/************************/
/* RISC-V CSR Functions */
/************************/

/* Read cycle counter (standard RISC-V CSR) */
static inline uint32_t read_csr_cycle(void)
{
    uint32_t cycle;
    asm volatile ("rdcycle %0" : "=r" (cycle));
    return cycle;
}

/* Read machine cycle counter (for M-mode) */
static inline uint32_t read_csr_mcycle(void)
{
    uint32_t cycle;
    asm volatile ("csrr %0, mcycle" : "=r" (cycle));
    return cycle;
}

/************************/
/* Timing Functions     */
/************************/

/* Use mcycle CSR - available in both Ceres-V and Spike
   Assumes ~50MHz CPU clock for time calculations */
#define CPU_FREQ_HZ        50000000
#define CORETIMETYPE       ee_u32
#define GETMYTIME(_t)      (*_t = read_csr_mcycle())
#define MYTIMEDIFF(fin, ini) ((fin) - (ini))
#define TIMER_RES_DIVIDER  1
#define SAMPLE_TIME_IMPLEMENTATION 1
#define EE_TICKS_PER_SEC   CPU_FREQ_HZ

static CORETIMETYPE start_time_val, stop_time_val;

void start_time(void)
{
    GETMYTIME(&start_time_val);
}

void stop_time(void)
{
    GETMYTIME(&stop_time_val);
}

CORE_TICKS get_time(void)
{
    CORE_TICKS elapsed = (CORE_TICKS)(MYTIMEDIFF(stop_time_val, start_time_val));
    return elapsed;
}

secs_ret time_in_secs(CORE_TICKS ticks)
{
    secs_ret retval = ((secs_ret)ticks) / (secs_ret)EE_TICKS_PER_SEC;
    return retval;
}

ee_u32 default_num_contexts = 1;

/************************/
/* Init/Fini Functions  */
/************************/

void portable_init(core_portable *p, int *argc, char *argv[])
{
    (void)argc;
    (void)argv;

    /* No initialization needed for minimal port */
    /* Check type sizes */
    if (sizeof(ee_ptr_int) != sizeof(ee_u8 *))
    {
        /* Error: type size mismatch - but we can't print anything */
        while(1); /* Hang */
    }
    if (sizeof(ee_u32) != 4)
    {
        /* Error: type size mismatch */
        while(1); /* Hang */
    }

    p->portable_id = 1;
}

void portable_fini(core_portable *p)
{
    p->portable_id = 0;

    /* Infinite loop at end - keeps commit log clean */
    while(1) {
        asm volatile ("nop");
    }
}
