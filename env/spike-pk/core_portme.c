/*
 * CoreMark port for RISC-V with Spike + pk
 * Uses rdcycle CSR for timing
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
/* RISC-V Timer Functions */
/************************/

/* External syscall declarations for pk */
struct timeval {
    long tv_sec;
    long tv_usec;
};

extern int gettimeofday(struct timeval *tv, void *tz);

/* Get time in microseconds using gettimeofday syscall */
static inline uint32_t get_usec(void)
{
    struct timeval tv;
    gettimeofday(&tv, 0);
    return (uint32_t)(tv.tv_sec * 1000000UL + tv.tv_usec);
}

/* Timing implementation using gettimeofday */
#define CORETIMETYPE uint32_t
#define GETMYTIME(_t) (*_t = get_usec())
#define MYTIMEDIFF(fin, ini) ((fin) - (ini))
#define TIMER_RES_DIVIDER 1
#define SAMPLE_TIME_IMPLEMENTATION 1
#define EE_TICKS_PER_SEC 1000000  /* Microseconds per second */

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
    /* Convert cycles to seconds */
    secs_ret retval = ((secs_ret)ticks) / (secs_ret)EE_TICKS_PER_SEC;
    return retval;
}

ee_u32 default_num_contexts = 1;

void portable_init(core_portable *p, int *argc, char *argv[])
{
    (void)argc;
    (void)argv;

    printf("\n");
    printf("=================================\n");
    printf("CoreMark on RISC-V (Spike + pk)\n");
    printf("=================================\n");
    printf("ISA: RV32IMC\n");
    printf("Timing: gettimeofday() syscall\n");
    printf("\n");

    if (sizeof(ee_ptr_int) != sizeof(ee_u8 *))
    {
        printf("ERROR! ee_ptr_int size mismatch!\n");
    }
    if (sizeof(ee_u32) != 4)
    {
        printf("ERROR! ee_u32 must be 32-bit!\n");
    }

    p->portable_id = 1;
}

void portable_fini(core_portable *p)
{
    printf("\n");
    printf("=================================\n");
    printf("CoreMark Complete!\n");
    printf("=================================\n");

    p->portable_id = 0;
}
