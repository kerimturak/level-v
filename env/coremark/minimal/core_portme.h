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

#ifndef CORE_PORTME_H
#define CORE_PORTME_H

#include <stdint.h>
#include <stddef.h>

/************************/
/* Data types and settings */
/************************/

/* Configuration : HAS_FLOAT
        Define to 1 if the platform supports floating point.
*/
#ifndef HAS_FLOAT
#define HAS_FLOAT 0
#endif

/* Configuration : HAS_TIME_H
        Define to 1 if platform has the time.h header file,
        and implementation of functions thereof.
*/
#ifndef HAS_TIME_H
#define HAS_TIME_H 0
#endif

/* Configuration : USE_CLOCK
        Define to 1 if platform has the time.h header file,
        and implementation of functions thereof.
*/
#ifndef USE_CLOCK
#define USE_CLOCK 0
#endif

/* Configuration : HAS_STDIO
        Define to 1 if the platform has stdio.h.
*/
#ifndef HAS_STDIO
#define HAS_STDIO 0
#endif

/* Configuration : HAS_PRINTF
        Define to 1 if platform has stdio.h and implements the printf function.
*/
#ifndef HAS_PRINTF
#define HAS_PRINTF 0
#endif

/* Definitions : COMPILER_VERSION, COMPILER_FLAGS
        Initialize these strings per platform
*/
#ifndef COMPILER_VERSION
#ifdef __GNUC__
#define COMPILER_VERSION "GCC"__VERSION__
#else
#define COMPILER_VERSION "Unknown"
#endif
#endif

#ifndef COMPILER_FLAGS
#define COMPILER_FLAGS FLAGS_STR /* This should be defined in the Makefile */
#endif

/* Data Types :
        To avoid compiler issues, define the data types that need to be used for
   8b, 16b and 32b in <core_portme.h>.
*/
typedef int16_t  ee_s16;
typedef uint16_t ee_u16;
typedef int32_t  ee_s32;
typedef uint32_t ee_u32;
typedef uint8_t  ee_u8;
typedef double   ee_f32;

/* align_mem :
        This macro is used to align an offset to point to a 32b value. It is
   used in the Matrix algorithm to initialize the input memory blocks.
*/
#define align_mem(x) (void *)(4 + (((ee_ptr_int)(x)-1) & ~3))

/* Configuration : SEED_METHOD
        Defines method to get seed values that cannot be computed at compile
   time.

        Valid values :
        SEED_ARG - from command line.
        SEED_FUNC - from a system function.
        SEED_VOLATILE - from volatile variables.
*/
#ifndef SEED_METHOD
#define SEED_METHOD SEED_VOLATILE
#endif

/* Configuration : MEM_METHOD
        Defines method to get a block of memry.

        Valid values :
        MEM_MALLOC - for platforms that implement malloc and have malloc.h.
        MEM_STATIC - to use a static memory array.
        MEM_STACK - to allocate the data block on the stack (NYI).
*/
#ifndef MEM_METHOD
#define MEM_METHOD MEM_STACK
#endif

/* Configuration : MULTITHREAD
        Define for parallel execution
*/
#ifndef MULTITHREAD
#define MULTITHREAD 1
#define USE_PTHREAD 0
#define USE_FORK    0
#define USE_SOCKET  0
#endif

/* Configuration : MAIN_HAS_NOARGC
        Needed if platform does not support getting arguments to main.
*/
#ifndef MAIN_HAS_NOARGC
#define MAIN_HAS_NOARGC 1
#endif

/* Configuration : MAIN_HAS_NORETURN
        Needed if platform does not support returning a value from main.
*/
#ifndef MAIN_HAS_NORETURN
#define MAIN_HAS_NORETURN 0
#endif

/* Variable : default_num_contexts
        Not used for this simple port, must contain the value 1.
*/
extern ee_u32 default_num_contexts;

typedef struct CORE_PORTABLE_S
{
    ee_u8 portable_id;
} core_portable;

/* target specific init/fini */
void portable_init(core_portable *p, int *argc, char *argv[]);
void portable_fini(core_portable *p);

#endif /* CORE_PORTME_H */

/* Additional type definitions */
typedef ee_u32 CORE_TICKS;
typedef size_t ee_size_t;
typedef int32_t ee_ptr_int;
typedef uint8_t ee_u8;
