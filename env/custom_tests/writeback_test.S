#*****************************************************************************
# writeback_test.S
#-----------------------------------------------------------------------------
#
# Test dcache writeback mechanism by:
# 1. Writing to multiple cache sets to fill cache
# 2. Forcing eviction by accessing conflicting addresses
# 3. Using fence.i to trigger dirty line writeback
#
#*****************************************************************************

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32M
RVTEST_CODE_BEGIN

  # Initialize test data base address
  la    x1, test_data_base

  #---------------------------------------------------------------------------
  # Test 1: Fill cache with dirty lines (write to 4-way cache)
  #---------------------------------------------------------------------------

  li    x2, 0xAABBCCDD
  li    x3, 0x11223344
  li    x4, 0x55667788
  li    x5, 0x99AABBCC

  # Write to way 0 - offset 0x0000
  sw    x2, 0(x1)
  sw    x3, 4(x1)
  sw    x4, 8(x1)
  sw    x5, 12(x1)

  # Write to way 1 - offset 0x0400 (1KB - should map to same set, different way)
  sw    x2, 1024(x1)
  sw    x3, 1028(x1)
  sw    x4, 1032(x1)
  sw    x5, 1036(x1)

  # Write to way 2 - offset 0x0800 (2KB)
  sw    x2, 2048(x1)
  sw    x3, 2052(x1)
  sw    x4, 2056(x1)
  sw    x5, 2060(x1)

  # Write to way 3 - offset 0x0C00 (3KB)
  sw    x2, 3072(x1)
  sw    x3, 3076(x1)
  sw    x4, 3080(x1)
  sw    x5, 3084(x1)

  #---------------------------------------------------------------------------
  # Test 2: Force eviction by accessing 5th conflicting address
  #---------------------------------------------------------------------------

  # Write to way 4 (same set) - offset 0x1000 (4KB)
  # This should evict one of the previous dirty lines
  li    x6, 0xDEADBEEF
  sw    x6, 4096(x1)
  sw    x6, 4100(x1)
  sw    x6, 4104(x1)
  sw    x6, 4108(x1)

  # More evictions - fill more sets
  sw    x6, 5120(x1)   # +1KB
  sw    x6, 6144(x1)   # +1KB
  sw    x6, 7168(x1)   # +1KB

  #---------------------------------------------------------------------------
  # Test 3: Verify writeback happened by reading back
  #---------------------------------------------------------------------------

  lw    x7, 0(x1)
  bne   x7, x2, test_fail

  lw    x7, 1024(x1)
  bne   x7, x2, test_fail

  lw    x7, 2048(x1)
  bne   x7, x2, test_fail

  lw    x7, 3072(x1)
  bne   x7, x2, test_fail

  #---------------------------------------------------------------------------
  # Test 4: fence.i to force all dirty lines to writeback
  #---------------------------------------------------------------------------

  # Write more dirty data
  li    x8, 0xCAFEBABE
  sw    x8, 16(x1)
  sw    x8, 1040(x1)
  sw    x8, 2064(x1)

  # Execute fence.i - should writeback all dirty lines
  fence.i

  # Verify data after fence.i
  lw    x9, 16(x1)
  bne   x9, x8, test_fail

  lw    x9, 1040(x1)
  bne   x9, x8, test_fail

  #---------------------------------------------------------------------------
  # Test 5: Stress test - many writes to cause multiple writebacks
  #---------------------------------------------------------------------------

  li    x10, 0         # Counter
  li    x11, 64        # Loop limit (64 cache lines)
  li    x12, 0x12345678

stress_loop:
  slli  x13, x10, 4    # Multiply by 16 (cache line size)
  add   x14, x1, x13

  sw    x12, 0(x14)
  sw    x12, 4(x14)
  sw    x12, 8(x14)
  sw    x12, 12(x14)

  addi  x10, x10, 1
  blt   x10, x11, stress_loop

  # Final fence.i to flush all dirty data
  fence.i

  #---------------------------------------------------------------------------
  # Test 6: Verify all stress test data
  #---------------------------------------------------------------------------

  li    x10, 0         # Reset counter

verify_loop:
  slli  x13, x10, 4
  add   x14, x1, x13

  lw    x15, 0(x14)
  bne   x15, x12, test_fail

  addi  x10, x10, 1
  blt   x10, x11, verify_loop

test_pass:
  li    a0, 1          # Success
  j     test_end

test_fail:
  li    a0, 0          # Failure

test_end:
  # Write result to UART for logging
  li    x20, 0x30000000  # UART base address
  sb    a0, 0(x20)

  # Infinite loop
  j     .

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

  .align 12  # Align to 4KB for cache testing
test_data_base:
  .space 8192  # 8KB data space for cache tests

RVTEST_DATA_END
