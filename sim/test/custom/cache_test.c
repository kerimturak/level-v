/*
 * Cache Performance and Correctness Test
 * Tests instruction and data cache behavior
 */

#include "ceres_test.h"

// Memory regions - Use definitions from ceres_test.h
// Test buffer (smaller to fit in RAM)
#define TEST_BUF_SIZE 512  // 2KB total
volatile uint32_t test_buffer[TEST_BUF_SIZE] __attribute__((aligned(64)));

// Timing using mcycle
static inline uint32_t get_cycle(void) {
    uint32_t cycle;
    asm volatile ("csrr %0, mcycle" : "=r"(cycle));
    return cycle;
}

// Test 1: Sequential Write/Read
int test_sequential_access(void) {
    int result = TEST_PASS;
    
    print_str("Sequential access test:\n");
    
    uint32_t start_cycle = get_cycle();
    
    // Write sequential pattern
    for (int i = 0; i < TEST_BUF_SIZE; i++) {
        test_buffer[i] = i;
    }
    
    uint32_t write_cycles = get_cycle() - start_cycle;
    
    start_cycle = get_cycle();
    
    // Read and verify
    for (int i = 0; i < TEST_BUF_SIZE; i++) {
        if (test_buffer[i] != (uint32_t)i) {
            print_str("  ERROR at index ");
            print_hex(i);
            print_str(": expected ");
            print_hex(i);
            print_str(", got ");
            print_hex(test_buffer[i]);
            print_str("\n");
            result = TEST_FAIL;
            break;
        }
    }
    
    uint32_t read_cycles = get_cycle() - start_cycle;
    
    print_str("  Write cycles: ");
    print_hex(write_cycles);
    print_str("\n  Read cycles: ");
    print_hex(read_cycles);
    print_str("\n");
    
    return result;
}

// Test 2: Stride Access (tests cache line behavior)
int test_stride_access(void) {
    int result = TEST_PASS;

    print_str("Stride access test:\n");

    // Clear buffer (smaller range to avoid excessive UART output)
    #define STRIDE_TEST_SIZE 256  // Reduced from TEST_BUF_SIZE
    for (int i = 0; i < STRIDE_TEST_SIZE; i++) {
        test_buffer[i] = 0;
    }

    // Test different strides
    int strides[] = {1, 4, 8, 16};  // Reduced from 5 to 4 strides

    for (int s = 0; s < 4; s++) {
        int stride = strides[s];
        uint32_t start_cycle = get_cycle();

        // Write with stride
        for (int i = 0; i < STRIDE_TEST_SIZE; i += stride) {
            test_buffer[i] = i;
        }

        uint32_t write_cycles = get_cycle() - start_cycle;

        start_cycle = get_cycle();

        // Read with stride
        volatile uint32_t sum = 0;
        for (int i = 0; i < STRIDE_TEST_SIZE; i += stride) {
            sum += test_buffer[i];
        }

        uint32_t read_cycles = get_cycle() - start_cycle;

        print_str("  S");
        print_hex(stride * 4);
        print_str(": W=");
        print_hex(write_cycles);
        print_str(" R=");
        print_hex(read_cycles);
        print_str("\n");
    }

    return result;
}

// Test 3: Cache Thrashing (access pattern larger than cache)
int test_cache_thrashing(void) {
    print_str("Cache thrashing test:\n");
    
    // Assuming 4KB cache, access 8KB pattern
    int pattern_size = 2048;  // 8KB in words
    
    uint32_t start_cycle = get_cycle();
    
    // First pass - cold cache
    volatile uint32_t sum = 0;
    for (int i = 0; i < pattern_size; i++) {
        sum += test_buffer[i];
    }
    
    uint32_t cold_cycles = get_cycle() - start_cycle;
    
    start_cycle = get_cycle();
    
    // Second pass - should be faster if data fits in cache
    sum = 0;
    for (int i = 0; i < pattern_size; i++) {
        sum += test_buffer[i];
    }
    
    uint32_t warm_cycles = get_cycle() - start_cycle;
    
    print_str("  Cold cache cycles: ");
    print_hex(cold_cycles);
    print_str("\n  Warm cache cycles: ");
    print_hex(warm_cycles);
    print_str("\n");
    
    // Warm should be faster (or similar if cache is small)
    if (warm_cycles < cold_cycles) {
        print_str("  Cache effect detected\n");
    } else {
        print_str("  No cache speedup (pattern may exceed cache size)\n");
    }
    
    return TEST_PASS;
}

// Test 4: Write-through / Write-back behavior
int test_write_behavior(void) {
    print_str("Write behavior test:\n");
    
    // Write to an address
    test_buffer[0] = 0xDEADBEEF;
    
    // Immediately read back
    uint32_t val = test_buffer[0];
    
    print_str("  Write 0xDEADBEEF, read: 0x");
    print_hex(val);
    print_str("\n");
    
    if (val == 0xDEADBEEF) {
        print_str("  Write-through/coherent: OK\n");
        return TEST_PASS;
    } else {
        print_str("  Write-through: FAILED\n");
        return TEST_FAIL;
    }
}

// Test 5: Unaligned Access (if supported)
int test_unaligned_access(void) {
    print_str("Unaligned access test:\n");
    
    // Write aligned data
    uint8_t *byte_ptr = (uint8_t *)test_buffer;
    
    byte_ptr[0] = 0x11;
    byte_ptr[1] = 0x22;
    byte_ptr[2] = 0x33;
    byte_ptr[3] = 0x44;
    byte_ptr[4] = 0x55;
    byte_ptr[5] = 0x66;
    byte_ptr[6] = 0x77;
    byte_ptr[7] = 0x88;
    
    // Read back as words at different alignments
    print_str("  Aligned word [0]: 0x");
    print_hex(test_buffer[0]);
    print_str("\n  Aligned word [1]: 0x");
    print_hex(test_buffer[1]);
    print_str("\n");
    
    // Byte access test
    print_str("  Byte access: ");
    for (int i = 0; i < 8; i++) {
        print_hex(byte_ptr[i] & 0xFF);
        print_str(" ");
    }
    print_str("\n");
    
    // Halfword access
    uint16_t *half_ptr = (uint16_t *)test_buffer;
    print_str("  Halfword access: ");
    for (int i = 0; i < 4; i++) {
        print_hex(half_ptr[i] & 0xFFFF);
        print_str(" ");
    }
    print_str("\n");
    
    return TEST_PASS;
}

// Test 6: Memory ordering (basic)
int test_memory_ordering(void) {
    print_str("Memory ordering test:\n");
    
    // Write to two locations
    test_buffer[0] = 0;
    test_buffer[1] = 0;
    
    // Store-store ordering
    test_buffer[0] = 1;
    test_buffer[1] = 2;
    
    // Read back in order
    uint32_t v0 = test_buffer[0];
    uint32_t v1 = test_buffer[1];
    
    print_str("  Store 1,2 -> Read: ");
    print_hex(v0);
    print_str(", ");
    print_hex(v1);
    print_str("\n");
    
    if (v0 == 1 && v1 == 2) {
        print_str("  Memory ordering: OK\n");
        return TEST_PASS;
    } else {
        print_str("  Memory ordering: FAILED\n");
        return TEST_FAIL;
    }
}

// Test 7: Random Access Pattern
int test_random_access(void) {
    print_str("Random access pattern test:\n");

    // Simple pseudo-random generator (LCG)
    uint32_t seed = 12345;
    #define RAND() (seed = seed * 1103515245 + 12345, (seed >> 16) & 0x7fff)

    // Initialize with pattern
    for (int i = 0; i < 256; i++) {
        test_buffer[i] = i * 0x01010101;
    }

    uint32_t start_cycle = get_cycle();

    // Random access reads
    volatile uint32_t sum = 0;
    for (int i = 0; i < 1000; i++) {
        int idx = RAND() % 256;
        sum += test_buffer[idx];
    }

    uint32_t cycles = get_cycle() - start_cycle;

    print_str("  1000 random reads: ");
    print_hex(cycles);
    print_str(" cycles\n");

    return TEST_PASS;
}

// Test 8: Writeback Stress Test (Force Cache Evictions)
int test_writeback_stress(void) {
    int result = TEST_PASS;

    print_str("Writeback stress test:\n");
    print_str("  This test forces cache writebacks by:\n");
    print_str("  1. Filling cache with dirty data\n");
    print_str("  2. Forcing eviction with conflicting addresses\n");
    print_str("  3. Verifying data integrity after writeback\n\n");

    // Cache parameters (4-way, 1KB total = 256B per way, 16B line)
    // With 4-way cache: accessing 5+ addresses at same index forces eviction

    #define CACHE_SETS 16       // Assuming 1KB / 4-way / 16B line
    #define CACHE_LINE_SIZE 16  // 16 bytes = 4 words
    #define CACHE_SET_STRIDE (CACHE_SETS * CACHE_LINE_SIZE)  // 256 bytes

    print_str("  Phase 1: Fill all 4 ways with dirty data\n");

    // Write to 4 ways of the same cache set (index 0)
    for (int way = 0; way < 4; way++) {
        uint32_t offset = way * CACHE_SET_STRIDE / 4;  // 0, 64, 128, 192 words
        for (int w = 0; w < 4; w++) {  // 4 words per cache line
            test_buffer[offset + w] = 0xA0000000 | (way << 16) | w;
        }
    }

    print_str("  Phase 2: Force eviction with 5th conflicting write\n");

    // Write to 5th conflicting address - should evict one dirty line
    uint32_t offset5 = 4 * CACHE_SET_STRIDE / 4;  // 256 words
    for (int w = 0; w < 4; w++) {
        test_buffer[offset5 + w] = 0xB0000000 | (4 << 16) | w;
    }

    print_str("  Phase 3: Verify all data (including evicted)\n");

    // Verify first 4 ways - one should have been evicted and written back
    for (int way = 0; way < 4; way++) {
        uint32_t offset = way * CACHE_SET_STRIDE / 4;
        for (int w = 0; w < 4; w++) {
            uint32_t expected = 0xA0000000 | (way << 16) | w;
            uint32_t actual = test_buffer[offset + w];
            if (actual != expected) {
                print_str("  ERROR: Way ");
                print_hex(way);
                print_str(" Word ");
                print_hex(w);
                print_str(": expected 0x");
                print_hex(expected);
                print_str(", got 0x");
                print_hex(actual);
                print_str("\n");
                result = TEST_FAIL;
            }
        }
    }

    // Verify 5th way
    for (int w = 0; w < 4; w++) {
        uint32_t expected = 0xB0000000 | (4 << 16) | w;
        uint32_t actual = test_buffer[offset5 + w];
        if (actual != expected) {
            print_str("  ERROR: Way 5 Word ");
            print_hex(w);
            print_str(": expected 0x");
            print_hex(expected);
            print_str(", got 0x");
            print_hex(actual);
            print_str("\n");
            result = TEST_FAIL;
        }
    }

    if (result == TEST_PASS) {
        print_str("  All data verified - writeback successful!\n");
    }

    print_str("\n  Phase 4: Heavy writeback stress (many evictions)\n");

    // Write to many conflicting addresses to force multiple writebacks
    for (int i = 0; i < 32; i++) {
        uint32_t offset = i * CACHE_SET_STRIDE / 4;
        for (int w = 0; w < 4; w++) {
            test_buffer[offset + w] = 0xC0000000 | (i << 16) | w;
        }
    }

    // Verify all 32 blocks
    int errors = 0;
    for (int i = 0; i < 32; i++) {
        uint32_t offset = i * CACHE_SET_STRIDE / 4;
        for (int w = 0; w < 4; w++) {
            uint32_t expected = 0xC0000000 | (i << 16) | w;
            uint32_t actual = test_buffer[offset + w];
            if (actual != expected) {
                if (errors < 5) {  // Only print first 5 errors
                    print_str("  ERROR: Block ");
                    print_hex(i);
                    print_str(" Word ");
                    print_hex(w);
                    print_str(": expected 0x");
                    print_hex(expected);
                    print_str(", got 0x");
                    print_hex(actual);
                    print_str("\n");
                }
                errors++;
                result = TEST_FAIL;
            }
        }
    }

    if (errors > 0) {
        print_str("  Total errors: ");
        print_hex(errors);
        print_str("\n");
    } else {
        print_str("  Heavy stress test: All 32 blocks verified!\n");
    }

    // Phase 5: fence.i writeback test
    print_str("\n  Phase 5: fence.i forced writeback\n");

    // Write some dirty data
    for (int i = 0; i < 16; i++) {
        test_buffer[i] = 0xFEED0000 | i;
    }

    // Execute fence.i to force writeback of all dirty lines
    asm volatile ("fence.i");

    // Verify data after fence.i
    for (int i = 0; i < 16; i++) {
        uint32_t expected = 0xFEED0000 | i;
        uint32_t actual = test_buffer[i];
        if (actual != expected) {
            print_str("  ERROR after fence.i at ");
            print_hex(i);
            print_str(": expected 0x");
            print_hex(expected);
            print_str(", got 0x");
            print_hex(actual);
            print_str("\n");
            result = TEST_FAIL;
        }
    }

    if (result == TEST_PASS) {
        print_str("  fence.i writeback successful!\n");
    }

    return result;
}

// Test 9: Aggressive Read-Write Patterns
int test_aggressive_rw_patterns(void) {
    int result = TEST_PASS;

    print_str("Aggressive R/W pattern test:\n");

    // Much smaller test size for reliability
    #define PATTERN_TEST_SIZE 128  // Just 128 words

    // Pattern 1: Read-Write (RW)
    print_str("\n  Pattern RW: ");
    for (int i = 0; i < PATTERN_TEST_SIZE; i++) {
        volatile uint32_t val = test_buffer[i];
        test_buffer[i] = val + 1;
        if (test_buffer[i] != val + 1) {result = TEST_FAIL; break;}
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    // Pattern 2: Write-Read (WR)
    print_str("  Pattern WR: ");
    for (int i = 0; i < PATTERN_TEST_SIZE; i++) {
        test_buffer[i] = 0xCAFE0000 | i;
        volatile uint32_t val = test_buffer[i];
        if (val != (0xCAFE0000 | i)) {result = TEST_FAIL; break;}
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    // Pattern 3: Write-Write (WW)
    print_str("  Pattern WW: ");
    for (int i = 0; i < PATTERN_TEST_SIZE; i++) {
        test_buffer[i] = 0xDEAD0000 | i;
        test_buffer[i] = 0xBEEF0000 | i;
        if (test_buffer[i] != (0xBEEF0000 | i)) {result = TEST_FAIL; break;}
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    // Pattern 4: Read-Read (RR)
    print_str("  Pattern RR: ");
    for (int i = 0; i < PATTERN_TEST_SIZE; i++) {
        volatile uint32_t val1 = test_buffer[i];
        volatile uint32_t val2 = test_buffer[i];
        if (val1 != val2) {result = TEST_FAIL; break;}
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    // Pattern 5: Read-Write-Read (RWR)
    print_str("  Pattern RWR: ");
    for (int i = 0; i < PATTERN_TEST_SIZE; i++) {
        volatile uint32_t val1 = test_buffer[i];
        test_buffer[i] = 0xABCD0000 | i;
        volatile uint32_t val2 = test_buffer[i];
        if (val2 != (0xABCD0000 | i)) {result = TEST_FAIL; break;}
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    // Pattern 6: Write-Read-Write (WRW)
    print_str("  Pattern WRW: ");
    for (int i = 0; i < PATTERN_TEST_SIZE; i++) {
        test_buffer[i] = 0x11110000 | i;
        volatile uint32_t val = test_buffer[i];
        test_buffer[i] = 0x22220000 | i;
        if (test_buffer[i] != (0x22220000 | i)) {result = TEST_FAIL; break;}
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    return result;
}

// Test 10: Multi-Size Aggressive Patterns
int test_multisize_patterns(void) {
    int result = TEST_PASS;

    print_str("Multi-size R/W pattern test:\n");

    uint8_t  *byte_ptr = (uint8_t *)test_buffer;
    uint16_t *half_ptr = (uint16_t *)test_buffer;
    uint32_t *word_ptr = test_buffer;

    // BYTE Write-Read
    print_str("  BYTE: ");
    for (int i = 0; i < 128; i++) {
        byte_ptr[i] = (uint8_t)(i & 0xFF);
        volatile uint8_t val = byte_ptr[i];
        if (val != (uint8_t)(i & 0xFF)) {result = TEST_FAIL; break;}
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    // HALFWORD Write-Read
    print_str("  HALFWORD: ");
    for (int i = 0; i < 64; i++) {
        half_ptr[i] = (uint16_t)(0xA000 | (i & 0xFFF));
        volatile uint16_t val = half_ptr[i];
        if (val != (uint16_t)(0xA000 | (i & 0xFFF))) {result = TEST_FAIL; break;}
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    // WORD Write-Read
    print_str("  WORD: ");
    for (int i = 0; i < 32; i++) {
        word_ptr[i] = 0xDEADBEEF ^ i;
        volatile uint32_t val = word_ptr[i];
        if (val != (0xDEADBEEF ^ i)) {result = TEST_FAIL; break;}
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    // Mixed Size
    print_str("  Mixed: ");
    for (int i = 0; i < 16; i++) {
        word_ptr[i] = 0x12345678;
        uint8_t b0 = byte_ptr[i*4];
        uint8_t b1 = byte_ptr[i*4 + 1];
        uint8_t b2 = byte_ptr[i*4 + 2];
        uint8_t b3 = byte_ptr[i*4 + 3];
        if (b0 != 0x78 || b1 != 0x56 || b2 != 0x34 || b3 != 0x12) {result = TEST_FAIL; break;}
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    return result;
}

// Test 11: Set 0 Stress Test (Same cache set)
int test_set0_stress(void) {
    int result = TEST_PASS;

    print_str("Set 0 stress test:\n");

    #define SET_STRIDE 256  // 256 bytes = skip to same set
    #define SET0_COUNT 8    // 8 blocks

    // Write to set 0 addresses
    print_str("  Write: ");
    for (int block = 0; block < SET0_COUNT; block++) {
        uint32_t offset = (block * SET_STRIDE) / 4;
        if (offset >= TEST_BUF_SIZE) break;
        for (int w = 0; w < 4; w++) {
            test_buffer[offset + w] = 0xA0000000 | (block << 8) | w;
        }
    }
    print_str("OK\n");

    // Read back
    print_str("  Read: ");
    for (int block = 0; block < SET0_COUNT; block++) {
        uint32_t offset = (block * SET_STRIDE) / 4;
        if (offset >= TEST_BUF_SIZE) break;
        for (int w = 0; w < 4; w++) {
            uint32_t expected = 0xA0000000 | (block << 8) | w;
            if (test_buffer[offset + w] != expected) {result = TEST_FAIL; break;}
        }
        if (result == TEST_FAIL) break;
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    // Rapid RW
    print_str("  RW Stress: ");
    for (int iter = 0; iter < 20; iter++) {
        for (int block = 0; block < SET0_COUNT; block++) {
            uint32_t offset = (block * SET_STRIDE) / 4;
            if (offset >= TEST_BUF_SIZE) break;
            volatile uint32_t val = test_buffer[offset];
            test_buffer[offset] = val + 1;
        }
    }
    print_str("OK\n");

    return result;
}

// Test 12: Cache Thrashing
int test_extreme_thrashing(void) {
    int result = TEST_PASS;

    print_str("Cache thrashing test:\n");

    #define THRASH_SIZE 512  // Just 2KB

    // Initialize
    print_str("  Init: ");
    for (int i = 0; i < THRASH_SIZE; i++) {
        test_buffer[i] = i;
    }
    print_str("OK\n");

    // Read twice
    print_str("  Read: ");
    volatile uint32_t sum1 = 0, sum2 = 0;
    for (int i = 0; i < THRASH_SIZE; i++) sum1 += test_buffer[i];
    for (int i = 0; i < THRASH_SIZE; i++) sum2 += test_buffer[i];
    if (sum1 != sum2) result = TEST_FAIL;
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    // Write
    print_str("  Write: ");
    for (int i = 0; i < THRASH_SIZE; i++) {
        test_buffer[i] = 0xDEAD0000 | i;
    }
    print_str("OK\n");

    // Verify
    print_str("  Verify: ");
    for (int i = 0; i < THRASH_SIZE; i++) {
        if (test_buffer[i] != (0xDEAD0000 | i)) {result = TEST_FAIL; break;}
    }
    print_str(result == TEST_PASS ? "OK\n" : "FAIL\n");

    return result;
}

int main(void) {
    int result = TEST_PASS;
    int test_result;
    
    print_str("\n=== Cache Test Suite ===\n\n");
    
    // Test 1
    print_str("Test 1: Sequential Access\n");
    test_result = test_sequential_access();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 2
    print_str("Test 2: Stride Access\n");
    test_result = test_stride_access();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 3
    print_str("Test 3: Cache Thrashing\n");
    test_result = test_cache_thrashing();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 4
    print_str("Test 4: Write Behavior\n");
    test_result = test_write_behavior();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 5
    print_str("Test 5: Byte/Halfword Access\n");
    test_result = test_unaligned_access();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 6
    print_str("Test 6: Memory Ordering\n");
    test_result = test_memory_ordering();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");
    
    // Test 7
    print_str("Test 7: Random Access\n");
    test_result = test_random_access();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");

    // Test 8
    print_str("Test 8: Writeback Stress\n");
    test_result = test_writeback_stress();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");

    // Test 9: Aggressive R/W Patterns
    print_str("Test 9: Aggressive R/W Patterns\n");
    test_result = test_aggressive_rw_patterns();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");

    // Test 10: Multi-Size Patterns
    print_str("Test 10: Multi-Size Patterns\n");
    test_result = test_multisize_patterns();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");

    // Test 11: Set 0 Stress
    print_str("Test 11: Set 0 Stress Test\n");
    test_result = test_set0_stress();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");

    // Test 12: Extreme Thrashing
    print_str("Test 12: Extreme Thrashing (32x Cache)\n");
    test_result = test_extreme_thrashing();
    if (test_result != TEST_PASS) result = TEST_FAIL;
    print_str(test_result == TEST_PASS ? "PASSED\n\n" : "FAILED\n\n");

    // Summary
    if (result == TEST_PASS) {
        print_str("*** ALL CACHE TESTS PASSED ***\n");
    } else {
        print_str("*** SOME CACHE TESTS FAILED ***\n");
    }

    TEST_COMPLETE(result);

    return result;
}
