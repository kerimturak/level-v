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
    
    // Clear buffer
    for (int i = 0; i < TEST_BUF_SIZE; i++) {
        test_buffer[i] = 0;
    }
    
    // Test different strides
    int strides[] = {1, 4, 8, 16, 32};  // 4, 16, 32, 64, 128 bytes
    
    for (int s = 0; s < 5; s++) {
        int stride = strides[s];
        uint32_t start_cycle = get_cycle();
        
        // Write with stride
        for (int i = 0; i < TEST_BUF_SIZE; i += stride) {
            test_buffer[i] = i;
        }
        
        uint32_t write_cycles = get_cycle() - start_cycle;
        
        start_cycle = get_cycle();
        
        // Read with stride
        volatile uint32_t sum = 0;
        for (int i = 0; i < TEST_BUF_SIZE; i += stride) {
            sum += test_buffer[i];
        }
        
        uint32_t read_cycles = get_cycle() - start_cycle;
        
        print_str("  Stride ");
        print_hex(stride * 4);
        print_str(" bytes: W=");
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

    // Summary
    if (result == TEST_PASS) {
        print_str("*** ALL CACHE TESTS PASSED ***\n");
    } else {
        print_str("*** SOME CACHE TESTS FAILED ***\n");
    }

    TEST_COMPLETE(result);

    return result;
}
