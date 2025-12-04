#!/usr/bin/env python3
# ============================================================
# Simple RISC-V DV Test Generator (Fallback)
# ============================================================

import argparse
import random

def generate_test(test_name, idx, seed, output_path):
    """Generate a simple test assembly file"""
    rng = random.Random(seed + idx)
    
    # Random values
    vals = [rng.randint(0, 0xFFFFFFFF) for _ in range(3)]
    
    code = f'''/* Generated test: {test_name} iteration {idx} */
    .section .text.init
    .global _start
    .global _pass
    .global _fail

_start:
    /* Initialize stack */
    la sp, _stack_top
    
    /* Initialize registers */
    li x1, 0x{vals[0]:08X}
    li x2, 0x{vals[1]:08X}
    li x3, 0x{vals[2]:08X}
    
    /* Arithmetic sequence */
    add x4, x1, x2
    sub x5, x2, x1
    and x6, x1, x3
    or  x7, x2, x3
    xor x8, x1, x2
    
    /* Shift operations */
    sll  x9, x1, {rng.randint(1,15)}
    srl  x10, x2, {rng.randint(1,15)}
    sra  x11, x3, {rng.randint(1,15)}
    
    /* Immediate operations */
    addi x12, x1, {rng.randint(-500, 500)}
    andi x13, x2, 0xFF
    ori  x14, x3, 0x0F
    
    /* Comparison */
    slt  x15, x1, x2
    sltu x16, x2, x3
    
    /* Memory operations */
    la   x17, data_section
    sw   x1, 0(x17)
    sw   x2, 4(x17)
    lw   x18, 0(x17)
    lw   x19, 4(x17)
    
    /* Verify */
    bne  x1, x18, _fail
    bne  x2, x19, _fail
    
    /* Jump to pass */
    j _pass

_pass:
    li a0, 0
    li t0, 0x1FFFFFFC
    sw a0, 0(t0)
1:  j 1b

_fail:
    li a0, 1
    li t0, 0x1FFFFFFC
    sw a0, 0(t0)
1:  j 1b

    .section .data
    .align 4
data_section:
    .space 64
    
    .section .bss
    .align 4
    .space 4096
_stack_top:
'''
    
    with open(output_path, 'w') as f:
        f.write(code)
    
    print(f'Generated: {output_path}')

def main():
    parser = argparse.ArgumentParser(description='Simple RISCV-DV Test Generator')
    parser.add_argument('--test', type=str, required=True, help='Test name')
    parser.add_argument('--idx', type=int, required=True, help='Iteration index')
    parser.add_argument('--seed', type=int, default=0, help='Random seed')
    parser.add_argument('--output', type=str, required=True, help='Output file')
    args = parser.parse_args()
    
    generate_test(args.test, args.idx, args.seed, args.output)

if __name__ == '__main__':
    main()
