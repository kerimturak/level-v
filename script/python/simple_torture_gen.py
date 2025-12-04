#!/usr/bin/env python3
# ============================================================
# Simple Torture Test Generator (Fallback)
# ============================================================
# Generates simple valid instruction sequences

import argparse
import random

def generate_simple_test(seed, name, output_path):
    """Generate a simple torture test assembly file"""
    rng = random.Random(seed)
    
    # Generate random initial values
    vals = [rng.randint(0, 0xFFFFFFFF) for _ in range(3)]
    
    code = f'''/* Auto-generated torture test - seed: {seed} */
    .section .text.init, "ax"
    .global _start
    .global _pass
    .global _fail

_start:
    /* Initialize */
    li sp, 0x80180000
    li gp, 0
    
    /* Random instruction sequence */
    li x1, 0x{vals[0]:08X}
    li x2, 0x{vals[1]:08X}
    li x3, 0x{vals[2]:08X}
    
    add x4, x1, x2
    sub x5, x2, x1
    xor x6, x4, x5
    or  x7, x1, x3
    and x8, x2, x3
    
    sll x9, x1, {rng.randint(1,15)}
    srl x10, x2, {rng.randint(1,15)}
    sra x11, x2, {rng.randint(1,15)}
    
    slti x12, x1, {rng.randint(-1000, 1000)}
    sltiu x13, x2, {rng.randint(0, 2000)}
    
    addi x14, x1, {rng.randint(-500, 500)}
    xori x15, x2, 0x{rng.randint(0, 255):02X}
    ori  x16, x3, 0x{rng.randint(0, 15):02X}
    andi x17, x1, 0x{rng.randint(0, 255):02X}
    
    /* Memory operations */
    la x18, test_data
    sw x1, 0(x18)
    sw x2, 4(x18)
    lw x19, 0(x18)
    lw x20, 4(x18)
    
    /* Verify */
    bne x1, x19, _fail
    bne x2, x20, _fail
    
    /* Branch tests */
    beq x1, x1, 1f
    j _fail
1:  bne x1, x2, 2f
    j _fail
2:  blt x1, x2, _fail
    bge x1, x2, 3f
    j _fail
3:  bltu x1, x2, 4f
    j _fail
4:  bgeu x2, x1, _pass
    j _fail

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
test_data:
    .space 64
'''
    
    with open(output_path, 'w') as f:
        f.write(code)
    
    print(f'Generated: {output_path}')

def main():
    parser = argparse.ArgumentParser(description='Simple Torture Test Generator')
    parser.add_argument('--seed', type=int, required=True, help='Random seed')
    parser.add_argument('--name', type=str, required=True, help='Test name')
    parser.add_argument('--output', type=str, required=True, help='Output file')
    args = parser.parse_args()
    
    generate_simple_test(args.seed, args.name, args.output)

if __name__ == '__main__':
    main()
