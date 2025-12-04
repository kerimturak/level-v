#!/usr/bin/env python3
"""
Simple RISC-V Torture Test Generator (Fallback)
===============================================
Generates simple but valid instruction sequences for basic testing.
Used as fallback when main generator is unavailable or for quick tests.

Features:
- Minimal dependencies
- Fast generation
- Guaranteed valid output
- Memory-safe operations

Author: Ceres-V Project
License: MIT
"""

import argparse
import random
import sys
import logging

logging.basicConfig(level=logging.INFO, format='[%(levelname)s] %(message)s')
logger = logging.getLogger(__name__)

def generate_simple_test(seed: int, name: str, output_path: str) -> None:
    """
    Generate a simple torture test assembly file.
    
    Args:
        seed: Random seed for reproducibility
        name: Test name (for comments)
        output_path: Output file path
        
    Raises:
        IOError: If file cannot be written
    """
    logger.info(f'Generating simple test: {name} (seed={seed})')
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
    
    try:
        with open(output_path, 'w') as f:
            f.write(code)
        logger.info(f'Successfully wrote: {output_path}')
    except IOError as e:
        logger.error(f'Failed to write file: {e}')
        raise

def main():
    parser = argparse.ArgumentParser(
        description='Simple RISC-V Torture Test Generator (Fallback)',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('--seed', type=int, required=True,
                        help='Random seed for reproducibility')
    parser.add_argument('--name', type=str, required=True,
                        help='Test name (for comments)')
    parser.add_argument('--output', type=str, required=True,
                        help='Output assembly file path')
    parser.add_argument('--verbose', action='store_true',
                        help='Enable verbose logging')
    
    args = parser.parse_args()
    
    if args.verbose:
        logger.setLevel(logging.DEBUG)
    
    # Validate arguments
    if args.seed < 0:
        logger.error('Seed must be non-negative')
        sys.exit(1)
    
    try:
        generate_simple_test(args.seed, args.name, args.output)
    except Exception as e:
        logger.error(f'Test generation failed: {e}')
        sys.exit(1)

if __name__ == '__main__':
    main()
