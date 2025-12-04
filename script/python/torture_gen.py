#!/usr/bin/env python3
"""
RISC-V Torture Test Generator for Ceres-V
==========================================
Generates random but valid RISC-V instruction sequences for processor stress testing.

Features:
- Configurable instruction mix and complexity
- Support for RV32I, M, C extensions
- Memory-safe load/store generation
- Branch coverage optimization
- Deterministic via seed control
- Comprehensive error handling

Author: Ceres-V Project
License: MIT
"""

import argparse
import random
import sys
import logging
from typing import List, Optional, Tuple, Callable
from dataclasses import dataclass
from enum import Enum

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='[%(levelname)s] %(message)s'
)
logger = logging.getLogger(__name__)


class Extension(Enum):
    """RISC-V ISA Extensions"""
    I = 'i'  # Base integer
    M = 'm'  # Integer multiplication/division
    C = 'c'  # Compressed instructions
    ZICSR = 'zicsr'  # CSR instructions


@dataclass
class GeneratorConfig:
    """Configuration for torture test generation"""
    seed: int
    max_instructions: int = 1000
    march: str = 'rv32imc'
    # Instruction mix weights (percentages)
    weight_r_type: int = 30
    weight_i_type: int = 25
    weight_shift: int = 10
    weight_load: int = 10
    weight_store: int = 10
    weight_lui_auipc: int = 5
    weight_compressed: int = 10
    # Branch/jump configuration
    branch_probability: float = 0.05  # Chance of inserting a branch
    max_branch_distance: int = 10  # Max instructions to skip
    # Memory configuration
    data_region_size: int = 256  # Bytes
    safe_offsets: List[int] = None  # Safe memory offsets
    
    def __post_init__(self):
        if self.safe_offsets is None:
            # Default safe word-aligned offsets
            self.safe_offsets = [i * 4 for i in range(self.data_region_size // 4)]
        
        # Validate march
        valid_march = ['rv32i', 'rv32im', 'rv32ic', 'rv32imc']
        if self.march not in valid_march:
            logger.warning(f'Unknown march "{self.march}", using rv32imc')
            self.march = 'rv32imc'
    
    def has_extension(self, ext: Extension) -> bool:
        """Check if an extension is enabled"""
        return ext.value in self.march.lower()


class RegisterFile:
    """Manages RISC-V register allocation and constraints"""
    
    # ABI names for reference
    ABI_NAMES = {
        'x0': 'zero', 'x1': 'ra', 'x2': 'sp', 'x3': 'gp', 'x4': 'tp',
        'x5': 't0', 'x6': 't1', 'x7': 't2', 'x8': 's0/fp', 'x9': 's1',
        'x10': 'a0', 'x11': 'a1', 'x12': 'a2', 'x13': 'a3', 'x14': 'a4',
        'x15': 'a5', 'x16': 'a6', 'x17': 'a7', 'x18': 's2', 'x19': 's3',
        'x20': 's4', 'x21': 's5', 'x22': 's6', 'x23': 's7', 'x24': 's8',
        'x25': 's9', 'x26': 's10', 'x27': 's11', 'x28': 't3', 'x29': 't4',
        'x30': 't5', 'x31': 't6',
    }
    
    def __init__(self):
        # All registers except x0 (hardwired zero)
        self.all_regs = [f'x{i}' for i in range(1, 32)]
        
        # x2 (sp), x3 (gp), x10 (data pointer) reserved
        self.reserved = ['x2', 'x3', 'x10']
        
        # General purpose (excluding reserved)
        self.gp_regs = [r for r in self.all_regs if r not in self.reserved]
        
        # Temporary registers (caller-saved)
        self.temp_regs = ['x5', 'x6', 'x7', 'x28', 'x29', 'x30', 'x31']
        
        # Saved registers (callee-saved)
        self.saved_regs = ['x8', 'x9', 'x18', 'x19', 'x20', 'x21',
                           'x22', 'x23', 'x24', 'x25', 'x26', 'x27']
    
    def get_random(self, rng: random.Random, exclude: List[str] = None) -> str:
        """Get random general-purpose register"""
        pool = [r for r in self.gp_regs if r not in (exclude or [])]
        return rng.choice(pool)
    
    def get_temp(self, rng: random.Random) -> str:
        """Get random temporary register"""
        return rng.choice(self.temp_regs)


class InstructionGenerator:
    """Generates individual RISC-V instructions"""
    
    def __init__(self, config: GeneratorConfig, rng: random.Random):
        self.config = config
        self.rng = rng
        self.regs = RegisterFile()
    
    def _rand_imm(self, bits: int, signed: bool = True) -> int:
        """Generate random immediate value"""
        if signed:
            return self.rng.randint(-(1 << (bits-1)), (1 << (bits-1)) - 1)
        return self.rng.randint(0, (1 << bits) - 1)
    
    def _rand_shamt(self) -> int:
        """Generate random shift amount (0-31 for RV32)"""
        return self.rng.randint(0, 31)
    
    def gen_r_type(self) -> str:
        """Generate R-type instruction (register-register)"""
        ops = ['add', 'sub', 'sll', 'slt', 'sltu', 'xor', 'srl', 'sra', 'or', 'and']
        
        # Add M extension ops if available
        if self.config.has_extension(Extension.M):
            ops.extend(['mul', 'mulh', 'mulhsu', 'mulhu', 
                       'div', 'divu', 'rem', 'remu'])
        
        op = self.rng.choice(ops)
        rd = self.regs.get_random(self.rng)
        rs1 = self.regs.get_random(self.rng)
        rs2 = self.regs.get_random(self.rng)
        
        return f'    {op:<8} {rd}, {rs1}, {rs2}'
    
    def gen_i_type(self) -> str:
        """Generate I-type instruction (register-immediate)"""
        ops = ['addi', 'slti', 'sltiu', 'xori', 'ori', 'andi']
        op = self.rng.choice(ops)
        rd = self.regs.get_random(self.rng)
        rs1 = self.regs.get_random(self.rng)
        imm = self._rand_imm(12)
        
        return f'    {op:<8} {rd}, {rs1}, {imm}'
    
    def gen_shift_imm(self) -> str:
        """Generate shift immediate instruction"""
        ops = ['slli', 'srli', 'srai']
        op = self.rng.choice(ops)
        rd = self.regs.get_random(self.rng)
        rs1 = self.regs.get_random(self.rng)
        shamt = self._rand_shamt()
        
        return f'    {op:<8} {rd}, {rs1}, {shamt}'
    
    def gen_load(self) -> str:
        """Generate load instruction"""
        ops = ['lb', 'lh', 'lw', 'lbu', 'lhu']
        op = self.rng.choice(ops)
        rd = self.regs.get_random(self.rng)
        offset = self.rng.choice(self.config.safe_offsets)
        
        return f'    {op:<8} {rd}, {offset}(x10)  # data_ptr'
    
    def gen_store(self) -> str:
        """Generate store instruction"""
        ops = ['sb', 'sh', 'sw']
        op = self.rng.choice(ops)
        rs = self.regs.get_random(self.rng)
        offset = self.rng.choice(self.config.safe_offsets)
        
        return f'    {op:<8} {rs}, {offset}(x10)  # data_ptr'
    
    def gen_lui_auipc(self) -> str:
        """Generate LUI or AUIPC instruction"""
        op = self.rng.choice(['lui', 'auipc'])
        rd = self.regs.get_random(self.rng)
        # 20-bit unsigned immediate
        imm = self._rand_imm(20, signed=False) & 0xFFFFF
        
        return f'    {op:<8} {rd}, 0x{imm:05X}'
    
    def gen_branch(self, label: str) -> str:
        """Generate conditional branch instruction"""
        ops = ['beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu']
        op = self.rng.choice(ops)
        rs1 = self.regs.get_random(self.rng)
        rs2 = self.regs.get_random(self.rng)
        
        return f'    {op:<8} {rs1}, {rs2}, {label}'
    
    def gen_compressed(self) -> str:
        """Generate compressed (16-bit) instruction"""
        if not self.config.has_extension(Extension.C):
            return self.gen_i_type()
        
        # C ALU operations only support x8-x15 (s0-a5)
        c_alu_regs = [f'x{i}' for i in range(8, 16)]
        
        # Safe C extension instructions
        # Note: c.lui cannot use x0 or x2 (sp)
        # Note: c.and/or/xor/sub only work with x8-x15
        ops = [
            lambda: f'    c.addi   {self.regs.get_random(self.rng)}, {self.rng.randint(-32, 31)}',
            lambda: f'    c.li     {self.regs.get_random(self.rng)}, {self.rng.randint(-32, 31)}',
            lambda: f'    c.lui    {self.regs.get_random(self.rng, exclude=["x2"])}, {self.rng.randint(1, 31)}',
            lambda: f'    c.mv     {self.regs.get_random(self.rng)}, {self.regs.get_random(self.rng)}',
            lambda: f'    c.add    {self.regs.get_random(self.rng)}, {self.regs.get_random(self.rng)}',
            lambda: f'    c.and    {self.rng.choice(c_alu_regs)}, {self.rng.choice(c_alu_regs)}',
            lambda: f'    c.or     {self.rng.choice(c_alu_regs)}, {self.rng.choice(c_alu_regs)}',
            lambda: f'    c.xor    {self.rng.choice(c_alu_regs)}, {self.rng.choice(c_alu_regs)}',
            lambda: f'    c.sub    {self.rng.choice(c_alu_regs)}, {self.rng.choice(c_alu_regs)}',
        ]
        
        try:
            return self.rng.choice(ops)()
        except Exception as e:
            logger.warning(f'Compressed instruction generation failed: {e}')
            return '    nop'
    
    def generate(self) -> str:
        """Generate a random instruction"""
        # Build weighted choices
        choices: List[Tuple[int, Callable]] = []
        
        if self.config.weight_r_type > 0:
            choices.append((self.config.weight_r_type, self.gen_r_type))
        if self.config.weight_i_type > 0:
            choices.append((self.config.weight_i_type, self.gen_i_type))
        if self.config.weight_shift > 0:
            choices.append((self.config.weight_shift, self.gen_shift_imm))
        if self.config.weight_load > 0:
            choices.append((self.config.weight_load, self.gen_load))
        if self.config.weight_store > 0:
            choices.append((self.config.weight_store, self.gen_store))
        if self.config.weight_lui_auipc > 0:
            choices.append((self.config.weight_lui_auipc, self.gen_lui_auipc))
        if self.config.weight_compressed > 0:
            choices.append((self.config.weight_compressed, self.gen_compressed))
        
        if not choices:
            logger.error('No instruction types enabled!')
            return '    nop'
        
        # Weighted random selection
        total_weight = sum(w for w, _ in choices)
        r = self.rng.randint(0, total_weight - 1)
        cumulative = 0
        
        for weight, gen_func in choices:
            cumulative += weight
            if r < cumulative:
                try:
                    return gen_func()
                except Exception as e:
                    logger.warning(f'Instruction generation failed: {e}')
                    return '    nop'
        
        return '    nop'


class TortureTestGenerator:
    """Main torture test generator"""
    
    def __init__(self, config: GeneratorConfig):
        self.config = config
        self.rng = random.Random(config.seed)
        self.insn_gen = InstructionGenerator(config, self.rng)
        self.label_counter = 0
    
    def _generate_header(self) -> List[str]:
        """Generate test file header"""
        return [
            f'/* ============================================== */',
            f'/* RISC-V Torture Test - Auto-generated         */',
            f'/* ============================================== */',
            f'/* Seed:         {self.config.seed:10d}             */',
            f'/* Instructions: {self.config.max_instructions:10d}             */',
            f'/* Architecture: {self.config.march:10s}             */',
            f'/* ============================================== */',
            '',
        ]
    
    def _generate_init(self) -> List[str]:
        """Generate initialization code"""
        lines = [
            '    .section .text',
            '    .global test_start',
            '',
            'test_start:',
            '    # Initialize data pointer',
            '    la      x10, test_data',
            '',
            '    # Initialize registers with pseudo-random values',
        ]
        
        # Initialize registers with known values
        for i in range(1, min(10, 32)):
            if f'x{i}' not in self.insn_gen.regs.reserved:
                val = self.rng.randint(0, 0xFFFFFFFF)
                lines.append(f'    li      x{i}, 0x{val:08X}')
        
        lines.extend(['', '    # Begin random instruction sequence', ''])
        return lines
    
    def _generate_body(self) -> List[str]:
        """Generate main instruction sequence"""
        lines = []
        insn_count = 0
        
        while insn_count < self.config.max_instructions:
            # Occasionally insert a forward branch
            if self.rng.random() < self.config.branch_probability:
                skip_count = self.rng.randint(2, self.config.max_branch_distance)
                label = f'L{self.label_counter}'
                self.label_counter += 1
                
                # Generate branch instruction
                lines.append(self.insn_gen.gen_branch(label))
                
                # Generate skipped instructions
                for _ in range(min(skip_count, self.config.max_instructions - insn_count - 1)):
                    lines.append('    nop      # skipped')
                    insn_count += 1
                
                lines.append(f'{label}:')
            else:
                # Generate regular instruction
                insn = self.insn_gen.generate()
                lines.append(insn)
            
            insn_count += 1
        
        return lines
    
    def _generate_footer(self) -> List[str]:
        """Generate test footer (data section)"""
        return [
            '',
            '    # Test passed - jump to pass handler',
            '    j       _pass',
            '',
            '    .section .data',
            '    .align 4',
            'test_data:',
            f'    .space  {self.config.data_region_size}',
            '',
        ]
    
    def generate(self) -> str:
        """Generate complete torture test"""
        logger.info(f'Generating torture test (seed={self.config.seed})')
        
        lines = []
        lines.extend(self._generate_header())
        lines.extend(self._generate_init())
        lines.extend(self._generate_body())
        lines.extend(self._generate_footer())
        
        code = '\n'.join(lines)
        logger.info(f'Generated {len(lines)} lines, {self.label_counter} branch labels')
        
        return code


def main():
    parser = argparse.ArgumentParser(
        description='RISC-V Torture Test Generator',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  %(prog)s --seed 42 --output test.S
  %(prog)s --seed 123 --max-insns 2000 --march rv32im --output test.S
  %(prog)s --seed 456 --verbose --output test.S
        '''
    )
    
    parser.add_argument('--seed', type=int, required=True,
                        help='Random seed for reproducibility')
    parser.add_argument('--output', type=str, required=True,
                        help='Output assembly file path')
    parser.add_argument('--max-insns', type=int, default=1000,
                        help='Maximum number of instructions (default: 1000)')
    parser.add_argument('--march', type=str, default='rv32imc',
                        help='Architecture string (default: rv32imc)')
    parser.add_argument('--data-size', type=int, default=256,
                        help='Data region size in bytes (default: 256)')
    parser.add_argument('--branch-prob', type=float, default=0.05,
                        help='Branch insertion probability (default: 0.05)')
    parser.add_argument('--verbose', action='store_true',
                        help='Enable verbose logging')
    
    args = parser.parse_args()
    
    if args.verbose:
        logger.setLevel(logging.DEBUG)
    
    # Validate arguments
    if args.seed < 0:
        logger.error('Seed must be non-negative')
        sys.exit(1)
    
    if args.max_insns < 10 or args.max_insns > 100000:
        logger.error('Max instructions must be between 10 and 100000')
        sys.exit(1)
    
    if not (0.0 <= args.branch_prob <= 1.0):
        logger.error('Branch probability must be between 0.0 and 1.0')
        sys.exit(1)
    
    # Create configuration
    config = GeneratorConfig(
        seed=args.seed,
        max_instructions=args.max_insns,
        march=args.march,
        data_region_size=args.data_size,
        branch_probability=args.branch_prob,
    )
    
    try:
        # Generate test
        generator = TortureTestGenerator(config)
        code = generator.generate()
        
        # Write output
        with open(args.output, 'w') as f:
            f.write(code)
        
        logger.info(f'Successfully wrote output to: {args.output}')
        
    except IOError as e:
        logger.error(f'Failed to write output file: {e}')
        sys.exit(1)
    except Exception as e:
        logger.error(f'Unexpected error: {e}')
        sys.exit(1)


if __name__ == '__main__':
    main()
