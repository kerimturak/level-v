#!/usr/bin/env python3
# ============================================================
# Simple RISC-V DV Test Generator (Fallback)
# Generates random instruction sequences for testing
# ============================================================

import argparse
import random
import json
from pathlib import Path

# Default instruction count
DEFAULT_INSTR_CNT = 500

# Register names (avoid x0, sp, gp, tp)
WORK_REGS = [f'x{i}' for i in range(5, 32)]
TEMP_REGS = ['t0', 't1', 't2', 't3', 't4', 't5', 't6']
SAVED_REGS = ['s0', 's1', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11']
ARG_REGS = ['a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7']


class RiscvTestGenerator:
    def __init__(self, seed: int, instr_cnt: int = DEFAULT_INSTR_CNT):
        self.rng = random.Random(seed)
        self.instr_cnt = instr_cnt
        self.label_counter = 0
        self.data_offset = 0
        
    def rand_reg(self) -> str:
        return self.rng.choice(WORK_REGS)
    
    def rand_imm12(self) -> int:
        return self.rng.randint(-2048, 2047)
    
    def rand_imm5(self) -> int:
        return self.rng.randint(0, 31)
    
    def rand_uimm(self) -> int:
        return self.rng.randint(0, 0xFFFFF)
    
    def new_label(self, prefix: str = 'L') -> str:
        self.label_counter += 1
        return f'{prefix}_{self.label_counter}'
    
    def gen_r_type(self) -> str:
        """Generate R-type instruction"""
        ops = ['add', 'sub', 'sll', 'slt', 'sltu', 'xor', 'srl', 'sra', 'or', 'and']
        op = self.rng.choice(ops)
        rd, rs1, rs2 = self.rand_reg(), self.rand_reg(), self.rand_reg()
        return f'    {op} {rd}, {rs1}, {rs2}'
    
    def gen_i_type(self) -> str:
        """Generate I-type instruction"""
        ops = ['addi', 'slti', 'sltiu', 'xori', 'ori', 'andi']
        op = self.rng.choice(ops)
        rd, rs1 = self.rand_reg(), self.rand_reg()
        imm = self.rand_imm12()
        return f'    {op} {rd}, {rs1}, {imm}'
    
    def gen_shift_imm(self) -> str:
        """Generate shift with immediate"""
        ops = ['slli', 'srli', 'srai']
        op = self.rng.choice(ops)
        rd, rs1 = self.rand_reg(), self.rand_reg()
        shamt = self.rand_imm5()
        return f'    {op} {rd}, {rs1}, {shamt}'
    
    def gen_lui_auipc(self) -> str:
        """Generate LUI or AUIPC"""
        op = self.rng.choice(['lui', 'auipc'])
        rd = self.rand_reg()
        imm = self.rand_uimm()
        return f'    {op} {rd}, 0x{imm:05X}'
    
    def gen_load(self) -> str:
        """Generate load instruction"""
        ops = ['lw', 'lh', 'lhu', 'lb', 'lbu']
        op = self.rng.choice(ops)
        rd = self.rand_reg()
        # Use aligned offset
        offset = (self.rng.randint(0, 15) * 4)
        return f'    {op} {rd}, {offset}(x20)'  # x20 = data pointer
    
    def gen_store(self) -> str:
        """Generate store instruction"""
        ops = ['sw', 'sh', 'sb']
        op = self.rng.choice(ops)
        rs2 = self.rand_reg()
        offset = (self.rng.randint(0, 15) * 4)
        return f'    {op} {rs2}, {offset}(x20)'
    
    def gen_branch_block(self) -> list:
        """Generate a branch with forward jump"""
        lines = []
        bops = ['beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu']
        op = self.rng.choice(bops)
        rs1, rs2 = self.rand_reg(), self.rand_reg()
        label = self.new_label('branch')
        
        lines.append(f'    {op} {rs1}, {rs2}, {label}')
        # Add some instructions in fall-through path
        for _ in range(self.rng.randint(2, 5)):
            lines.append(self.gen_r_type())
        lines.append(f'{label}:')
        
        return lines
    
    def gen_jump_block(self) -> list:
        """Generate JAL/JALR sequence"""
        lines = []
        label = self.new_label('func')
        ret_label = self.new_label('ret')
        
        lines.append(f'    jal ra, {label}')
        lines.append(f'    j {ret_label}')
        lines.append(f'{label}:')
        # Function body
        for _ in range(self.rng.randint(3, 8)):
            lines.append(self.gen_r_type())
        lines.append(f'    jalr x0, ra, 0')
        lines.append(f'{ret_label}:')
        
        return lines
    
    def gen_loop_block(self) -> list:
        """Generate a loop structure"""
        lines = []
        loop_label = self.new_label('loop')
        exit_label = self.new_label('exit')
        
        counter_reg = self.rand_reg()
        limit = self.rng.randint(3, 10)
        
        lines.append(f'    li {counter_reg}, {limit}')
        lines.append(f'{loop_label}:')
        
        # Loop body
        for _ in range(self.rng.randint(3, 8)):
            lines.append(self.gen_r_type())
        
        lines.append(f'    addi {counter_reg}, {counter_reg}, -1')
        lines.append(f'    bnez {counter_reg}, {loop_label}')
        lines.append(f'{exit_label}:')
        
        return lines
    
    def gen_mul_div(self) -> str:
        """Generate M extension instructions"""
        ops = ['mul', 'mulh', 'mulhsu', 'mulhu', 'div', 'divu', 'rem', 'remu']
        op = self.rng.choice(ops)
        rd, rs1, rs2 = self.rand_reg(), self.rand_reg(), self.rand_reg()
        return f'    {op} {rd}, {rs1}, {rs2}'
    
    def gen_compressed(self) -> str:
        """Generate C extension instructions (will be compressed by assembler)"""
        # Generate instructions that can be compressed
        choices = [
            lambda: f'    addi {self.rng.choice(SAVED_REGS)}, {self.rng.choice(SAVED_REGS)}, {self.rng.randint(-32, 31)}',
            lambda: f'    add {self.rand_reg()}, {self.rand_reg()}, {self.rand_reg()}',
            lambda: f'    mv {self.rand_reg()}, {self.rand_reg()}',
            lambda: f'    li {self.rand_reg()}, {self.rng.randint(-32, 31)}',
        ]
        return self.rng.choice(choices)()
    
    def generate_instructions(self, test_type: str) -> list:
        """Generate random instruction sequence based on test type"""
        lines = []
        
        # Distribution based on test type
        if 'arithmetic' in test_type:
            weights = {'r': 40, 'i': 30, 'shift': 15, 'lui': 10, 'mul': 5}
        elif 'jump' in test_type:
            weights = {'r': 20, 'branch': 30, 'jump': 30, 'i': 20}
        elif 'loop' in test_type:
            weights = {'r': 25, 'loop': 40, 'i': 20, 'branch': 15}
        elif 'rand' in test_type:
            weights = {'r': 25, 'i': 20, 'shift': 10, 'lui': 5, 'load': 10, 
                      'store': 10, 'branch': 10, 'mul': 5, 'comp': 5}
        else:
            weights = {'r': 30, 'i': 25, 'shift': 10, 'lui': 5, 'load': 10, 
                      'store': 10, 'branch': 5, 'mul': 5}
        
        instr_generated = 0
        while instr_generated < self.instr_cnt:
            choice = self.rng.choices(list(weights.keys()), list(weights.values()))[0]
            
            if choice == 'r':
                lines.append(self.gen_r_type())
                instr_generated += 1
            elif choice == 'i':
                lines.append(self.gen_i_type())
                instr_generated += 1
            elif choice == 'shift':
                lines.append(self.gen_shift_imm())
                instr_generated += 1
            elif choice == 'lui':
                lines.append(self.gen_lui_auipc())
                instr_generated += 1
            elif choice == 'load':
                lines.append(self.gen_load())
                instr_generated += 1
            elif choice == 'store':
                lines.append(self.gen_store())
                instr_generated += 1
            elif choice == 'branch':
                block = self.gen_branch_block()
                lines.extend(block)
                instr_generated += len([l for l in block if not l.strip().endswith(':')])
            elif choice == 'jump':
                block = self.gen_jump_block()
                lines.extend(block)
                instr_generated += len([l for l in block if not l.strip().endswith(':')])
            elif choice == 'loop':
                block = self.gen_loop_block()
                lines.extend(block)
                instr_generated += len([l for l in block if not l.strip().endswith(':')])
            elif choice == 'mul':
                lines.append(self.gen_mul_div())
                instr_generated += 1
            elif choice == 'comp':
                lines.append(self.gen_compressed())
                instr_generated += 1
        
        return lines


def generate_test(test_name: str, idx: int, seed: int, output_path: str, 
                  instr_cnt: int = DEFAULT_INSTR_CNT):
    """Generate a test assembly file"""
    
    gen = RiscvTestGenerator(seed + idx * 1000, instr_cnt)
    
    # Generate random initial values for registers
    init_vals = [gen.rng.randint(1, 0x7FFFFFFF) for _ in range(16)]
    
    # Generate instruction sequence
    instructions = gen.generate_instructions(test_name)
    instr_block = '\n'.join(instructions)
    
    code = f'''/* ============================================================
 * Generated test: {test_name}
 * Iteration: {idx}
 * Seed: {seed + idx * 1000}
 * Instruction count: ~{instr_cnt}
 * ============================================================ */

    .section .text.init
    .global _start
    .global _pass
    .global _fail

_start:
    /* Initialize stack pointer */
    la sp, _stack_top
    
    /* Initialize data pointer for load/store */
    la x20, data_section
    
    /* Initialize work registers with random values */
    li x5,  0x{init_vals[0]:08X}
    li x6,  0x{init_vals[1]:08X}
    li x7,  0x{init_vals[2]:08X}
    li x8,  0x{init_vals[3]:08X}
    li x9,  0x{init_vals[4]:08X}
    li x10, 0x{init_vals[5]:08X}
    li x11, 0x{init_vals[6]:08X}
    li x12, 0x{init_vals[7]:08X}
    li x13, 0x{init_vals[8]:08X}
    li x14, 0x{init_vals[9]:08X}
    li x15, 0x{init_vals[10]:08X}
    li x16, 0x{init_vals[11]:08X}
    li x17, 0x{init_vals[12]:08X}
    li x18, 0x{init_vals[13]:08X}
    li x19, 0x{init_vals[14]:08X}
    li x21, 0x{init_vals[15]:08X}
    
    /* ============================================================
     * Test instruction sequence
     * ============================================================ */
    
{instr_block}
    
    /* ============================================================
     * Test completed - jump to pass
     * ============================================================ */
    j _pass

_pass:
    /* Signal pass via memory-mapped register */
    li a0, 0
    li t0, 0x1FFFFFFC
    sw a0, 0(t0)
1:  j 1b

_fail:
    /* Signal fail via memory-mapped register */
    li a0, 1
    li t0, 0x1FFFFFFC
    sw a0, 0(t0)
1:  j 1b

    /* ============================================================
     * Data section
     * ============================================================ */
    .section .data
    .align 4
data_section:
    .fill 256, 4, 0xDEADBEEF
    
    /* ============================================================
     * BSS and stack
     * ============================================================ */
    .section .bss
    .align 4
    .space 8192
_stack_top:
'''
    
    with open(output_path, 'w') as f:
        f.write(code)
    
    actual_instr = len([l for l in instructions if l.strip() and not l.strip().endswith(':')])
    print(f'Generated: {output_path} (~{actual_instr} instructions)')


def load_config(config_path: str) -> dict:
    """Load configuration from JSON file"""
    try:
        with open(config_path, 'r') as f:
            return json.load(f)
    except:
        return {}


def main():
    parser = argparse.ArgumentParser(
        description='RISC-V DV Fallback Test Generator',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('--test', type=str, required=True, help='Test name')
    parser.add_argument('--idx', type=int, required=True, help='Iteration index')
    parser.add_argument('--seed', type=int, default=0, help='Random seed')
    parser.add_argument('--output', type=str, required=True, help='Output file')
    parser.add_argument('--instr-cnt', type=int, default=DEFAULT_INSTR_CNT, 
                        help=f'Number of instructions (default: {DEFAULT_INSTR_CNT})')
    parser.add_argument('--config', type=str, help='JSON config file')
    
    args = parser.parse_args()
    
    # Try to get instr_cnt from config if provided
    instr_cnt = args.instr_cnt
    if args.config:
        config = load_config(args.config)
        instr_cnt = config.get('generator', {}).get('instr_cnt', instr_cnt)
    
    generate_test(args.test, args.idx, args.seed, args.output, instr_cnt)


if __name__ == '__main__':
    main()
