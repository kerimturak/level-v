#!/usr/bin/env python3
# ============================================================
# RISC-V Torture Test Generator for Ceres-V
# ============================================================
# Generates random valid instruction sequences for stress testing

import argparse
import random
import sys

class TortureGenerator:
    """Generates random RISC-V instruction sequences"""
    
    def __init__(self, seed, march='rv32imc'):
        self.rng = random.Random(seed)
        self.march = march
        self.regs = [f'x{i}' for i in range(1, 32)]  # Skip x0
        # x10 is reserved for data pointer, exclude from general use
        self.regs_no_dataptr = [f'x{i}' for i in range(1, 32) if i != 10]
        self.temp_regs = ['x5', 'x6', 'x7', 'x28', 'x29', 'x30', 'x31']
        self.saved_regs = ['x8', 'x9', 'x18', 'x19', 'x20', 'x21', 'x22', 'x23', 'x24', 'x25', 'x26', 'x27']
        
    def rand_reg(self):
        """Return a random register excluding x10 (data pointer)"""
        return self.rng.choice(self.regs_no_dataptr)
    
    def rand_reg_no_sp(self):
        """Return a random register excluding x2 (sp) and x10 for c.lui"""
        regs_no_sp = [f'x{i}' for i in range(1, 32) if i not in (2, 10)]
        return self.rng.choice(regs_no_sp)
    
    def rand_temp(self):
        return self.rng.choice(self.temp_regs)
    
    def rand_imm(self, bits=12, signed=True):
        if signed:
            return self.rng.randint(-(1 << (bits-1)), (1 << (bits-1)) - 1)
        return self.rng.randint(0, (1 << bits) - 1)
    
    def rand_shamt(self):
        return self.rng.randint(0, 31)
    
    def gen_r_type(self):
        """Generate R-type instruction"""
        ops = ['add', 'sub', 'sll', 'slt', 'sltu', 'xor', 'srl', 'sra', 'or', 'and']
        if 'm' in self.march:
            ops.extend(['mul', 'mulh', 'mulhsu', 'mulhu', 'div', 'divu', 'rem', 'remu'])
        
        op = self.rng.choice(ops)
        rd = self.rand_reg()
        rs1 = self.rand_reg()
        rs2 = self.rand_reg()
        return f'    {op} {rd}, {rs1}, {rs2}'
    
    def gen_i_type(self):
        """Generate I-type instruction"""
        ops = ['addi', 'slti', 'sltiu', 'xori', 'ori', 'andi']
        op = self.rng.choice(ops)
        rd = self.rand_reg()
        rs1 = self.rand_reg()
        imm = self.rand_imm()
        return f'    {op} {rd}, {rs1}, {imm}'
    
    def gen_shift_imm(self):
        """Generate shift immediate instruction"""
        ops = ['slli', 'srli', 'srai']
        op = self.rng.choice(ops)
        rd = self.rand_reg()
        rs1 = self.rand_reg()
        shamt = self.rand_shamt()
        return f'    {op} {rd}, {rs1}, {shamt}'
    
    def gen_load(self):
        """Generate load instruction"""
        ops = ['lb', 'lh', 'lw', 'lbu', 'lhu']
        op = self.rng.choice(ops)
        rd = self.rand_reg()
        # Use safe memory offset
        offset = self.rng.choice([0, 4, 8, 12, 16, 20, 24, 28])
        return f'    {op} {rd}, {offset}(x10)  /* x10 = data pointer */'
    
    def gen_store(self):
        """Generate store instruction"""
        ops = ['sb', 'sh', 'sw']
        op = self.rng.choice(ops)
        rs = self.rand_reg()
        offset = self.rng.choice([0, 4, 8, 12, 16, 20, 24, 28])
        return f'    {op} {rs}, {offset}(x10)  /* x10 = data pointer */'
    
    def gen_lui_auipc(self):
        """Generate LUI or AUIPC"""
        op = self.rng.choice(['lui', 'auipc'])
        rd = self.rand_reg()
        imm = self.rand_imm(20, signed=False) & 0xFFFFF
        return f'    {op} {rd}, {imm}'
    
    def gen_jal(self, label):
        """Generate JAL to forward label"""
        rd = self.rng.choice(['x0', 'x1'])
        return f'    jal {rd}, {label}'
    
    def gen_compressed(self):
        """Generate compressed instruction"""
        if 'c' not in self.march:
            return self.gen_i_type()
        
        # C extension instructions (RV32C subset)
        # Note: c.lui cannot use x0 or x2 (sp), use rand_reg_no_sp
        # Note: c.addi16sp is a different instruction for sp
        choices = [
            lambda: f'    c.addi {self.rand_reg()}, {self.rng.randint(-32, 31)}',
            lambda: f'    c.li {self.rand_reg()}, {self.rng.randint(-32, 31)}',
            lambda: f'    c.lui {self.rand_reg_no_sp()}, {self.rng.randint(1, 31)}',
            lambda: f'    c.mv {self.rand_reg()}, {self.rand_reg()}',
            lambda: f'    c.add {self.rand_reg()}, {self.rand_reg()}',
        ]
        return self.rng.choice(choices)()
    
    def gen_instruction(self):
        """Generate a random instruction"""
        weights = [
            (30, self.gen_r_type),
            (25, self.gen_i_type),
            (10, self.gen_shift_imm),
            (10, self.gen_load),
            (10, self.gen_store),
            (5, self.gen_lui_auipc),
            (10, self.gen_compressed),
        ]
        
        total = sum(w for w, _ in weights)
        r = self.rng.randint(0, total - 1)
        cumulative = 0
        for weight, gen in weights:
            cumulative += weight
            if r < cumulative:
                return gen()
        return self.gen_i_type()
    
    def generate(self, max_insns):
        """Generate a complete torture test"""
        lines = []
        lines.append(f'/* Auto-generated torture test */')
        lines.append(f'/* Seed: {self.rng.getstate()[1][0]} */')
        lines.append(f'/* Architecture: {self.march} */')
        lines.append('')
        lines.append('    .section .text')
        lines.append('    .global test_start')
        lines.append('')
        lines.append('test_start:')
        lines.append('    /* Initialize data pointer */')
        lines.append('    la x10, test_data')
        lines.append('')
        lines.append('    /* Initialize some registers with known values */')
        
        # Initialize some registers
        for i in range(1, 10):
            val = self.rng.randint(0, 0xFFFFFFFF)
            lines.append(f'    li x{i+10}, 0x{val:08X}')
        
        lines.append('')
        lines.append('    /* Random instruction sequence */')
        
        # Generate random instructions with occasional forward jumps
        label_count = 0
        i = 0
        while i < max_insns:
            # Occasionally insert a forward jump
            if self.rng.random() < 0.02:
                skip_count = self.rng.randint(2, 5)
                label = f'L{label_count}'
                lines.append(f'    j {label}')
                for _ in range(skip_count):
                    lines.append('    nop  /* skipped */')
                    i += 1
                lines.append(f'{label}:')
                label_count += 1
            else:
                try:
                    insn = self.gen_instruction()
                    lines.append(insn)
                except:
                    lines.append('    nop')
            i += 1
        
        lines.append('')
        lines.append('    /* Test passed */')
        lines.append('    j _pass')
        lines.append('')
        lines.append('    .section .data')
        lines.append('    .align 4')
        lines.append('test_data:')
        lines.append('    .space 256')
        
        return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description='RISC-V Torture Test Generator')
    parser.add_argument('--seed', type=int, default=0, help='Random seed')
    parser.add_argument('--max-insns', type=int, default=1000, help='Max instructions')
    parser.add_argument('--march', type=str, default='rv32imc', help='Architecture')
    parser.add_argument('--output', type=str, required=True, help='Output file')
    args = parser.parse_args()
    
    gen = TortureGenerator(args.seed, args.march)
    code = gen.generate(args.max_insns)
    
    with open(args.output, 'w') as f:
        f.write(code)
    
    print(f'Generated: {args.output}')

if __name__ == '__main__':
    main()
