#!/usr/bin/env python3
"""
Branch Predictor Statistics Comparison Tool
Compares old and new bp_stats.log files to measure improvement
"""

import os
import re
import sys
from pathlib import Path

def parse_bp_stats(filepath):
    """Parse bp_stats.log and extract key metrics"""
    stats = {
        'total': 0,
        'correct': 0,
        'mispred': 0,
        'cond_total': 0,
        'cond_correct': 0,
        'cond_mispred': 0,
        'jal_total': 0,
        'jal_correct': 0,
        'jalr_total': 0,
        'jalr_correct': 0,
    }
    
    if not os.path.exists(filepath):
        return None
    
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Parse Total Control Transfers
    m = re.search(r'Total Control Transfers\s*:\s*(\d+)', content)
    if m: stats['total'] = int(m.group(1))
    
    m = re.search(r'Correct Predictions\s*:\s*(\d+)', content)
    if m: stats['correct'] = int(m.group(1))
    
    m = re.search(r'Mispredictions\s*:\s*(\d+)', content)
    if m: stats['mispred'] = int(m.group(1))
    
    # Parse Conditional Branch section
    lines = content.split('\n')
    in_cond = False
    for i, line in enumerate(lines):
        if 'Conditional Branch' in line:
            in_cond = True
            continue
        if in_cond:
            if 'Total' in line and ':' in line:
                m = re.search(r':\s*(\d+)', line)
                if m: stats['cond_total'] = int(m.group(1))
            elif 'Correct' in line and ':' in line:
                m = re.search(r':\s*(\d+)', line)
                if m: stats['cond_correct'] = int(m.group(1))
            elif 'Mispredicted' in line and ':' in line:
                m = re.search(r':\s*(\d+)', line)
                if m: stats['cond_mispred'] = int(m.group(1))
                in_cond = False
    
    # Parse JAL
    in_jal = False
    for line in lines:
        if 'JAL (Direct Jump)' in line:
            in_jal = True
            continue
        if in_jal:
            if 'Total' in line and ':' in line:
                m = re.search(r':\s*(\d+)', line)
                if m: stats['jal_total'] = int(m.group(1))
            elif 'Correct' in line and ':' in line:
                m = re.search(r':\s*(\d+)', line)
                if m: stats['jal_correct'] = int(m.group(1))
                in_jal = False
    
    return stats

def main():
    old_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("build/results/logs/verilator")
    new_dir = Path(sys.argv[2]) if len(sys.argv) > 2 else Path("results/logs/verilator")
    
    print("=" * 70)
    print("         Branch Predictor Comparison: OLD vs NEW")
    print("=" * 70)
    print(f"Old: {old_dir}")
    print(f"New: {new_dir}")
    print("=" * 70)
    
    # Collect all test names with bp_stats
    tests = set()
    for d in [old_dir, new_dir]:
        if d.exists():
            for test_dir in d.iterdir():
                if test_dir.is_dir():
                    bp_file = test_dir / "bp_stats.log"
                    if bp_file.exists():
                        tests.add(test_dir.name)
    
    # Filter for branch-related tests
    branch_tests = [t for t in sorted(tests) if any(x in t.lower() for x in 
                   ['beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'jal', 'jalr', 
                    'cbeqz', 'cbnez', 'cj-', 'cjal', 'cjr'])]
    
    if not branch_tests:
        print("No branch tests found!")
        return
    
    old_total_cond = 0
    old_correct_cond = 0
    new_total_cond = 0
    new_correct_cond = 0
    
    print(f"\n{'Test':<30} {'Old Cond%':>12} {'New Cond%':>12} {'Δ':>8}")
    print("-" * 70)
    
    for test in branch_tests:
        old_stats = parse_bp_stats(old_dir / test / "bp_stats.log")
        new_stats = parse_bp_stats(new_dir / test / "bp_stats.log")
        
        old_pct = "-"
        new_pct = "-"
        delta = ""
        
        if old_stats and old_stats['cond_total'] > 0:
            old_pct = f"{100*old_stats['cond_correct']/old_stats['cond_total']:.1f}%"
            old_total_cond += old_stats['cond_total']
            old_correct_cond += old_stats['cond_correct']
        
        if new_stats and new_stats['cond_total'] > 0:
            new_pct = f"{100*new_stats['cond_correct']/new_stats['cond_total']:.1f}%"
            new_total_cond += new_stats['cond_total']
            new_correct_cond += new_stats['cond_correct']
        
        if old_stats and new_stats and old_stats['cond_total'] > 0 and new_stats['cond_total'] > 0:
            old_acc = 100*old_stats['cond_correct']/old_stats['cond_total']
            new_acc = 100*new_stats['cond_correct']/new_stats['cond_total']
            diff = new_acc - old_acc
            delta = f"+{diff:.1f}" if diff > 0 else f"{diff:.1f}"
        
        print(f"{test:<30} {old_pct:>12} {new_pct:>12} {delta:>8}")
    
    print("-" * 70)
    
    # Overall summary
    old_overall = 100*old_correct_cond/old_total_cond if old_total_cond > 0 else 0
    new_overall = 100*new_correct_cond/new_total_cond if new_total_cond > 0 else 0
    diff = new_overall - old_overall
    
    print(f"\n{'OVERALL (Conditional)':<30} {old_overall:>11.1f}% {new_overall:>11.1f}% {'+' if diff > 0 else ''}{diff:.1f}%")
    print(f"{'Total Branches':<30} {old_total_cond:>12} {new_total_cond:>12}")
    print(f"{'Correct Predictions':<30} {old_correct_cond:>12} {new_correct_cond:>12}")
    print("=" * 70)

if __name__ == "__main__":
    main()
