#!/usr/bin/env python3
"""
RISC-V DV Configuration Reader
Reads test configuration from JSON file and outputs for Makefile consumption
"""

import argparse
import json
import sys
from pathlib import Path


def load_config(config_path: Path) -> dict:
    """Load and return the JSON configuration."""
    if not config_path.exists():
        print(f"Error: Config file not found: {config_path}", file=sys.stderr)
        sys.exit(1)
    
    with open(config_path, 'r') as f:
        return json.load(f)


def get_enabled_tests(config: dict) -> list:
    """Get list of enabled tests."""
    tests = config.get('tests', [])
    return [t for t in tests if t.get('enabled', True)]


def cmd_list_tests(config: dict, args) -> None:
    """List all enabled tests."""
    tests = get_enabled_tests(config)
    for test in tests:
        print(test['name'])


def cmd_get_iterations(config: dict, args) -> None:
    """Get iterations for a specific test."""
    tests = get_enabled_tests(config)
    for test in tests:
        if test['name'] == args.test:
            print(test.get('iterations', 1))
            return
    # Default if not found
    print(1)


def cmd_get_test_config(config: dict, args) -> None:
    """Get full configuration for a test as KEY=VALUE pairs."""
    tests = get_enabled_tests(config)
    gen = config.get('generator', {})
    
    for test in tests:
        if test['name'] == args.test:
            print(f"TEST_NAME={test['name']}")
            print(f"TEST_ITER={test.get('iterations', 1)}")
            print(f"TEST_ISA={gen.get('isa', 'rv32imc')}")
            print(f"TEST_MABI={gen.get('mabi', 'ilp32')}")
            print(f"TEST_MMODE={1 if gen.get('mmode', True) else 0}")
            print(f"TEST_SEED={gen.get('seed', 0)}")
            return
    
    print(f"Error: Test not found: {args.test}", file=sys.stderr)
    sys.exit(1)


def cmd_get_all_tests(config: dict, args) -> None:
    """Get all enabled tests with their iterations as 'name:iterations' pairs."""
    tests = get_enabled_tests(config)
    for test in tests:
        name = test['name']
        iters = test.get('iterations', 1)
        print(f"{name}:{iters}")


def cmd_get_generator(config: dict, args) -> None:
    """Get generator configuration."""
    gen = config.get('generator', {})
    print(f"ISA={gen.get('isa', 'rv32imc')}")
    print(f"MABI={gen.get('mabi', 'ilp32')}")
    print(f"MMODE={1 if gen.get('mmode', True) else 0}")
    print(f"SEED={gen.get('seed', 0)}")


def cmd_get_value(config: dict, args) -> None:
    """Get a specific value from config using dot notation (e.g., generator.isa)."""
    keys = args.key.split('.')
    value = config
    
    try:
        for key in keys:
            if isinstance(value, list):
                key = int(key)
            value = value[key]
        
        if isinstance(value, bool):
            print("true" if value else "false")
        elif isinstance(value, (dict, list)):
            print(json.dumps(value))
        else:
            print(value)
    except (KeyError, IndexError, TypeError):
        if args.default is not None:
            print(args.default)
        else:
            print(f"Error: Key not found: {args.key}", file=sys.stderr)
            sys.exit(1)


def cmd_summary(config: dict, args) -> None:
    """Print a summary of the configuration."""
    gen = config.get('generator', {})
    tests = get_enabled_tests(config)
    
    print("=" * 50)
    print("RISC-V DV Configuration Summary")
    print("=" * 50)
    print(f"ISA:  {gen.get('isa', 'rv32imc')}")
    print(f"ABI:  {gen.get('mabi', 'ilp32')}")
    print(f"Seed: {gen.get('seed', 0)}")
    print()
    print("Enabled Tests:")
    print("-" * 50)
    total_iters = 0
    for test in tests:
        iters = test.get('iterations', 1)
        total_iters += iters
        desc = test.get('description', '')
        print(f"  {test['name']}: {iters} iterations")
        if desc:
            print(f"    └─ {desc}")
    print("-" * 50)
    print(f"Total: {len(tests)} tests, {total_iters} iterations")


def main():
    parser = argparse.ArgumentParser(
        description='RISC-V DV Configuration Reader',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --config riscv-dv.json list-tests
  %(prog)s --config riscv-dv.json get-iterations --test riscv_arithmetic_basic_test
  %(prog)s --config riscv-dv.json get-all-tests
  %(prog)s --config riscv-dv.json get-value --key generator.isa
  %(prog)s --config riscv-dv.json summary
        """
    )
    
    parser.add_argument(
        '--config', '-c',
        type=Path,
        required=True,
        help='Path to the JSON configuration file'
    )
    
    subparsers = parser.add_subparsers(dest='command', help='Commands')
    
    # list-tests
    subparsers.add_parser('list-tests', help='List all enabled tests')
    
    # get-iterations
    p_iter = subparsers.add_parser('get-iterations', help='Get iterations for a test')
    p_iter.add_argument('--test', '-t', required=True, help='Test name')
    
    # get-test-config
    p_test = subparsers.add_parser('get-test-config', help='Get full test configuration')
    p_test.add_argument('--test', '-t', required=True, help='Test name')
    
    # get-all-tests
    subparsers.add_parser('get-all-tests', help='Get all tests with iterations')
    
    # get-generator
    subparsers.add_parser('get-generator', help='Get generator configuration')
    
    # get-value
    p_val = subparsers.add_parser('get-value', help='Get a specific config value')
    p_val.add_argument('--key', '-k', required=True, help='Key in dot notation')
    p_val.add_argument('--default', '-d', help='Default value if key not found')
    
    # summary
    subparsers.add_parser('summary', help='Print configuration summary')
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        sys.exit(1)
    
    config = load_config(args.config)
    
    commands = {
        'list-tests': cmd_list_tests,
        'get-iterations': cmd_get_iterations,
        'get-test-config': cmd_get_test_config,
        'get-all-tests': cmd_get_all_tests,
        'get-generator': cmd_get_generator,
        'get-value': cmd_get_value,
        'summary': cmd_summary,
    }
    
    commands[args.command](config, args)


if __name__ == '__main__':
    main()
