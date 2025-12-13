#!/usr/bin/env python3
"""
Test Manager for CERES RISC-V
==============================

Central CLI tool for managing and running tests with integrated debug logging
and automatic Spike validation.

Features:
- Run tests by name, suite, or tags
- Add/remove tests from registry
- List and filter tests
- Interactive test selection
- Automatic debug report generation
- Automatic Spike validation (configurable per suite)
- Parallel test execution (future)

Usage:
    # Run single test with auto-validation
    python3 script/python/test_manager.py run --test rv32ui-p-add

    # Run test suite
    python3 script/python/test_manager.py run --suite isa_basic

    # Run by tags
    python3 script/python/test_manager.py run --tags quick,isa

    # List tests
    python3 script/python/test_manager.py list --suite benchmarks
    python3 script/python/test_manager.py list --tags performance

    # Add new test
    python3 script/python/test_manager.py add --test my_test --suite custom

    # Interactive mode
    python3 script/python/test_manager.py interactive
"""

import json
import sys
import argparse
import subprocess
from pathlib import Path
from typing import List, Dict, Any, Optional
import os

# Add script directory to path for imports
sys.path.insert(0, str(Path(__file__).parent))

try:
    from debug_logger import DebugLogger
except ImportError:
    print("Warning: debug_logger not found, debug logging disabled", file=sys.stderr)
    DebugLogger = None

# Try to import validation runner
try:
    from validation_runner import ValidationRunner, ValidationResult
    VALIDATION_AVAILABLE = True
except ImportError:
    print("Warning: validation_runner not found, validation disabled", file=sys.stderr)
    VALIDATION_AVAILABLE = False
    ValidationRunner = None
    ValidationResult = None


class Colors:
    RED = '\033[0;31m'
    GREEN = '\033[0;32m'
    YELLOW = '\033[1;33m'
    CYAN = '\033[0;36m'
    MAGENTA = '\033[0;35m'
    RESET = '\033[0m'
    BOLD = '\033[1m'


class TestRegistry:
    """Manages the test registry JSON file."""

    def __init__(self, registry_path: str = "script/config/test_registry.json"):
        self.registry_path = Path(registry_path)
        if not self.registry_path.exists():
            print(f"{Colors.RED}Error: Test registry not found: {registry_path}{Colors.RESET}")
            sys.exit(1)

        with open(self.registry_path) as f:
            self.registry = json.load(f)

    def get_test_suites(self) -> Dict[str, Any]:
        """Get all test suites."""
        return self.registry.get("test_suites", {})

    def get_suite(self, suite_name: str) -> Optional[Dict[str, Any]]:
        """Get a specific test suite."""
        return self.get_test_suites().get(suite_name)

    def should_validate(self, suite_name: str) -> bool:
        """Check if validation is enabled for this suite."""
        suite = self.get_suite(suite_name)
        if not suite:
            return True  # Default: validate

        # Check if validation is explicitly disabled
        validation_config = suite.get("validation", {})
        if isinstance(validation_config, dict):
            return validation_config.get("enabled", True)

        # Benchmarks typically don't need validation
        if "benchmark" in suite.get("tags", []):
            return False

        return True

    def get_tests_by_suite(self, suite_name: str) -> List[str]:
        """Get all test names in a suite."""
        suite = self.get_suite(suite_name)
        if not suite:
            return []

        tests = []

        # If suite has explicit tests dict
        if "tests" in suite:
            for test_name, test_info in suite["tests"].items():
                if test_info.get("enabled", True):
                    tests.append(test_name)

        # If suite has flist
        elif "flist" in suite:
            flist_path = Path(suite["flist"])
            if flist_path.exists():
                with open(flist_path) as f:
                    for line in f:
                        line = line.strip()
                        if line and not line.startswith('#'):
                            # Apply filter if present
                            if "filter" in suite:
                                import fnmatch
                                if fnmatch.fnmatch(line, suite["filter"]):
                                    tests.append(line)
                            else:
                                tests.append(line)

        return tests

    def get_tests_by_tags(self, tags: List[str]) -> List[Dict[str, Any]]:
        """Get tests matching any of the given tags."""
        matching_tests = []

        for suite_name, suite in self.get_test_suites().items():
            if not suite.get("enabled", True):
                continue

            suite_tags = suite.get("tags", [])

            # Check if suite has matching tags
            if any(tag in suite_tags for tag in tags):
                # Get all tests from this suite
                test_names = self.get_tests_by_suite(suite_name)
                for test_name in test_names:
                    matching_tests.append({
                        "name": test_name,
                        "suite": suite_name,
                        "tags": suite_tags,
                        "config": suite.get("config")
                    })

            # Check individual tests in suite
            if "tests" in suite:
                for test_name, test_info in suite["tests"].items():
                    if not test_info.get("enabled", True):
                        continue

                    test_tags = test_info.get("tags", [])
                    if any(tag in test_tags for tag in tags):
                        matching_tests.append({
                            "name": test_name,
                            "suite": suite_name,
                            "tags": test_tags,
                            "config": test_info.get("config") or suite.get("config")
                        })

        return matching_tests

    def get_test_config(self, test_name: str, suite_name: str = None) -> Optional[str]:
        """Get configuration file path for a test."""
        if suite_name:
            suite = self.get_suite(suite_name)
            if suite:
                if "tests" in suite and test_name in suite["tests"]:
                    return suite["tests"][test_name].get("config") or suite.get("config")
                return suite.get("config")

        # Search all suites
        for suite in self.get_test_suites().values():
            if "tests" in suite and test_name in suite["tests"]:
                return suite["tests"][test_name].get("config") or suite.get("config")

        return None

    def find_suite_for_test(self, test_name: str) -> Optional[str]:
        """Find which suite a test belongs to."""
        for suite_name, suite in self.get_test_suites().items():
            tests = self.get_tests_by_suite(suite_name)
            if test_name in tests:
                return suite_name
        return None

    def add_test(self, test_name: str, suite_name: str, config: str = None):
        """Add a new test to the registry."""
        if suite_name not in self.get_test_suites():
            print(f"{Colors.RED}Error: Suite '{suite_name}' does not exist{Colors.RESET}")
            return False

        suite = self.registry["test_suites"][suite_name]

        # Initialize tests dict if not present
        if "tests" not in suite:
            suite["tests"] = {}

        # Add test
        suite["tests"][test_name] = {
            "description": f"Test {test_name}",
            "enabled": True,
            "tags": ["custom"],
            "config": config
        }

        # Save registry
        with open(self.registry_path, 'w') as f:
            json.dump(self.registry, f, indent=2)

        print(f"{Colors.GREEN}✓ Added test '{test_name}' to suite '{suite_name}'{Colors.RESET}")
        return True

    def remove_test(self, test_name: str, suite_name: str = None):
        """Remove a test from the registry."""
        if suite_name:
            suites_to_check = [suite_name]
        else:
            suites_to_check = list(self.get_test_suites().keys())

        removed = False
        for sname in suites_to_check:
            suite = self.registry["test_suites"].get(sname)
            if suite and "tests" in suite and test_name in suite["tests"]:
                del suite["tests"][test_name]
                removed = True
                print(f"{Colors.GREEN}✓ Removed test '{test_name}' from suite '{sname}'{Colors.RESET}")

        if removed:
            with open(self.registry_path, 'w') as f:
                json.dump(self.registry, f, indent=2)
        else:
            print(f"{Colors.YELLOW}Warning: Test '{test_name}' not found{Colors.RESET}")

        return removed


class TestRunner:
    """Runs tests with debug logging and validation integration."""

    def __init__(self, registry: TestRegistry, debug_enable: bool = True, validation_enable: bool = True):
        self.registry = registry
        self.debug_enable = debug_enable
        self.validation_enable = validation_enable
        self.root_dir = Path.cwd()
        self.makefile = "Makefile.verilator"
        self.results_dir = self.root_dir / "results"

    def run_test(self, test_name: str, suite_name: str = None, **kwargs) -> Dict[str, Any]:
        """
        Run a single test with optional validation.

        Returns dict with:
            - simulation_status: COMPLETED/CRASHED
            - validation_status: VALIDATED_PASS/FAIL/SKIPPED
            - final_status: PASSED/FAILED
            - duration_s: float
        """
        # Find suite if not provided
        if not suite_name:
            suite_name = self.registry.find_suite_for_test(test_name)

        # Check if validation should run
        should_validate = self.validation_enable and self.registry.should_validate(suite_name) if suite_name else True

        # Debug logger
        logger = None
        if self.debug_enable and DebugLogger:
            logger = DebugLogger(test_name, "test_run", self.makefile)
            if logger:
                logger.track_file_read(f"script/config/test_registry.json")

        result = {
            "test_name": test_name,
            "suite": suite_name,
            "simulation_status": None,
            "validation_status": "SKIPPED",
            "validation_result": None,
            "final_status": None,
            "duration_s": 0,
            "passed": False
        }

        try:
            # 1. RUN RTL SIMULATION
            print(f"\n{Colors.CYAN}{'='*80}{Colors.RESET}")
            print(f"{Colors.BOLD}Running Test: {test_name}{Colors.RESET}")
            if suite_name:
                print(f"{Colors.CYAN}Suite: {suite_name}{Colors.RESET}")
            print(f"{Colors.CYAN}{'='*80}{Colors.RESET}\n")

            # Build make command
            make_cmd = ["make", "-f", self.makefile, "run", f"TEST_NAME={test_name}"]

            # Add optional parameters
            if "max_cycles" in kwargs:
                make_cmd.append(f"MAX_CYCLES={kwargs['max_cycles']}")
            if "trace" in kwargs and not kwargs["trace"]:
                make_cmd.append("TRACE=0")
            if "mode" in kwargs:
                make_cmd.append(f"MODE={kwargs['mode']}")

            print(f"{Colors.CYAN}[1/2] RTL Simulation{Colors.RESET}")
            print(f"  Command: {' '.join(make_cmd)}\n")

            if logger:
                with logger.step("rtl_simulation", "makefile_target") as step:
                    step.command(' '.join(make_cmd))
                    step.arguments(make_cmd[4:])  # Arguments after "make -f ... run"

                    import time
                    start = time.time()
                    rtl_result = subprocess.run(make_cmd, cwd=self.root_dir)
                    duration = time.time() - start

                    step.exit_code(rtl_result.returncode)
                    result["duration_s"] = duration
            else:
                import time
                start = time.time()
                rtl_result = subprocess.run(make_cmd, cwd=self.root_dir)
                result["duration_s"] = time.time() - start

            # Check RTL result
            if rtl_result.returncode != 0:
                result["simulation_status"] = "CRASHED"
                result["final_status"] = "FAILED"
                print(f"\n{Colors.RED}✗ SIMULATION CRASHED{Colors.RESET}")
                print(f"{Colors.RED}  Exit code: {rtl_result.returncode}{Colors.RESET}\n")
                if logger:
                    logger.set_result("SIMULATION_CRASHED", rtl_result.returncode)
                    logger.add_error(f"Simulation crashed with exit code {rtl_result.returncode}")
                return result

            result["simulation_status"] = "COMPLETED"
            print(f"\n{Colors.GREEN}✓ SIMULATION COMPLETED{Colors.RESET}")
            print(f"  Duration: {result['duration_s']:.2f}s\n")

            # 2. RUN VALIDATION (if enabled)
            if should_validate and VALIDATION_AVAILABLE:
                print(f"{Colors.CYAN}[2/2] Spike Validation{Colors.RESET}\n")

                # Determine log directory
                log_dir = self.results_dir / "logs" / "verilator" / test_name

                if logger:
                    with logger.step("spike_validation", "python_script") as step:
                        # Build command string for logging
                        val_cmd_parts = [
                            "python3", "script/python/validation_runner.py",
                            "--test-name", test_name,
                            "--log-dir", str(log_dir)
                        ]
                        if kwargs.get("spike_isa"):
                            val_cmd_parts.extend(["--spike-isa", kwargs.get("spike_isa")])
                        if kwargs.get("spike_pc"):
                            val_cmd_parts.extend(["--spike-pc", kwargs.get("spike_pc")])

                        step.command(' '.join(val_cmd_parts))
                        step.arguments(val_cmd_parts[2:])  # Arguments after "python3 script..."

                        # Run validation
                        validator = ValidationRunner(
                            test_name=test_name,
                            build_dir=self.root_dir / "build",
                            log_dir=log_dir,
                            root_dir=self.root_dir
                        )

                        validation = validator.validate(
                            skip_spike=False,
                            spike_isa=kwargs.get("spike_isa"),
                            spike_pc=kwargs.get("spike_pc")
                        )

                        step.exit_code(0 if validation.passed else 1)
                else:
                    validator = ValidationRunner(
                        test_name=test_name,
                        build_dir=self.root_dir / "build",
                        log_dir=log_dir,
                        root_dir=self.root_dir
                    )
                    validation = validator.validate()

                result["validation_status"] = validation.status
                result["validation_result"] = validation.to_dict()

                if validation.passed:
                    result["final_status"] = "PASSED"
                    result["passed"] = True
                    print(f"\n{Colors.GREEN}{'='*80}{Colors.RESET}")
                    print(f"{Colors.GREEN}✅ TEST PASSED - VALIDATED{Colors.RESET}")
                    print(f"{Colors.GREEN}{'='*80}{Colors.RESET}")
                    print(f"  RTL Instructions:   {validation.rtl_instructions}")
                    print(f"  Spike Instructions: {validation.spike_instructions}")
                    print(f"  Match:              {validation.match_percentage:.1f}%")
                    print(f"{Colors.GREEN}{'='*80}{Colors.RESET}\n")

                    # Generate HTML report
                    diff_log = log_dir / "diff.log"
                    if diff_log.exists():
                        html_report = log_dir / "test_report.html"
                        html_generator = self.root_dir / "script" / "python" / "makefile" / "html_diff_generator.py"

                        if html_generator.exists():
                            print(f"{Colors.CYAN}[HTML REPORT] Generating interactive report...{Colors.RESET}")
                            try:
                                html_cmd = [
                                    "python3",
                                    str(html_generator),
                                    "--diff-log", str(diff_log),
                                    "--output", str(html_report),
                                    "--test-name", test_name
                                ]
                                html_result = subprocess.run(
                                    html_cmd,
                                    capture_output=True,
                                    text=True,
                                    timeout=30
                                )

                                if html_result.returncode == 0 and html_report.exists():
                                    print(f"{Colors.GREEN}  ✓ HTML Report: {html_report}{Colors.RESET}")
                                    result["html_report"] = str(html_report)
                                else:
                                    print(f"{Colors.YELLOW}  ⚠ HTML report generation had issues{Colors.RESET}")
                            except Exception as html_err:
                                print(f"{Colors.YELLOW}  ⚠ HTML report generation failed: {html_err}{Colors.RESET}")

                    if logger:
                        logger.set_result("VALIDATED_PASS", 0)
                else:
                    result["final_status"] = "FAILED"
                    print(f"\n{Colors.RED}{'='*80}{Colors.RESET}")
                    print(f"{Colors.RED}❌ TEST FAILED - VALIDATION MISMATCH{Colors.RESET}")
                    print(f"{Colors.RED}{'='*80}{Colors.RESET}")
                    print(f"  RTL Instructions:   {validation.rtl_instructions}")
                    print(f"  Matched:            {validation.matched_instructions} ({validation.match_percentage:.1f}%)")
                    if validation.first_mismatch_line:
                        print(f"  First Mismatch:     Line {validation.first_mismatch_line}")
                    print(f"{Colors.RED}{'='*80}{Colors.RESET}\n")

                    if logger:
                        logger.set_result("VALIDATED_FAIL", 1)
                        logger.add_error(f"Validation failed: logs don't match ({validation.match_percentage:.1f}%)")

            else:
                # No validation
                result["validation_status"] = "SKIPPED"
                result["final_status"] = "SIMULATION_COMPLETED"
                result["passed"] = True  # Simulation OK

                print(f"{Colors.YELLOW}[INFO] Validation skipped{Colors.RESET}")
                print(f"\n{Colors.GREEN}✓ SIMULATION COMPLETED (validation skipped){Colors.RESET}\n")

                if logger:
                    logger.set_result("SIMULATION_COMPLETED", 0)

            return result

        except Exception as e:
            print(f"{Colors.RED}Error running test: {e}{Colors.RESET}")
            result["simulation_status"] = "ERROR"
            result["final_status"] = "ERROR"
            if logger:
                logger.add_error(str(e))
                logger.set_result("ERROR", -1)
            return result

        finally:
            if logger:
                logger.save()

    def run_tests(self, test_names: List[str], suite_name: str = None, **kwargs) -> Dict[str, Dict]:
        """Run multiple tests sequentially."""
        results = {}

        for test_name in test_names:
            results[test_name] = self.run_test(test_name, suite_name, **kwargs)

        # Print summary
        print(f"\n{Colors.CYAN}{'='*80}{Colors.RESET}")
        print(f"{Colors.BOLD}Test Summary{Colors.RESET}")
        print(f"{Colors.CYAN}{'='*80}{Colors.RESET}\n")

        passed = sum(1 for r in results.values() if r.get("passed", False))
        failed = len(results) - passed

        print(f"  {Colors.GREEN}Passed: {passed}{Colors.RESET}")
        print(f"  {Colors.RED}Failed: {failed}{Colors.RESET}")
        print(f"  Total:  {len(results)}\n")

        if failed > 0:
            print(f"{Colors.YELLOW}Failed tests:{Colors.RESET}")
            for test, result in results.items():
                if not result.get("passed", False):
                    status = result.get("final_status", "UNKNOWN")
                    print(f"  • {test:30s} [{status}]")
            print()

        return results


def cmd_run(args):
    """Handle 'run' command."""
    registry = TestRegistry()
    runner = TestRunner(
        registry=registry,
        debug_enable=not args.no_debug,
        validation_enable=not args.no_validation
    )

    # Determine which tests to run
    tests_to_run = []
    suite_name = None

    if args.test:
        # Single test
        tests_to_run = [args.test]

    elif args.suite:
        # Test suite
        suite_name = args.suite
        tests_to_run = registry.get_tests_by_suite(args.suite)
        if not tests_to_run:
            print(f"{Colors.RED}Error: No tests found in suite '{args.suite}'{Colors.RESET}")
            return 1

    elif args.tags:
        # Tests by tags
        tags = [t.strip() for t in args.tags.split(',')]
        test_dicts = registry.get_tests_by_tags(tags)
        tests_to_run = [t["name"] for t in test_dicts]
        if not tests_to_run:
            print(f"{Colors.RED}Error: No tests found with tags: {tags}{Colors.RESET}")
            return 1

    else:
        print(f"{Colors.RED}Error: Must specify --test, --suite, or --tags{Colors.RESET}")
        return 1

    # Run tests
    kwargs = {}
    if args.max_cycles:
        kwargs["max_cycles"] = args.max_cycles
    if args.no_trace:
        kwargs["trace"] = False
    if args.mode:
        kwargs["mode"] = args.mode

    results = runner.run_tests(tests_to_run, suite_name, **kwargs)

    # Exit with failure if any test failed
    all_passed = all(r.get("passed", False) for r in results.values())
    return 0 if all_passed else 1


def cmd_list(args):
    """Handle 'list' command."""
    registry = TestRegistry()

    if args.suite:
        # List tests in suite
        tests = registry.get_tests_by_suite(args.suite)
        suite_info = registry.get_suite(args.suite)

        print(f"\n{Colors.BOLD}Suite: {args.suite}{Colors.RESET}")
        if suite_info:
            print(f"Description: {suite_info.get('description', 'N/A')}")
            print(f"Tags: {', '.join(suite_info.get('tags', []))}")
            print(f"Enabled: {suite_info.get('enabled', True)}")

            # Validation status
            validation_enabled = registry.should_validate(args.suite)
            val_color = Colors.GREEN if validation_enabled else Colors.YELLOW
            print(f"Validation: {val_color}{'Enabled' if validation_enabled else 'Disabled'}{Colors.RESET}\n")

        print(f"{Colors.CYAN}Tests ({len(tests)}): {Colors.RESET}")
        for test in tests:
            print(f"  • {test}")
        print()

    elif args.tags:
        # List tests by tags
        tags = [t.strip() for t in args.tags.split(',')]
        test_dicts = registry.get_tests_by_tags(tags)

        print(f"\n{Colors.BOLD}Tests with tags: {', '.join(tags)}{Colors.RESET}\n")
        print(f"{Colors.CYAN}Found {len(test_dicts)} tests:{Colors.RESET}")

        for test_dict in test_dicts:
            print(f"  • {test_dict['name']:40s} [{test_dict['suite']}]")
        print()

    else:
        # List all suites
        suites = registry.get_test_suites()

        print(f"\n{Colors.BOLD}Available Test Suites:{Colors.RESET}\n")

        for suite_name, suite_info in suites.items():
            enabled = "✓" if suite_info.get("enabled", True) else "✗"
            test_count = len(registry.get_tests_by_suite(suite_name))

            validation_enabled = registry.should_validate(suite_name)
            val_indicator = f"{Colors.GREEN}[V]{Colors.RESET}" if validation_enabled else f"{Colors.DIM}[−]{Colors.RESET}"

            print(f"  {enabled} {val_indicator} {Colors.CYAN}{suite_name:20s}{Colors.RESET} "
                  f"({test_count:3d} tests) - {suite_info.get('description', 'N/A')}")

        print(f"\n{Colors.DIM}Legend: [V] = Validation enabled, [−] = Validation disabled{Colors.RESET}\n")

    return 0


def cmd_add(args):
    """Handle 'add' command."""
    registry = TestRegistry()
    success = registry.add_test(args.test, args.suite, args.config)
    return 0 if success else 1


def cmd_remove(args):
    """Handle 'remove' command."""
    registry = TestRegistry()
    success = registry.remove_test(args.test, args.suite)
    return 0 if success else 1


def main():
    parser = argparse.ArgumentParser(
        description="CERES RISC-V Test Manager",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # Run command
    run_parser = subparsers.add_parser("run", help="Run tests")
    run_group = run_parser.add_mutually_exclusive_group(required=True)
    run_group.add_argument("--test", help="Run single test by name")
    run_group.add_argument("--suite", help="Run all tests in suite")
    run_group.add_argument("--tags", help="Run tests matching tags (comma-separated)")
    run_parser.add_argument("--max-cycles", type=int, help="Override max cycles")
    run_parser.add_argument("--no-trace", action="store_true", help="Disable waveform tracing")
    run_parser.add_argument("--mode", choices=["debug", "release", "profile"], help="Build mode")
    run_parser.add_argument("--no-debug", action="store_true", help="Disable debug logging")
    run_parser.add_argument("--no-validation", action="store_true", help="Skip Spike validation")

    # List command
    list_parser = subparsers.add_parser("list", help="List tests")
    list_parser.add_argument("--suite", help="List tests in suite")
    list_parser.add_argument("--tags", help="List tests with tags (comma-separated)")

    # Add command
    add_parser = subparsers.add_parser("add", help="Add test to registry")
    add_parser.add_argument("--test", required=True, help="Test name")
    add_parser.add_argument("--suite", required=True, help="Suite name")
    add_parser.add_argument("--config", help="Config file path")

    # Remove command
    remove_parser = subparsers.add_parser("remove", help="Remove test from registry")
    remove_parser.add_argument("--test", required=True, help="Test name")
    remove_parser.add_argument("--suite", help="Suite name (optional)")

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        return 1

    # Dispatch to command handlers
    if args.command == "run":
        return cmd_run(args)
    elif args.command == "list":
        return cmd_list(args)
    elif args.command == "add":
        return cmd_add(args)
    elif args.command == "remove":
        return cmd_remove(args)


if __name__ == "__main__":
    sys.exit(main())
