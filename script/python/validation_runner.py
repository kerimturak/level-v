#!/usr/bin/env python3
"""
CERES RISC-V Validation Runner
===============================

RTL simülasyon çıktısını Spike golden reference ile karşılaştırır.

Workflow:
1. RTL simülasyonu zaten çalıştırılmış olmalı (commit_trace.log mevcut)
2. Spike golden model çalıştırılır
3. RTL ve Spike commit logları karşılaştırılır
4. Validation sonucu döndürülür

Usage:
    python3 validation_runner.py \\
        --test-name rv32ui-p-add \\
        --build-dir build \\
        --log-dir build/log/verilator/rv32ui-p-add

    python3 validation_runner.py \\
        --test-name rv32ui-p-add \\
        --rtl-log build/log/test/commit_trace.log \\
        --spike-log build/log/test/spike_commit.log \\
        --skip-spike  # Only compare existing logs
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Dict, Any, Optional
from dataclasses import dataclass


# ═══════════════════════════════════════════════════════════════════════════
# Colors
# ═══════════════════════════════════════════════════════════════════════════
class Color:
    RED = '\033[0;31m'
    GREEN = '\033[0;32m'
    YELLOW = '\033[1;33m'
    CYAN = '\033[0;36m'
    RESET = '\033[0m'
    BOLD = '\033[1m'


# ═══════════════════════════════════════════════════════════════════════════
# Validation Result
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class ValidationResult:
    """Validation sonucu."""
    test_name: str
    rtl_log_exists: bool
    spike_ran: bool
    spike_success: bool
    comparison_ran: bool
    logs_match: bool

    # Metrics
    rtl_instructions: int = 0
    spike_instructions: int = 0
    matched_instructions: int = 0
    first_mismatch_line: Optional[int] = None
    match_percentage: float = 0.0

    # Errors
    errors: list = None
    warnings: list = None

    def __post_init__(self):
        if self.errors is None:
            self.errors = []
        if self.warnings is None:
            self.warnings = []

    @property
    def status(self) -> str:
        """Final validation status."""
        if not self.rtl_log_exists:
            return "RTL_LOG_MISSING"
        if not self.spike_ran:
            return "SPIKE_SKIPPED"
        if not self.spike_success:
            return "SPIKE_FAILED"
        if not self.comparison_ran:
            return "COMPARISON_SKIPPED"
        if self.logs_match:
            return "VALIDATED_PASS"
        else:
            return "VALIDATED_FAIL"

    @property
    def passed(self) -> bool:
        """Did validation pass?"""
        return self.status == "VALIDATED_PASS"

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary."""
        return {
            "test_name": self.test_name,
            "status": self.status,
            "passed": self.passed,
            "rtl_log_exists": self.rtl_log_exists,
            "spike": {
                "ran": self.spike_ran,
                "success": self.spike_success
            },
            "comparison": {
                "ran": self.comparison_ran,
                "logs_match": self.logs_match
            },
            "metrics": {
                "rtl_instructions": self.rtl_instructions,
                "spike_instructions": self.spike_instructions,
                "matched_instructions": self.matched_instructions,
                "first_mismatch_line": self.first_mismatch_line,
                "match_percentage": round(self.match_percentage, 2)
            },
            "errors": self.errors,
            "warnings": self.warnings
        }


# ═══════════════════════════════════════════════════════════════════════════
# Validation Runner
# ═══════════════════════════════════════════════════════════════════════════
class ValidationRunner:
    """Spike validation orchestrator."""

    def __init__(self, test_name: str, build_dir: Path, log_dir: Path, root_dir: Path = None):
        self.test_name = test_name
        self.build_dir = build_dir
        self.log_dir = log_dir
        self.root_dir = root_dir or Path.cwd()

        # File paths
        self.rtl_log = log_dir / "commit_trace.log"
        self.spike_log = log_dir / "spike_commit.log"
        self.diff_log = log_dir / "diff.log"

        # Makefile paths
        self.makefile_spike = self.root_dir / "Makefile.spike"

    def run_spike(self, spike_isa: str = None, spike_pc: str = None) -> bool:
        """Run Spike golden model."""
        print(f"\n{Color.CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{Color.RESET}")
        print(f"{Color.CYAN}  Running Spike Golden Reference{Color.RESET}")
        print(f"{Color.CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{Color.RESET}")

        cmd = [
            "make", "-f", str(self.makefile_spike),
            "run-spike",
            f"TEST_NAME={self.test_name}",
            f"BUILD_DIR={self.build_dir}",
            f"LOG_DIR={self.log_dir}"
        ]

        if spike_isa:
            cmd.append(f"SPIKE_ISA={spike_isa}")
        if spike_pc:
            cmd.append(f"SPIKE_PC={spike_pc}")

        print(f"{Color.CYAN}[SPIKE]{Color.RESET} Command: {' '.join(cmd)}")

        try:
            result = subprocess.run(
                cmd,
                cwd=self.root_dir,
                check=False,
                capture_output=False
            )

            if result.returncode == 0:
                print(f"{Color.GREEN}[SUCCESS]{Color.RESET} Spike completed successfully")
                return True
            else:
                print(f"{Color.RED}[ERROR]{Color.RESET} Spike failed with exit code {result.returncode}")
                return False

        except Exception as e:
            print(f"{Color.RED}[ERROR]{Color.RESET} Exception running Spike: {e}")
            return False

    def compare_logs(self, skip_csr: bool = False, resync: bool = False) -> bool:
        """Compare RTL and Spike logs."""
        print(f"\n{Color.CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{Color.RESET}")
        print(f"{Color.CYAN}  Comparing RTL vs Spike Logs{Color.RESET}")
        print(f"{Color.CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{Color.RESET}")

        cmd = [
            "make", "-f", str(self.makefile_spike),
            "compare",
            f"TEST_NAME={self.test_name}",
            f"BUILD_DIR={self.build_dir}",
            f"RTL_LOG={self.rtl_log}",
            f"SPIKE_LOG={self.spike_log}",
            f"LOG_DIR={self.log_dir}"
        ]

        if skip_csr:
            cmd.append("SKIP_CSR=1")
        if resync:
            cmd.append("RESYNC=1")

        print(f"{Color.CYAN}[COMPARE]{Color.RESET} Command: {' '.join(cmd)}")

        try:
            result = subprocess.run(
                cmd,
                cwd=self.root_dir,
                check=False,
                capture_output=False
            )

            if result.returncode == 0:
                print(f"{Color.GREEN}[SUCCESS]{Color.RESET} Logs match!")
                return True
            else:
                print(f"{Color.RED}[FAILURE]{Color.RESET} Logs differ")
                return False

        except Exception as e:
            print(f"{Color.RED}[ERROR]{Color.RESET} Exception comparing logs: {e}")
            return False

    def extract_metrics(self) -> Dict[str, int]:
        """Extract metrics from diff log."""
        metrics = {
            "rtl_instructions": 0,
            "spike_instructions": 0,
            "matched_instructions": 0,
            "first_mismatch_line": None,
            "match_percentage": 0.0
        }

        # Count RTL instructions
        if self.rtl_log.exists():
            try:
                with open(self.rtl_log) as f:
                    metrics["rtl_instructions"] = sum(1 for _ in f)
            except:
                pass

        # Count Spike instructions
        if self.spike_log.exists():
            try:
                with open(self.spike_log) as f:
                    # Spike log format: "core   0: 0x80000000 (0x00000297) ..."
                    # Count non-empty lines that look like commits
                    metrics["spike_instructions"] = sum(
                        1 for line in f
                        if line.strip() and "core" in line and "0x" in line
                    )
            except:
                pass

        # Parse diff log for match info
        if self.diff_log.exists():
            try:
                with open(self.diff_log) as f:
                    content = f.read()

                    # Look for match percentage
                    if "match" in content.lower():
                        metrics["matched_instructions"] = metrics["rtl_instructions"]
                        metrics["match_percentage"] = 100.0
                    elif "mismatch" in content.lower():
                        # Try to find first mismatch line number
                        for line in content.split('\n'):
                            if "line" in line.lower() and any(c.isdigit() for c in line):
                                # Extract number
                                nums = ''.join(c for c in line if c.isdigit() or c == ' ')
                                try:
                                    metrics["first_mismatch_line"] = int(nums.strip().split()[0])
                                    metrics["matched_instructions"] = metrics["first_mismatch_line"] - 1
                                    break
                                except:
                                    pass
            except:
                pass

        # Calculate match percentage
        if metrics["rtl_instructions"] > 0:
            metrics["match_percentage"] = (
                metrics["matched_instructions"] / metrics["rtl_instructions"] * 100.0
            )

        return metrics

    def validate(
        self,
        skip_spike: bool = False,
        skip_csr: bool = False,
        resync: bool = False,
        spike_isa: str = None,
        spike_pc: str = None
    ) -> ValidationResult:
        """Run full validation pipeline."""

        result = ValidationResult(
            test_name=self.test_name,
            rtl_log_exists=False,
            spike_ran=False,
            spike_success=False,
            comparison_ran=False,
            logs_match=False
        )

        # Check RTL log exists
        if not self.rtl_log.exists():
            result.errors.append(f"RTL log not found: {self.rtl_log}")
            print(f"{Color.RED}[ERROR]{Color.RESET} RTL log not found: {self.rtl_log}")
            return result

        result.rtl_log_exists = True

        # Run Spike (unless skipped)
        if not skip_spike:
            result.spike_ran = True
            result.spike_success = self.run_spike(spike_isa, spike_pc)

            if not result.spike_success:
                result.errors.append("Spike execution failed")
                return result
        else:
            print(f"{Color.YELLOW}[INFO]{Color.RESET} Spike skipped, using existing log")
            if not self.spike_log.exists():
                result.errors.append(f"Spike log not found: {self.spike_log}")
                return result
            result.spike_ran = True
            result.spike_success = True

        # Compare logs
        result.comparison_ran = True
        result.logs_match = self.compare_logs(skip_csr, resync)

        # Extract metrics
        metrics = self.extract_metrics()
        result.rtl_instructions = metrics["rtl_instructions"]
        result.spike_instructions = metrics["spike_instructions"]
        result.matched_instructions = metrics["matched_instructions"]
        result.first_mismatch_line = metrics["first_mismatch_line"]
        result.match_percentage = metrics["match_percentage"]

        return result


# ═══════════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════════
def parse_args():
    parser = argparse.ArgumentParser(
        description="CERES RISC-V Validation Runner (Spike + Compare)",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )

    # Required
    parser.add_argument(
        "--test-name", "-t",
        required=True,
        help="Test name (e.g., rv32ui-p-add)"
    )

    # Paths
    parser.add_argument(
        "--build-dir",
        default="build",
        help="Build directory (default: build)"
    )
    parser.add_argument(
        "--log-dir", "-l",
        required=True,
        help="Log directory containing RTL logs"
    )
    parser.add_argument(
        "--root-dir",
        help="Project root directory (default: current)"
    )

    # Spike options
    parser.add_argument(
        "--skip-spike",
        action="store_true",
        help="Skip Spike run, only compare existing logs"
    )
    parser.add_argument(
        "--spike-isa",
        help="Spike ISA string"
    )
    parser.add_argument(
        "--spike-pc",
        help="Spike start PC"
    )

    # Compare options
    parser.add_argument(
        "--skip-csr",
        action="store_true",
        help="Skip CSR comparison"
    )
    parser.add_argument(
        "--resync",
        action="store_true",
        help="Enable resync mode for comparison"
    )

    # Output
    parser.add_argument(
        "--json-output",
        help="Save validation result as JSON"
    )
    parser.add_argument(
        "--quiet", "-q",
        action="store_true",
        help="Quiet mode (minimal output)"
    )

    return parser.parse_args()


def main():
    args = parse_args()

    # Setup paths
    build_dir = Path(args.build_dir).resolve()
    log_dir = Path(args.log_dir).resolve()
    root_dir = Path(args.root_dir).resolve() if args.root_dir else Path.cwd()

    if not args.quiet:
        print(f"\n{Color.BOLD}CERES RISC-V Validation Runner{Color.RESET}")
        print(f"{Color.CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{Color.RESET}")
        print(f"  Test:      {args.test_name}")
        print(f"  Build Dir: {build_dir}")
        print(f"  Log Dir:   {log_dir}")
        print(f"{Color.CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{Color.RESET}\n")

    # Run validation
    runner = ValidationRunner(
        test_name=args.test_name,
        build_dir=build_dir,
        log_dir=log_dir,
        root_dir=root_dir
    )

    result = runner.validate(
        skip_spike=args.skip_spike,
        skip_csr=args.skip_csr,
        resync=args.resync,
        spike_isa=args.spike_isa,
        spike_pc=args.spike_pc
    )

    # Print result
    if not args.quiet:
        print(f"\n{Color.CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{Color.RESET}")
        print(f"{Color.BOLD}Validation Result{Color.RESET}")
        print(f"{Color.CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{Color.RESET}")

        status_color = Color.GREEN if result.passed else Color.RED
        print(f"  Status:    {status_color}{result.status}{Color.RESET}")
        print(f"  RTL Instr: {result.rtl_instructions}")
        print(f"  Spike Instr: {result.spike_instructions}")
        print(f"  Matched:   {result.matched_instructions} ({result.match_percentage:.1f}%)")

        if result.first_mismatch_line:
            print(f"  1st Mismatch: Line {result.first_mismatch_line}")

        if result.errors:
            print(f"\n  {Color.RED}Errors:{Color.RESET}")
            for err in result.errors:
                print(f"    • {err}")

        if result.warnings:
            print(f"\n  {Color.YELLOW}Warnings:{Color.RESET}")
            for warn in result.warnings:
                print(f"    • {warn}")

        print(f"{Color.CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{Color.RESET}\n")

    # Save JSON output
    if args.json_output:
        output_path = Path(args.json_output)
        with open(output_path, 'w') as f:
            json.dump(result.to_dict(), f, indent=2)
        print(f"{Color.GREEN}[SUCCESS]{Color.RESET} JSON saved: {output_path}")

    # Exit code
    return 0 if result.passed else 1


if __name__ == "__main__":
    sys.exit(main())
