#!/usr/bin/env python3
"""
Debug Logger for CERES RISC-V Makefile & Script Execution
==========================================================

Provides comprehensive audit trail and debug reporting for all
Makefile targets and Python scripts execution.

Features:
- Automatic execution flow tracking
- File access monitoring
- Environment snapshot
- Performance metrics
- Error/warning aggregation
- Hierarchical step tracking

Usage:
    from debug_logger import DebugLogger

    logger = DebugLogger("test_name", "target_name")
    with logger.step("build", "makefile_target") as step:
        step.command("verilator --cc ...")
        result = subprocess.run(...)
        step.exit_code(result.returncode)

    logger.save()
"""

import json
import time
import os
import sys
import subprocess
import traceback
import hashlib
from datetime import datetime
from pathlib import Path
from typing import Optional, Dict, List, Any
from contextlib import contextmanager

# Optional dependency
try:
    import psutil
    PSUTIL_AVAILABLE = True
except ImportError:
    PSUTIL_AVAILABLE = False
    print("Warning: psutil not available, performance metrics disabled", file=sys.stderr)


class ExecutionStep:
    """Represents a single execution step in the debug trace."""

    def __init__(self, step_num: int, step_type: str, name: str, debug_dir: Path):
        self.step_num = step_num
        self.data = {
            "step": step_num,
            "type": step_type,
            "name": name,
            "timestamp": datetime.now().isoformat(),
            "duration_ms": 0,
            "exit_code": None,
            "command": None,
            "args": [],
            "stdout_file": None,
            "stderr_file": None,
            "log_file": None,
            "errors": [],
            "warnings": []
        }
        self.debug_dir = debug_dir
        self.start_time = time.time()
        self.process = None

    def command(self, cmd: str):
        """Record the command being executed."""
        self.data["command"] = cmd

    def arguments(self, args: List[str]):
        """Record script arguments."""
        self.data["args"] = args

    def exit_code(self, code: int):
        """Record exit code."""
        self.data["exit_code"] = code

    def error(self, msg: str):
        """Record an error."""
        self.data["errors"].append({
            "timestamp": datetime.now().isoformat(),
            "message": msg
        })

    def warning(self, msg: str):
        """Record a warning."""
        self.data["warnings"].append({
            "timestamp": datetime.now().isoformat(),
            "message": msg
        })

    def log_output(self, stdout: str = None, stderr: str = None):
        """Save stdout/stderr to files."""
        if stdout:
            stdout_file = self.debug_dir / f"step{self.step_num}_stdout.log"
            stdout_file.write_text(stdout)
            self.data["stdout_file"] = str(stdout_file.relative_to(Path.cwd()))

        if stderr:
            stderr_file = self.debug_dir / f"step{self.step_num}_stderr.log"
            stderr_file.write_text(stderr)
            self.data["stderr_file"] = str(stderr_file.relative_to(Path.cwd()))

    def finalize(self):
        """Finalize the step (calculate duration)."""
        self.data["duration_ms"] = int((time.time() - self.start_time) * 1000)
        return self.data


class DebugLogger:
    """
    Main debug logger that tracks entire Makefile/script execution.
    """

    def __init__(self, test_name: str, target: str, makefile: str = "Makefile.verilator"):
        self.test_name = test_name
        self.target = target
        self.makefile = makefile
        self.start_time = time.time()
        self.session_id = hashlib.md5(f"{test_name}{time.time()}".encode()).hexdigest()[:8]

        # Create debug directory
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.report_name = f"run_{timestamp}_{test_name}.json"
        self.debug_dir = Path("build/debug_reports") / f"{timestamp}_{test_name}"
        self.debug_dir.mkdir(parents=True, exist_ok=True)

        # Initialize report structure
        self.report = {
            "metadata": self._get_metadata(),
            "environment": self._get_environment(),
            "execution_flow": [],
            "files_accessed": {
                "read": [],
                "written": [],
                "modified": []
            },
            "config_snapshot": {},
            "result": {
                "status": "RUNNING",
                "exit_code": None,
                "duration_total_ms": 0,
                "errors": [],
                "warnings": []
            },
            "performance": {}
        }

        self.step_counter = 0
        if PSUTIL_AVAILABLE:
            self.initial_process = psutil.Process()
        else:
            self.initial_process = None

        # Start monitoring
        self._snapshot_configs()

    def _get_metadata(self) -> Dict[str, Any]:
        """Collect metadata about the execution."""
        metadata = {
            "timestamp": datetime.now().isoformat(),
            "test_name": self.test_name,
            "makefile": self.makefile,
            "target": self.target,
            "user": os.environ.get("USER", "unknown"),
            "hostname": os.uname().nodename,
            "session_id": self.session_id
        }

        # Git info
        try:
            git_commit = subprocess.check_output(
                ["git", "rev-parse", "--short", "HEAD"],
                stderr=subprocess.DEVNULL
            ).decode().strip()
            git_branch = subprocess.check_output(
                ["git", "rev-parse", "--abbrev-ref", "HEAD"],
                stderr=subprocess.DEVNULL
            ).decode().strip()
            metadata["git_commit"] = git_commit
            metadata["git_branch"] = git_branch
        except:
            pass

        return metadata

    def _get_environment(self) -> Dict[str, Any]:
        """Capture environment information."""
        env = {
            "cwd": str(Path.cwd()),
            "shell": os.environ.get("SHELL", "unknown"),
            "python_version": sys.version.split()[0],
            "env_vars": {}
        }

        # Capture relevant environment variables
        relevant_vars = [
            "TEST_NAME", "MAX_CYCLES", "MODE", "TRACE", "MEM_FILE",
            "LOG_COMMIT", "LOG_BP", "LOG_RAM", "LOG_UART", "SIM_FAST",
            "ENABLE_SPIKE", "ENABLE_COMPARE", "ENABLE_HTML_REPORT"
        ]
        for var in relevant_vars:
            if var in os.environ:
                env["env_vars"][var] = os.environ[var]

        # Tool versions
        try:
            verilator_ver = subprocess.check_output(
                ["verilator", "--version"],
                stderr=subprocess.DEVNULL
            ).decode().strip().split()[1]
            env["verilator_version"] = verilator_ver
        except:
            pass

        return env

    def _snapshot_configs(self):
        """Snapshot all relevant config files."""
        config_files = [
            "script/config/verilator.json",
            "script/config/test_registry.json",
            f"script/config/tests/{self.test_name}.json"
        ]

        for config_file in config_files:
            config_path = Path(config_file)
            if config_path.exists():
                try:
                    with open(config_path) as f:
                        self.report["config_snapshot"][config_file] = json.load(f)
                except:
                    pass

    @contextmanager
    def step(self, name: str, step_type: str = "generic"):
        """
        Context manager for tracking a single execution step.

        Args:
            name: Name of the step (e.g., "build", "run_simulation")
            step_type: Type of step (makefile_target, python_script, shell_command)
        """
        self.step_counter += 1
        step = ExecutionStep(self.step_counter, step_type, name, self.debug_dir)

        print(f"[DEBUG] Step {self.step_counter}: {step_type} - {name}", file=sys.stderr)

        try:
            yield step
        except Exception as e:
            step.error(f"Exception: {str(e)}")
            step.error(traceback.format_exc())
            step.exit_code(-1)
            raise
        finally:
            self.report["execution_flow"].append(step.finalize())

    def track_file_read(self, filepath: str):
        """Track a file read operation."""
        if filepath not in self.report["files_accessed"]["read"]:
            self.report["files_accessed"]["read"].append(filepath)

    def track_file_write(self, filepath: str):
        """Track a file write operation."""
        if filepath not in self.report["files_accessed"]["written"]:
            self.report["files_accessed"]["written"].append(filepath)

    def add_error(self, msg: str):
        """Add a global error."""
        self.report["result"]["errors"].append({
            "timestamp": datetime.now().isoformat(),
            "message": msg
        })

    def add_warning(self, msg: str):
        """Add a global warning."""
        self.report["result"]["warnings"].append({
            "timestamp": datetime.now().isoformat(),
            "message": msg
        })

    def set_result(self, status: str, exit_code: int = 0):
        """Set the final result status."""
        self.report["result"]["status"] = status
        self.report["result"]["exit_code"] = exit_code

    def _collect_performance_metrics(self):
        """Collect performance statistics."""
        if not PSUTIL_AVAILABLE:
            return

        try:
            process = psutil.Process()
            self.report["performance"] = {
                "cpu_percent": process.cpu_percent(interval=0.1),
                "memory_mb": process.memory_info().rss / (1024 * 1024),
                "io_read_mb": process.io_counters().read_bytes / (1024 * 1024),
                "io_write_mb": process.io_counters().write_bytes / (1024 * 1024),
                "num_threads": process.num_threads()
            }
        except:
            pass

    def save(self):
        """Save the debug report to disk."""
        # Finalize timing
        self.report["result"]["duration_total_ms"] = int(
            (time.time() - self.start_time) * 1000
        )

        # Collect performance metrics
        self._collect_performance_metrics()

        # Save main report
        report_path = Path("build/debug_reports") / self.report_name
        report_path.parent.mkdir(parents=True, exist_ok=True)

        with open(report_path, 'w') as f:
            json.dump(self.report, f, indent=2)

        # Create symlink to latest
        latest_link = Path("build/debug_reports") / f"latest_{self.test_name}.json"
        if latest_link.exists() or latest_link.is_symlink():
            latest_link.unlink()
        latest_link.symlink_to(report_path.name)

        print(f"\n[DEBUG] Report saved: {report_path}")
        print(f"[DEBUG] View with: python3 script/python/debug_viewer.py {report_path}")

        return report_path


class MakefileDebugWrapper:
    """
    Wrapper to integrate debug logging into Makefile targets.

    Usage in Makefile:
        export PYTHONPATH := $(ROOT_DIR):$(PYTHONPATH)
        export DEBUG_ENABLE := 1

        run:
            @python3 -c "from script.python.debug_logger import MakefileDebugWrapper; \
                MakefileDebugWrapper.start('$(TEST_NAME)', 'run')"
            @# ... your normal commands ...
            @python3 -c "from script.python.debug_logger import MakefileDebugWrapper; \
                MakefileDebugWrapper.end(0)"
    """

    _logger: Optional[DebugLogger] = None

    @classmethod
    def start(cls, test_name: str, target: str):
        """Start debug logging for a Makefile target."""
        if os.environ.get("DEBUG_ENABLE") == "1":
            cls._logger = DebugLogger(test_name, target)

    @classmethod
    def end(cls, exit_code: int):
        """End debug logging and save report."""
        if cls._logger:
            status = "PASSED" if exit_code == 0 else "FAILED"
            cls._logger.set_result(status, exit_code)
            cls._logger.save()
            cls._logger = None

    @classmethod
    def get(cls) -> Optional[DebugLogger]:
        """Get current logger instance."""
        return cls._logger


if __name__ == "__main__":
    # Example usage
    logger = DebugLogger("rv32ui-p-add", "run")

    with logger.step("build", "makefile_target") as step:
        step.command("verilator --cc ...")
        step.exit_code(0)

    with logger.step("simulate", "python_script") as step:
        step.arguments(["--test", "rv32ui-p-add"])
        step.exit_code(0)

    logger.set_result("PASSED", 0)
    logger.save()
