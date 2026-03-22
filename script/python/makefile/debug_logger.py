#!/usr/bin/env python3
"""
Level RISC-V — Debug Logger for Python Tools

Common debug logging infrastructure for all Python tools.
Creates a detailed debug log file on each run.

Usage:
    from debug_logger import DebugLogger
    
    logger = DebugLogger("verilator", log_dir)
    logger.section("Configuration")
    logger.param("test_name", "rv32ui-p-add")
    logger.command(["vsim", "-c", ...])
    logger.save()
"""

import json
import os
import sys
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Union


# ═══════════════════════════════════════════════════════════════════════════
# Debug Logger Class
# ═══════════════════════════════════════════════════════════════════════════
class DebugLogger:
    """
    Debug log builder.

    On each run:
    - Records all parameters
    - Shows what came from which config
    - Logs full command lines
    - Records error conditions in detail
    """
    
    def __init__(
        self, 
        tool_name: str, 
        log_dir: Optional[Path] = None,
        enabled: bool = True,
        console_echo: bool = False
    ):
        """
        Args:
            tool_name: Tool name (verilator, modelsim, etc.)
            log_dir: Log directory (None uses a temporary directory)
            enabled: Whether debug logging is enabled
            console_echo: Also echo to the console
        """
        self.tool_name = tool_name
        self.enabled = enabled
        self.console_echo = console_echo
        self.start_time = datetime.now()
        
        # Log directory
        if log_dir:
            self.log_dir = Path(log_dir)
        else:
            self.log_dir = Path("/tmp") / f"level_{tool_name}_debug"
        
        # Log contents
        self.lines: List[str] = []
        self.sections: List[Dict[str, Any]] = []
        self.current_section: Optional[Dict[str, Any]] = None
        
        # Metadata
        self.metadata = {
            "tool": tool_name,
            "start_time": self.start_time.isoformat(),
            "python_version": sys.version,
            "cwd": os.getcwd(),
            "argv": sys.argv,
            "env": self._get_relevant_env(),
        }
        
        # Startup banner
        self._write_header()
    
    def _get_relevant_env(self) -> Dict[str, str]:
        """Get relevant environment variables."""
        relevant_vars = [
            "PATH", "LD_LIBRARY_PATH", "VERILATOR_ROOT",
            "MODEL_TECH", "MTI_HOME", "LM_LICENSE_FILE",
            "HOME", "USER", "PWD"
        ]
        return {k: os.environ.get(k, "") for k in relevant_vars if os.environ.get(k)}
    
    def _write_header(self) -> None:
        """Write log header."""
        self._log("=" * 80)
        self._log(f"  Level RISC-V — {self.tool_name.upper()} Debug Log")
        self._log("=" * 80)
        self._log(f"  Started: {self.start_time.strftime('%Y-%m-%d %H:%M:%S')}")
        self._log(f"  CWD:     {os.getcwd()}")
        self._log(f"  Python:  {sys.version.split()[0]}")
        self._log("=" * 80)
        self._log("")
    
    def _log(self, line: str) -> None:
        """Append a line."""
        if not self.enabled:
            return
        self.lines.append(line)
        if self.console_echo:
            print(f"[DEBUG] {line}")
    
    # ═══════════════════════════════════════════════════════════════════════
    # Section Management
    # ═══════════════════════════════════════════════════════════════════════
    def section(self, name: str) -> None:
        """Start a new section."""
        if self.current_section:
            self.sections.append(self.current_section)
        
        self.current_section = {
            "name": name,
            "timestamp": datetime.now().isoformat(),
            "params": {},
            "commands": [],
            "notes": []
        }
        
        self._log("")
        self._log(f"┌{'─' * 78}┐")
        self._log(f"│ {name:<76} │")
        self._log(f"└{'─' * 78}┘")
    
    # ═══════════════════════════════════════════════════════════════════════
    # Parameter Logging
    # ═══════════════════════════════════════════════════════════════════════
    def param(
        self, 
        name: str, 
        value: Any, 
        source: str = "unknown",
        note: str = ""
    ) -> None:
        """
        Log a parameter.

        Args:
            name: Parameter name
            value: Parameter value
            source: Source (cli, json, default, env, computed)
            note: Optional note
        """
        if not self.enabled:
            return
        
        # Convert value to string
        if isinstance(value, Path):
            value_str = str(value)
        elif isinstance(value, (list, dict)):
            value_str = json.dumps(value, default=str)
        else:
            value_str = str(value)
        
        # Truncate long values
        if len(value_str) > 60:
            display_value = value_str[:57] + "..."
        else:
            display_value = value_str
        
        # Source indicator
        source_map = {
            "cli": "CLI",
            "json": "JSON",
            "default": "DEF",
            "env": "ENV",
            "computed": "CALC",
            "override": "OVR",
            "unknown": "???"
        }
        src_tag = source_map.get(source, source[:4].upper())
        
        line = f"  [{src_tag:4}] {name:<25} = {display_value}"
        if note:
            line += f"  # {note}"
        
        self._log(line)
        
        # Add to current section
        if self.current_section:
            self.current_section["params"][name] = {
                "value": value,
                "source": source,
                "note": note
            }
    
    def params_from_dict(
        self, 
        params: Dict[str, Any], 
        source: str = "unknown",
        prefix: str = ""
    ) -> None:
        """Log all parameters from a dict."""
        for key, value in params.items():
            full_key = f"{prefix}.{key}" if prefix else key
            self.param(full_key, value, source)
    
    def params_from_dataclass(
        self, 
        obj: Any, 
        source: str = "unknown",
        prefix: str = ""
    ) -> None:
        """Log all fields from a dataclass."""
        if hasattr(obj, "__dataclass_fields__"):
            for field_name in obj.__dataclass_fields__:
                value = getattr(obj, field_name)
                full_key = f"{prefix}.{field_name}" if prefix else field_name
                self.param(full_key, value, source)
    
    # ═══════════════════════════════════════════════════════════════════════
    # Command Logging
    # ═══════════════════════════════════════════════════════════════════════
    def command(
        self, 
        cmd: Union[str, List[str]], 
        description: str = "",
        cwd: Optional[Path] = None
    ) -> None:
        """
        Log the command to run.

        Args:
            cmd: Command (string or list)
            description: Description
            cwd: Working directory
        """
        if not self.enabled:
            return
        
        if isinstance(cmd, list):
            cmd_str = " \\\n    ".join(cmd)
            cmd_full = " ".join(cmd)
        else:
            cmd_str = cmd
            cmd_full = cmd
        
        self._log("")
        self._log(f"  ▶ Command: {description or 'Execute'}")
        if cwd:
            self._log(f"    CWD: {cwd}")
        self._log(f"    $ {cmd_str}")
        self._log("")
        
        if self.current_section:
            self.current_section["commands"].append({
                "cmd": cmd_full,
                "description": description,
                "cwd": str(cwd) if cwd else None
            })
    
    # ═══════════════════════════════════════════════════════════════════════
    # Notes and Warnings
    # ═══════════════════════════════════════════════════════════════════════
    def note(self, message: str) -> None:
        """Add a note."""
        self._log(f"  📝 {message}")
        if self.current_section:
            self.current_section["notes"].append(message)
    
    def warning(self, message: str) -> None:
        """Add a warning."""
        self._log(f"  ⚠️  WARNING: {message}")
        if self.current_section:
            self.current_section["notes"].append(f"[WARN] {message}")
    
    def error(self, message: str) -> None:
        """Add an error."""
        self._log(f"  ❌ ERROR: {message}")
        if self.current_section:
            self.current_section["notes"].append(f"[ERROR] {message}")
    
    def success(self, message: str) -> None:
        """Add a success message."""
        self._log(f"  ✅ {message}")
    
    # ═══════════════════════════════════════════════════════════════════════
    # File Operations
    # ═══════════════════════════════════════════════════════════════════════
    def file_check(self, path: Path, description: str = "") -> bool:
        """Check file existence and log."""
        exists = path.exists()
        status = "✓" if exists else "✗"
        size = ""
        if exists and path.is_file():
            size_bytes = path.stat().st_size
            if size_bytes > 1024*1024:
                size = f" ({size_bytes/1024/1024:.1f} MB)"
            elif size_bytes > 1024:
                size = f" ({size_bytes/1024:.1f} KB)"
            else:
                size = f" ({size_bytes} B)"
        
        desc = f" - {description}" if description else ""
        self._log(f"  [{status}] {path}{size}{desc}")
        return exists
    
    def file_list(self, directory: Path, pattern: str = "*") -> List[Path]:
        """Log directory listing."""
        if not directory.exists():
            self._log(f"  Directory not found: {directory}")
            return []
        
        files = sorted(directory.glob(pattern))
        self._log(f"  📁 {directory}/ ({len(files)} files matching '{pattern}')")
        for f in files[:10]:  # First 10
            self.file_check(f)
        if len(files) > 10:
            self._log(f"  ... and {len(files) - 10} more files")
        return files
    
    # ═══════════════════════════════════════════════════════════════════════
    # Config Source Tracking
    # ═══════════════════════════════════════════════════════════════════════
    def config_source(
        self,
        param_name: str,
        cli_value: Any,
        json_value: Any,
        default_value: Any,
        final_value: Any
    ) -> None:
        """
        Show config source in detail.

        Makes clear where each value came from.
        """
        # Determine source
        if cli_value is not None and cli_value != default_value:
            source = "cli"
            chosen = cli_value
        elif json_value is not None and json_value != default_value:
            source = "json"
            chosen = json_value
        else:
            source = "default"
            chosen = default_value
        
        # Override check
        if final_value != chosen:
            source = "override"
        
        self._log(f"  {param_name}:")
        self._log(f"    CLI:     {cli_value}")
        self._log(f"    JSON:    {json_value}")
        self._log(f"    Default: {default_value}")
        self._log(f"    → Final: {final_value} (from {source})")
    
    # ═══════════════════════════════════════════════════════════════════════
    # Result and Save
    # ═══════════════════════════════════════════════════════════════════════
    def result(
        self,
        success: bool,
        exit_code: int = 0,
        message: str = "",
        details: Optional[Dict[str, Any]] = None
    ) -> None:
        """Log the outcome."""
        end_time = datetime.now()
        elapsed = (end_time - self.start_time).total_seconds()
        
        self._log("")
        self._log("=" * 80)
        if success:
            self._log(f"  ✅ SUCCESS - {message or 'Completed successfully'}")
        else:
            self._log(f"  ❌ FAILED - {message or 'Execution failed'}")
        self._log(f"  Exit Code: {exit_code}")
        self._log(f"  Duration:  {elapsed:.2f} seconds")
        self._log(f"  Ended:     {end_time.strftime('%Y-%m-%d %H:%M:%S')}")
        
        if details:
            self._log("")
            self._log("  Details:")
            for key, value in details.items():
                self._log(f"    {key}: {value}")
        
        self._log("=" * 80)
        
        # Update metadata
        self.metadata["end_time"] = end_time.isoformat()
        self.metadata["elapsed_seconds"] = elapsed
        self.metadata["success"] = success
        self.metadata["exit_code"] = exit_code
    
    def save(self) -> Optional[Path]:
        """
        Save the debug log.

        Returns:
            Path to the saved log file, or None
        """
        if not self.enabled:
            return None
        
        # Append final open section
        if self.current_section:
            self.sections.append(self.current_section)
        
        # Create directory
        self.log_dir.mkdir(parents=True, exist_ok=True)
        
        # Text log
        timestamp = self.start_time.strftime("%Y%m%d_%H%M%S")
        log_file = self.log_dir / f"debug_{self.tool_name}_{timestamp}.log"
        
        with open(log_file, "w") as f:
            f.write("\n".join(self.lines))
        
        # JSON log (structured)
        json_file = self.log_dir / f"debug_{self.tool_name}_{timestamp}.json"
        json_data = {
            "metadata": self.metadata,
            "sections": self.sections
        }
        
        with open(json_file, "w") as f:
            json.dump(json_data, f, indent=2, default=str)
        
        # Also write fixed-name "latest" copies for easy access
        latest_log = self.log_dir / f"debug_{self.tool_name}_latest.log"
        latest_json = self.log_dir / f"debug_{self.tool_name}_latest.json"
        
        with open(latest_log, "w") as f:
            f.write("\n".join(self.lines))
        with open(latest_json, "w") as f:
            json.dump(json_data, f, indent=2, default=str)
        
        return log_file
    
    # ═══════════════════════════════════════════════════════════════════════
    # Context Manager
    # ═══════════════════════════════════════════════════════════════════════
    def __enter__(self) -> "DebugLogger":
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        if exc_type:
            self.error(f"Exception: {exc_type.__name__}: {exc_val}")
        self.save()


# ═══════════════════════════════════════════════════════════════════════════
# Helper Functions
# ═══════════════════════════════════════════════════════════════════════════
def create_logger(
    tool_name: str,
    log_dir: Optional[Path] = None,
    debug_enabled: bool = True
) -> DebugLogger:
    """
    Create a debug logger.

    Controlled by DEBUG environment variable or --debug flag.
    """
    # Determine debug mode
    enabled = debug_enabled or os.environ.get("LEVEL_DEBUG", "0") == "1"
    
    return DebugLogger(
        tool_name=tool_name,
        log_dir=log_dir,
        enabled=enabled,
        console_echo=os.environ.get("LEVEL_DEBUG_ECHO", "0") == "1"
    )


# ═══════════════════════════════════════════════════════════════════════════
# Test
# ═══════════════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    # Test
    with create_logger("test", Path("/tmp/test_debug"), True) as logger:
        logger.section("Configuration")
        logger.param("test_name", "rv32ui-p-add", "cli")
        logger.param("max_cycles", 100000, "json")
        logger.param("trace_enabled", True, "default")
        
        logger.section("Files")
        logger.file_check(Path("/tmp/test.mem"), "Memory file")
        
        logger.section("Execution")
        logger.command(["verilator", "--version"], "Check version")
        
        logger.result(True, 0, "Test completed")
    
    print("Debug log saved to /tmp/test_debug/")
