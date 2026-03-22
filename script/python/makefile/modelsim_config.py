#!/usr/bin/env python3
"""
Level RISC-V — ModelSim Configuration Manager

Reads the JSON configuration file, validates it, and converts it to a Python dict.
Includes schema validation, profile merging, and a warning system.

Usage:
    from modelsim_config import load_config, SimConfig
    
    config = load_config(profile="debug")
    print(config.simulation.sim_time)
"""

import json
import os
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Union
import warnings


# ═══════════════════════════════════════════════════════════════════════════
# ANSI Colors
# ═══════════════════════════════════════════════════════════════════════════
class Color:
    RED = "\033[0;31m"
    GREEN = "\033[0;32m"
    YELLOW = "\033[1;33m"
    CYAN = "\033[0;36m"
    MAGENTA = "\033[0;35m"
    BLUE = "\033[0;34m"
    WHITE = "\033[1;37m"
    DIM = "\033[2m"
    RESET = "\033[0m"
    BOLD = "\033[1m"

    @classmethod
    def disable(cls):
        for attr in ['RED', 'GREEN', 'YELLOW', 'CYAN', 'MAGENTA', 'BLUE', 'WHITE', 'DIM', 'RESET', 'BOLD']:
            setattr(cls, attr, "")


# ═══════════════════════════════════════════════════════════════════════════
# Warning/Error Messages
# ═══════════════════════════════════════════════════════════════════════════
def warn(msg: str) -> None:
    print(f"{Color.YELLOW}[CONFIG WARN]{Color.RESET} {msg}", file=sys.stderr)


def error(msg: str) -> None:
    print(f"{Color.RED}[CONFIG ERROR]{Color.RESET} {msg}", file=sys.stderr)


def info(msg: str) -> None:
    print(f"{Color.CYAN}[CONFIG]{Color.RESET} {msg}")


# ═══════════════════════════════════════════════════════════════════════════
# Configuration Schema Definition
# ═══════════════════════════════════════════════════════════════════════════
# This schema defines all valid fields and defaults in the JSON file

CONFIG_SCHEMA = {
    "simulation": {
        "time_resolution": {"type": "str", "default": "ns", "choices": ["ps", "ns", "us", "ms", "s"]},
        "sim_time": {"type": "str", "default": "100us"},
        "voptargs": {"type": "str", "default": "+acc=npr"},
        "quiet": {"type": "bool", "default": False},
    },
    "compile": {
        "sv_mode": {"type": "bool", "default": True},
        "mfcu": {"type": "bool", "default": True},
        "svinputport": {"type": "str", "default": "relaxed", "choices": ["relaxed", "compat", "var"]},
        "incremental": {"type": "bool", "default": False},
    },
    "debug": {
        "acc": {"type": "str", "default": "npr"},
        "fsmdebug": {"type": "bool", "default": False},
        "classdebug": {"type": "bool", "default": False},
        "assertdebug": {"type": "bool", "default": False},
    },
    "coverage": {
        "enabled": {"type": "bool", "default": False},
        "statement": {"type": "bool", "default": True},
        "branch": {"type": "bool", "default": True},
        "condition": {"type": "bool", "default": True},
        "expression": {"type": "bool", "default": True},
        "fsm": {"type": "bool", "default": True},
        "toggle": {"type": "bool", "default": True},
    },
    "language": {
        "sv_standard": {"type": "str", "default": "sv12compat"},
        "define_macros": {"type": "list", "default": []},
        "include_dirs": {"type": "list", "default": []},
        "timescale": {"type": "str", "default": "1ns/1ps"},
    },
    "gls": {
        "timing_checks": {"type": "bool", "default": False},
        "specify_delays": {"type": "bool", "default": False},
        "delay_mode": {"type": "str", "default": "typ", "choices": ["min", "max", "typ", "zero", "unit"]},
    },
    "messages": {
        "suppress": {"type": "list", "default": ["vlog-2583", "vlog-2275"]},
        "nowarn": {"type": "list", "default": []},
        "error": {"type": "list", "default": []},
        "fatal": {"type": "list", "default": []},
        "source_on_error": {"type": "bool", "default": True},
    },
    "multicore": {
        "enabled": {"type": "bool", "default": False},
        "threads": {"type": "int", "default": 2, "min": 1, "max": 64},
    },
}

# Known top-level keys (including special keys like profiles, $schema, _comment)
# "lint" kept for compatibility with older modelsim.json (unused)
KNOWN_TOP_KEYS = set(CONFIG_SCHEMA.keys()) | {"profiles", "$schema", "_comment", "_version", "lint"}


# ═══════════════════════════════════════════════════════════════════════════
# Configuration Data Classes
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class SimulationConfig:
    time_resolution: str = "ns"
    sim_time: str = "100us"
    voptargs: str = "+acc=npr"
    quiet: bool = False


@dataclass
class CompileConfig:
    sv_mode: bool = True
    mfcu: bool = True
    svinputport: str = "relaxed"
    incremental: bool = False


@dataclass
class DebugConfig:
    acc: str = "npr"
    fsmdebug: bool = False
    classdebug: bool = False
    assertdebug: bool = False


@dataclass
class CoverageConfig:
    enabled: bool = False
    statement: bool = True
    branch: bool = True
    condition: bool = True
    expression: bool = True
    fsm: bool = True
    toggle: bool = True

    def get_spec_string(self) -> str:
        """Build coverage spec string (e.g. 'sbceft')"""
        if not self.enabled:
            return ""
        spec = ""
        if self.statement: spec += "s"
        if self.branch: spec += "b"
        if self.condition: spec += "c"
        if self.expression: spec += "e"
        if self.fsm: spec += "f"
        if self.toggle: spec += "t"
        return spec


@dataclass
class LanguageConfig:
    sv_standard: str = "sv12compat"
    define_macros: List[str] = field(default_factory=list)
    include_dirs: List[str] = field(default_factory=list)
    timescale: str = "1ns/1ps"


@dataclass
class GlsConfig:
    timing_checks: bool = False
    specify_delays: bool = False
    delay_mode: str = "typ"

    def get_delay_flag(self) -> str:
        """Return delay-mode flag for vsim"""
        mode_map = {
            "min": "+mindelays",
            "max": "+maxdelays",
            "typ": "+typdelays",
            "zero": "+delay_mode_zero",
            "unit": "+delay_mode_unit",
        }
        return mode_map.get(self.delay_mode, "+typdelays")


@dataclass
class MessagesConfig:
    suppress: List[str] = field(default_factory=lambda: ["vlog-2583", "vlog-2275"])
    nowarn: List[str] = field(default_factory=list)
    error: List[str] = field(default_factory=list)
    fatal: List[str] = field(default_factory=list)
    source_on_error: bool = True


@dataclass 
class MulticoreConfig:
    enabled: bool = False
    threads: int = 2


@dataclass
class ModelSimConfig:
    """Root configuration container"""
    simulation: SimulationConfig = field(default_factory=SimulationConfig)
    compile: CompileConfig = field(default_factory=CompileConfig)
    debug: DebugConfig = field(default_factory=DebugConfig)
    coverage: CoverageConfig = field(default_factory=CoverageConfig)
    language: LanguageConfig = field(default_factory=LanguageConfig)
    gls: GlsConfig = field(default_factory=GlsConfig)
    messages: MessagesConfig = field(default_factory=MessagesConfig)
    multicore: MulticoreConfig = field(default_factory=MulticoreConfig)
    
    # Meta bilgiler
    profile_name: Optional[str] = None
    config_file: Optional[Path] = None
    local_config_file: Optional[Path] = None
    
    # Warnings collected during load/validate
    warnings: List[str] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════════════
# Validation Functions
# ═══════════════════════════════════════════════════════════════════════════
class ConfigValidator:
    """Configuration validation"""
    
    def __init__(self):
        self.warnings: List[str] = []
        self.errors: List[str] = []
    
    def validate_type(self, value: Any, expected_type: str, path: str) -> bool:
        """Validate value type"""
        type_map = {
            "str": str,
            "bool": bool,
            "int": int,
            "float": (int, float),
            "list": list,
        }
        expected = type_map.get(expected_type)
        if expected and not isinstance(value, expected):
            self.errors.append(f"{path}: expected type '{expected_type}', got '{type(value).__name__}'")
            return False
        return True
    
    def validate_choices(self, value: Any, choices: List[Any], path: str) -> bool:
        """Check value is one of allowed choices"""
        if value not in choices:
            self.errors.append(f"{path}: '{value}' invalid. Allowed: {choices}")
            return False
        return True
    
    def validate_range(self, value: int, min_val: Optional[int], max_val: Optional[int], path: str) -> bool:
        """Check numeric value is within range"""
        if min_val is not None and value < min_val:
            self.errors.append(f"{path}: {value} is below minimum {min_val}")
            return False
        if max_val is not None and value > max_val:
            self.errors.append(f"{path}: {value} is above maximum {max_val}")
            return False
        return True
    
    def check_unknown_keys(self, data: Dict, schema: Dict, path: str = "") -> None:
        """Detect unknown keys"""
        if not isinstance(data, dict):
            return
        
        known_keys = set(schema.keys()) if isinstance(schema, dict) else set()
        
        for key in data.keys():
            if key.startswith("_"):  # skip _comment etc.
                continue
            if key not in known_keys:
                self.warnings.append(f"{path}.{key}" if path else key)
    
    def validate_section(self, data: Dict, section_name: str, schema: Dict) -> Dict:
        """Validate one section and fill defaults"""
        result = {}
        section_data = data.get(section_name, {})
        
        if not isinstance(section_data, dict):
            self.errors.append(f"{section_name}: expected dict, got {type(section_data).__name__}")
            section_data = {}
        
        # Unknown keys in section
        known_keys = set(schema.keys())
        for key in section_data.keys():
            if key.startswith("_"):
                continue
            if key not in known_keys:
                self.warnings.append(f"{section_name}.{key}: unknown parameter")
        
        # Validate each field
        for field_name, field_schema in schema.items():
            path = f"{section_name}.{field_name}"
            
            if field_name in section_data:
                value = section_data[field_name]
                
                # Type check
                self.validate_type(value, field_schema["type"], path)
                
                # Choices check
                if "choices" in field_schema:
                    self.validate_choices(value, field_schema["choices"], path)
                
                # Range check
                if field_schema["type"] == "int":
                    self.validate_range(
                        value,
                        field_schema.get("min"),
                        field_schema.get("max"),
                        path
                    )
                
                result[field_name] = value
            else:
                # Use default
                result[field_name] = field_schema["default"]
        
        return result


# ═══════════════════════════════════════════════════════════════════════════
# Config Loading Functions
# ═══════════════════════════════════════════════════════════════════════════
def find_config_files(config_dir: Optional[Path] = None) -> tuple[Optional[Path], Optional[Path]]:
    """Locate configuration files"""
    if config_dir is None:
        # Relative to script location
        script_dir = Path(__file__).parent.parent.parent  # script/python/makefile -> script
        config_dir = script_dir / "config"
    
    main_config = config_dir / "modelsim.json"
    local_config = config_dir / "modelsim.local.json"
    
    if not main_config.exists():
        return None, None
    
    return main_config, local_config if local_config.exists() else None


def merge_dicts(base: Dict, override: Dict) -> Dict:
    """Recursively merge two dicts"""
    result = base.copy()
    
    for key, value in override.items():
        if key in result and isinstance(result[key], dict) and isinstance(value, dict):
            result[key] = merge_dicts(result[key], value)
        else:
            result[key] = value
    
    return result


def apply_profile(config_data: Dict, profile_name: str) -> Dict:
    """Apply named profile overlay"""
    profiles = config_data.get("profiles", {})
    
    if profile_name not in profiles:
        available = list(profiles.keys())
        raise ValueError(f"Profile not found: '{profile_name}'. Available: {available}")
    
    profile = profiles[profile_name]
    
    # Merge each profile section into base config
    result = config_data.copy()
    for section in CONFIG_SCHEMA.keys():
        if section in profile:
            if section not in result:
                result[section] = {}
            result[section] = merge_dicts(result.get(section, {}), profile[section])
    
    return result


def load_config(
    config_file: Optional[Path] = None,
    local_config_file: Optional[Path] = None,
    profile: Optional[str] = None,
    strict: bool = False,
    quiet: bool = False,
) -> ModelSimConfig:
    """
    Load and validate configuration.

    Args:
        config_file: Main config file (None = auto-discover)
        local_config_file: Local override file
        profile: Profile name to apply
        strict: If True, treat warnings as errors
        quiet: If True, suppress warning banners

    Returns:
        ModelSimConfig: Validated configuration object

    Raises:
        FileNotFoundError: Config file missing
        ValueError: Invalid configuration
    """
    # Resolve files
    if config_file is None:
        config_file, auto_local = find_config_files()
        if local_config_file is None:
            local_config_file = auto_local
    
    if config_file is None or not config_file.exists():
        raise FileNotFoundError(f"Configuration file not found: {config_file}")
    
    # Read JSON
    with open(config_file, 'r', encoding='utf-8') as f:
        config_data = json.load(f)
    
    # Merge local override
    if local_config_file and local_config_file.exists():
        with open(local_config_file, 'r', encoding='utf-8') as f:
            local_data = json.load(f)
        config_data = merge_dicts(config_data, local_data)
        if not quiet:
            info(f"Loaded local override: {local_config_file.name}")
    
    # Apply profile
    if profile:
        config_data = apply_profile(config_data, profile)
        if not quiet:
            info(f"Applied profile: {profile}")
    
    # Validate
    validator = ConfigValidator()
    
    # Unknown top-level keys
    for key in config_data.keys():
        if key not in KNOWN_TOP_KEYS and not key.startswith("_"):
            validator.warnings.append(f"Unknown top-level key: '{key}'")
    
    # Validate each schema section
    validated = {}
    for section_name, section_schema in CONFIG_SCHEMA.items():
        validated[section_name] = validator.validate_section(config_data, section_name, section_schema)
    
    # Print warnings
    if validator.warnings and not quiet:
        print(f"\n{Color.YELLOW}{'═' * 60}{Color.RESET}")
        print(f"{Color.YELLOW}  ⚠ Configuration warnings ({len(validator.warnings)}){Color.RESET}")
        print(f"{Color.YELLOW}{'═' * 60}{Color.RESET}")
        for warning in validator.warnings:
            print(f"  {Color.YELLOW}•{Color.RESET} {warning}")
        print(f"{Color.YELLOW}{'═' * 60}{Color.RESET}\n")
        
        if strict:
            raise ValueError(f"Strict mode: {len(validator.warnings)} warning(s)")
    
    # Errors
    if validator.errors:
        print(f"\n{Color.RED}{'═' * 60}{Color.RESET}")
        print(f"{Color.RED}  ✗ Configuration errors ({len(validator.errors)}){Color.RESET}")
        print(f"{Color.RED}{'═' * 60}{Color.RESET}")
        for err in validator.errors:
            print(f"  {Color.RED}•{Color.RESET} {err}")
        print(f"{Color.RED}{'═' * 60}{Color.RESET}\n")
        raise ValueError(f"Configuration has {len(validator.errors)} error(s)")
    
    # Build dataclasses
    result = ModelSimConfig(
        simulation=SimulationConfig(**validated["simulation"]),
        compile=CompileConfig(**validated["compile"]),
        debug=DebugConfig(**validated["debug"]),
        coverage=CoverageConfig(**validated["coverage"]),
        language=LanguageConfig(**validated["language"]),
        gls=GlsConfig(**validated["gls"]),
        messages=MessagesConfig(**validated["messages"]),
        multicore=MulticoreConfig(**validated["multicore"]),
        profile_name=profile,
        config_file=config_file,
        local_config_file=local_config_file,
        warnings=validator.warnings,
    )
    
    return result


# ═══════════════════════════════════════════════════════════════════════════
# Config Summary
# ═══════════════════════════════════════════════════════════════════════════
def _kv(key: str, value: Any, indent: int = 4) -> None:
    """Print key-value line."""
    spaces = " " * indent
    key_fmt = f"{Color.DIM}{key}:{Color.RESET}"
    print(f"{spaces}{key_fmt:20} {value}")

def _section(title: str) -> None:
    """Print section heading."""
    print(f"\n  {Color.BOLD}{Color.WHITE}▸ {title}{Color.RESET}")

def _bool_str(val: bool) -> str:
    """Format boolean with color."""
    if val:
        return f"{Color.GREEN}Yes{Color.RESET}"
    return f"{Color.DIM}No{Color.RESET}"

def print_config_summary(config: ModelSimConfig) -> None:
    """Print configuration summary"""
    print()
    print(f"{Color.CYAN}{'═' * 60}{Color.RESET}")
    print(f"{Color.CYAN}  ModelSim configuration summary{Color.RESET}")
    print(f"{Color.CYAN}{'═' * 60}{Color.RESET}")
    
    # Source info
    if config.config_file or config.profile_name:
        print()
        if config.config_file:
            _kv("Config", config.config_file)
        if config.local_config_file:
            _kv("Local", config.local_config_file)
        if config.profile_name:
            _kv("Profile", f"{Color.CYAN}{config.profile_name}{Color.RESET}")
    
    _section("Simulation")
    _kv("Sim Time", config.simulation.sim_time)
    _kv("Resolution", config.simulation.time_resolution)
    _kv("Voptargs", config.simulation.voptargs)
    
    _section("Compile")
    _kv("SV Mode", _bool_str(config.compile.sv_mode))
    _kv("MFCU", _bool_str(config.compile.mfcu))
    _kv("Inputport", config.compile.svinputport)
    
    _section("Coverage")
    _kv("Enabled", _bool_str(config.coverage.enabled))
    if config.coverage.enabled:
        _kv("Spec", f"+cover={config.coverage.get_spec_string()}")
    
    _section("GLS")
    _kv("Timing", _bool_str(config.gls.timing_checks))
    _kv("Delay Mode", config.gls.delay_mode)
    
    # Warnings
    if config.warnings:
        print()
        print(f"  {Color.YELLOW}⚠ {len(config.warnings)} warning(s){Color.RESET}")
        for w in config.warnings[:3]:  # show at most 3
            print(f"    {Color.DIM}• {w}{Color.RESET}")
        if len(config.warnings) > 3:
            print(f"    {Color.DIM}... and {len(config.warnings) - 3} more{Color.RESET}")
    
    print(f"\n{Color.CYAN}{'═' * 60}{Color.RESET}\n")


# ═══════════════════════════════════════════════════════════════════════════
# CLI Interface
# ═══════════════════════════════════════════════════════════════════════════
def main():
    """CLI entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Level RISC-V ModelSim Configuration Manager",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    
    parser.add_argument(
        "--config", "-c",
        type=Path,
        help="Main configuration file"
    )
    
    parser.add_argument(
        "--local", "-l",
        type=Path,
        help="Local override file"
    )
    
    parser.add_argument(
        "--profile", "-p",
        help="Profile to apply (fast, debug, coverage, gls)"
    )
    
    parser.add_argument(
        "--strict", "-s",
        action="store_true",
        help="Treat warnings as errors"
    )
    
    parser.add_argument(
        "--quiet", "-q",
        action="store_true",
        help="Show errors only"
    )
    
    parser.add_argument(
        "--summary",
        action="store_true",
        help="Print configuration summary"
    )
    
    parser.add_argument(
        "--get",
        help="Print one dotted path (e.g. simulation.sim_time)"
    )
    
    parser.add_argument(
        "--validate",
        action="store_true",
        help="Validate configuration"
    )

    parser.add_argument(
        "--make",
        action="store_true",
        help="Emit Make variables fragment for Makefile integration"
    )
    
    parser.add_argument(
        "--no-color",
        action="store_true",
        help="Disable colored output"
    )
    
    args = parser.parse_args()
    
    if args.no_color or not sys.stdout.isatty():
        Color.disable()
    
    try:
        config = load_config(
            config_file=args.config,
            local_config_file=args.local,
            profile=args.profile,
            strict=args.strict,
            quiet=args.quiet,
        )
        
        if args.get:
            # Print single dotted path
            parts = args.get.split(".")
            value = config
            for part in parts:
                if hasattr(value, part):
                    value = getattr(value, part)
                else:
                    error(f"Field not found: {args.get}")
                    return 1
            print(value)
        
        elif args.summary or args.validate:
            print_config_summary(config)
            if config.warnings:
                return 1 if args.strict else 0

        elif args.make:
            # Print Makefile variable fragment
            # Emit MODELSIM_* variables and CFG_SV_DEFINES for compatibility
            def fmt_bool(v):
                return "1" if v else "0"

            # Basic simulation vars
            print(f"MODELSIM_TIME_RES ?= {config.simulation.time_resolution}")
            print(f"SIM_TIME ?= {config.simulation.sim_time}")

            # Compile settings
            print(f"MODELSIM_SV_MODE ?= {'-sv' if config.compile.sv_mode else ''}")
            print(f"MODELSIM_MFCU ?= {'-mfcu' if config.compile.mfcu else '-sfcu'}")
            print(f"MODELSIM_SVINPUTPORT ?= {config.compile.svinputport}")

            # Debug
            print(f"MODELSIM_ACC ?= {config.debug.acc}")
            if config.debug.fsmdebug:
                print('MODELSIM_FSMDEBUG ?= -fsmdebug')
            if config.debug.assertdebug:
                print('MODELSIM_ASSERTDEBUG ?= -assertdebug')

            # Coverage
            if config.coverage.enabled:
                print(f"MODELSIM_COVERAGE ?= +cover={config.coverage.get_spec_string()}")
            else:
                print("MODELSIM_COVERAGE ?=")

            # Language
            print(f"MODELSIM_SV_COMPAT ?= -{config.language.sv_standard}")
            print(f"MODELSIM_TIMESCALE ?= {config.language.timescale}")

            # GLS
            if not config.gls.timing_checks:
                print('MODELSIM_NOTIMINGCHECKS ?= +notimingchecks')

            # Messages
            if config.messages.suppress:
                s = ' '.join([f"-suppress {m}" for m in config.messages.suppress])
                print(f"MODELSIM_SUPPRESS ?= {s}")
            if config.messages.nowarn:
                nw = ' '.join([f"-nowarn {m}" for m in config.messages.nowarn])
                print(f"MODELSIM_NOWARN ?= {nw}")
            if config.messages.source_on_error:
                print('MODELSIM_SOURCE ?= -source')

            # Multicore
            if config.multicore.enabled:
                print(f"MODELSIM_MULTICORE ?= -mtc {config.multicore.threads}")

            # Pass any language define_macros into MODELSIM_DEFINES and CFG_SV_DEFINES
            if config.language.define_macros:
                defines = ' '.join([f"+define+{d}" for d in config.language.define_macros])
                print(f"MODELSIM_DEFINES ?= {defines}")
                # Also provide CFG_SV_DEFINES for legacy usage
                cfg_defs = ' '.join([f"+define+{d}" for d in config.language.define_macros])
                print(f"CFG_SV_DEFINES := {cfg_defs}")

            # Include dirs (provide INC_DIRS fragment if present)
            if config.language.include_dirs:
                incs = ' '.join(config.language.include_dirs)
                print(f"INC_DIRS ?= {incs}")

            return 0

        else:
            # Default: print summary
            print_config_summary(config)
            return 0
    
    except FileNotFoundError as e:
        error(str(e))
        return 1
    except ValueError as e:
        error(str(e))
        return 1
    except json.JSONDecodeError as e:
        error(f"JSON parse error: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
