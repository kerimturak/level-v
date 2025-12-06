#!/usr/bin/env python3
"""
CERES RISC-V — Verilator Configuration Manager

JSON konfigürasyon dosyasını okur, doğrular ve Python dict'e dönüştürür.
Schema validation, profile merging ve uyarı sistemi içerir.

Kullanım:
    from verilator_config import load_config, VerilatorConfig
    
    config = load_config(profile="debug")
    print(config.simulation.max_cycles)
"""

import json
import os
import sys
import copy
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Union


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


def supports_color() -> bool:
    """Terminal renk desteğini kontrol et."""
    if not sys.stdout.isatty():
        return False
    if os.environ.get("NO_COLOR"):
        return False
    term = os.environ.get("TERM", "")
    if term == "dumb":
        return False
    return True


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
CONFIG_SCHEMA = {
    "simulation": {
        "max_cycles": {"type": "int", "default": 100000},
        "timeout": {"type": "int", "default": 0},
        "threads": {"type": "str", "default": "auto"},
        "seed": {"type": "str", "default": "auto"},
    },
    "build": {
        "mode": {"type": "str", "default": "release", "choices": ["debug", "release", "profile"]},
        "jobs": {"type": "str", "default": "auto"},
        "opt_level": {"type": "str", "default": "-O3", "choices": ["-O0", "-O1", "-O2", "-O3"]},
        "cpp_standard": {"type": "str", "default": "c++17"},
    },
    "trace": {
        "enabled": {"type": "bool", "default": True},
        "format": {"type": "str", "default": "fst", "choices": ["fst", "vcd"]},
        "depth": {"type": "int", "default": 99},
        "structs": {"type": "bool", "default": True},
        "params": {"type": "bool", "default": True},
        "threads": {"type": "int", "default": 1},
        "underscore": {"type": "bool", "default": False},
    },
    "coverage": {
        "enabled": {"type": "bool", "default": False},
        "line": {"type": "bool", "default": True},
        "toggle": {"type": "bool", "default": True},
        "user": {"type": "bool", "default": False},
    },
    "optimization": {
        "output_split": {"type": "int", "default": 20000},
        "output_split_cfuncs": {"type": "int", "default": 5000},
        "unroll_count": {"type": "int", "default": 64},
        "unroll_stmts": {"type": "int", "default": 30000},
        "x_assign": {"type": "str", "default": "fast", "choices": ["0", "1", "fast", "unique"]},
        "x_initial": {"type": "str", "default": "fast", "choices": ["0", "1", "fast", "unique"]},
    },
    "features": {
        "vpi": {"type": "bool", "default": False},
        "hierarchical": {"type": "bool", "default": False},
        "savable": {"type": "bool", "default": False},
        "debug_check": {"type": "bool", "default": False},
    },
    "logging": {
        "fast_sim": {"type": "bool", "default": False},
        "bp_log": {"type": "bool", "default": False},
        "bp_verbose": {"type": "bool", "default": False},
        "commit_trace": {"type": "bool", "default": True},
        "pipeline_log": {"type": "bool", "default": True},
        "ram_log": {"type": "bool", "default": True},
        "uart_log": {"type": "bool", "default": True},
    },
    "warnings": {
        "fatal": {"type": "bool", "default": False},
        "lint": {"type": "bool", "default": False},
        "style": {"type": "bool", "default": False},
        "width": {"type": "bool", "default": False},
        "unused": {"type": "bool", "default": False},
        "unoptflat": {"type": "bool", "default": False},
    },
}


# ═══════════════════════════════════════════════════════════════════════════
# Dataclass Definitions
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class SimulationConfig:
    max_cycles: int = 100000
    timeout: int = 0
    threads: str = "auto"
    seed: str = "auto"
    
    def get_threads(self) -> int:
        """Thread sayısını hesapla."""
        if self.threads == "auto":
            import multiprocessing
            return multiprocessing.cpu_count()
        return int(self.threads)


@dataclass
class BuildConfig:
    mode: str = "release"
    jobs: str = "auto"
    opt_level: str = "-O3"
    cpp_standard: str = "c++17"
    
    def get_jobs(self) -> int:
        """Job sayısını hesapla."""
        if self.jobs == "auto":
            import multiprocessing
            return multiprocessing.cpu_count()
        return int(self.jobs)


@dataclass
class TraceConfig:
    enabled: bool = True
    format: str = "fst"
    depth: int = 99
    structs: bool = True
    params: bool = True
    threads: int = 1
    underscore: bool = False
    
    def get_flags(self) -> List[str]:
        """Trace flag'lerini döndür."""
        if not self.enabled:
            return []
        
        flags = []
        if self.format == "fst":
            flags.append("--trace-fst")
        else:
            flags.append("--trace")
        
        if self.structs:
            flags.append("--trace-structs")
        if self.params:
            flags.append("--trace-params")
        if self.underscore:
            flags.append("--trace-underscore")
        
        flags.append(f"--trace-depth {self.depth}")
        
        if self.threads > 1:
            flags.append(f"--trace-threads {self.threads}")
        
        return flags


@dataclass
class CoverageConfig:
    enabled: bool = False
    line: bool = True
    toggle: bool = True
    user: bool = False
    
    def get_flags(self) -> List[str]:
        """Coverage flag'lerini döndür."""
        if not self.enabled:
            return []
        
        flags = ["--coverage"]
        if self.line:
            flags.append("--coverage-line")
        if self.toggle:
            flags.append("--coverage-toggle")
        if self.user:
            flags.append("--coverage-user")
        
        return flags


@dataclass
class OptimizationConfig:
    output_split: int = 20000
    output_split_cfuncs: int = 5000
    unroll_count: int = 64
    unroll_stmts: int = 30000
    x_assign: str = "fast"
    x_initial: str = "fast"
    
    def get_flags(self) -> List[str]:
        """Optimization flag'lerini döndür."""
        return [
            f"--output-split {self.output_split}",
            f"--output-split-cfuncs {self.output_split_cfuncs}",
            f"--unroll-count {self.unroll_count}",
            f"--unroll-stmts {self.unroll_stmts}",
            f"--x-assign {self.x_assign}",
            f"--x-initial {self.x_initial}",
        ]


@dataclass
class FeaturesConfig:
    vpi: bool = False
    hierarchical: bool = False
    savable: bool = False
    debug_check: bool = False
    
    def get_flags(self) -> List[str]:
        """Feature flag'lerini döndür."""
        flags = []
        if self.vpi:
            flags.append("--vpi")
        if self.hierarchical:
            flags.append("--hierarchical")
        if self.savable:
            flags.append("--savable")
        if self.debug_check:
            flags.append("--debug-check")
        return flags


@dataclass
class LoggingConfig:
    fast_sim: bool = False
    bp_log: bool = False
    bp_verbose: bool = False
    commit_trace: bool = True
    pipeline_log: bool = True
    ram_log: bool = True
    uart_log: bool = True
    
    def get_defines(self) -> List[str]:
        """SV define'ları döndür."""
        defines = []
        if self.fast_sim:
            defines.append("+define+SIM_FAST")
        if self.bp_log:
            defines.append("+define+LOG_BP")
        if self.bp_verbose:
            defines.append("+define+LOG_BP_VERBOSE")
        if self.commit_trace:
            defines.append("+define+LOG_COMMIT")
        if self.pipeline_log:
            defines.append("+define+LOG_PIPELINE")
        if self.ram_log:
            defines.append("+define+LOG_RAM")
        if self.uart_log:
            defines.append("+define+LOG_UART")
        return defines


@dataclass
class WarningsConfig:
    fatal: bool = False
    lint: bool = False
    style: bool = False
    width: bool = False
    unused: bool = False
    unoptflat: bool = False
    
    def get_flags(self) -> List[str]:
        """Warning suppression flag'lerini döndür."""
        flags = []
        if not self.fatal:
            flags.append("--Wno-fatal")
        if not self.lint:
            flags.append("--Wno-lint")
        if not self.style:
            flags.append("--Wno-style")
        if not self.width:
            flags.extend(["--Wno-WIDTH", "--Wno-WIDTHEXPAND", "--Wno-WIDTHTRUNC"])
        if not self.unused:
            flags.extend(["--Wno-UNUSED", "--Wno-UNDRIVEN"])
        if not self.unoptflat:
            flags.append("--Wno-UNOPTFLAT")
        return flags


@dataclass
class VerilatorConfig:
    """Ana konfigürasyon sınıfı."""
    simulation: SimulationConfig = field(default_factory=SimulationConfig)
    build: BuildConfig = field(default_factory=BuildConfig)
    trace: TraceConfig = field(default_factory=TraceConfig)
    coverage: CoverageConfig = field(default_factory=CoverageConfig)
    optimization: OptimizationConfig = field(default_factory=OptimizationConfig)
    features: FeaturesConfig = field(default_factory=FeaturesConfig)
    logging: LoggingConfig = field(default_factory=LoggingConfig)
    warnings: WarningsConfig = field(default_factory=WarningsConfig)
    
    # Meta bilgiler
    config_file: Optional[Path] = None
    local_config_file: Optional[Path] = None
    profile_name: Optional[str] = None
    config_warnings: List[str] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════════════
# Config Validation
# ═══════════════════════════════════════════════════════════════════════════
class ConfigValidator:
    """Konfigürasyon doğrulayıcı."""
    
    def __init__(self, schema: dict):
        self.schema = schema
        self.warnings: List[str] = []
        self.errors: List[str] = []
    
    def validate(self, data: dict, path: str = "") -> bool:
        """Konfigürasyonu doğrula ve bilinmeyen key'ler için uyarı üret."""
        # Özel key'leri atla
        skip_keys = {"$schema", "_comment", "_description", "profiles"}
        
        for key in data:
            if key in skip_keys:
                continue
            
            full_path = f"{path}.{key}" if path else key
            
            if key not in self.schema:
                self.warnings.append(f"Bilinmeyen parametre: '{full_path}'")
            elif isinstance(data[key], dict) and isinstance(self.schema.get(key), dict):
                # Alt key'ler için bir sonraki seviye schema
                if "type" in self.schema[key]:
                    # Bu bir leaf node, dict beklenmiyordu
                    self.warnings.append(f"'{full_path}' için dict değil skaler değer bekleniyor")
                else:
                    self.validate(data[key], self.schema[key], full_path)
        
        return len(self.errors) == 0
    
    def validate(self, data: dict, schema: dict = None, path: str = "") -> bool:
        """Konfigürasyonu doğrula."""
        if schema is None:
            schema = self.schema
        
        skip_keys = {"$schema", "_comment", "_description", "profiles"}
        
        for key in data:
            if key in skip_keys:
                continue
            
            full_path = f"{path}.{key}" if path else key
            
            if key not in schema:
                self.warnings.append(f"Bilinmeyen parametre: '{full_path}'")
            elif isinstance(data[key], dict):
                if isinstance(schema.get(key), dict) and "type" not in schema[key]:
                    self.validate(data[key], schema[key], full_path)
        
        return len(self.errors) == 0


# ═══════════════════════════════════════════════════════════════════════════
# Config Loading
# ═══════════════════════════════════════════════════════════════════════════
def deep_merge(base: dict, override: dict) -> dict:
    """İki dict'i derin merge et."""
    result = copy.deepcopy(base)
    
    for key, value in override.items():
        if key in result and isinstance(result[key], dict) and isinstance(value, dict):
            result[key] = deep_merge(result[key], value)
        else:
            result[key] = copy.deepcopy(value)
    
    return result


def apply_profile(data: dict, profile_name: str) -> dict:
    """Profil ayarlarını uygula."""
    profiles = data.get("profiles", {})
    
    if profile_name not in profiles:
        available = ", ".join(profiles.keys())
        raise ValueError(f"Profil bulunamadı: '{profile_name}'. Mevcut: {available}")
    
    profile = profiles[profile_name]
    
    # Profili base config'e merge et
    result = copy.deepcopy(data)
    for section, values in profile.items():
        if section.startswith("_"):
            continue
        if section in result and isinstance(values, dict):
            result[section] = deep_merge(result[section], values)
        else:
            result[section] = values
    
    return result


def dict_to_config(data: dict) -> VerilatorConfig:
    """Dict'i VerilatorConfig'e dönüştür."""
    config = VerilatorConfig()
    
    if "simulation" in data:
        sim = data["simulation"]
        config.simulation = SimulationConfig(
            max_cycles=sim.get("max_cycles", 100000),
            timeout=sim.get("timeout", 0),
            threads=str(sim.get("threads", "auto")),
            seed=str(sim.get("seed", "auto")),
        )
    
    if "build" in data:
        build = data["build"]
        config.build = BuildConfig(
            mode=build.get("mode", "release"),
            jobs=str(build.get("jobs", "auto")),
            opt_level=build.get("opt_level", "-O3"),
            cpp_standard=build.get("cpp_standard", "c++17"),
        )
    
    if "trace" in data:
        trace = data["trace"]
        config.trace = TraceConfig(
            enabled=trace.get("enabled", True),
            format=trace.get("format", "fst"),
            depth=trace.get("depth", 99),
            structs=trace.get("structs", True),
            params=trace.get("params", True),
            threads=trace.get("threads", 1),
            underscore=trace.get("underscore", False),
        )
    
    if "coverage" in data:
        cov = data["coverage"]
        config.coverage = CoverageConfig(
            enabled=cov.get("enabled", False),
            line=cov.get("line", True),
            toggle=cov.get("toggle", True),
            user=cov.get("user", False),
        )
    
    if "optimization" in data:
        opt = data["optimization"]
        config.optimization = OptimizationConfig(
            output_split=opt.get("output_split", 20000),
            output_split_cfuncs=opt.get("output_split_cfuncs", 5000),
            unroll_count=opt.get("unroll_count", 64),
            unroll_stmts=opt.get("unroll_stmts", 30000),
            x_assign=opt.get("x_assign", "fast"),
            x_initial=opt.get("x_initial", "fast"),
        )
    
    if "features" in data:
        feat = data["features"]
        config.features = FeaturesConfig(
            vpi=feat.get("vpi", False),
            hierarchical=feat.get("hierarchical", False),
            savable=feat.get("savable", False),
            debug_check=feat.get("debug_check", False),
        )
    
    if "logging" in data:
        log = data["logging"]
        config.logging = LoggingConfig(
            fast_sim=log.get("fast_sim", False),
            bp_log=log.get("bp_log", False),
            bp_verbose=log.get("bp_verbose", False),
            commit_trace=log.get("commit_trace", True),
            pipeline_log=log.get("pipeline_log", True),
            ram_log=log.get("ram_log", True),
            uart_log=log.get("uart_log", True),
        )
    
    if "warnings" in data:
        warns = data["warnings"]
        config.warnings = WarningsConfig(
            fatal=warns.get("fatal", False),
            lint=warns.get("lint", False),
            style=warns.get("style", False),
            width=warns.get("width", False),
            unused=warns.get("unused", False),
            unoptflat=warns.get("unoptflat", False),
        )
    
    return config


def load_config(
    config_path: Optional[Path] = None,
    local_path: Optional[Path] = None,
    profile: Optional[str] = None,
    strict: bool = False,
) -> VerilatorConfig:
    """
    Konfigürasyonu yükle.
    
    Args:
        config_path: Ana config dosyası
        local_path: Lokal override dosyası
        profile: Uygulanacak profil
        strict: Uyarıları hata olarak ele al
    
    Returns:
        VerilatorConfig nesnesi
    """
    # Varsayılan path
    if config_path is None:
        script_dir = Path(__file__).parent.parent.parent
        config_path = script_dir / "config" / "verilator.json"
    
    config_path = Path(config_path)
    
    if not config_path.exists():
        warn(f"Config dosyası bulunamadı: {config_path}")
        return VerilatorConfig()
    
    # Ana config'i oku
    with open(config_path) as f:
        data = json.load(f)
    
    # Lokal override varsa merge et
    if local_path is None:
        local_path = config_path.parent / "verilator.local.json"
    
    if local_path.exists():
        with open(local_path) as f:
            local_data = json.load(f)
        data = deep_merge(data, local_data)
    
    # Profil uygula
    if profile:
        try:
            data = apply_profile(data, profile)
            info(f"Profil uygulandı: {profile}")
        except ValueError as e:
            error(str(e))
            if strict:
                sys.exit(1)
    
    # Validate
    validator = ConfigValidator(CONFIG_SCHEMA)
    validator.validate(data)
    
    for w in validator.warnings:
        warn(w)
    
    if strict and validator.warnings:
        error("Strict modda uyarılar hata olarak değerlendiriliyor.")
        sys.exit(1)
    
    # Config nesnesine dönüştür
    config = dict_to_config(data)
    config.config_file = config_path
    config.local_config_file = local_path if local_path.exists() else None
    config.profile_name = profile
    config.config_warnings = validator.warnings
    
    return config


# ═══════════════════════════════════════════════════════════════════════════
# Config Summary
# ═══════════════════════════════════════════════════════════════════════════
def _kv(key: str, value: Any, indent: int = 4) -> None:
    """Key-value çifti yazdır."""
    spaces = " " * indent
    key_fmt = f"{Color.DIM}{key}:{Color.RESET}"
    print(f"{spaces}{key_fmt:20} {value}")

def _section(title: str) -> None:
    """Section başlığı yazdır."""
    print(f"\n  {Color.BOLD}{Color.WHITE}▸ {title}{Color.RESET}")

def _bool_str(val: bool) -> str:
    """Boolean değeri renkli string'e çevir."""
    if val:
        return f"{Color.GREEN}Yes{Color.RESET}"
    return f"{Color.DIM}No{Color.RESET}"

def print_config_summary(config: VerilatorConfig) -> None:
    """Konfigürasyon özetini yazdır."""
    print()
    print(f"{Color.CYAN}{'═' * 60}{Color.RESET}")
    print(f"{Color.CYAN}  Verilator Konfigürasyon Özeti{Color.RESET}")
    print(f"{Color.CYAN}{'═' * 60}{Color.RESET}")
    
    # Kaynak bilgisi
    if config.config_file or config.profile_name:
        print()
        if config.config_file:
            _kv("Config", config.config_file)
        if config.local_config_file:
            _kv("Local", config.local_config_file)
        if config.profile_name:
            _kv("Profil", f"{Color.CYAN}{config.profile_name}{Color.RESET}")
    
    _section("Simulation")
    _kv("Max Cycles", f"{config.simulation.max_cycles:,}")
    _kv("Threads", config.simulation.threads)
    _kv("Seed", config.simulation.seed)
    
    _section("Build")
    _kv("Mode", config.build.mode)
    _kv("Opt Level", config.build.opt_level)
    _kv("Jobs", config.build.jobs)
    _kv("C++ Std", config.build.cpp_standard)
    
    _section("Trace")
    _kv("Enabled", _bool_str(config.trace.enabled))
    if config.trace.enabled:
        _kv("Format", config.trace.format.upper())
        _kv("Depth", config.trace.depth)
    
    _section("Coverage")
    _kv("Enabled", _bool_str(config.coverage.enabled))
    if config.coverage.enabled:
        parts = []
        if config.coverage.line:
            parts.append("line")
        if config.coverage.toggle:
            parts.append("toggle")
        if config.coverage.user:
            parts.append("user")
        _kv("Types", ", ".join(parts))
    
    _section("Logging")
    _kv("Fast Sim", _bool_str(config.logging.fast_sim))
    _kv("Commit Trace", _bool_str(config.logging.commit_trace))
    _kv("BP Log", _bool_str(config.logging.bp_log))
    
    # Uyarılar
    if config.config_warnings:
        print()
        print(f"  {Color.YELLOW}⚠ {len(config.config_warnings)} uyarı{Color.RESET}")
        for w in config.config_warnings[:3]:
            print(f"    {Color.DIM}• {w}{Color.RESET}")
        if len(config.config_warnings) > 3:
            print(f"    {Color.DIM}... ve {len(config.config_warnings) - 3} uyarı daha{Color.RESET}")
    
    print(f"\n{Color.CYAN}{'═' * 60}{Color.RESET}\n")


# ═══════════════════════════════════════════════════════════════════════════
# CLI Interface
# ═══════════════════════════════════════════════════════════════════════════
def main():
    """CLI entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="CERES RISC-V Verilator Configuration Manager",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    
    parser.add_argument(
        "--config", "-c",
        type=Path,
        help="Ana konfigürasyon dosyası"
    )
    
    parser.add_argument(
        "--local", "-l",
        type=Path,
        help="Lokal override dosyası"
    )
    
    parser.add_argument(
        "--profile", "-p",
        help="Uygulanacak profil (fast, debug, coverage, benchmark)"
    )
    
    parser.add_argument(
        "--strict", "-s",
        action="store_true",
        help="Uyarıları hata olarak ele al"
    )
    
    parser.add_argument(
        "--quiet", "-q",
        action="store_true",
        help="Sadece hataları göster"
    )
    
    parser.add_argument(
        "--no-color",
        action="store_true",
        help="Renkleri devre dışı bırak"
    )
    
    parser.add_argument(
        "--validate",
        action="store_true",
        help="Sadece doğrula, özet gösterme"
    )
    
    parser.add_argument(
        "--show-flags",
        action="store_true",
        help="Verilator flag'lerini göster"
    )
    
    args = parser.parse_args()
    
    # Renk desteği
    if args.no_color or not supports_color():
        Color.disable()
    
    # Config yükle
    config = load_config(
        config_path=args.config,
        local_path=args.local,
        profile=args.profile,
        strict=args.strict,
    )
    
    if args.validate:
        if config.config_warnings:
            print(f"{Color.YELLOW}Uyarılar:{Color.RESET}")
            for w in config.config_warnings:
                print(f"  • {w}")
            return 1 if args.strict else 0
        else:
            print(f"{Color.GREEN}✓ Konfigürasyon geçerli{Color.RESET}")
            return 0
    
    if args.show_flags:
        print("Verilator Flags:")
        print("  Trace:", " ".join(config.trace.get_flags()))
        print("  Coverage:", " ".join(config.coverage.get_flags()))
        print("  Optimization:", " ".join(config.optimization.get_flags()))
        print("  Features:", " ".join(config.features.get_flags()))
        print("  Warnings:", " ".join(config.warnings.get_flags()))
        print("  Defines:", " ".join(config.logging.get_defines()))
        return 0
    
    if not args.quiet:
        print_config_summary(config)
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
