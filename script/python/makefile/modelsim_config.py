#!/usr/bin/env python3
"""
CERES RISC-V — ModelSim Configuration Manager

JSON konfigürasyon dosyasını okur, doğrular ve Python dict'e dönüştürür.
Schema validation, profile merging ve uyarı sistemi içerir.

Kullanım:
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
# Bu schema, JSON dosyasındaki tüm geçerli alanları ve varsayılan değerlerini tanımlar

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
    "lint": {
        "enabled": {"type": "bool", "default": True},
        "mode": {"type": "str", "default": "default", "choices": ["default", "fast", "full"]},
        "pedantic": {"type": "bool", "default": False},
        "style_checks": {"type": "bool", "default": True},
        "width_checks": {"type": "bool", "default": True},
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

# Bilinen üst-düzey anahtarlar (profiles, $schema, _comment gibi özel alanlar dahil)
KNOWN_TOP_KEYS = set(CONFIG_SCHEMA.keys()) | {"profiles", "$schema", "_comment", "_version"}


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
class LintConfig:
    enabled: bool = True
    mode: str = "default"
    pedantic: bool = False
    style_checks: bool = True
    width_checks: bool = True


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
        """Coverage spec string oluştur (e.g., 'sbceft')"""
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
        """Delay mode flag'ını döndür"""
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
    """Ana konfigürasyon container'ı"""
    simulation: SimulationConfig = field(default_factory=SimulationConfig)
    compile: CompileConfig = field(default_factory=CompileConfig)
    lint: LintConfig = field(default_factory=LintConfig)
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
    
    # Uyarılar
    warnings: List[str] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════════════
# Validation Functions
# ═══════════════════════════════════════════════════════════════════════════
class ConfigValidator:
    """Konfigürasyon doğrulama sınıfı"""
    
    def __init__(self):
        self.warnings: List[str] = []
        self.errors: List[str] = []
    
    def validate_type(self, value: Any, expected_type: str, path: str) -> bool:
        """Değer tipini doğrula"""
        type_map = {
            "str": str,
            "bool": bool,
            "int": int,
            "float": (int, float),
            "list": list,
        }
        expected = type_map.get(expected_type)
        if expected and not isinstance(value, expected):
            self.errors.append(f"{path}: Beklenen tip '{expected_type}', alınan '{type(value).__name__}'")
            return False
        return True
    
    def validate_choices(self, value: Any, choices: List[Any], path: str) -> bool:
        """Değerin geçerli seçenekler arasında olup olmadığını kontrol et"""
        if value not in choices:
            self.errors.append(f"{path}: '{value}' geçersiz. Geçerli değerler: {choices}")
            return False
        return True
    
    def validate_range(self, value: int, min_val: Optional[int], max_val: Optional[int], path: str) -> bool:
        """Sayısal değerin aralıkta olup olmadığını kontrol et"""
        if min_val is not None and value < min_val:
            self.errors.append(f"{path}: {value} minimum değer {min_val}'den küçük")
            return False
        if max_val is not None and value > max_val:
            self.errors.append(f"{path}: {value} maksimum değer {max_val}'den büyük")
            return False
        return True
    
    def check_unknown_keys(self, data: Dict, schema: Dict, path: str = "") -> None:
        """Bilinmeyen anahtarları tespit et"""
        if not isinstance(data, dict):
            return
        
        known_keys = set(schema.keys()) if isinstance(schema, dict) else set()
        
        for key in data.keys():
            if key.startswith("_"):  # _comment gibi özel alanları atla
                continue
            if key not in known_keys:
                self.warnings.append(f"{path}.{key}" if path else key)
    
    def validate_section(self, data: Dict, section_name: str, schema: Dict) -> Dict:
        """Bir bölümü doğrula ve varsayılanlarla doldur"""
        result = {}
        section_data = data.get(section_name, {})
        
        if not isinstance(section_data, dict):
            self.errors.append(f"{section_name}: Dict bekleniyor, {type(section_data).__name__} alındı")
            section_data = {}
        
        # Bilinmeyen anahtarları kontrol et
        known_keys = set(schema.keys())
        for key in section_data.keys():
            if key.startswith("_"):
                continue
            if key not in known_keys:
                self.warnings.append(f"{section_name}.{key}: Bilinmeyen parametre")
        
        # Her alanı doğrula
        for field_name, field_schema in schema.items():
            path = f"{section_name}.{field_name}"
            
            if field_name in section_data:
                value = section_data[field_name]
                
                # Tip kontrolü
                self.validate_type(value, field_schema["type"], path)
                
                # Seçenek kontrolü
                if "choices" in field_schema:
                    self.validate_choices(value, field_schema["choices"], path)
                
                # Aralık kontrolü
                if field_schema["type"] == "int":
                    self.validate_range(
                        value,
                        field_schema.get("min"),
                        field_schema.get("max"),
                        path
                    )
                
                result[field_name] = value
            else:
                # Varsayılan değeri kullan
                result[field_name] = field_schema["default"]
        
        return result


# ═══════════════════════════════════════════════════════════════════════════
# Config Loading Functions
# ═══════════════════════════════════════════════════════════════════════════
def find_config_files(config_dir: Optional[Path] = None) -> tuple[Optional[Path], Optional[Path]]:
    """Konfigürasyon dosyalarını bul"""
    if config_dir is None:
        # Script dizinine göre bul
        script_dir = Path(__file__).parent.parent.parent  # script/python/makefile -> script
        config_dir = script_dir / "config"
    
    main_config = config_dir / "modelsim.json"
    local_config = config_dir / "modelsim.local.json"
    
    if not main_config.exists():
        return None, None
    
    return main_config, local_config if local_config.exists() else None


def merge_dicts(base: Dict, override: Dict) -> Dict:
    """İki dict'i recursive olarak birleştir"""
    result = base.copy()
    
    for key, value in override.items():
        if key in result and isinstance(result[key], dict) and isinstance(value, dict):
            result[key] = merge_dicts(result[key], value)
        else:
            result[key] = value
    
    return result


def apply_profile(config_data: Dict, profile_name: str) -> Dict:
    """Profili uygula"""
    profiles = config_data.get("profiles", {})
    
    if profile_name not in profiles:
        available = list(profiles.keys())
        raise ValueError(f"Profil bulunamadı: '{profile_name}'. Mevcut profiller: {available}")
    
    profile = profiles[profile_name]
    
    # Profildeki her bölümü base config ile birleştir
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
    Konfigürasyonu yükle ve doğrula.
    
    Args:
        config_file: Ana konfigürasyon dosyası (None ise otomatik bul)
        local_config_file: Lokal override dosyası
        profile: Uygulanacak profil adı
        strict: True ise uyarıları hata olarak ele al
        quiet: True ise uyarıları gösterme
    
    Returns:
        ModelSimConfig: Doğrulanmış konfigürasyon nesnesi
    
    Raises:
        FileNotFoundError: Konfigürasyon dosyası bulunamazsa
        ValueError: Geçersiz konfigürasyon
    """
    # Dosyaları bul
    if config_file is None:
        config_file, auto_local = find_config_files()
        if local_config_file is None:
            local_config_file = auto_local
    
    if config_file is None or not config_file.exists():
        raise FileNotFoundError(f"Konfigürasyon dosyası bulunamadı: {config_file}")
    
    # JSON'ları oku
    with open(config_file, 'r', encoding='utf-8') as f:
        config_data = json.load(f)
    
    # Lokal override'ı birleştir
    if local_config_file and local_config_file.exists():
        with open(local_config_file, 'r', encoding='utf-8') as f:
            local_data = json.load(f)
        config_data = merge_dicts(config_data, local_data)
        if not quiet:
            info(f"Lokal override yüklendi: {local_config_file.name}")
    
    # Profili uygula
    if profile:
        config_data = apply_profile(config_data, profile)
        if not quiet:
            info(f"Profil uygulandı: {profile}")
    
    # Doğrulama
    validator = ConfigValidator()
    
    # Üst düzey bilinmeyen anahtarları kontrol et
    for key in config_data.keys():
        if key not in KNOWN_TOP_KEYS and not key.startswith("_"):
            validator.warnings.append(f"Bilinmeyen üst düzey anahtar: '{key}'")
    
    # Her bölümü doğrula
    validated = {}
    for section_name, section_schema in CONFIG_SCHEMA.items():
        validated[section_name] = validator.validate_section(config_data, section_name, section_schema)
    
    # Uyarıları göster
    if validator.warnings and not quiet:
        print(f"\n{Color.YELLOW}{'═' * 60}{Color.RESET}")
        print(f"{Color.YELLOW}  ⚠ Konfigürasyon Uyarıları ({len(validator.warnings)} adet){Color.RESET}")
        print(f"{Color.YELLOW}{'═' * 60}{Color.RESET}")
        for warning in validator.warnings:
            print(f"  {Color.YELLOW}•{Color.RESET} {warning}")
        print(f"{Color.YELLOW}{'═' * 60}{Color.RESET}\n")
        
        if strict:
            raise ValueError(f"Strict modda {len(validator.warnings)} uyarı bulundu")
    
    # Hataları kontrol et
    if validator.errors:
        print(f"\n{Color.RED}{'═' * 60}{Color.RESET}")
        print(f"{Color.RED}  ✗ Konfigürasyon Hataları ({len(validator.errors)} adet){Color.RESET}")
        print(f"{Color.RED}{'═' * 60}{Color.RESET}")
        for err in validator.errors:
            print(f"  {Color.RED}•{Color.RESET} {err}")
        print(f"{Color.RED}{'═' * 60}{Color.RESET}\n")
        raise ValueError(f"Konfigürasyonda {len(validator.errors)} hata bulundu")
    
    # Dataclass'lara dönüştür
    result = ModelSimConfig(
        simulation=SimulationConfig(**validated["simulation"]),
        compile=CompileConfig(**validated["compile"]),
        lint=LintConfig(**validated["lint"]),
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

def print_config_summary(config: ModelSimConfig) -> None:
    """Konfigürasyon özetini yazdır"""
    print()
    print(f"{Color.CYAN}{'═' * 60}{Color.RESET}")
    print(f"{Color.CYAN}  ModelSim Konfigürasyon Özeti{Color.RESET}")
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
    _kv("Sim Time", config.simulation.sim_time)
    _kv("Resolution", config.simulation.time_resolution)
    _kv("Voptargs", config.simulation.voptargs)
    
    _section("Compile")
    _kv("SV Mode", _bool_str(config.compile.sv_mode))
    _kv("MFCU", _bool_str(config.compile.mfcu))
    _kv("Inputport", config.compile.svinputport)
    
    _section("Lint")
    _kv("Enabled", _bool_str(config.lint.enabled))
    if config.lint.enabled:
        _kv("Mode", config.lint.mode)
        _kv("Pedantic", _bool_str(config.lint.pedantic))
    
    _section("Coverage")
    _kv("Enabled", _bool_str(config.coverage.enabled))
    if config.coverage.enabled:
        _kv("Spec", f"+cover={config.coverage.get_spec_string()}")
    
    _section("GLS")
    _kv("Timing", _bool_str(config.gls.timing_checks))
    _kv("Delay Mode", config.gls.delay_mode)
    
    # Uyarılar
    if config.warnings:
        print()
        print(f"  {Color.YELLOW}⚠ {len(config.warnings)} uyarı{Color.RESET}")
        for w in config.warnings[:3]:  # Max 3 uyarı göster
            print(f"    {Color.DIM}• {w}{Color.RESET}")
        if len(config.warnings) > 3:
            print(f"    {Color.DIM}... ve {len(config.warnings) - 3} uyarı daha{Color.RESET}")
    
    print(f"\n{Color.CYAN}{'═' * 60}{Color.RESET}\n")


# ═══════════════════════════════════════════════════════════════════════════
# CLI Interface
# ═══════════════════════════════════════════════════════════════════════════
def main():
    """CLI entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="CERES RISC-V ModelSim Configuration Manager",
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
        help="Uygulanacak profil (fast, debug, lint_only, coverage, gls)"
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
        "--summary",
        action="store_true",
        help="Konfigürasyon özetini göster"
    )
    
    parser.add_argument(
        "--get",
        help="Belirli bir değeri al (örn: simulation.sim_time)"
    )
    
    parser.add_argument(
        "--validate",
        action="store_true",
        help="Konfigürasyonu doğrula"
    )

    parser.add_argument(
        "--make",
        action="store_true",
        help="Makefile için Make değişkenleri çıktısı (Make fragment)"
    )
    
    parser.add_argument(
        "--no-color",
        action="store_true",
        help="Renkli çıktıyı devre dışı bırak"
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
            # Belirli bir değeri al
            parts = args.get.split(".")
            value = config
            for part in parts:
                if hasattr(value, part):
                    value = getattr(value, part)
                else:
                    error(f"Alan bulunamadı: {args.get}")
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
            print(f"MODELSIM_VOPTARGS ?= {config.simulation.voptargs}")
            if config.simulation.quiet:
                print("MODELSIM_QUIET ?= -quiet")

            # Compile settings
            print(f"MODELSIM_SV_MODE ?= {'-sv' if config.compile.sv_mode else ''}")
            print(f"MODELSIM_MFCU ?= {'-mfcu' if config.compile.mfcu else '-sfcu'}")
            print(f"MODELSIM_SVINPUTPORT ?= {config.compile.svinputport}")

            # Lint
            print(f"MODELSIM_LINT_ENABLED ?= {fmt_bool(config.lint.enabled)}")
            print(f"MODELSIM_LINT_MODE ?= {config.lint.mode}")
            if config.lint.pedantic:
                print('MODELSIM_PEDANTIC ?= -pedanticerrors')

            # Debug
            print(f"MODELSIM_ACC ?= {config.debug.acc}")
            if config.debug.fsmdebug:
                print('MODELSIM_FSMDEBUG ?= -fsmdebug')
            if config.debug.classdebug:
                print('MODELSIM_CLASSDEBUG ?= -classdebug')
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
            if not config.gls.specify_delays:
                print('MODELSIM_NOSPECIFY ?= +nospecify')
            print(f"MODELSIM_DELAY_MODE ?= {config.gls.get_delay_flag()}")

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
            # Varsayılan: özet göster
            print_config_summary(config)
            return 0
    
    except FileNotFoundError as e:
        error(str(e))
        return 1
    except ValueError as e:
        error(str(e))
        return 1
    except json.JSONDecodeError as e:
        error(f"JSON parse hatası: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
