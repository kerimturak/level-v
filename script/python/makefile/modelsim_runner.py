#!/usr/bin/env python3
"""
CERES RISC-V — ModelSim/Questa Simulation Runner

Bu script ModelSim simülasyonunu çalıştırır ve log dosyalarını yönetir.
JSON konfigürasyon dosyasından ayarları okur.

Kullanım:
    python3 modelsim_runner.py --test=rv32ui-p-add --work-dir=build/work ...
    python3 modelsim_runner.py --test=rv32ui-p-add --profile=debug
    
Debug:
    CERES_DEBUG=1 python3 modelsim_runner.py --test rv32ui-p-add
    python3 modelsim_runner.py --test rv32ui-p-add --debug
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional, List

# Aynı dizindeki config modülünü import et
try:
    from modelsim_config import (
        load_config, 
        ModelSimConfig, 
        print_config_summary,
        Color as ConfigColor
    )
    HAS_CONFIG_MODULE = True
except ImportError:
    HAS_CONFIG_MODULE = False

# Debug logger import
try:
    from debug_logger import DebugLogger, create_logger
except ImportError:
    # Fallback: dummy logger
    class DebugLogger:
        def __init__(self, *args, **kwargs): pass
        def section(self, *args, **kwargs): pass
        def param(self, *args, **kwargs): pass
        def params_from_dataclass(self, *args, **kwargs): pass
        def params_from_dict(self, *args, **kwargs): pass
        def command(self, *args, **kwargs): pass
        def note(self, *args, **kwargs): pass
        def warning(self, *args, **kwargs): pass
        def error(self, *args, **kwargs): pass
        def success(self, *args, **kwargs): pass
        def file_check(self, *args, **kwargs): return True
        def result(self, *args, **kwargs): pass
        def save(self): return None
        def __enter__(self): return self
        def __exit__(self, *args): pass
    
    def create_logger(*args, **kwargs):
        return DebugLogger()


# ═══════════════════════════════════════════════════════════════════════════
# ANSI Colors
# ═══════════════════════════════════════════════════════════════════════════
class Color:
    RED = "\033[0;31m"
    GREEN = "\033[0;32m"
    YELLOW = "\033[0;33m"
    CYAN = "\033[0;36m"
    MAGENTA = "\033[0;35m"
    BLUE = "\033[0;34m"
    WHITE = "\033[1;37m"
    RESET = "\033[0m"
    BOLD = "\033[1m"
    DIM = "\033[2m"

    @classmethod
    def disable(cls):
        for attr in ['RED', 'GREEN', 'YELLOW', 'CYAN', 'MAGENTA', 'BLUE', 'WHITE', 'RESET', 'BOLD', 'DIM']:
            setattr(cls, attr, "")


def info(msg: str) -> None:
    print(f"{Color.CYAN}[INFO]{Color.RESET} {msg}")


def warn(msg: str) -> None:
    print(f"{Color.YELLOW}[WARN]{Color.RESET} {msg}")


def error(msg: str) -> None:
    print(f"{Color.RED}[ERROR]{Color.RESET} {msg}", file=sys.stderr)


def success(msg: str) -> None:
    print(f"{Color.GREEN}[OK]{Color.RESET} {msg}")


def header(title: str, char: str = "═") -> None:
    """Renkli başlık banner'ı yazdır"""
    width = 60
    line = char * width
    print(f"\n{Color.CYAN}{line}{Color.RESET}")
    print(f"{Color.CYAN}{Color.BOLD}  {title}{Color.RESET}")
    print(f"{Color.CYAN}{line}{Color.RESET}")


def subheader(title: str) -> None:
    """Alt başlık yazdır"""
    print(f"\n{Color.MAGENTA}▶ {title}{Color.RESET}")


def keyval(key: str, value: str, indent: int = 2) -> None:
    """Anahtar-değer çifti yazdır"""
    spaces = " " * indent
    print(f"{spaces}{Color.DIM}{key}:{Color.RESET} {Color.WHITE}{value}{Color.RESET}")


# ═══════════════════════════════════════════════════════════════════════════
# Runtime Configuration (CLI + JSON merged)
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class SimRunConfig:
    """Simülasyon runtime konfigürasyonu - CLI args + JSON config birleşimi"""
    # Test bilgileri
    test_name: str
    work_dir: Path
    log_dir: Path
    mem_dirs: List[Path]
    
    # Simülasyon ayarları (JSON'dan veya CLI'dan)
    sim_time: str = "20000ns"
    time_res: str = "ns"
    tb_level: str = "tb_wrapper"
    gui: bool = False
    quiet: bool = False
    
    # ModelSim ayarları
    voptargs: str = "+acc=npr"
    no_timing_checks: bool = True
    no_specify: bool = True
    delay_mode: str = "+typdelays"
    
    # Coverage
    coverage_enabled: bool = False
    coverage_spec: str = ""
    
    # Debug
    fsmdebug: bool = False
    classdebug: bool = False
    assertdebug: bool = False
    
    # Messages
    suppress_codes: List[str] = field(default_factory=list)
    
    # Dosya yolları (otomatik bulunacak)
    mem_file: Optional[Path] = None
    addr_file: Optional[Path] = None
    do_file: Optional[Path] = None
    
    # Ek define'lar
    defines: List[str] = field(default_factory=list)
    
    # Build dizini (addr dosyası için)
    build_dir: Optional[Path] = None
    
    # JSON config bilgisi
    json_config: Optional["ModelSimConfig"] = None
    profile_name: Optional[str] = None
    
    # Override tracking
    cli_overrides: List[str] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════════════
# Memory File Resolution
# ═══════════════════════════════════════════════════════════════════════════
def find_mem_file(test_name: str, mem_dirs: List[Path]) -> Optional[Path]:
    """Test için memory dosyasını bul."""
    for mem_dir in mem_dirs:
        if not mem_dir.exists():
            continue
        for ext in [".mem", ".hex"]:
            mem_file = mem_dir / f"{test_name}{ext}"
            if mem_file.exists():
                return mem_file.resolve()
    return None


def find_addr_file(test_name: str, build_dir: Path) -> Optional[Path]:
    """Pass/fail adres dosyasını bul."""
    possible_paths = [
        build_dir / "tests" / "riscv-tests" / "pass_fail_addr" / f"{test_name}_addr.txt",
        build_dir / "tests" / "riscv-arch-test" / "pass_fail_addr" / f"{test_name}_addr.txt",
        build_dir / "tests" / "pass_fail_addr" / f"{test_name}_addr.txt",
    ]
    
    for path in possible_paths:
        if path.exists():
            return path.resolve()
    return None


# ═══════════════════════════════════════════════════════════════════════════
# Log Directory Management
# ═══════════════════════════════════════════════════════════════════════════
def prepare_log_dir(log_dir: Path, clean: bool = True) -> None:
    """Log dizinini hazırla."""
    if clean and log_dir.exists():
        info(f"Önceki loglar temizleniyor: {log_dir}")
        shutil.rmtree(log_dir)
    log_dir.mkdir(parents=True, exist_ok=True)


# ═══════════════════════════════════════════════════════════════════════════
# VSIM Command Builder
# ═══════════════════════════════════════════════════════════════════════════
def build_vsim_command(config: SimRunConfig) -> List[str]:
    """vsim komut satırını oluştur."""
    cmd = ["vsim"]
    
    # GUI veya batch mode
    if not config.gui:
        cmd.append("-c")
    
    # Quiet mode
    if config.quiet:
        cmd.append("-quiet")
    
    # Work library ve top module
    cmd.append(f"{config.work_dir}.{config.tb_level}")
    
    # DO komutu
    if config.gui and config.do_file:
        cmd.extend(["-do", str(config.do_file)])
    else:
        cmd.extend(["-do", f"run {config.sim_time}; quit"])
    
    # Zaman çözünürlüğü
    cmd.extend(["-t", config.time_res])
    
    # Optimizasyon argümanları
    cmd.append(f"-voptargs={config.voptargs}")
    
    # Timing kontrolleri
    if config.no_timing_checks:
        cmd.append("+notimingchecks")
    if config.no_specify:
        cmd.append("+nospecify")
    if config.delay_mode:
        cmd.append(config.delay_mode)
    
    # Debug flags
    if config.fsmdebug:
        cmd.append("-fsmdebug")
    if config.classdebug:
        cmd.append("-classdebug")
    if config.assertdebug:
        cmd.append("-assertdebug")
    
    # Coverage
    if config.coverage_enabled and config.coverage_spec:
        cmd.append(f"+cover={config.coverage_spec}")
        cmd.append("-coverage")
    
    # Runtime plusargs (NOT +define+ - those must be at compile time)
    # Note: +define+ flags are preprocessor directives and must be passed to vlog, not vsim
    cmd.extend([
        f"+test_name={config.test_name}",
        "+simulator=modelsim",
    ])
    
    # Adres dosyası
    if config.addr_file:
        cmd.append(f"+addr_file={config.addr_file}")
    
    # Log dosyaları
    cmd.append(f"+trace_file={config.log_dir}/commit_trace.log")
    cmd.append(f"+log_path={config.log_dir}/ceres.log")
    cmd.append(f"+DUMP_FILE={config.log_dir}/waveform.wlf")
    
    # Memory dosyası
    if config.mem_file:
        cmd.append(f"+INIT_FILE={config.mem_file}")
    
    # Test adı
    cmd.append(f"+UVM_TESTNAME={config.test_name}")
    
    return cmd


# ═══════════════════════════════════════════════════════════════════════════
# Configuration Merge (JSON + CLI)
# ═══════════════════════════════════════════════════════════════════════════
def merge_config_with_cli(
    json_config: Optional["ModelSimConfig"],
    args: argparse.Namespace,
    mem_dirs: List[Path]
) -> SimRunConfig:
    """
    JSON konfigürasyonu ile CLI argümanlarını birleştir.
    CLI argümanları JSON'ı override eder.
    """
    cli_overrides = []
    
    # Varsayılan değerler
    defaults = {
        "sim_time": "20000ns",
        "time_res": "ns",
        "voptargs": "+acc=npr",
        "no_timing_checks": True,
        "no_specify": True,
        "delay_mode": "+typdelays",
        "quiet": False,
        "coverage_enabled": False,
        "coverage_spec": "",
        "fsmdebug": False,
        "classdebug": False,
        "assertdebug": False,
        "suppress_codes": [],
    }
    
    # JSON config varsa, değerleri al
    if json_config:
        defaults.update({
            "sim_time": json_config.simulation.sim_time,
            "time_res": json_config.simulation.time_resolution,
            "voptargs": json_config.simulation.voptargs,
            "quiet": json_config.simulation.quiet,
            "no_timing_checks": not json_config.gls.timing_checks,
            "no_specify": not json_config.gls.specify_delays,
            "delay_mode": json_config.gls.get_delay_flag(),
            "coverage_enabled": json_config.coverage.enabled,
            "coverage_spec": json_config.coverage.get_spec_string(),
            "fsmdebug": json_config.debug.fsmdebug,
            "classdebug": json_config.debug.classdebug,
            "assertdebug": json_config.debug.assertdebug,
            "suppress_codes": json_config.messages.suppress,
        })
    
    # CLI override'ları uygula
    # CLI'dan gelen değerler her zaman JSON'u override eder
    final = defaults.copy()
    
    # sim_time: CLI'dan geliyorsa kullan
    final["sim_time"] = args.sim_time
    if json_config and args.sim_time != json_config.simulation.sim_time:
        cli_overrides.append(f"sim_time={args.sim_time} (JSON: {json_config.simulation.sim_time})")
    
    # time_res: CLI'dan geliyorsa kullan  
    final["time_res"] = args.time_res
    if json_config and args.time_res != json_config.simulation.time_resolution:
        cli_overrides.append(f"time_res={args.time_res}")
    
    # voptargs: CLI'dan geliyorsa kullan
    final["voptargs"] = args.voptargs
    if json_config and args.voptargs != json_config.simulation.voptargs:
        cli_overrides.append(f"voptargs={args.voptargs}")
    
    if args.gui:
        cli_overrides.append("gui=True")
    
    # Uyarıları göster
    if cli_overrides and json_config:
        info(f"CLI override: {', '.join(cli_overrides)}")
    
    return SimRunConfig(
        test_name=args.test_name,
        work_dir=args.work_dir,
        log_dir=args.log_dir,
        mem_dirs=mem_dirs,
        sim_time=final["sim_time"],
        time_res=final["time_res"],
        tb_level=args.tb_level,
        gui=args.gui,
        quiet=final["quiet"],
        voptargs=final["voptargs"],
        no_timing_checks=final["no_timing_checks"],
        no_specify=final["no_specify"],
        delay_mode=final["delay_mode"],
        coverage_enabled=final["coverage_enabled"],
        coverage_spec=final["coverage_spec"],
        fsmdebug=final["fsmdebug"],
        classdebug=final["classdebug"],
        assertdebug=final["assertdebug"],
        suppress_codes=final["suppress_codes"],
        do_file=args.do_file,
        mem_file=args.mem_file,
        defines=args.defines or [],
        build_dir=args.build_dir,
        json_config=json_config,
        profile_name=args.profile if hasattr(args, 'profile') else None,
        cli_overrides=cli_overrides,
    )


# ═══════════════════════════════════════════════════════════════════════════
# Simulation Runner
# ═══════════════════════════════════════════════════════════════════════════
def run_simulation(config: SimRunConfig, logger: Optional[DebugLogger] = None) -> int:
    """Simülasyonu çalıştır ve sonucu döndür."""
    
    # Debug logger
    if logger is None:
        logger = DebugLogger("modelsim", config.log_dir, enabled=False)
    
    logger.section("Run Configuration")
    logger.params_from_dataclass(config, source="merged")
    
    # Başlık banner'ı
    print()
    header(f"CERES RISC-V Simulation")
    
    # Test bilgisi
    mode_str = f"{Color.CYAN}GUI{Color.RESET}" if config.gui else f"{Color.GREEN}Batch{Color.RESET}"
    print(f"  {Color.WHITE}Test:{Color.RESET}   {Color.YELLOW}{config.test_name}{Color.RESET}")
    print(f"  {Color.WHITE}Mode:{Color.RESET}   {mode_str}")
    
    # JSON config bilgisi
    if config.json_config:
        profile_str = f" → {Color.CYAN}{config.profile_name}{Color.RESET}" if config.profile_name else ""
        print(f"  {Color.WHITE}Config:{Color.RESET} JSON{profile_str}")
        if config.cli_overrides:
            print(f"  {Color.WHITE}CLI Overrides:{Color.RESET} {Color.DIM}{', '.join(config.cli_overrides)}{Color.RESET}")
    
    print()
    
    logger.section("File Discovery")
    
    # Memory dosyasını bul
    subheader("Dosya Arama")
    
    if not config.mem_file:
        config.mem_file = find_mem_file(config.test_name, config.mem_dirs)
        if not config.mem_file:
            logger.error(f"Memory file not found: {config.test_name}")
            logger.note(f"Searched dirs: {[str(d) for d in config.mem_dirs]}")
            error(f"Memory dosyası bulunamadı: {config.test_name}")
            error(f"Aranan dizinler: {[str(d) for d in config.mem_dirs]}")
            logger.result(False, 1, "Memory file not found")
            logger.save()
            return 1
    
    logger.param("mem_file", config.mem_file, "found")
    keyval("Memory", str(config.mem_file))
    
    # Adres dosyasını bul
    if config.build_dir:
        config.addr_file = find_addr_file(config.test_name, config.build_dir)
        if config.addr_file:
            logger.param("addr_file", config.addr_file, "found")
            keyval("Adres", str(config.addr_file))
        else:
            logger.note("Address file not found, skipping")
            print(f"  {Color.DIM}Adres dosyası bulunamadı, atlanıyor.{Color.RESET}")
    
    # Log dizinini hazırla
    prepare_log_dir(config.log_dir)
    logger.note(f"Log directory prepared: {config.log_dir}")
    
    # Komutu oluştur
    cmd = build_vsim_command(config)
    
    logger.section("Command")
    logger.command(cmd, "ModelSim vsim", config.log_dir)
    
    # Simülasyon ayarları özeti
    print()
    subheader("Simülasyon Ayarları")
    keyval("Sim Time", config.sim_time)
    keyval("Resolution", config.time_res)
    keyval("Log Dir", str(config.log_dir))
    if config.coverage_enabled:
        keyval("Coverage", f"{Color.GREEN}enabled{Color.RESET} ({config.coverage_spec})")
    
    # Log dosyası yolu
    run_log = config.log_dir / "modelsim_run.log"
    
    logger.section("Execution")
    
    # Simülasyon başlat
    print()
    subheader("Çalıştırılıyor")
    print(f"  {Color.DIM}$ vsim ...{Color.RESET}")
    print()
    
    start_time = datetime.now()
    logger.note(f"Simulation started at {start_time.isoformat()}")
    
    try:
        if config.gui:
            logger.note("Running in GUI mode")
            result = subprocess.run(cmd)
            exit_code = result.returncode
        else:
            with open(run_log, "w") as log_file:
                process = subprocess.Popen(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True
                )
                
                for line in process.stdout:
                    print(line, end="")
                    log_file.write(line)
                
                process.wait()
                exit_code = process.returncode
    
    except FileNotFoundError:
        logger.error("'vsim' command not found")
        error("'vsim' komutu bulunamadı. ModelSim kurulu ve PATH'de mi?")
        logger.result(False, 127, "vsim not found")
        logger.save()
        return 127
    except KeyboardInterrupt:
        logger.warning("Simulation interrupted by user")
        warn("Simülasyon kullanıcı tarafından durduruldu.")
        exit_code = 130
    
    end_time = datetime.now()
    elapsed = (end_time - start_time).total_seconds()
    
    logger.section("Results")
    logger.param("exit_code", exit_code, "execution")
    logger.param("elapsed_seconds", round(elapsed, 2), "execution")
    
    # Summary JSON oluştur
    summary = {
        "test": config.test_name,
        "simulator": "modelsim",
        "mem_file": str(config.mem_file) if config.mem_file else None,
        "exit_code": exit_code,
        "log_dir": str(config.log_dir),
        "sim_time": config.sim_time,
        "elapsed_seconds": round(elapsed, 2),
        "timestamp": end_time.isoformat(),
        "mode": "gui" if config.gui else "batch",
        "config": {
            "source": "json" if config.json_config else "cli",
            "profile": config.profile_name,
            "cli_overrides": config.cli_overrides,
        },
        "settings": {
            "time_resolution": config.time_res,
            "voptargs": config.voptargs,
            "coverage_enabled": config.coverage_enabled,
        }
    }
    
    summary_file = config.log_dir / "summary.json"
    with open(summary_file, "w") as f:
        json.dump(summary, f, indent=2)
    
    logger.note(f"Summary saved to: {summary_file}")
    
    # Sonuç banner'ı
    print()
    if exit_code == 0:
        logger.success(f"Simulation passed: {config.test_name}")
        logger.result(True, 0, "Simulation completed successfully", {
            "test": config.test_name,
            "elapsed": f"{elapsed:.2f}s",
            "log_dir": str(config.log_dir)
        })
        
        print(f"{Color.GREEN}{'═' * 60}{Color.RESET}")
        print(f"{Color.GREEN}  ✓ Simülasyon Başarılı{Color.RESET}")
        print(f"{Color.GREEN}{'═' * 60}{Color.RESET}")
        keyval("Test", config.test_name)
        keyval("Süre", f"{elapsed:.1f} saniye")
        keyval("Loglar", str(config.log_dir))
    else:
        logger.error(f"Simulation failed: {config.test_name} (exit={exit_code})")
        logger.result(False, exit_code, "Simulation failed", {
            "test": config.test_name,
            "elapsed": f"{elapsed:.2f}s",
            "log_dir": str(config.log_dir)
        })
        
        print(f"{Color.RED}{'═' * 60}{Color.RESET}")
        print(f"{Color.RED}  ✗ Simülasyon Başarısız (exit={exit_code}){Color.RESET}")
        print(f"{Color.RED}{'═' * 60}{Color.RESET}")
        keyval("Test", config.test_name)
        keyval("Loglar", str(config.log_dir))
        print(f"  {Color.DIM}Detaylar için: {run_log}{Color.RESET}")
    
    # Debug log kaydet
    debug_log_path = logger.save()
    if debug_log_path:
        print(f"  {Color.DIM}Debug log: {debug_log_path}{Color.RESET}")
    
    print()
    
    return exit_code


# ═══════════════════════════════════════════════════════════════════════════
# CLI Interface
# ═══════════════════════════════════════════════════════════════════════════
def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="CERES RISC-V ModelSim/Questa Simulation Runner",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
JSON Konfigürasyon:
  Ayarlar önce script/config/modelsim.json'dan okunur.
  CLI argümanları JSON değerlerini override eder.
  
Profiller:
  --profile ile önceden tanımlı profiller kullanılabilir:
    fast      - Hızlı simülasyon, minimal debug
    debug     - Tam debug özellikleri
    coverage  - Coverage toplama
    gls       - Gate-level simulation

Örnekler:
  %(prog)s --test=rv32ui-p-add --work-dir=build/work --log-dir=results/logs
  %(prog)s --test=rv32ui-p-add --profile=debug
  %(prog)s --test=rv32ui-p-add --gui --sim-time=50000ns
        """
    )
    
    # Zorunlu parametreler
    parser.add_argument(
        "--test", "-t",
        required=True,
        dest="test_name",
        help="Test adı (örn: rv32ui-p-add)"
    )
    
    parser.add_argument(
        "--work-dir", "-w",
        required=True,
        type=Path,
        help="ModelSim work dizini (örn: build/work)"
    )
    
    parser.add_argument(
        "--log-dir", "-l",
        required=True,
        type=Path,
        help="Log çıktı dizini"
    )
    
    parser.add_argument(
        "--mem-dirs", "-m",
        required=True,
        help="Memory dosyası arama dizinleri (boşlukla ayrılmış)"
    )
    
    # JSON config
    parser.add_argument(
        "--config", "-c",
        type=Path,
        help="JSON konfigürasyon dosyası (varsayılan: script/config/modelsim.json)"
    )
    
    parser.add_argument(
        "--profile", "-p",
        help="Kullanılacak profil (fast, debug, coverage, gls)"
    )
    
    parser.add_argument(
        "--no-config",
        action="store_true",
        help="JSON konfigürasyonu yükleme, sadece CLI args kullan"
    )
    
    # Opsiyonel parametreler
    parser.add_argument(
        "--build-dir", "-b",
        type=Path,
        help="Build dizini (addr dosyası için)"
    )
    
    parser.add_argument(
        "--sim-time", "-s",
        default="20000ns",
        help="Simülasyon süresi (varsayılan: 20000ns veya JSON'dan)"
    )
    
    parser.add_argument(
        "--tb-level",
        default="tb_wrapper",
        help="Top-level testbench modülü (varsayılan: tb_wrapper)"
    )
    
    parser.add_argument(
        "--gui", "-g",
        action="store_true",
        help="GUI modunda çalıştır"
    )
    
    parser.add_argument(
        "--do-file",
        type=Path,
        help="GUI modu için DO dosyası"
    )
    
    parser.add_argument(
        "--mem-file",
        type=Path,
        help="Memory dosyası (belirtilmezse otomatik bulunur)"
    )
    
    parser.add_argument(
        "--defines", "-D",
        action="append",
        default=[],
        help="Ek +define'lar (birden fazla kullanılabilir)"
    )
    
    parser.add_argument(
        "--no-color",
        action="store_true",
        help="Renkli çıktıyı devre dışı bırak"
    )
    
    parser.add_argument(
        "--voptargs",
        default="+acc=npr",
        help="VOPT argümanları (varsayılan: +acc=npr veya JSON'dan)"
    )
    
    parser.add_argument(
        "--time-res",
        default="ns",
        help="Zaman çözünürlüğü (varsayılan: ns veya JSON'dan)"
    )
    
    parser.add_argument(
        "--show-config",
        action="store_true",
        help="Konfigürasyonu göster ve çık"
    )
    
    parser.add_argument(
        "--validate-config",
        action="store_true",
        help="JSON konfigürasyonunu doğrula ve çık"
    )
    
    parser.add_argument(
        "--debug",
        action="store_true",
        help="Debug logging'i etkinleştir (CERES_DEBUG=1 ile de aktif edilebilir)"
    )
    
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    
    # Renkleri devre dışı bırak (gerekirse)
    if args.no_color or not sys.stdout.isatty():
        Color.disable()
        if HAS_CONFIG_MODULE:
            ConfigColor.disable()
    
    # Debug logging kontrolü
    debug_enabled = args.debug or os.environ.get("CERES_DEBUG", "0") == "1"
    
    # JSON config yükle
    json_config = None
    if HAS_CONFIG_MODULE and not args.no_config:
        try:
            json_config = load_config(
                config_file=args.config,
                profile=args.profile,
                quiet=True,  # Runner kendi mesajlarını gösterecek
            )
            
            # Validate-only modu
            if args.validate_config:
                print_config_summary(json_config)
                if json_config.warnings:
                    return 1
                success("Konfigürasyon geçerli")
                return 0
            
            # Show-config modu
            if args.show_config:
                print_config_summary(json_config)
                return 0
                
        except FileNotFoundError:
            warn("JSON config bulunamadı, varsayılan değerler kullanılacak")
        except ValueError as e:
            error(f"JSON config hatası: {e}")
            return 1
    elif not HAS_CONFIG_MODULE and not args.no_config:
        warn("modelsim_config modülü yüklenemedi, sadece CLI args kullanılacak")
    
    # Memory dizinlerini parse et
    mem_dirs = [Path(d.strip()) for d in args.mem_dirs.split() if d.strip()]
    
    # Config oluştur (JSON + CLI merge)
    config = merge_config_with_cli(json_config, args, mem_dirs)
    
    # Debug logger oluştur
    logger = create_logger(
        tool_name="modelsim",
        log_dir=config.log_dir,
        debug_enabled=debug_enabled
    )
    
    # CLI arguments logla
    logger.section("CLI Arguments")
    logger.params_from_dict(vars(args), source="cli")
    
    # JSON config logla
    if json_config:
        logger.section("JSON Configuration")
        logger.param("config_file", str(args.config) if args.config else "default", "json")
        logger.param("profile", args.profile or "default", "json")
    
    return run_simulation(config, logger)


if __name__ == "__main__":
    sys.exit(main())
