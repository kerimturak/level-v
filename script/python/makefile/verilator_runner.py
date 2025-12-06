#!/usr/bin/env python3
"""
CERES RISC-V — Verilator Simulation Runner

Verilator simülasyonunu JSON config ile çalıştırır.
ModelSim runner ile aynı pattern'ı kullanır.

Kullanım:
    python verilator_runner.py --test rv32ui-p-add --config verilator.json
    python verilator_runner.py --test coremark --profile benchmark
    
Debug:
    CERES_DEBUG=1 python verilator_runner.py --test rv32ui-p-add
    python verilator_runner.py --test rv32ui-p-add --debug
"""

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional

# Config modülünü import et
try:
    from verilator_config import (
        Color, load_config, VerilatorConfig, supports_color
    )
except ImportError:
    # Aynı dizinden import
    sys.path.insert(0, str(Path(__file__).parent))
    from verilator_config import (
        Color, load_config, VerilatorConfig, supports_color
    )

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
# Output Helpers
# ═══════════════════════════════════════════════════════════════════════════
def info(msg: str) -> None:
    print(f"{Color.CYAN}[INFO]{Color.RESET} {msg}")


def warn(msg: str) -> None:
    print(f"{Color.YELLOW}[WARN]{Color.RESET} {msg}", file=sys.stderr)


def error(msg: str) -> None:
    print(f"{Color.RED}[ERROR]{Color.RESET} {msg}", file=sys.stderr)


def success(msg: str) -> None:
    print(f"{Color.GREEN}[OK]{Color.RESET} {msg}")


def header(title: str, char: str = "═") -> None:
    """Renkli başlık banner'ı yazdır."""
    width = 60
    print(f"{Color.CYAN}{char * width}{Color.RESET}")
    print(f"{Color.CYAN}  {title}{Color.RESET}")
    print(f"{Color.CYAN}{char * width}{Color.RESET}")


def subheader(title: str) -> None:
    """Alt başlık yazdır."""
    print(f"\n{Color.BLUE}▶ {title}{Color.RESET}")


def keyval(key: str, value: str, indent: int = 2) -> None:
    """Anahtar-değer çifti yazdır."""
    spaces = " " * indent
    print(f"{spaces}{Color.DIM}{key}:{Color.RESET} {value}")


# ═══════════════════════════════════════════════════════════════════════════
# Run Configuration
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class SimRunConfig:
    """Simülasyon çalışma konfigürasyonu."""
    test_name: str
    bin_path: Path
    log_dir: Path
    mem_file: Optional[Path] = None
    addr_file: Optional[Path] = None
    
    # Simulation params
    max_cycles: int = 100000
    threads: int = 1
    seed: Optional[int] = None
    
    # Trace
    trace_enabled: bool = True
    trace_format: str = "fst"
    
    # Coverage
    coverage_enabled: bool = False
    coverage_file: Optional[Path] = None
    
    # Logging
    fast_sim: bool = False
    commit_trace: bool = True
    bp_log: bool = False
    
    # Paths
    mem_dirs: List[Path] = field(default_factory=list)
    build_dir: Optional[Path] = None
    
    # Meta
    json_config: Optional[VerilatorConfig] = None
    profile_name: Optional[str] = None
    cli_overrides: List[str] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════════════
# File Finders
# ═══════════════════════════════════════════════════════════════════════════
def find_mem_file(test_name: str, mem_dirs: List[Path]) -> Optional[Path]:
    """Memory dosyasını bul."""
    extensions = [".mem", ".hex", ".bin"]
    
    for mem_dir in mem_dirs:
        if not mem_dir.exists():
            continue
        
        for ext in extensions:
            # Doğrudan dosya
            mem_file = mem_dir / f"{test_name}{ext}"
            if mem_file.exists():
                return mem_file
            
            # Alt dizinlerde ara
            for subdir in mem_dir.iterdir():
                if subdir.is_dir():
                    mem_file = subdir / f"{test_name}{ext}"
                    if mem_file.exists():
                        return mem_file
    
    return None


def find_addr_file(test_name: str, build_dir: Path) -> Optional[Path]:
    """Pass/fail adres dosyasını bul."""
    patterns = [
        f"pass_fail_addr/{test_name}_addr.txt",
        f"{test_name}_addr.txt",
        f"addr/{test_name}.txt",
    ]
    
    for pattern in patterns:
        addr_file = build_dir / pattern
        if addr_file.exists():
            return addr_file
    
    # Recursive search
    for addr_file in build_dir.rglob(f"*{test_name}*addr*.txt"):
        return addr_file
    
    return None


def find_executable(obj_dir: Path, top_module: str = "ceres_wrapper") -> Optional[Path]:
    """Verilator executable'ını bul."""
    exe_name = f"V{top_module}"
    exe_path = obj_dir / exe_name
    
    if exe_path.exists() and os.access(exe_path, os.X_OK):
        return exe_path
    
    return None


# ═══════════════════════════════════════════════════════════════════════════
# Directory Management
# ═══════════════════════════════════════════════════════════════════════════
def prepare_log_dir(log_dir: Path) -> None:
    """Log dizinini hazırla, varsa temizle."""
    if log_dir.exists():
        info(f"Önceki loglar temizleniyor: {log_dir}")
        import shutil
        shutil.rmtree(log_dir)
    
    log_dir.mkdir(parents=True, exist_ok=True)


# ═══════════════════════════════════════════════════════════════════════════
# Command Builder
# ═══════════════════════════════════════════════════════════════════════════
def build_run_command(config: SimRunConfig) -> List[str]:
    """Verilator çalıştırma komutunu oluştur."""
    cmd = [str(config.bin_path)]
    
    # Max cycles - MUST be first positional argument (C++ testbench expects argv[1])
    cmd.append(str(config.max_cycles))
    
    # Memory file
    if config.mem_file:
        cmd.append(f"+INIT_FILE={config.mem_file}")
    
    # Simulator identifier
    cmd.append("+simulator=verilator")
    
    # Test name
    cmd.append(f"+test_name={config.test_name}")
    
    # Address file
    if config.addr_file:
        cmd.append(f"+addr_file={config.addr_file}")
    
    # Trace/waveform output
    if config.trace_enabled:
        trace_file = config.log_dir / f"waveform.{config.trace_format}"
        cmd.append(f"+DUMP_FILE={trace_file}")
    
    # Commit trace log
    cmd.append(f"+trace_file={config.log_dir}/commit_trace.log")
    
    # Konata/pipeline log
    cmd.append(f"+log_path={config.log_dir}/ceres.log")
    
    # UART log
    cmd.append(f"+uart_log_path={config.log_dir}/uart_output.log")
    
    # BP stats directory
    cmd.append(f"+BP_LOG_DIR={config.log_dir}")
    
    # Coverage
    if config.coverage_enabled and config.coverage_file:
        cmd.append(f"+coverage_file={config.coverage_file}")
    
    # Seed
    if config.seed is not None:
        cmd.append(f"+seed={config.seed}")
    
    return cmd


# ═══════════════════════════════════════════════════════════════════════════
# Simulation Runner
# ═══════════════════════════════════════════════════════════════════════════
def run_simulation(config: SimRunConfig, logger: Optional[DebugLogger] = None) -> int:
    """Simülasyonu çalıştır ve sonucu döndür."""
    
    # Debug logger
    if logger is None:
        logger = DebugLogger("verilator", config.log_dir, enabled=False)
    
    logger.section("Run Configuration")
    logger.params_from_dataclass(config, source="merged")
    
    # Başlık banner'ı
    print()
    header("CERES RISC-V Verilator Simulation")
    
    # Test bilgisi
    print(f"  {Color.WHITE}Test:{Color.RESET}   {Color.YELLOW}{config.test_name}{Color.RESET}")
    print(f"  {Color.WHITE}Mode:{Color.RESET}   {Color.GREEN}Verilator{Color.RESET}")
    
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
    
    # Executable kontrol
    logger.file_check(config.bin_path, "Verilator executable")
    if not config.bin_path.exists():
        logger.error(f"Executable not found: {config.bin_path}")
        error(f"Executable bulunamadı: {config.bin_path}")
        error("Önce 'make verilate' çalıştırın.")
        logger.result(False, 1, "Executable not found")
        logger.save()
        return 1
    
    keyval("Executable", str(config.bin_path))
    
    # Log dizinini hazırla
    prepare_log_dir(config.log_dir)
    logger.note(f"Log directory prepared: {config.log_dir}")
    
    # Komutu oluştur
    cmd = build_run_command(config)
    
    logger.section("Command")
    logger.command(cmd, "Verilator simulation", config.log_dir)
    
    # Simülasyon ayarları özeti
    print()
    subheader("Simülasyon Ayarları")
    keyval("Max Cycles", f"{config.max_cycles:,}")
    keyval("Trace", "Enabled" if config.trace_enabled else "Disabled")
    keyval("Log Dir", str(config.log_dir))
    if config.coverage_enabled:
        keyval("Coverage", f"{Color.GREEN}enabled{Color.RESET}")
    
    logger.section("Execution")
    
    # Simülasyon başlat
    print()
    subheader("Çalıştırılıyor")
    print(f"  {Color.DIM}$ {config.bin_path.name} ...{Color.RESET}")
    print()
    
    # Log dosyası yolu
    run_log = config.log_dir / "verilator_run.log"
    
    start_time = datetime.now()
    logger.note(f"Simulation started at {start_time.isoformat()}")
    
    try:
        with open(run_log, "w") as log_file:
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                cwd=config.log_dir,
            )
            
            for line in process.stdout:
                print(line, end="")
                log_file.write(line)
            
            process.wait()
            exit_code = process.returncode
    
    except FileNotFoundError:
        logger.error(f"Executable could not run: {config.bin_path}")
        error(f"Executable çalıştırılamadı: {config.bin_path}")
        logger.result(False, 127, "Executable not found")
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
        "simulator": "verilator",
        "mem_file": str(config.mem_file) if config.mem_file else None,
        "exit_code": exit_code,
        "log_dir": str(config.log_dir),
        "max_cycles": config.max_cycles,
        "elapsed_seconds": round(elapsed, 2),
        "timestamp": end_time.isoformat(),
        "config": {
            "source": "json" if config.json_config else "cli",
            "profile": config.profile_name,
            "cli_overrides": config.cli_overrides,
        },
        "settings": {
            "trace_enabled": config.trace_enabled,
            "trace_format": config.trace_format,
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
        
        # Waveform bilgisi
        if config.trace_enabled:
            trace_file = config.log_dir / f"waveform.{config.trace_format}"
            if trace_file.exists():
                keyval("Waveform", str(trace_file))
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
# Config Merging
# ═══════════════════════════════════════════════════════════════════════════
def merge_config_with_cli(
    json_config: Optional[VerilatorConfig],
    args: argparse.Namespace,
) -> SimRunConfig:
    """JSON config ve CLI argümanlarını birleştir."""
    
    cli_overrides = []
    
    # JSON'dan başla veya varsayılanları kullan
    if json_config:
        max_cycles = json_config.simulation.max_cycles
        threads = json_config.simulation.get_threads()
        trace_enabled = json_config.trace.enabled
        trace_format = json_config.trace.format
        coverage_enabled = json_config.coverage.enabled
        fast_sim = json_config.logging.fast_sim
        commit_trace = json_config.logging.commit_trace
        bp_log = json_config.logging.bp_log
    else:
        max_cycles = 100000
        threads = 1
        trace_enabled = True
        trace_format = "fst"
        coverage_enabled = False
        fast_sim = False
        commit_trace = True
        bp_log = False
    
    # CLI override'ları
    if args.max_cycles is not None:
        if json_config and args.max_cycles != max_cycles:
            cli_overrides.append(f"max_cycles={args.max_cycles} (JSON: {max_cycles})")
        max_cycles = args.max_cycles
    
    if args.no_trace:
        if trace_enabled:
            cli_overrides.append("trace=disabled")
        trace_enabled = False
    
    if args.coverage:
        if not coverage_enabled:
            cli_overrides.append("coverage=enabled")
        coverage_enabled = True
    
    if args.fast:
        if not fast_sim:
            cli_overrides.append("fast_sim=enabled")
        fast_sim = True
        trace_enabled = False
    
    # Path'leri parse et
    mem_dirs = [Path(d) for d in args.mem_dirs.split()] if args.mem_dirs else []
    
    return SimRunConfig(
        test_name=args.test,
        bin_path=Path(args.bin_path),
        log_dir=Path(args.log_dir),
        mem_file=Path(args.mem_file) if args.mem_file else None,
        max_cycles=max_cycles,
        threads=threads,
        trace_enabled=trace_enabled,
        trace_format=trace_format,
        coverage_enabled=coverage_enabled,
        coverage_file=Path(args.coverage_file) if args.coverage_file else None,
        fast_sim=fast_sim,
        commit_trace=commit_trace,
        bp_log=bp_log,
        mem_dirs=mem_dirs,
        build_dir=Path(args.build_dir) if args.build_dir else None,
        json_config=json_config,
        profile_name=args.profile if hasattr(args, 'profile') else None,
        cli_overrides=cli_overrides,
    )


# ═══════════════════════════════════════════════════════════════════════════
# CLI Interface
# ═══════════════════════════════════════════════════════════════════════════
def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="CERES RISC-V Verilator Simulation Runner",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
JSON Konfigürasyon:
  Ayarlar önce script/config/verilator.json'dan okunur.
  CLI argümanları JSON değerlerini override eder.
  
Profiller:
  --profile fast       Maksimum hız, trace yok
  --profile debug      Tam debug, tüm trace'ler aktif
  --profile coverage   Coverage modu
  --profile benchmark  Benchmark modu, BP logging aktif

Örnekler:
  %(prog)s --test rv32ui-p-add --bin-path build/obj_dir/Vceres_wrapper
  %(prog)s --test coremark --profile benchmark --max-cycles 10000000
  %(prog)s --test dhrystone --fast
        """
    )
    
    # Zorunlu argümanlar
    required = parser.add_argument_group("required arguments")
    required.add_argument(
        "--test", "-t",
        dest="test",
        required=True,
        help="Test adı (örn: rv32ui-p-add)"
    )
    required.add_argument(
        "--bin-path", "-b",
        dest="bin_path",
        required=True,
        help="Verilator executable path"
    )
    required.add_argument(
        "--log-dir", "-l",
        dest="log_dir",
        required=True,
        help="Log çıktı dizini"
    )
    required.add_argument(
        "--mem-dirs", "-m",
        dest="mem_dirs",
        required=True,
        help="Memory dosyası arama dizinleri (boşlukla ayrılmış)"
    )
    
    # Config argümanları
    config_group = parser.add_argument_group("configuration")
    config_group.add_argument(
        "--config", "-c",
        help="JSON konfigürasyon dosyası"
    )
    config_group.add_argument(
        "--profile", "-p",
        help="Kullanılacak profil (fast, debug, coverage, benchmark)"
    )
    config_group.add_argument(
        "--no-config",
        action="store_true",
        help="JSON konfigürasyonu yükleme"
    )
    
    # Simülasyon argümanları
    sim_group = parser.add_argument_group("simulation")
    sim_group.add_argument(
        "--max-cycles",
        type=int,
        help="Maksimum cycle sayısı"
    )
    sim_group.add_argument(
        "--no-trace",
        action="store_true",
        help="Trace'i devre dışı bırak"
    )
    sim_group.add_argument(
        "--coverage",
        action="store_true",
        help="Coverage'ı etkinleştir"
    )
    sim_group.add_argument(
        "--coverage-file",
        help="Coverage output dosyası"
    )
    sim_group.add_argument(
        "--fast",
        action="store_true",
        help="Hızlı mod (trace yok, minimal logging)"
    )
    
    # Path argümanları
    path_group = parser.add_argument_group("paths")
    path_group.add_argument(
        "--build-dir",
        help="Build dizini (addr dosyası için)"
    )
    path_group.add_argument(
        "--mem-file",
        help="Doğrudan memory dosyası belirt"
    )
    
    # Diğer
    parser.add_argument(
        "--no-color",
        action="store_true",
        help="Renkleri devre dışı bırak"
    )
    parser.add_argument(
        "--dry-run", "-n",
        action="store_true",
        help="Komutu çalıştırmadan göster"
    )
    parser.add_argument(
        "--show-config",
        action="store_true",
        help="Konfigürasyonu göster ve çık"
    )
    parser.add_argument(
        "--debug",
        action="store_true",
        help="Debug logging'i etkinleştir (CERES_DEBUG=1 ile de aktif edilebilir)"
    )
    
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    
    # Renk desteği
    if args.no_color or not supports_color():
        Color.disable()
    
    # Debug logging kontrolü
    debug_enabled = args.debug or os.environ.get("CERES_DEBUG", "0") == "1"
    
    # JSON config yükle
    json_config = None
    if not args.no_config:
        config_path = Path(args.config) if args.config else None
        try:
            json_config = load_config(
                config_path=config_path,
                profile=args.profile,
            )
        except Exception as e:
            warn(f"JSON config yüklenemedi: {e}")
    
    # Config'i birleştir
    config = merge_config_with_cli(json_config, args)
    
    # Debug logger oluştur
    logger = create_logger(
        tool_name="verilator",
        log_dir=config.log_dir,
        debug_enabled=debug_enabled
    )
    
    # CLI arguments logla
    logger.section("CLI Arguments")
    logger.params_from_dict(vars(args), source="cli")
    
    # JSON config logla
    if json_config:
        logger.section("JSON Configuration")
        logger.param("config_file", args.config or "default", "json")
        logger.param("profile", args.profile or "default", "json")
    
    # Show config mode
    if args.show_config:
        if json_config:
            from verilator_config import print_config_summary
            print_config_summary(json_config)
        else:
            info("JSON config yüklenmedi")
        return 0
    
    # Dry run mode
    if args.dry_run:
        cmd = build_run_command(config)
        logger.section("Dry Run")
        logger.command(cmd, "Would execute", config.log_dir)
        logger.save()
        print(f"{Color.CYAN}Dry-run mode:{Color.RESET}")
        print(f"  {' '.join(cmd)}")
        return 0
    
    # Simülasyonu çalıştır
    return run_simulation(config, logger)


if __name__ == "__main__":
    sys.exit(main())
