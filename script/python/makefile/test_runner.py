#!/usr/bin/env python3
"""
CERES RISC-V — Test Runner

Test pipeline'ını yönetir:
1. Test environment hazırlama
2. RTL simülasyonu çalıştırma
3. Spike golden reference çalıştırma
4. Log karşılaştırma
5. Rapor oluşturma

Kullanım:
    python test_runner.py --test rv32ui-p-add
    python test_runner.py --test rv32ui-p-add --sim verilator --skip-spike
    python test_runner.py --test rv32ui-p-add --debug
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
from typing import Any, Dict, List, Optional, Tuple

# Debug logger import
try:
    from debug_logger import DebugLogger, create_logger
except ImportError:
    sys.path.insert(0, str(Path(__file__).parent))
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


def supports_color() -> bool:
    return sys.stdout.isatty() and os.environ.get("TERM", "") != "dumb"


# ═══════════════════════════════════════════════════════════════════════════
# Output Helpers
# ═══════════════════════════════════════════════════════════════════════════
def info(msg: str) -> None:
    print(f"{Color.CYAN}[INFO]{Color.RESET} {msg}")


def warn(msg: str) -> None:
    print(f"{Color.YELLOW}[WARN]{Color.RESET} {msg}")


def error(msg: str) -> None:
    print(f"{Color.RED}[ERROR]{Color.RESET} {msg}", file=sys.stderr)


def success(msg: str) -> None:
    print(f"{Color.GREEN}[OK]{Color.RESET} {msg}")


def step(num: int, total: int, title: str) -> None:
    """Step başlığı yazdır."""
    print()
    print(f"{Color.YELLOW}{'━' * 50}{Color.RESET}")
    print(f"{Color.GREEN}  Step {num}/{total}: {title}{Color.RESET}")
    print(f"{Color.YELLOW}{'━' * 50}{Color.RESET}")


def header(title: str) -> None:
    """Ana başlık yazdır."""
    print()
    print(f"{Color.YELLOW}{'━' * 50}{Color.RESET}")
    print(f"{Color.GREEN}  {title}{Color.RESET}")
    print(f"{Color.YELLOW}{'━' * 50}{Color.RESET}")


def keyval(key: str, value: str, indent: int = 0) -> None:
    """Anahtar-değer çifti yazdır."""
    spaces = " " * indent
    print(f"{spaces}{Color.YELLOW}[INFO]{Color.RESET} {key:<12}: {value}")


# ═══════════════════════════════════════════════════════════════════════════
# Test Type Detection
# ═══════════════════════════════════════════════════════════════════════════
TEST_TYPE_PATTERNS = {
    "isa": [
        r"^rv32u[imc]-p-",      # rv32ui-p-add, rv32um-p-mul, rv32uc-p-rvc
        r"^rv32m[imc]-p-",      # rv32mi-p-...
        r"^rv32s[imc]-p-",      # rv32si-p-...
    ],
    "arch": [
        r"^[A-Z]-.+-\d{2}$",    # I-ADD-01, M-MUL-01, C-ADDI-01
    ],
    "imperas": [
        r"^I-[A-Z]+-",          # I-ADD-01 (Imperas format)
        r"^M-[A-Z]+-",
        r"^C-[A-Z]+-",
    ],
    "bench": [
        "dhrystone", "median", "multiply", "qsort", "rsort", "spmv",
        "towers", "vvadd", "mm", "mt-matmul", "mt-vvadd"
    ],
    "coremark": ["coremark"],
    "embench": [
        "aha-mont64", "crc32", "cubic", "edn", "huffbench", "matmult-int",
        "md5sum", "minver", "nbody", "nettle-aes", "nettle-sha256",
        "nsichneu", "picojpeg", "primecount", "qrduino", "sglib-combined",
        "slre", "st", "statemate", "tarfind", "ud", "wikisort"
    ]
}


def detect_test_type(test_name: str, build_dir: Path) -> str:
    """
    Test tipini tespit et.
    
    Önce dosya varlığına, sonra pattern'a bakar.
    """
    import re
    
    # 1. Dosya tabanlı tespit
    type_paths = {
        "isa": build_dir / "tests/riscv-tests/elf",
        "arch": build_dir / "tests/riscv-arch-test/elf",
        "imperas": build_dir / "tests/imperas/elf",
        "bench": build_dir / "tests/riscv-benchmarks/elf",
        "coremark": build_dir / "tests/coremark",
        "embench": build_dir / "tests/embench/elf",
        "dhrystone": build_dir / "tests/dhrystone",
        "torture": build_dir / "tests/torture/elf",
        "custom": build_dir / "tests/custom",
    }
    
    for test_type, base_path in type_paths.items():
        # .elf uzantılı veya uzantısız dosya ara
        for ext in [".elf", ""]:
            elf_path = base_path / f"{test_name}{ext}"
            if elf_path.exists():
                return test_type
    
    # 2. Pattern tabanlı tespit
    for test_type, patterns in TEST_TYPE_PATTERNS.items():
        for pattern in patterns:
            if isinstance(pattern, str) and pattern.startswith("^"):
                # Regex pattern
                if re.match(pattern, test_name):
                    return test_type
            elif test_name == pattern or test_name.startswith(pattern):
                # Exact or prefix match
                return test_type
    
    # 3. Varsayılan: isa
    return "isa"


def get_test_paths(test_name: str, test_type: str, build_dir: Path) -> Dict[str, Path]:
    """Test tipine göre path'leri döndür."""
    
    type_roots = {
        "isa": "riscv-tests",
        "arch": "riscv-arch-test",
        "imperas": "imperas",
        "bench": "riscv-benchmarks",
        "coremark": "coremark",
        "embench": "embench",
        "dhrystone": "dhrystone",
        "torture": "torture",
        "riscv-dv": "riscv-dv",
        "custom": "custom",
    }
    
    root_name = type_roots.get(test_type, "custom")
    test_root = build_dir / "tests" / root_name
    
    # ELF uzantısı
    elf_ext = ".elf" if test_type not in ["isa", "bench"] else ""
    
    return {
        "test_root": test_root,
        "elf_dir": test_root / "elf",
        "mem_dir": test_root / "mem",
        "hex_dir": test_root / "hex",
        "dump_dir": test_root / "dump",
        "addr_dir": test_root / "pass_fail_addr",
        "elf_file": test_root / "elf" / f"{test_name}{elf_ext}",
        "mem_file": test_root / "mem" / f"{test_name}.mem",
        "hex_file": test_root / "hex" / f"{test_name}.hex",
        "dump_file": test_root / "dump" / f"{test_name}.dump",
        "addr_file": test_root / "pass_fail_addr" / f"{test_name}_addr.txt",
    }


# ═══════════════════════════════════════════════════════════════════════════
# Test Configuration
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class TestConfig:
    """Test çalıştırma konfigürasyonu."""
    test_name: str
    test_type: str
    simulator: str  # verilator, modelsim
    
    # Paths
    build_dir: Path
    root_dir: Path
    log_dir: Path
    
    # Test paths (auto-filled)
    test_paths: Dict[str, Path] = field(default_factory=dict)
    
    # Simulation settings
    max_cycles: int = 100000
    
    # Pipeline control
    skip_spike: bool = False
    skip_compare: bool = False
    quick_mode: bool = False  # RTL only, no Spike
    
    # Spike settings
    spike_isa: str = "rv32imc_zicsr_zicntr_zifencei"
    spike_pc: str = "0x80000000"  # Başlangıç PC - RTL reset vector ile aynı olmalı
    spike_priv: str = "m"  # Privilege mode
    spike_log_commits: bool = True
    
    # Output files
    rtl_log: Optional[Path] = None
    spike_log: Optional[Path] = None
    report_file: Optional[Path] = None
    
    def __post_init__(self):
        """Path'leri otomatik doldur."""
        if not self.test_paths:
            self.test_paths = get_test_paths(
                self.test_name, self.test_type, self.build_dir
            )
        
        # Log dosyaları
        if not self.rtl_log:
            self.rtl_log = self.log_dir / "rtl_commit.log"
        if not self.spike_log:
            self.spike_log = self.log_dir / "spike_commit.log"
        if not self.report_file:
            self.report_file = self.log_dir / "test_report.txt"


# ═══════════════════════════════════════════════════════════════════════════
# Test Pipeline Steps
# ═══════════════════════════════════════════════════════════════════════════

def prepare_test(config: TestConfig, logger: DebugLogger) -> bool:
    """
    Step 1: Test ortamını hazırla.
    
    - Log dizinlerini oluştur
    - Gerekli dosyaların varlığını kontrol et
    - Rapor dosyasını başlat
    """
    logger.section("Test Preparation")
    
    header("CERES RISC-V Test Runner")
    keyval("Test Name", config.test_name)
    keyval("Test Type", config.test_type)
    keyval("Simulator", config.simulator)
    keyval("Max Cycles", str(config.max_cycles))
    keyval("Log Dir", str(config.log_dir))
    
    # Log dizini oluştur (önce temizle)
    if config.log_dir.exists():
        info(f"Removing previous logs: {config.log_dir}")
        shutil.rmtree(config.log_dir)
    config.log_dir.mkdir(parents=True, exist_ok=True)
    logger.note(f"Created log directory: {config.log_dir}")
    
    # Gerekli dosyaları kontrol et
    logger.section("File Verification")
    
    elf_file = config.test_paths["elf_file"]
    mem_file = config.test_paths["mem_file"]
    
    logger.file_check(elf_file, "ELF file")
    if not elf_file.exists():
        logger.error(f"ELF file not found: {elf_file}")
        error(f"ELF file not found: {elf_file}")
        error("Build tests first: make isa_auto or make arch_auto")
        return False
    keyval("ELF File", str(elf_file))
    
    logger.file_check(mem_file, "Memory file")
    if not mem_file.exists():
        logger.warning(f"Memory file not found: {mem_file}")
        warn(f"Memory file not found: {mem_file}")
    else:
        keyval("MEM File", str(mem_file))
    
    # Addr dosyası (opsiyonel)
    addr_file = config.test_paths.get("addr_file")
    if addr_file and addr_file.exists():
        keyval("ADDR File", str(addr_file))
        logger.param("addr_file", addr_file, "found")
    
    # Rapor dosyasını başlat
    with open(config.report_file, "w") as f:
        f.write("=== CERES Test Report ===\n")
        f.write(f"Test: {config.test_name}\n")
        f.write(f"Type: {config.test_type}\n")
        f.write(f"Simulator: {config.simulator}\n")
        f.write(f"Date: {datetime.now().isoformat()}\n")
        f.write("\n")
    
    logger.success("Test environment prepared")
    success("Test environment prepared")
    return True


def run_rtl_simulation(config: TestConfig, logger: DebugLogger) -> Tuple[bool, int]:
    """
    Step 2: RTL simülasyonunu çalıştır.
    
    Returns:
        (success, exit_code)
    """
    logger.section("RTL Simulation")
    step(1, 3 if not config.skip_spike else 1, "Running RTL Simulation")
    
    mem_file = config.test_paths["mem_file"]
    addr_file = config.test_paths.get("addr_file")
    
    if config.simulator == "verilator":
        # Verilator runner'ı çağır
        runner_script = config.root_dir / "script/python/makefile/verilator_runner.py"
        
        cmd = [
            sys.executable, str(runner_script),
            "--test", config.test_name,
            "--bin-path", str(config.build_dir / "obj_dir/Vceres_wrapper"),
            "--log-dir", str(config.log_dir),
            "--mem-dirs", str(config.test_paths["mem_dir"]),
            "--max-cycles", str(config.max_cycles),
            "--build-dir", str(config.build_dir / "tests"),
        ]
        
        if addr_file and addr_file.exists():
            # addr_file runner'a verilecek (build_dir üzerinden bulacak)
            pass
        
        logger.command(cmd, "Verilator runner")
        
    elif config.simulator == "modelsim":
        # ModelSim runner'ı çağır
        runner_script = config.root_dir / "script/python/makefile/modelsim_runner.py"
        
        mem_dirs = " ".join([
            str(config.build_dir / "tests/embench/mem"),
            str(config.build_dir / "tests/imperas/mem"),
            str(config.build_dir / "tests/riscv-arch-test/mem"),
            str(config.build_dir / "tests/riscv-dv/mem"),
            str(config.build_dir / "tests/riscv-tests/mem"),
            str(config.build_dir / "tests/torture/mem"),
            str(config.build_dir / "tests/coremark"),
            str(config.build_dir / "tests/custom"),
        ])
        
        cmd = [
            sys.executable, str(runner_script),
            f"--test={config.test_name}",
            f"--work-dir={config.build_dir}/work",
            f"--log-dir={config.log_dir}",
            f"--mem-dirs={mem_dirs}",
            f"--build-dir={config.build_dir}",
            "--tb-level=tb_wrapper",
        ]
        
        logger.command(cmd, "ModelSim runner")
    else:
        logger.error(f"Unknown simulator: {config.simulator}")
        error(f"Unknown simulator: {config.simulator}")
        return False, 1
    
    # Komutu çalıştır
    try:
        result = subprocess.run(
            cmd,
            capture_output=False,
            text=True,
            cwd=config.root_dir,
        )
        exit_code = result.returncode
        
        # Rapor dosyasına yaz
        with open(config.report_file, "a") as f:
            f.write(f"RTL_EXIT_CODE={exit_code}\n")
        
        if exit_code == 0:
            logger.success("RTL simulation completed")
            success("RTL simulation complete")
            return True, 0
        else:
            logger.error(f"RTL simulation failed with exit code {exit_code}")
            error(f"RTL simulation failed with exit code {exit_code}")
            return False, exit_code
            
    except Exception as e:
        logger.error(f"Failed to run RTL simulation: {e}")
        error(f"Failed to run RTL simulation: {e}")
        return False, 1


def run_spike(config: TestConfig, logger: DebugLogger) -> Tuple[bool, int]:
    """
    Step 3: Spike golden reference çalıştır.
    
    Spike'ı debug modunda çalıştırır ve PASS adresinde durdurur.
    Bu şekilde RTL ile aynı sayıda instruction execute edilir.
    
    Returns:
        (success, exit_code)
    """
    if config.skip_spike:
        logger.note("Spike comparison skipped")
        step(2, 3, "Spike comparison disabled (benchmark mode)")
        return True, 0
    
    logger.section("Spike Golden Reference")
    step(2, 3, "Running Spike Golden Model")
    
    elf_file = config.test_paths["elf_file"]
    addr_file = config.test_paths["addr_file"]
    
    # PASS adresini oku
    pass_addr = None
    if addr_file.exists():
        try:
            with open(addr_file) as f:
                parts = f.read().strip().split()
                if parts:
                    pass_addr = parts[0]  # İlk değer PASS adresi
                    logger.param("pass_addr", pass_addr, "spike")
                    info(f"PASS address: {pass_addr}")
        except Exception as e:
            logger.warning(f"Failed to read address file: {e}")
    
    if not pass_addr:
        logger.warning(f"Address file not found or empty: {addr_file}")
        warn(f"Address file not found: {addr_file} - Spike may run indefinitely")
    
    # Debug command dosyası oluştur (PASS adresinde dur)
    debug_cmd_file = config.log_dir / "spike_debug.cmd"
    if pass_addr:
        with open(debug_cmd_file, "w") as f:
            # "until pc 0 <addr>" - core 0'da <addr> PC'sine ulaşınca dur
            f.write(f"until pc 0 {pass_addr}\n")
            f.write("quit\n")
        logger.note(f"Created debug command: until pc 0 {pass_addr}")
    
    # Spike komutunu oluştur
    cmd = ["spike"]
    
    # Debug mode ve command file (PASS adresinde durmak için)
    if pass_addr:
        cmd.extend(["-d", f"--debug-cmd={debug_cmd_file}"])
    
    # ISA, PC ve privilege mode parametreleri (Makefile ile aynı)
    cmd.append(f"--isa={config.spike_isa}")
    cmd.append(f"--pc={config.spike_pc}")
    cmd.append(f"--priv={config.spike_priv}")
    
    if config.spike_log_commits:
        cmd.extend(["-l", "--log-commits"])
    
    cmd.append(str(elf_file))
    
    logger.command(cmd, "Spike simulation")
    info(f"Running: spike -d --isa={config.spike_isa} --pc={config.spike_pc} {elf_file.name}")
    
    try:
        # Spike çıktısını log dosyasına yaz
        with open(config.spike_log, "w") as log_file:
            result = subprocess.run(
                cmd,
                stdout=log_file,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=300,  # 5 dakika timeout
            )
        
        exit_code = result.returncode
        
        with open(config.report_file, "a") as f:
            f.write(f"SPIKE_EXIT_CODE={exit_code}\n")
        
        if exit_code == 0:
            # Spike log satır sayısını göster
            with open(config.spike_log) as f:
                line_count = sum(1 for _ in f)
            
            logger.param("spike_log_lines", line_count, "execution")
            success(f"Spike simulation complete ({line_count} commits)")
            return True, 0
        else:
            logger.error(f"Spike simulation failed with exit code {exit_code}")
            error(f"Spike simulation failed with exit code {exit_code}")
            return False, exit_code
            
    except subprocess.TimeoutExpired:
        logger.error("Spike simulation timed out after 5 minutes")
        error("Spike simulation timed out after 5 minutes")
        return False, 124
    except FileNotFoundError:
        logger.error("Spike not found. Is it installed and in PATH?")
        error("Spike not found. Is it installed and in PATH?")
        return False, 127
    except Exception as e:
        logger.error(f"Failed to run Spike: {e}")
        error(f"Failed to run Spike: {e}")
        return False, 1


def compare_logs(config: TestConfig, logger: DebugLogger) -> Tuple[bool, int]:
    """
    Step 4: RTL ve Spike loglarını karşılaştır.
    
    Returns:
        (match, diff_count)
    """
    if config.skip_compare or config.skip_spike:
        logger.note("Log comparison skipped")
        return True, 0
    
    logger.section("Log Comparison")
    step(3, 3, "Comparing RTL and Spike Logs")
    
    rtl_log = config.log_dir / "commit_trace.log"  # RTL commit trace
    spike_log = config.spike_log
    
    if not rtl_log.exists():
        logger.warning(f"RTL log not found: {rtl_log}")
        warn(f"RTL log not found: {rtl_log}")
        return False, -1
    
    if not spike_log.exists():
        logger.warning(f"Spike log not found: {spike_log}")
        warn(f"Spike log not found: {spike_log}")
        return False, -1
    
    # Basit satır sayısı karşılaştırması
    with open(rtl_log) as f:
        rtl_lines = [l.strip() for l in f if l.strip() and not l.startswith("#")]
    
    with open(spike_log) as f:
        spike_lines = [l.strip() for l in f if l.strip() and not l.startswith("#")]
    
    logger.param("rtl_commits", len(rtl_lines), "comparison")
    logger.param("spike_commits", len(spike_lines), "comparison")
    
    info(f"RTL commits:   {len(rtl_lines)}")
    info(f"Spike commits: {len(spike_lines)}")
    
    # Detaylı karşılaştırma - compare_logs.py script'ini kullan
    compare_script = config.root_dir / "script/python/makefile/compare_logs.py"
    
    if compare_script.exists():
        # Makefile ile aynı argümanları kullan - .log uzantısı gerekli!
        diff_log = config.log_dir / "diff.log"
        cmd = [
            sys.executable, str(compare_script),
            "--rtl", str(rtl_log),
            "--spike", str(spike_log),
            "--output", str(diff_log),
            "--test-name", config.test_name,
        ]
        
        # Opsiyonel dump ve addr dosyaları
        dump_file = config.test_paths.get("dump_file")
        if dump_file and dump_file.exists():
            cmd.extend(["--dump", str(dump_file)])
        
        addr_file = config.test_paths.get("addr_file")
        if addr_file and addr_file.exists():
            cmd.extend(["--addr", str(addr_file)])
        
        logger.command(cmd, "Compare logs")
        
        # Script çıktısını hem göster hem logla
        result = subprocess.run(cmd, capture_output=False, text=True)
        
        if result.returncode == 0:
            logger.success("Logs match!")
            return True, 0
        else:
            logger.error("Logs differ!")
            info(f"See: {config.log_dir / 'diff_visual_diff.log'}")
            return False, result.returncode
    else:
        logger.warning(f"Compare script not found: {compare_script}")
        warn(f"Compare script not found, using simple line comparison")
        
        # Basit karşılaştırma (fallback)
        if len(rtl_lines) == len(spike_lines):
            # İlk farklı satırı bul
            for i, (rtl, spike) in enumerate(zip(rtl_lines, spike_lines)):
                if rtl != spike:
                    logger.error(f"First difference at line {i+1}")
                    error(f"First difference at line {i+1}")
                    info(f"RTL:   {rtl[:80]}")
                    info(f"Spike: {spike[:80]}")
                    return False, 1
            
            logger.success("Logs match!")
            success("✓ RTL and Spike logs match!")
            return True, 0
        else:
            logger.error(f"Line count differs: RTL={len(rtl_lines)}, Spike={len(spike_lines)}")
            error(f"Line count differs: RTL={len(rtl_lines)}, Spike={len(spike_lines)}")
            return False, abs(len(rtl_lines) - len(spike_lines))


def generate_report(config: TestConfig, logger: DebugLogger, 
                   rtl_success: bool, spike_success: bool, compare_success: bool) -> None:
    """
    Step 5: Final rapor oluştur.
    """
    logger.section("Test Report")
    
    overall_success = rtl_success and (config.skip_spike or spike_success) and (config.skip_compare or compare_success)
    
    with open(config.report_file, "a") as f:
        f.write("\n=== Results ===\n")
        f.write(f"RTL_SUCCESS={rtl_success}\n")
        f.write(f"SPIKE_SUCCESS={spike_success}\n")
        f.write(f"COMPARE_SUCCESS={compare_success}\n")
        f.write(f"OVERALL_SUCCESS={overall_success}\n")
    
    print()
    if overall_success:
        print(f"{Color.GREEN}{'═' * 50}{Color.RESET}")
        print(f"{Color.GREEN}  ✓ TEST PASSED: {config.test_name}{Color.RESET}")
        print(f"{Color.GREEN}{'═' * 50}{Color.RESET}")
        logger.success(f"Test passed: {config.test_name}")
    else:
        print(f"{Color.RED}{'═' * 50}{Color.RESET}")
        print(f"{Color.RED}  ✗ TEST FAILED: {config.test_name}{Color.RESET}")
        print(f"{Color.RED}{'═' * 50}{Color.RESET}")
        logger.error(f"Test failed: {config.test_name}")
        # Provide helpful failure artifacts paths
        diff_log = config.log_dir / "diff.log"
        visual_diff = config.log_dir / "diff_visual_diff.log"
        html_diff = config.log_dir / "diff.html"
        dump_file = config.test_paths.get("dump_file")
        # Print paths to console for quick inspection
        print()
        print(f"[INFO] Report      : {config.report_file}")
        print(f"[INFO] Logs        : {config.log_dir}")
        if diff_log.exists():
            print(f"[INFO] Diff status : {diff_log}")
        else:
            print(f"[INFO] Diff status : {diff_log} (not generated)")
        if visual_diff.exists():
            print(f"[INFO] Visual diff : {visual_diff}")
        if html_diff.exists():
            print(f"[INFO] HTML diff   : {html_diff}")
        if dump_file and Path(dump_file).exists():
            print(f"[INFO] Dump file   : {dump_file}")
        # Also append these paths into the report file
        with open(config.report_file, "a") as f:
            f.write(f"DIFF_LOG={diff_log}\n")
            f.write(f"VISUAL_DIFF={visual_diff}\n")
            f.write(f"HTML_DIFF={html_diff}\n")
            if dump_file:
                f.write(f"DUMP_FILE={dump_file}\n")
    
    keyval("Report", str(config.report_file))
    keyval("Logs", str(config.log_dir))


# ═══════════════════════════════════════════════════════════════════════════
# Main Pipeline
# ═══════════════════════════════════════════════════════════════════════════

def run_test_pipeline(config: TestConfig, logger: DebugLogger) -> int:
    """
    Ana test pipeline'ı.
    
    Returns:
        Exit code (0 = success)
    """
    logger.section("Test Pipeline Start")
    logger.params_from_dataclass(config, source="config")
    
    start_time = datetime.now()
    
    # Step 1: Prepare
    if not prepare_test(config, logger):
        logger.result(False, 1, "Preparation failed")
        return 1
    
    # Step 2: RTL
    rtl_success, rtl_code = run_rtl_simulation(config, logger)
    if not rtl_success and not config.quick_mode:
        generate_report(config, logger, rtl_success, False, False)
        logger.result(False, rtl_code, "RTL simulation failed")
        return rtl_code
    
    # Quick mode: sadece RTL
    if config.quick_mode:
        generate_report(config, logger, rtl_success, True, True)
        end_time = datetime.now()
        elapsed = (end_time - start_time).total_seconds()
        logger.param("elapsed_seconds", round(elapsed, 2), "execution")
        logger.result(rtl_success, 0 if rtl_success else 1, "Quick mode completed")
        logger.save()
        return 0 if rtl_success else 1
    
    # Step 3: Spike
    spike_success, spike_code = run_spike(config, logger)
    
    # Step 4: Compare
    compare_success, diff_count = compare_logs(config, logger)
    
    # Step 5: Report
    generate_report(config, logger, rtl_success, spike_success, compare_success)
    
    end_time = datetime.now()
    elapsed = (end_time - start_time).total_seconds()
    
    logger.param("elapsed_seconds", round(elapsed, 2), "execution")
    
    overall_success = rtl_success and spike_success and compare_success
    logger.result(overall_success, 0 if overall_success else 1, 
                 "Test completed" if overall_success else "Test failed")
    logger.save()
    
    return 0 if overall_success else 1


# ═══════════════════════════════════════════════════════════════════════════
# CLI Interface
# ═══════════════════════════════════════════════════════════════════════════

def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="CERES RISC-V Test Runner",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --test-name rv32ui-p-add
  %(prog)s --test-name rv32ui-p-add --simulator modelsim
  %(prog)s --test-name coremark --no-spike
  %(prog)s --test-name rv32ui-p-add --quick
"""
    )
    
    # Required
    parser.add_argument(
        "--test-name", "-t",
        required=True,
        help="Test name (e.g., rv32ui-p-add, I-ADD-01, coremark)"
    )
    
    # Test type
    parser.add_argument(
        "--test-type",
        choices=["isa", "arch", "imperas", "bench", "coremark", "embench", "dhrystone", "torture", "custom", "riscv-dv"],
        help="Test type (auto-detected if not specified)"
    )
    
    # Simulator
    parser.add_argument(
        "--simulator", "-s",
        default="verilator",
        choices=["verilator", "modelsim"],
        help="Simulator to use (default: verilator)"
    )
    
    # Paths (from Makefile)
    parser.add_argument(
        "--build-dir", "-b",
        help="Build directory (default: $ROOT_DIR/build)"
    )
    parser.add_argument(
        "--root-dir", "-r",
        help="Project root directory (default: auto-detect)"
    )
    parser.add_argument(
        "--sim-dir",
        help="Simulation sources directory (default: $ROOT_DIR/sim)"
    )
    parser.add_argument(
        "--results-dir",
        help="Results directory (default: $ROOT_DIR/results)"
    )
    parser.add_argument(
        "--test-log-dir",
        help="Test log directory (overrides default)"
    )
    
    # Simulation
    parser.add_argument(
        "--max-cycles", "-c",
        type=int,
        default=100000,
        help="Maximum simulation cycles (default: 100000)"
    )
    
    # Log control (from Makefile)
    parser.add_argument("--log-commit", action="store_true", help="Enable commit logging")
    parser.add_argument("--log-bp", action="store_true", help="Enable branch predictor logging")
    parser.add_argument("--konata-tracer", action="store_true", help="Enable Konata tracer")
    parser.add_argument("--trace", action="store_true", help="Enable waveform tracing")
    
    # Pipeline control
    parser.add_argument(
        "--enable-spike",
        action="store_true",
        default=True,
        help="Enable Spike golden reference"
    )
    parser.add_argument(
        "--no-spike",
        action="store_true",
        help="Disable Spike golden reference"
    )
    parser.add_argument(
        "--enable-compare",
        action="store_true",
        default=True,
        help="Enable log comparison"
    )
    parser.add_argument(
        "--no-compare",
        action="store_true",
        help="Disable log comparison"
    )
    parser.add_argument(
        "--quick", "-q",
        action="store_true",
        help="Quick mode: RTL only, skip Spike and compare"
    )
    
    # Compare options
    parser.add_argument("--skip-csr", action="store_true", help="Skip CSR comparison")
    parser.add_argument("--resync", action="store_true", help="Resync on mismatch")
    parser.add_argument("--resync-window", type=int, default=8, help="Resync window size")
    
    # Debug
    parser.add_argument(
        "--debug",
        action="store_true",
        help="Enable debug logging"
    )
    parser.add_argument(
        "--no-color",
        action="store_true",
        help="Disable colored output"
    )
    
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    
    # Color support
    if args.no_color or not supports_color():
        Color.disable()
    
    # Root directory
    if args.root_dir:
        root_dir = Path(args.root_dir)
    else:
        # Script konumundan root'u bul
        root_dir = Path(__file__).parent.parent.parent.parent
    
    # Build directory
    build_dir = Path(args.build_dir) if args.build_dir else root_dir / "build"
    
    # Sim directory
    sim_dir = Path(args.sim_dir) if args.sim_dir else root_dir / "sim"
    
    # Results directory
    results_dir = Path(args.results_dir) if args.results_dir else root_dir / "results"
    
    # Test type detection
    test_name = args.test_name
    if args.test_type:
        test_type = args.test_type
    else:
        test_type = detect_test_type(test_name, build_dir)
        info(f"Auto-detected test type: {test_type}")
    
    # Log directory
    if args.test_log_dir:
        log_dir = Path(args.test_log_dir)
    else:
        log_dir = results_dir / "logs" / args.simulator / test_name
    
    # Pipeline control: --no-spike ve --no-compare bayraklarını işle
    skip_spike = args.no_spike or args.quick or not args.enable_spike
    skip_compare = args.no_compare or args.quick or not args.enable_compare
    
    # Config oluştur
    config = TestConfig(
        test_name=test_name,
        test_type=test_type,
        simulator=args.simulator,
        build_dir=build_dir,
        root_dir=root_dir,
        log_dir=log_dir,
        max_cycles=args.max_cycles,
        skip_spike=skip_spike,
        skip_compare=skip_compare,
        quick_mode=args.quick,
    )
    
    # Extra log options (environment variables for sub-runners)
    if args.log_commit:
        os.environ["LOG_COMMIT"] = "1"
    if args.log_bp:
        os.environ["LOG_BP"] = "1"
    if args.konata_tracer:
        os.environ["KONATA_TRACER"] = "1"
    if args.trace:
        os.environ["TRACE"] = "1"
    
    # Debug logger
    debug_enabled = args.debug or os.environ.get("CERES_DEBUG", "0") == "1"
    logger = create_logger(
        tool_name="test_runner",
        log_dir=log_dir,
        debug_enabled=debug_enabled
    )
    
    # CLI args logla
    logger.section("CLI Arguments")
    logger.params_from_dict(vars(args), source="cli")
    
    # Extra config params
    logger.section("Resolved Configuration")
    logger.param("root_dir", root_dir, "resolved")
    logger.param("build_dir", build_dir, "resolved")
    logger.param("sim_dir", sim_dir, "resolved")
    logger.param("results_dir", results_dir, "resolved")
    logger.param("log_dir", log_dir, "resolved")
    logger.param("skip_spike", skip_spike, "resolved")
    logger.param("skip_compare", skip_compare, "resolved")
    
    # Pipeline çalıştır
    return run_test_pipeline(config, logger)


if __name__ == "__main__":
    sys.exit(main())
