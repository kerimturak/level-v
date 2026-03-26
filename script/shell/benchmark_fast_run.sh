#!/usr/bin/env bash
# Level-V — Hızlı benchmark koşuları (SIM_FAST + MINIMAL_SOC + düşük/orta MAX_CYCLES).
# Skor metni: UART loglarına bakın (aşağıdaki show_score).
#
# Kullanım:
#   ./script/shell/benchmark_fast_run.sh list    # sadece komutları yazdırır
#   ./script/shell/benchmark_fast_run.sh all     # sırayla dener (uzun sürer)
#   ./script/shell/benchmark_fast_run.sh coremark
#
# Önkoşullar: repo kökünden; RISCV_PREFIX (örn. riscv-none-elf); gerekli subrepo/build.

set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

export RISCV_PREFIX="${RISCV_PREFIX:-riscv-none-elf}"

# Verilator modeli — küçük cache/BP, trace kapalı
VFAST="SIM_FAST=1 MINIMAL_SOC=1 TRACE=0"

# CoreMark: skor satırı için yeterli iterasyon (daha hızlı deneme: 50)
COREMARK_ITER="${COREMARK_ITER:-200}"

# RTL döngü üst sınırı — “score” için CoreMark yine de wall-clock kuralına takılabilir (core_main 10s kuralı)
CM_CYCLES="${CM_CYCLES:-15000000}"
DHRY_CYCLES="${DHRY_CYCLES:-3000000}"
BENCH_CYCLES="${BENCH_CYCLES:-400000}"
EMB_CYCLES="${EMB_CYCLES:-400000}"

show_score() {
	local name="$1"
	local log="$ROOT/results/logs/verilator/$name/uart_output.log"
	if [[ -f "$log" ]]; then
		echo "──── UART: $log ────"
		tail -n 40 "$log"
	else
		echo "(yok) $log"
	fi
	echo ""
}

cmd_coremark() {
	echo "=== CoreMark ==="
	echo "make verilate TEST_CONFIG=coremark $VFAST"
	echo "make coremark COREMARK_ITERATIONS=$COREMARK_ITER"
	echo "make run_coremark MAX_CYCLES=$CM_CYCLES"
	echo "# Sonuç: results/logs/verilator/coremark/uart_output.log"
}

run_coremark() {
	make verilate TEST_CONFIG=coremark $VFAST
	make coremark COREMARK_ITERATIONS="$COREMARK_ITER"
	make run_coremark MAX_CYCLES="$CM_CYCLES"
	show_score coremark
}

cmd_dhrystone() {
	echo "=== Dhrystone ==="
	echo "make verilate TEST_CONFIG=dhrystone $VFAST"
	echo "make dhrystone"
	echo "make dhrystone_run MAX_CYCLES=$DHRY_CYCLES"
	echo "# Sonuç: results/logs/verilator/dhrystone/uart_output.log"
}

run_dhrystone() {
	make verilate TEST_CONFIG=dhrystone $VFAST
	make dhrystone
	# Üst Makefile MAX_CYCLES alt make’lere iletilir
	make dhrystone_run MAX_CYCLES="$DHRY_CYCLES"
	show_score dhrystone
}

cmd_riscv_bench() {
	echo "=== riscv-tests benchmarks (sim/test/riscv_benchmark.flist) ==="
	echo "# Önce: make bench_auto   veya bench_build + bench_import"
	echo "make verilate TEST_CONFIG=bench $VFAST"
	echo "make bench BENCH_MAX_CYCLES=$BENCH_CYCLES"
	echo "# Sonuç (örnek): results/logs/verilator/median/uart_output.log"
}

run_riscv_bench() {
	if [[ ! -d "$ROOT/build/tests/riscv-benchmarks/elf" ]] || [[ -z "$(ls -A "$ROOT/build/tests/riscv-benchmarks/elf" 2>/dev/null)" ]]; then
		echo "[WARN] riscv-benchmarks elf yok; önce: make bench_auto"
		return 0
	fi
	make verilate TEST_CONFIG=bench $VFAST
	make bench BENCH_MAX_CYCLES="$BENCH_CYCLES"
	echo "Örnek log:"
	show_score median
}

cmd_embench() {
	echo "=== Embench-IoT ==="
	echo "# Önce: make embench (veya repo hazırsa)"
	echo "make verilate TEST_CONFIG=embench $VFAST"
	echo "make embench_run_all MAX_CYCLES=$EMB_CYCLES"
	echo "# veya tek: make embench_run_one BENCH=crc32 MAX_CYCLES=$EMB_CYCLES"
	echo "# Sonuç: results/logs/verilator/<bench>/uart_output.log"
}

run_embench() {
	if [[ ! -d "$ROOT/build/tests/embench/mem" ]] || [[ -z "$(ls -A "$ROOT/build/tests/embench/mem"/*.mem 2>/dev/null)" ]]; then
		echo "[WARN] Embench .mem yok; önce: make embench (veya embench_clone + build)"
		return 0
	fi
	make verilate TEST_CONFIG=embench $VFAST
	make embench_run_all MAX_CYCLES="$EMB_CYCLES"
}

list_only() {
	cmd_coremark
	echo ""
	cmd_dhrystone
	echo ""
	cmd_riscv_bench
	echo ""
	cmd_embench
	echo ""
	echo "Tek test (Verilator, bench profili, hızlı):"
	echo "  make verilate TEST_CONFIG=bench $VFAST"
	echo "  make run_verilator TEST_NAME=median TEST_CONFIG=bench NO_ADDR=1 MAX_CYCLES=$BENCH_CYCLES MEM_FILE=\$(pwd)/build/tests/riscv-benchmarks/mem/median.mem"
	echo "  # .mem yolu import sonrası; yoksa: make bench_import"
}

case "${1:-list}" in
	list|commands)
		list_only
		;;
	coremark)
		run_coremark
		;;
	dhrystone)
		run_dhrystone
		;;
	bench|riscv)
		run_riscv_bench
		;;
	embench)
		run_embench
		;;
	all)
		run_coremark
		run_dhrystone
		run_riscv_bench
		run_embench
		echo "Bitti. Özet için: grep -R . results/logs/verilator/*/uart_output.log | tail"
		;;
	*)
		echo "Usage: $0 list|coremark|dhrystone|bench|embench|all"
		exit 1
		;;
esac
