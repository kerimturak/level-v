#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COREMARK_DIR="${COREMARK_DIR:-$ROOT_DIR/../coremark}"
CROSS="${CROSS:-riscv32-unknown-elf-}"
ENV_COMMON="$ROOT_DIR/env/common"
OUT_DIR="${OUT_DIR:-$ROOT_DIR/build/tests/coremark_env}"
ITERATIONS="${ITERATIONS:-1}"

usage(){
  cat <<EOF
Usage: $0 [--coremark-dir DIR] [--cross PREFIX] [--out-dir DIR] [--iterations N]

Build CoreMark using env/common linker script, crt and syscalls.

Defaults:
  COREMARK_DIR=$COREMARK_DIR
  CROSS=$CROSS
  ENV_COMMON=$ENV_COMMON
  OUT_DIR=$OUT_DIR
  ITERATIONS=$ITERATIONS

Examples:
  $0 --coremark-dir /home/kerim/coremark --iterations 1

EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --coremark-dir) COREMARK_DIR="$2"; shift 2;;
    --cross) CROSS="$2"; shift 2;;
    --out-dir) OUT_DIR="$2"; shift 2;;
    --iterations) ITERATIONS="$2"; shift 2;;
    -h|--help) usage; exit 0;;
    *) echo "Unknown arg: $1"; usage; exit 1;;
  esac
done

mkdir -p "$OUT_DIR"

CC="${CROSS}gcc"
OBJCOPY="${CROSS}objcopy"

echo "Building CoreMark using:"
echo "  COREMARK_DIR=$COREMARK_DIR"
echo "  CROSS=$CROSS"
echo "  ENV_COMMON=$ENV_COMMON"
echo "  OUT_DIR=$OUT_DIR"
echo "  ITERATIONS=$ITERATIONS"

if ! command -v "$CC" >/dev/null 2>&1; then
  echo "Error: compiler $CC not found in PATH" >&2
  exit 1
fi

INCLUDES=(
  -I"$COREMARK_DIR"
  -I"$COREMARK_DIR/barebones"
  -I"$ROOT_DIR/build/coremark_build/coremark_src/barebones"
  -I"$ROOT_DIR/subrepo/riscv-tests/env"
  -I"$ENV_COMMON"
)

COREMARK_DIR=/home/kerim/riscv/ceres-riscv/build/coremark_build/coremark_src
SOURCES=(
  "$COREMARK_DIR/core_main.c"
  "$COREMARK_DIR/core_list_join.c"
  "$COREMARK_DIR/core_matrix.c"
  "$COREMARK_DIR/core_state.c"
  "$COREMARK_DIR/core_util.c"
  "$COREMARK_DIR/barebones/core_portme.c"
  "$ENV_COMMON/crt.S"
  "$ENV_COMMON/syscalls.c"
)

OUT_ELF="$OUT_DIR/coremark.elf"
OUT_BIN="$OUT_DIR/coremark.bin"
OUT_MEM="$OUT_DIR/coremark.mem"

try_compile(){
  local march_opt="$1"
  echo "Trying build with -march=$march_opt"
  OBJ_DIR="$(mktemp -d)"
  set -x
  # Compile C sources (except core_portme) without mapping printf
  for src in \
    "$COREMARK_DIR/core_main.c" \
    "$COREMARK_DIR/core_list_join.c" \
    "$COREMARK_DIR/core_matrix.c" \
    "$COREMARK_DIR/core_state.c" \
    "$COREMARK_DIR/core_util.c"; do
    "$CC" -march="$march_opt" -mabi=ilp32 -O2 -c ${INCLUDES[*]} -o "$OBJ_DIR/$(basename "$src" .c).o" "$src" || { set +x; return 1; }
  done

  # core_portme needs ITERATIONS and printf mapping to ee_printf
  "$CC" -march="$march_opt" -mabi=ilp32 -O2 -c ${INCLUDES[*]} -DITERATIONS="$ITERATIONS" -Dprintf=ee_printf -o "$OBJ_DIR/core_portme.o" "$COREMARK_DIR/barebones/core_portme.c" || { set +x; return 1; }

  # compile syscalls (do not map printf here)
  "$CC" -march="$march_opt" -mabi=ilp32 -O2 -c ${INCLUDES[*]} -o "$OBJ_DIR/syscalls.o" "$ENV_COMMON/syscalls.c" || { set +x; return 1; }

  # assemble crt.S (include headers path)
  "$CC" -march="$march_opt" -mabi=ilp32 -O2 -c ${INCLUDES[*]} -o "$OBJ_DIR/crt.o" "$ENV_COMMON/crt.S" || { set +x; return 1; }

  # Link; include libgcc for helper routines (soft-fp helpers)
  "$CC" -march="$march_opt" -mabi=ilp32 -nostdlib -static -T "$ENV_COMMON/test.ld" -o "$OUT_ELF" "$OBJ_DIR"/*.o -lgcc || { set +x; return 1; }
  set +x
  rm -rf "$OBJ_DIR"
  return 0
}

# First try with zicsr-aware march if assembler CSR ops are used
if try_compile "rv32imc_zicsr"; then
  echo "Build succeeded with rv32imc_zicsr"
elif try_compile "rv32imc_zicsr"; then
  echo "Build succeeded with rv32imc"
else
  echo "Build failed with attempted ISA variants." >&2
  exit 1
fi

echo "Generating binary and .mem"
"$OBJCOPY" -O binary "$OUT_ELF" "$OUT_BIN"

if [[ -x "$ROOT_DIR/tools/elf_to_mem.py" ]]; then
  python3 "$ROOT_DIR/tools/elf_to_mem.py" --in "$OUT_BIN" --out "$OUT_MEM" --block-bytes 16 --word-size 4 --word-endian little --word-order high-to-low
else
  # Fallback: write simple hex words (little-endian 32-bit) one per line
  echo "# elf_to_mem.py not found; producing raw binary only" >&2
fi

echo "Build outputs in: $OUT_DIR"
readelf -l "$OUT_ELF" || true

echo "Done. To run on Spike use something like:"
echo "  spike --isa=rv32imc -m0x80000000:64M $OUT_ELF"
