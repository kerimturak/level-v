#!/usr/bin/env bash
set -euo pipefail

# setup_coremark.sh
# Clone CoreMark (if missing), configure a simple build for a RISC-V cross toolchain,
# build an ELF, generate binary and .mem using tools/elf_to_mem.py
# Usage: ./tools/setup_coremark.sh [--coremark-dir DIR] [--cross CROSS] [--march MARCH] [--mabi MABI]

COREMARK_DIR="coremark"
CROSS=${CROSS:-riscv32-unknown-elf-}
MARCH=${MARCH:-rv32imc}
MABI=${MABI:-ilp32}
OUT_DIR="build/coremark_build"
MEM_OUT_DIR="build/tests/mem"
THREADS=${THREADS:-4}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --coremark-dir) COREMARK_DIR="$2"; shift 2;;
    --cross) CROSS="$2"; shift 2;;
    --march) MARCH="$2"; shift 2;;
    --mabi) MABI="$2"; shift 2;;
    --out) OUT_DIR="$2"; shift 2;;
    --help) echo "Usage: $0 [--coremark-dir DIR] [--cross CROSS] [--march MARCH] [--mabi MABI]"; exit 0;;
    *) echo "Unknown arg: $1"; exit 1;;
  esac
done

echo "CoreMark setup helper"
echo "COREMARK_DIR=$COREMARK_DIR CROSS=$CROSS MARCH=$MARCH MABI=$MABI"

# Remember repository root so we can write output files using absolute paths
ROOT_DIR="$(pwd)"

# If a git submodule is configured, try to init/update it
if [ -f .gitmodules ]; then
  echo "Attempting to init/update git submodules (if configured)..."
  git submodule update --init --recursive || true
fi

if [ ! -d "$COREMARK_DIR" ]; then
  echo "CoreMark directory '$COREMARK_DIR' not found. Cloning from upstream..."
  git clone https://github.com/eembc/coremark.git "$COREMARK_DIR"
fi

# Create out dirs
mkdir -p "$OUT_DIR"
mkdir -p "$MEM_OUT_DIR"

# Attempt to build CoreMark using its Makefile, but keep it flexible.
# CoreMark repo has a set of ports; the easiest way is to build the "coremark" benchmark
# using a small portable configuration.

# Copy CoreMark sources into OUT_DIR/coremark_src but exclude the .git
# directory (some environments restrict copying .git objects). Use tar to
# avoid recreating problematic .git files.
mkdir -p "$OUT_DIR/coremark_src"
(
  cd "$COREMARK_DIR"
  tar --exclude='.git' -cf - .
) | (
  cd "$OUT_DIR/coremark_src"
  tar -xf -
)

pushd "$OUT_DIR/coremark_src" > /dev/null

# Try to build a barebone coremark using CROSS toolchain
# The CoreMark repo uses ports; we'll compile the benchmark C files directly.

# Determine compiler (prefer CROSS gcc if available)
if command -v "${CROSS}gcc" >/dev/null 2>&1; then
  CC="${CROSS}gcc"
  OBJCOPY="${CROSS}objcopy"
else
  echo "Warning: ${CROSS}gcc not found, falling back to host gcc for a quick build."
  CC=gcc
  OBJCOPY=objcopy
fi

SRCS=()
for f in core_mark.c core_main.c core_util.c core_list_join.c core_matrix.c core_state.c; do
  if [ -f "$f" ]; then SRCS+=("$f"); fi
done
# Prefer the barebones ported core_portme.c if present
if [ -f ./barebones/core_portme.c ]; then
  SRCS+=("./barebones/core_portme.c")
elif [ -f ./core_portme.c ]; then
  SRCS+=("./core_portme.c")
fi

if [ ${#SRCS[@]} -eq 0 ]; then
  echo "No CoreMark C sources found in $COREMARK_DIR; aborting." >&2
  exit 1
fi

if [ "$CC" = "gcc" ]; then
  CFLAGS="-O2 -DCOREMARK_PORTME_USE_STDINT -DVALIDATION_RUN -DITERATIONS=1 -Dprintf=ee_printf"
  LDFLAGS=""
else
  CFLAGS="-march=${MARCH} -mabi=${MABI} -O2 -DCOREMARK_PORTME_USE_STDINT -DVALIDATION_RUN -DITERATIONS=1 -Dprintf=ee_printf"
  LDFLAGS="-Ttext=0x80000000 -static"
fi

# When building from inside $OUT_DIR/coremark_src, write the ELF into the
# current directory to avoid path resolution issues during linking.
OUTPUT_ELF="./coremark.elf"

echo "Compiling CoreMark to $OUTPUT_ELF"
$CC $CFLAGS -I. -I./barebones "${SRCS[@]}" -o "$OUTPUT_ELF" $LDFLAGS || {
  echo "Compilation failed; try adjusting CROSS/MARCH/MABI or check toolchain availability." >&2
  exit 1
}

# Produce binary and .mem (write binary in current dir, then copy to OUT_DIR)
OUTPUT_BIN="./coremark.bin"
$OBJCOPY -O binary "$OUTPUT_ELF" "$OUTPUT_BIN"
  cp "$OUTPUT_BIN" "$ROOT_DIR/$OUT_DIR/coremark.bin"

# Convert to .mem using the Python tool
MEM_FILE="$ROOT_DIR/$MEM_OUT_DIR/coremark.mem"
python3 "$ROOT_DIR/tools/elf_to_mem.py" --in "$ROOT_DIR/$OUT_DIR/coremark.bin" --out "$MEM_FILE" --block-bytes 16 --word-size 4 --word-endian little --word-order high-to-low

echo "CoreMark built. .mem written to: $MEM_FILE"
popd > /dev/null

# Suggest next steps
cat <<EOF
Done. Next steps:
 - Inspect $MEM_FILE and move it to your simulator expected path (or set +INIT_FILE=...).
 - Run Verilator/ModelSim with +fetch_log enabled to verify fetch traces.
EOF
