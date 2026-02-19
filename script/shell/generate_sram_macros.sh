#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DESIGN_DIR="${ROOT_DIR}/asic/openlane/designs/ceres_wrapper"
MACRO_REPO_URL="${MACRO_REPO_URL:-https://github.com/efabless/sky130_sram_macros.git}"
MACRO_NAME="${MACRO_NAME:-sky130_sram_1kbyte_1rw1r_32x256_8}"

OUT_ROOT="${DESIGN_DIR}/macros"
OUT_DIR="${OUT_ROOT}/${MACRO_NAME}"
CACHE_ROOT="${ROOT_DIR}/build/cache"
SRC_REPO_DIR="${CACHE_ROOT}/sky130_sram_macros"
SRC_DIR="${SRC_REPO_DIR}/${MACRO_NAME}"

usage() {
    cat <<EOF
Usage: $0 [--clean]

Downloads (or updates) SRAM macro collateral and materializes it under:
  ${OUT_DIR}

Outputs:
  - ${MACRO_NAME}.lef
  - ${MACRO_NAME}.gds
  - ${MACRO_NAME}_TT_1p8V_25C.lib
  - ${MACRO_NAME}.v

Environment variables:
  MACRO_REPO_URL  (default: ${MACRO_REPO_URL})
  MACRO_NAME      (default: ${MACRO_NAME})
EOF
}

need_cmd() {
    command -v "$1" >/dev/null 2>&1 || {
        echo "[sram] ERROR: '$1' not found in PATH"
        exit 1
    }
}

clean_only=0
if [[ "${1:-}" == "--clean" ]]; then
    clean_only=1
elif [[ -n "${1:-}" ]]; then
    usage
    exit 1
fi

mkdir -p "${OUT_ROOT}"

if [[ ${clean_only} -eq 1 ]]; then
    rm -rf "${OUT_DIR}"
    echo "[sram] Cleaned: ${OUT_DIR}"
    exit 0
fi

need_cmd git

mkdir -p "${CACHE_ROOT}"
if [[ -d "${SRC_REPO_DIR}/.git" ]]; then
    echo "[sram] Updating cache repo: ${SRC_REPO_DIR}"
    git -C "${SRC_REPO_DIR}" fetch --depth 1 origin main >/dev/null 2>&1 || true
    git -C "${SRC_REPO_DIR}" checkout -q main >/dev/null 2>&1 || true
    git -C "${SRC_REPO_DIR}" reset -q --hard origin/main >/dev/null 2>&1 || true
else
    echo "[sram] Cloning macro repo: ${MACRO_REPO_URL}"
    rm -rf "${SRC_REPO_DIR}"
    git clone --depth 1 "${MACRO_REPO_URL}" "${SRC_REPO_DIR}"
fi

if [[ ! -d "${SRC_DIR}" ]]; then
    echo "[sram] ERROR: Macro directory not found: ${SRC_DIR}"
    exit 1
fi

mkdir -p "${OUT_DIR}"

required_files=(
    "${MACRO_NAME}.lef"
    "${MACRO_NAME}.gds"
    "${MACRO_NAME}_TT_1p8V_25C.lib"
    "${MACRO_NAME}.v"
)

for f in "${required_files[@]}"; do
    if [[ ! -f "${SRC_DIR}/${f}" ]]; then
        echo "[sram] ERROR: Missing source file: ${SRC_DIR}/${f}"
        exit 1
    fi
done

for f in "${required_files[@]}"; do
    cp -f "${SRC_DIR}/${f}" "${OUT_DIR}/${f}"
done

# ── Liberty max_transition fix ──────────────────────────────────
# OpenSRAM jeneratörü, timing tablosunun index_1 üst sınırını (0.04 ns)
# max_transition olarak atıyor. Bu 40 ps değeri gerçek bir fiziksel sınır
# değil, sadece karakterizasyon aralığının üst sınırı.
# SKY130 standart hücreleri 1.5 ns kullanır; SRAM pinleri de bunu destekler.
# Düzeltilmezse OpenLane Step 16'da RSZ-0090 hatası verir.
# Bkz: macros/<MACRO_NAME>/README.md
LIB_FILE="${OUT_DIR}/${MACRO_NAME}_TT_1p8V_25C.lib"
if [[ -f "${LIB_FILE}" ]]; then
    if grep -q 'max_transition.*: 0.04;' "${LIB_FILE}"; then
        echo "[sram] Fixing Liberty max_transition (0.04 → 1.5 ns)..."
        sed -i 's/max_transition\(\s*\): 0.04;/max_transition\1: 1.5;/g' "${LIB_FILE}"
        sed -i 's/default_max_transition\(\s*\): 0.5 ;/default_max_transition\1: 1.5 ;/g' "${LIB_FILE}"
        echo "[sram] Liberty max_transition fixed for OpenLane compatibility."
    fi
fi

echo "[sram] Macro generated/materialized: ${MACRO_NAME}"
echo "[sram] Output directory: ${OUT_DIR}"
ls -lh "${OUT_DIR}" | sed 's/^/[sram] /'
