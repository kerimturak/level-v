#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ASIC_SUBMODULES=(
    "subrepo/asic-tools/OpenLane"
    "subrepo/asic-tools/OpenROAD"
    "subrepo/asic-tools/OpenROAD-flow-scripts"
    "subrepo/asic-tools/caravel"
    "subrepo/asic-tools/caravel_user_project"
)

cd "${ROOT_DIR}"

for sm in "${ASIC_SUBMODULES[@]}"; do
    echo "[asic-subrepo] update: ${sm}"
  git submodule update --init --depth 1 "${sm}"
done

cat <<EOF
[asic-subrepo] done.

Not:
  - sky130 PDK repo çok büyük olduğu için burada clone edilmiyor.
  - PDK için Volare yolu önerilir: PDK_ROOT=\$HOME/.volare, PDK=sky130A
EOF
