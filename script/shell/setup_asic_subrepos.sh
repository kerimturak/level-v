#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SUBREPO_DIR="${ROOT_DIR}/subrepo"
ASIC_SUBREPO_DIR="${SUBREPO_DIR}/asic-tools"

mkdir -p "${ASIC_SUBREPO_DIR}"

clone_or_update() {
    local name="$1"
    local url="$2"
    local branch="${3:-}"
    local target="${ASIC_SUBREPO_DIR}/${name}"

    if [[ -d "${target}/.git" ]]; then
        echo "[asic-subrepo] update: ${name}"
        git -C "${target}" fetch --depth 1 origin "${branch:-HEAD}" >/dev/null 2>&1 || true
        if [[ -n "${branch}" ]]; then
            git -C "${target}" checkout "${branch}" >/dev/null 2>&1 || true
            git -C "${target}" pull --ff-only origin "${branch}" >/dev/null 2>&1 || true
        fi
    else
        echo "[asic-subrepo] clone : ${name} <- ${url}"
        if [[ -n "${branch}" ]]; then
            git clone --depth 1 --branch "${branch}" "${url}" "${target}"
        else
            git clone --depth 1 "${url}" "${target}"
        fi
    fi
}

echo "[asic-subrepo] target dir: ${ASIC_SUBREPO_DIR}"

# Core physical-design flow repositories
clone_or_update "OpenLane" "https://github.com/The-OpenROAD-Project/OpenLane.git" "master"
clone_or_update "OpenROAD" "https://github.com/The-OpenROAD-Project/OpenROAD.git" "master"
clone_or_update "OpenROAD-flow-scripts" "https://github.com/The-OpenROAD-Project/OpenROAD-flow-scripts.git" "master"

# Open MPW / shuttle templates
clone_or_update "caravel_user_project" "https://github.com/efabless/caravel_user_project.git" "main"
clone_or_update "caravel" "https://github.com/efabless/caravel.git" "main"

cat <<EOF
[asic-subrepo] done.

Not:
  - sky130 PDK repo çok büyük olduğu için burada clone edilmiyor.
  - PDK için Volare yolu önerilir: PDK_ROOT=\$HOME/.volare, PDK=sky130A
EOF
