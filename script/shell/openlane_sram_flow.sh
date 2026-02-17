#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OPENLANE_FLOW="${ROOT_DIR}/script/shell/openlane_flow.sh"
SRAM_GEN="${ROOT_DIR}/script/shell/generate_sram_macros.sh"
RESUME_TCL="${ROOT_DIR}/asic/openlane/resume_routing.tcl"
OPENLANE_IMAGE="${OPENLANE_IMAGE:-efabless/openlane:2023.09.07}"
PDK_ROOT="${PDK_ROOT:-${HOME}/.volare}"
PDK="${PDK:-sky130A}"
DOCKER_CPUS="${DOCKER_CPUS:-}"
DOCKER_CPU_SHARES="${DOCKER_CPU_SHARES:-}"

usage() {
    cat <<EOF
Usage: $0 <setup|sram|run|resume>

Commands:
  setup   : OpenLane setup + SRAM macro materialization
  sram    : Only materialize SRAM macros
  run     : SRAM + source prep + full OpenLane run
  resume  : SRAM + continue using interactive resume_routing.tcl
EOF
}

run_resume() {
    local docker_extra_args=()
    [[ -n "${DOCKER_CPUS}" ]] && docker_extra_args+=(--cpus "${DOCKER_CPUS}")
    [[ -n "${DOCKER_CPU_SHARES}" ]] && docker_extra_args+=(--cpu-shares "${DOCKER_CPU_SHARES}")
    docker run --rm \
        -u "$(id -u):$(id -g)" \
        -e PDK_ROOT="${PDK_ROOT}" \
        -e PDK="${PDK}" \
        "${docker_extra_args[@]}" \
        -v "${ROOT_DIR}:${ROOT_DIR}" \
        -v "${PDK_ROOT}:${PDK_ROOT}" \
        -w "${ROOT_DIR}" \
        "${OPENLANE_IMAGE}" \
        /bin/bash -lc "/openlane/flow.tcl -interactive -file ${RESUME_TCL}"
}

cmd="${1:-}"
case "${cmd}" in
    setup)
        bash "${OPENLANE_FLOW}" setup
        bash "${SRAM_GEN}"
        ;;
    sram)
        bash "${SRAM_GEN}"
        ;;
    run)
        bash "${SRAM_GEN}"
        bash "${OPENLANE_FLOW}" run
        ;;
    resume)
        bash "${SRAM_GEN}"
        run_resume
        ;;
    *)
        usage
        exit 1
        ;;
esac
