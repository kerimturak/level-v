#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DESIGN_DIR="${ROOT_DIR}/asic/openlane/designs/level_wrapper"
CONFIG_TCL="${DESIGN_DIR}/config.tcl"

RESULTS_ROOT="${RESULTS_ROOT:-${ROOT_DIR}/results/asic/librelane/level_wrapper}"
RUNS_DIR="${RESULTS_ROOT}/runs"

PDK_ROOT="${PDK_ROOT:-${HOME}/.volare}"
PDK="${PDK:-sky130A}"
TAG="${TAG:-run_$(date +%Y%m%d_%H%M%S)}"

LIBRELANE_MODE="${LIBRELANE_MODE:-docker}" # docker|local
LIBRELANE_CMD="${LIBRELANE_CMD:-librelane}"
LIBRELANE_PY_FALLBACK="${LIBRELANE_PY_FALLBACK:-python3 -m librelane}"
LIBRELANE_DOCKER_MOUNTS="${LIBRELANE_DOCKER_MOUNTS:-}"

usage() {
    cat <<EOF
Usage: $0 <setup|prep|run|report|clean|check>

Commands:
  setup   : Check LibreLane CLI and run smoke test
  prep    : Prepare RTL sources under asic/openlane/designs/level_wrapper/src
  run     : Run LibreLane flow with existing OpenLane-compatible config.tcl
  report  : Show latest run summary and key report paths
  clean   : Remove LibreLane runs and prepared src
  check   : Print dependency status

Environment variables:
  LIBRELANE_MODE        docker|local (default: ${LIBRELANE_MODE})
  LIBRELANE_CMD         CLI binary (default: ${LIBRELANE_CMD})
  LIBRELANE_PY_FALLBACK Python fallback command (default: ${LIBRELANE_PY_FALLBACK})
  LIBRELANE_DOCKER_MOUNTS Extra mounts (space-separated), used as repeated --docker-mount
  PDK_ROOT              PDK root path (default: ${PDK_ROOT})
  PDK                   PDK variant   (default: ${PDK})
  TAG                   Run tag       (default: ${TAG})
  RESULTS_ROOT          Output root   (default: ${RESULTS_ROOT})
EOF
}

has_cmd() {
    command -v "$1" >/dev/null 2>&1
}

resolve_librelane_cmd() {
    if has_cmd "${LIBRELANE_CMD}"; then
        echo "${LIBRELANE_CMD}"
        return 0
    fi

    if has_cmd python3; then
        echo "${LIBRELANE_PY_FALLBACK}"
        return 0
    fi

    return 1
}

latest_run_dir() {
    if [[ ! -d "${RUNS_DIR}" ]]; then
        return 1
    fi
    ls -1dt "${RUNS_DIR}"/* 2>/dev/null | head -n1
}

do_check() {
    local cli
    cli="$(resolve_librelane_cmd || true)"

    echo "[librelane:check] ROOT_DIR   : ${ROOT_DIR}"
    echo "[librelane:check] DESIGN_DIR : ${DESIGN_DIR}"
    echo "[librelane:check] CONFIG_TCL : ${CONFIG_TCL}"
    echo "[librelane:check] PDK_ROOT   : ${PDK_ROOT}"
    echo "[librelane:check] PDK        : ${PDK}"
    echo "[librelane:check] MODE       : ${LIBRELANE_MODE}"

    if [[ -n "${cli}" ]]; then
        echo "[librelane:check] CLI        : ${cli}"
    else
        echo "[librelane:check] CLI        : MISSING"
    fi

    [[ -f "${CONFIG_TCL}" ]] && echo "[librelane:check] config.tcl present" || echo "[librelane:check] ERROR: config.tcl missing"
    [[ -d "${PDK_ROOT}/${PDK}" ]] && echo "[librelane:check] PDK present" || echo "[librelane:check] WARNING: PDK missing at ${PDK_ROOT}/${PDK}"
}

do_setup() {
    local cli
    cli="$(resolve_librelane_cmd || true)"
    if [[ -z "${cli}" ]]; then
        echo "[librelane:setup] ERROR: LibreLane CLI not found."
        echo "[librelane:setup] Install with: python3 -m pip install --upgrade librelane"
        exit 1
    fi

    echo "[librelane:setup] CLI: ${cli}"
    echo "[librelane:setup] Running smoke test..."
    # Smoke test validates that CLI and environment are working.
    ${cli} --smoke-test
}

do_prep() {
    "${ROOT_DIR}/script/shell/prepare_openlane_sources.sh"
}

run_librelane() {
    local cli
    cli="$(resolve_librelane_cmd || true)"
    if [[ -z "${cli}" ]]; then
        echo "[librelane:run] ERROR: LibreLane CLI not found."
        exit 1
    fi

    local args=()
    args+=(--pdk-root "${PDK_ROOT}")
    args+=(--run-tag "${TAG}")

    if [[ "${LIBRELANE_MODE}" == "docker" ]]; then
        args+=(--dockerized)
        if [[ -n "${LIBRELANE_DOCKER_MOUNTS}" ]]; then
            # shellcheck disable=SC2206
            local mounts=( ${LIBRELANE_DOCKER_MOUNTS} )
            local m
            for m in "${mounts[@]}"; do
                args+=(--docker-mount "${m}")
            done
        fi
    elif [[ "${LIBRELANE_MODE}" != "local" ]]; then
        echo "[librelane:run] ERROR: LIBRELANE_MODE must be docker or local"
        exit 1
    fi

    mkdir -p "${RUNS_DIR}"

    # Use symlinked run directory to keep outputs under results/asic/librelane.
    mkdir -p "${DESIGN_DIR}"
    rm -rf "${DESIGN_DIR}/runs"
    ln -s "${RUNS_DIR}" "${DESIGN_DIR}/runs"

    echo "[librelane:run] Running with mode=${LIBRELANE_MODE}"
    echo "[librelane:run] config=${CONFIG_TCL}"
    echo "[librelane:run] tag=${TAG}"
    ${cli} "${args[@]}" "${CONFIG_TCL}"
}

do_run() {
    do_prep

    if [[ ! -f "${CONFIG_TCL}" ]]; then
        echo "[librelane:run] ERROR: config.tcl not found: ${CONFIG_TCL}"
        exit 1
    fi

    run_librelane
    do_report
}

do_report() {
    local run_dir
    if ! run_dir="$(latest_run_dir)"; then
        echo "[librelane:report] No runs found in ${RUNS_DIR}"
        exit 1
    fi

    echo "[librelane:report] Latest run: ${run_dir}"

    local metrics_csv="${run_dir}/final/metrics.csv"
    local metrics_json="${run_dir}/final/metrics.json"
    local resolved="${run_dir}/resolved.json"
    local final_gds="${run_dir}/final/gds/${PDK}/${DESIGN_DIR##*/}.gds"
    local final_def="${run_dir}/final/def/${PDK}/${DESIGN_DIR##*/}.def"
    local final_netlist="${run_dir}/final/nl/${PDK}/${DESIGN_DIR##*/}.nl.v"

    [[ -f "${resolved}" ]] && echo "  Resolved   : ${resolved}" || true
    [[ -f "${metrics_csv}" ]] && echo "  MetricsCSV : ${metrics_csv}" || true
    [[ -f "${metrics_json}" ]] && echo "  MetricsJSON: ${metrics_json}" || true
    [[ -f "${final_gds}" ]] && echo "  GDS        : ${final_gds}" || true
    [[ -f "${final_def}" ]] && echo "  DEF        : ${final_def}" || true
    [[ -f "${final_netlist}" ]] && echo "  Netlist    : ${final_netlist}" || true
}

do_clean() {
    rm -rf "${RUNS_DIR}" "${DESIGN_DIR}/src" "${DESIGN_DIR}/sources_manifest.txt"
    rm -f "${DESIGN_DIR}/runs"
    echo "[librelane:clean] Cleaned runs and prepared source tree."
}

main() {
    local cmd="${1:-}"
    case "${cmd}" in
        setup) do_setup ;;
        prep) do_prep ;;
        run) do_run ;;
        report) do_report ;;
        clean) do_clean ;;
        check) do_check ;;
        *) usage; exit 1 ;;
    esac
}

main "$@"