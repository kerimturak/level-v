#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DESIGN_DIR="${ROOT_DIR}/asic/openlane/designs/ceres_wrapper"
RESULTS_ROOT="${RESULTS_ROOT:-${ROOT_DIR}/results/asic/openlane/ceres_wrapper}"
RUNS_DIR="${RESULTS_ROOT}/runs"

OPENLANE_IMAGE="${OPENLANE_IMAGE:-efabless/openlane:2023.09.07}"
PDK_ROOT="${PDK_ROOT:-${HOME}/.volare}"
PDK="${PDK:-sky130A}"
TAG="${TAG:-run_$(date +%Y%m%d_%H%M%S)}"
DOCKER_CPUS="${DOCKER_CPUS:-}"
DOCKER_CPU_SHARES="${DOCKER_CPU_SHARES:-}"
OPENLANE_MODE="${OPENLANE_MODE:-auto}"   # auto|docker|local
OPENLANE_LOCAL_ROOT="${OPENLANE_LOCAL_ROOT:-${ROOT_DIR}/subrepo/asic-tools/OpenLane}"

usage() {
    cat <<EOF
Usage: $0 <setup|prep|run|report|clean>

Commands:
  setup   : Check Docker and pull OpenLane image
  prep    : Prepare OpenLane source tree from rtl/
  run     : Run full OpenLane flow (prep + flow.tcl)
  report  : Show latest run summary and key report paths
  clean   : Remove OpenLane generated run data and prepared src/

Environment variables:
  OPENLANE_IMAGE  Docker image (default: ${OPENLANE_IMAGE})
  PDK_ROOT        PDK root path  (default: ${PDK_ROOT})
  PDK             PDK variant    (default: ${PDK})
    RESULTS_ROOT    Run output root (default: ${RESULTS_ROOT})
  TAG             OpenLane tag   (default: auto timestamp)
    OPENLANE_MODE   auto|docker|local (default: ${OPENLANE_MODE})
    OPENLANE_LOCAL_ROOT  Local OpenLane repo (default: ${OPENLANE_LOCAL_ROOT})
EOF
}

need_cmd() {
    local cmd="$1"
    command -v "${cmd}" >/dev/null 2>&1 || {
        echo "[openlane] ERROR: '${cmd}' not found in PATH"
        exit 1
    }
}

latest_run_dir() {
    if [[ ! -d "${RUNS_DIR}" ]]; then
        return 1
    fi
    ls -1dt "${RUNS_DIR}"/* 2>/dev/null | head -n1
}

has_docker() {
    command -v docker >/dev/null 2>&1
}

has_local_openlane() {
    [[ -f "${OPENLANE_LOCAL_ROOT}/flow.tcl" ]]
}

run_openlane_docker() {
    echo "[openlane:run] Mode: docker"
    mkdir -p "${RUNS_DIR}"
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
        /bin/bash -lc "/openlane/flow.tcl -design ${DESIGN_DIR} -tag ${TAG} -run_path ${RUNS_DIR}"
}

run_openlane_local() {
    echo "[openlane:run] Mode: local"
    echo "[openlane:run] OPENLANE_LOCAL_ROOT=${OPENLANE_LOCAL_ROOT}"
    mkdir -p "${RUNS_DIR}"
    "${OPENLANE_LOCAL_ROOT}/flow.tcl" -design "${DESIGN_DIR}" -tag "${TAG}" -run_path "${RUNS_DIR}"
}

do_setup() {
    if has_docker; then
        echo "[openlane:setup] Pulling image: ${OPENLANE_IMAGE}"
        docker pull "${OPENLANE_IMAGE}"
    else
        echo "[openlane:setup] WARNING: Docker bulunamadı."
        if has_local_openlane; then
            echo "[openlane:setup] Local OpenLane bulundu: ${OPENLANE_LOCAL_ROOT}"
        else
            echo "[openlane:setup] Local OpenLane de bulunamadı."
            echo "[openlane:setup] Çözüm: make asic_subrepos veya Docker kurulumu"
        fi
    fi

    echo "[openlane:setup] PDK root: ${PDK_ROOT}"
    if [[ ! -d "${PDK_ROOT}/${PDK}" ]]; then
        echo "[openlane:setup] WARNING: ${PDK_ROOT}/${PDK} bulunamadı."
        echo "[openlane:setup] PDK henüz kurulu değilse OpenLane/Volare ile sky130A yüklemelisin."
    else
        echo "[openlane:setup] PDK dizini bulundu."
    fi
}

do_prep() {
    "${ROOT_DIR}/script/shell/prepare_openlane_sources.sh"
}

do_run() {
    do_prep

    if [[ ! -f "${DESIGN_DIR}/config.tcl" ]]; then
        echo "[openlane:run] ERROR: config.tcl bulunamadı: ${DESIGN_DIR}/config.tcl"
        exit 1
    fi

    if [[ ! -d "${PDK_ROOT}/${PDK}" ]]; then
        echo "[openlane:run] ERROR: PDK bulunamadı: ${PDK_ROOT}/${PDK}"
        echo "[openlane:run] Önce sky130A PDK kurulumunu tamamla."
        exit 1
    fi

    echo "[openlane:run] Running OpenLane"
    echo "  DESIGN_DIR : ${DESIGN_DIR}"
    echo "  RUNS_DIR   : ${RUNS_DIR}"
    echo "  PDK_ROOT   : ${PDK_ROOT}"
    echo "  PDK        : ${PDK}"
    echo "  TAG        : ${TAG}"

    case "${OPENLANE_MODE}" in
        docker)
            if ! has_docker; then
                echo "[openlane:run] ERROR: OPENLANE_MODE=docker ama docker yok."
                exit 1
            fi
            run_openlane_docker
            ;;
        local)
            if ! has_local_openlane; then
                echo "[openlane:run] ERROR: OPENLANE_MODE=local ama flow.tcl yok: ${OPENLANE_LOCAL_ROOT}/flow.tcl"
                exit 1
            fi
            run_openlane_local
            ;;
        auto)
            if has_docker; then
                run_openlane_docker
            elif has_local_openlane; then
                run_openlane_local
            else
                echo "[openlane:run] ERROR: Ne docker var ne local OpenLane var."
                echo "[openlane:run] Çözüm: Docker kur veya make asic_subrepos sonrası OPENLANE_MODE=local kullan."
                exit 1
            fi
            ;;
        *)
            echo "[openlane:run] ERROR: Geçersiz OPENLANE_MODE=${OPENLANE_MODE} (auto|docker|local)"
            exit 1
            ;;
    esac

    echo "[openlane:run] Completed."
    do_report
}

do_report() {
    local run_dir
    if ! run_dir="$(latest_run_dir)"; then
        echo "[openlane:report] Henüz run yok: ${RUNS_DIR}"
        exit 1
    fi

    echo "[openlane:report] Latest run: ${run_dir}"

    local summary="${run_dir}/reports/metrics.csv"
    local final_gds="${run_dir}/results/final/gds/ceres_wrapper.gds"
    local final_def="${run_dir}/results/final/def/ceres_wrapper.def"
    local final_netlist="${run_dir}/results/final/verilog/gl/ceres_wrapper.v"

    [[ -f "${summary}" ]] && echo "  Metrics : ${summary}" || true
    [[ -f "${final_gds}" ]] && echo "  GDS     : ${final_gds}" || true
    [[ -f "${final_def}" ]] && echo "  DEF     : ${final_def}" || true
    [[ -f "${final_netlist}" ]] && echo "  Netlist : ${final_netlist}" || true

    local drc_count
    drc_count=$(find "${run_dir}" -type f -name '*.rpt' -o -name '*.log' 2>/dev/null | xargs grep -h "Total Number of violations" 2>/dev/null | tail -n1 || true)
    [[ -n "${drc_count}" ]] && echo "  DRC     : ${drc_count}" || true
}

do_clean() {
    rm -rf "${RUNS_DIR}" "${DESIGN_DIR}/src" "${DESIGN_DIR}/sources_manifest.txt"
    echo "[openlane:clean] Cleaned: ${RUNS_DIR} and prepared src/"
}

main() {
    local cmd="${1:-}"
    case "${cmd}" in
        setup) do_setup ;;
        prep) do_prep ;;
        run) do_run ;;
        report) do_report ;;
        clean) do_clean ;;
        *) usage; exit 1 ;;
    esac
}

main "$@"
