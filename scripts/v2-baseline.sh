#!/usr/bin/env bash
set -euo pipefail

# Consolidated V2 baseline management script.
# Usage:
#   ./scripts/v2-baseline.sh [check|freeze|run|sla]
#
# Modes:
#   check   Verify V2 baseline artifact integrity (default)
#   freeze  Capture/freeze V2 baseline metrics + conformance artifacts
#   run     Run V2 benchmark matrix across workloads
#   sla     Check performance SLA thresholds and CI gate ordering

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

MODE="${1:-check}"

hash_file() {
  local file="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "${file}" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "${file}" | awk '{print $1}'
  else
    echo "error: need sha256sum or shasum for artifact hashing" >&2
    exit 2
  fi
}

# --- Check Mode: Verify baseline artifact integrity ---
do_check() {
  local ARTIFACT_DIR="${ROOT_DIR}/artifacts/v2/baseline"
  local SNAPSHOT_FILE="${ARTIFACT_DIR}/hash_snapshot.json"

  read_snapshot_value() {
    local key="$1"
    sed -n "s/.*\"${key}\":[[:space:]]*\"\\([0-9a-f]*\\)\".*/\\1/p" "${SNAPSHOT_FILE}" | head -n1
  }

  require_file() {
    local file="$1"
    if [[ ! -f "${file}" ]]; then
      echo "error: missing required artifact file: ${file}" >&2
      exit 1
    fi
  }

  require_file "${ARTIFACT_DIR}/suite_manifest.json"
  require_file "${ARTIFACT_DIR}/metrics.json"
  require_file "${ARTIFACT_DIR}/conformance.json"
  require_file "${SNAPSHOT_FILE}"

  local expected_metrics expected_conformance expected_suite
  expected_metrics="$(read_snapshot_value "metrics_sha256")"
  expected_conformance="$(read_snapshot_value "conformance_sha256")"
  expected_suite="$(read_snapshot_value "suite_manifest_sha256")"

  local actual_metrics actual_conformance actual_suite
  actual_metrics="$(hash_file "${ARTIFACT_DIR}/metrics.json")"
  actual_conformance="$(hash_file "${ARTIFACT_DIR}/conformance.json")"
  actual_suite="$(hash_file "${ARTIFACT_DIR}/suite_manifest.json")"

  local errors=0

  if [[ "${expected_metrics}" != "${actual_metrics}" ]]; then
    echo "FAIL metrics hash mismatch"
    echo "  expected: ${expected_metrics}"
    echo "  actual:   ${actual_metrics}"
    errors=$((errors + 1))
  else
    echo "OK   metrics hash"
  fi

  if [[ "${expected_conformance}" != "${actual_conformance}" ]]; then
    echo "FAIL conformance hash mismatch"
    echo "  expected: ${expected_conformance}"
    echo "  actual:   ${actual_conformance}"
    errors=$((errors + 1))
  else
    echo "OK   conformance hash"
  fi

  if [[ "${expected_suite}" != "${actual_suite}" ]]; then
    echo "FAIL suite manifest hash mismatch"
    echo "  expected: ${expected_suite}"
    echo "  actual:   ${actual_suite}"
    errors=$((errors + 1))
  else
    echo "OK   suite manifest hash"
  fi

  if ! rg -q '"envelope_diff_artifact"' "${ARTIFACT_DIR}/metrics.json"; then
    echo "FAIL metrics artifact missing envelope_diff_artifact payload"
    errors=$((errors + 1))
  else
    echo "OK   envelope diff artifact present"
  fi

  local canonical_rate
  canonical_rate="$(
    sed -n '/"canonical"[[:space:]]*:[[:space:]]*{/,/}/ s/.*"pass_rate":[[:space:]]*\([0-9.]*\).*/\1/p' \
      "${ARTIFACT_DIR}/conformance.json" | head -n1
  )"
  if [[ -z "${canonical_rate}" ]]; then
    echo "FAIL conformance artifact missing canonical pass rate"
    errors=$((errors + 1))
  else
    echo "OK   canonical pass-rate present (${canonical_rate})"
  fi

  local threaded_rate
  threaded_rate="$(
    sed -n '/"threaded"[[:space:]]*:[[:space:]]*{/,/}/ s/.*"pass_rate":[[:space:]]*\([0-9.]*\).*/\1/p' \
      "${ARTIFACT_DIR}/conformance.json" | head -n1
  )"
  if [[ -z "${threaded_rate}" ]]; then
    echo "FAIL conformance artifact missing threaded pass rate"
    errors=$((errors + 1))
  else
    echo "OK   threaded pass-rate present (${threaded_rate})"
  fi

  if (( errors > 0 )); then
    exit 1
  fi
}

# --- Freeze Mode: Capture baseline artifacts ---
do_freeze() {
  local ARTIFACT_DIR="${ROOT_DIR}/artifacts/v2/baseline"
  mkdir -p "${ARTIFACT_DIR}"

  echo "== V2 Baseline Freeze =="
  echo "artifact dir: ${ARTIFACT_DIR}"

  cat > "${ARTIFACT_DIR}/suite_manifest.json" <<'JSON'
{
  "schema_version": 1,
  "benchmark_suite": {
    "capture_command": "cargo run -p telltale-vm --features multi-thread --example v2_baseline_capture -- --output artifacts/v2/baseline/metrics.json",
    "metrics": [
      "throughput_steps_per_sec",
      "throughput_sessions_per_sec",
      "p50_step_latency_us",
      "p99_step_latency_us",
      "lock_contention_events_per_1k_steps",
      "mean_wave_width",
      "max_wave_width"
    ]
  },
  "conformance_corpus": {
    "canonical": [
      "cargo test -p telltale-vm --test conformance_lean",
      "cargo test -p telltale-vm --test equivalence_lean",
      "cargo test -p telltale-vm --test differential_step_corpus"
    ],
    "threaded": [
      "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_feature_contract",
      "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_equivalence",
      "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_lane_runtime"
    ]
  }
}
JSON

  echo "-> capturing benchmark/metrics artifact"
  cargo run -p telltale-vm --features multi-thread --example v2_baseline_capture -- \
    --output "${ARTIFACT_DIR}/metrics.json"

  local canonical_total=0 canonical_pass=0 threaded_total=0 threaded_pass=0

  run_test() {
    local label="$1"
    shift
    echo "-> ${label}: $*"
    if "$@"; then
      return 0
    fi
    return 1
  }

  echo "-> running canonical conformance corpus"
  for test_name in conformance_lean equivalence_lean differential_step_corpus; do
    canonical_total=$((canonical_total + 1))
    if run_test "${test_name}" cargo test -p telltale-vm --test "${test_name}"; then
      canonical_pass=$((canonical_pass + 1))
    fi
  done

  echo "-> running threaded conformance corpus"
  for test_name in threaded_feature_contract threaded_equivalence threaded_lane_runtime; do
    threaded_total=$((threaded_total + 1))
    if run_test "${test_name}" env TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test "${test_name}"; then
      threaded_pass=$((threaded_pass + 1))
    fi
  done

  local canonical_rate threaded_rate
  canonical_rate="$(awk -v p="${canonical_pass}" -v t="${canonical_total}" 'BEGIN{if(t==0){printf "0.000"}else{printf "%.3f", p/t}}')"
  threaded_rate="$(awk -v p="${threaded_pass}" -v t="${threaded_total}" 'BEGIN{if(t==0){printf "0.000"}else{printf "%.3f", p/t}}')"

  cat > "${ARTIFACT_DIR}/conformance.json" <<JSON
{
  "schema_version": 1,
  "canonical": {
    "passed": ${canonical_pass},
    "total": ${canonical_total},
    "pass_rate": ${canonical_rate}
  },
  "threaded": {
    "passed": ${threaded_pass},
    "total": ${threaded_total},
    "pass_rate": ${threaded_rate}
  }
}
JSON

  local metrics_sha conformance_sha suite_sha
  metrics_sha="$(hash_file "${ARTIFACT_DIR}/metrics.json")"
  conformance_sha="$(hash_file "${ARTIFACT_DIR}/conformance.json")"
  suite_sha="$(hash_file "${ARTIFACT_DIR}/suite_manifest.json")"

  cat > "${ARTIFACT_DIR}/hash_snapshot.json" <<JSON
{
  "schema_version": 1,
  "metrics_sha256": "${metrics_sha}",
  "conformance_sha256": "${conformance_sha}",
  "suite_manifest_sha256": "${suite_sha}"
}
JSON

  echo "Baseline artifacts written:"
  echo "  - ${ARTIFACT_DIR}/suite_manifest.json"
  echo "  - ${ARTIFACT_DIR}/metrics.json"
  echo "  - ${ARTIFACT_DIR}/conformance.json"
  echo "  - ${ARTIFACT_DIR}/hash_snapshot.json"
}

# --- Run Mode: Run benchmark matrix ---
do_run() {
  local OUT_DIR="${ROOT_DIR}/artifacts/v2/benchmark_matrix"
  local DISJOINT_OUT="${OUT_DIR}/disjoint.json"
  local CONTENDED_OUT="${OUT_DIR}/contended.json"
  local CONTENDED_M1_OUT="${OUT_DIR}/contended_m1_stress.json"
  local SUMMARY_OUT="${OUT_DIR}/summary.json"

  mkdir -p "${OUT_DIR}"

  echo "== V2 Benchmark Matrix =="
  echo "-> disjoint workload"
  cargo run -p telltale-vm --example v2_baseline_capture --features multi-thread -- \
    --workload disjoint \
    --output "${DISJOINT_OUT}"

  echo "-> contended workload"
  cargo run -p telltale-vm --example v2_baseline_capture --features multi-thread -- \
    --workload contended \
    --output "${CONTENDED_OUT}"

  echo "-> contended M1-stress reference workload"
  cargo run -p telltale-vm --example v2_baseline_capture --features multi-thread -- \
    --workload contended \
    --tuning-profile m1_stress_reference \
    --output "${CONTENDED_M1_OUT}"

  python3 - "${DISJOINT_OUT}" "${CONTENDED_OUT}" "${CONTENDED_M1_OUT}" "${SUMMARY_OUT}" <<'PY'
import json
import sys
from pathlib import Path

disjoint_path = Path(sys.argv[1])
contended_path = Path(sys.argv[2])
contended_m1_path = Path(sys.argv[3])
summary_path = Path(sys.argv[4])

disjoint = json.loads(disjoint_path.read_text(encoding="utf-8"))
contended = json.loads(contended_path.read_text(encoding="utf-8"))
contended_m1 = json.loads(contended_m1_path.read_text(encoding="utf-8"))


def summarize(run: dict) -> dict:
    c = run["canonical"]
    t = run["threaded"]
    throughput_ratio = (t["throughput_steps_per_sec"] / c["throughput_steps_per_sec"]) if c["throughput_steps_per_sec"] else 0.0
    p99_regression = (
        ((t["p99_step_latency_us"] - c["p99_step_latency_us"]) / c["p99_step_latency_us"]) * 100.0
        if c["p99_step_latency_us"]
        else 0.0
    )
    return {
        "workload": run["workload"],
        "throughput_ratio_threaded_vs_canonical": throughput_ratio,
        "p99_latency_regression_percent": p99_regression,
        "threaded_lock_contention_events_per_1k_steps": t["lock_contention_events_per_1k_steps"],
        "threaded_mutex_lock_contention_events_per_1k_steps": t["mutex_lock_contention_events_per_1k_steps"],
        "threaded_planner_conflict_events_per_1k_steps": t["planner_conflict_events_per_1k_steps"],
        "canonical_mean_wave_width": c["mean_wave_width"],
        "threaded_mean_wave_width": t["mean_wave_width"],
        "threaded_max_wave_width": t["max_wave_width"],
    }


summary = {
    "schema_version": 1,
    "disjoint": summarize(disjoint),
    "contended": summarize(contended),
    "contended_m1_stress_reference": summarize(contended_m1),
    "lock_contention_reduction_vs_m1_stress_percent": (
        (
            contended_m1["threaded"]["lock_contention_events_per_1k_steps"]
            - contended["threaded"]["lock_contention_events_per_1k_steps"]
        )
        / contended_m1["threaded"]["lock_contention_events_per_1k_steps"]
        * 100.0
        if contended_m1["threaded"]["lock_contention_events_per_1k_steps"] > 0.0
        else 0.0
    ),
}
summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
print(json.dumps(summary, indent=2))
PY

  echo "OK   wrote:"
  echo "  - ${DISJOINT_OUT}"
  echo "  - ${CONTENDED_OUT}"
  echo "  - ${CONTENDED_M1_OUT}"
  echo "  - ${SUMMARY_OUT}"
}

# --- SLA Mode: Check performance governance ---
do_sla() {
  local JUSTFILE="${ROOT_DIR}/justfile"
  local SUMMARY_FILE="${ROOT_DIR}/artifacts/v2/benchmark_matrix/summary.json"

  if [[ ! -f "${JUSTFILE}" ]]; then
    echo "error: justfile not found at ${JUSTFILE}" >&2
    exit 2
  fi

  line_of() {
    local pattern="$1"
    rg -n "${pattern}" "${JUSTFILE}" | head -n1 | cut -d: -f1
  }

  require_line() {
    local label="$1"
    local pattern="$2"
    local line
    line="$(line_of "${pattern}")"
    if [[ -z "${line}" ]]; then
      echo "FAIL missing in ci-dry-run: ${label}" >&2
      exit 1
    fi
    echo "${line}"
  }

  local line_capability line_parity line_v2_baseline line_bench
  line_capability="$(require_line "check-capability-gates" "^[[:space:]]+just check-capability-gates$")"
  line_parity="$(require_line "check-parity" "^[[:space:]]+just check-parity$")"
  line_v2_baseline="$(require_line "v2-baseline check" "^[[:space:]]+just v2-baseline check$")"
  line_bench="$(require_line "bench-check" "^[[:space:]]+just bench-check$")"

  local errors=0

  check_before_bench() {
    local label="$1"
    local line="$2"
    if (( line >= line_bench )); then
      echo "FAIL ${label} must run before bench-check (line ${line} >= ${line_bench})"
      errors=$((errors + 1))
    else
      echo "OK   ${label} runs before bench-check"
    fi
  }

  check_before_bench "check-capability-gates" "${line_capability}"
  check_before_bench "check-parity" "${line_parity}"
  check_before_bench "v2-baseline check" "${line_v2_baseline}"

  if (( errors > 0 )); then
    exit 1
  fi

  if [[ ! -f "${SUMMARY_FILE}" ]]; then
    echo "FAIL missing benchmark summary: ${SUMMARY_FILE}" >&2
    echo "Run ./scripts/v2-baseline.sh run before this check." >&2
    exit 1
  fi

  local THROUGHPUT_RATIO_MIN="${TT_SLA_THROUGHPUT_RATIO_MIN:-1.0}"
  local P99_REGRESSION_MAX_PERCENT="${TT_SLA_P99_REGRESSION_MAX_PERCENT:-15.0}"
  local LOCK_CONTENTION_REDUCTION_MIN_PERCENT="${TT_SLA_LOCK_CONTENTION_REDUCTION_MIN_PERCENT:-50.0}"

  python3 - "${SUMMARY_FILE}" \
    "${THROUGHPUT_RATIO_MIN}" \
    "${P99_REGRESSION_MAX_PERCENT}" \
    "${LOCK_CONTENTION_REDUCTION_MIN_PERCENT}" <<'PY'
import json
import sys
from pathlib import Path

summary_path = Path(sys.argv[1])
throughput_min = float(sys.argv[2])
p99_max = float(sys.argv[3])
lock_min = float(sys.argv[4])

summary = json.loads(summary_path.read_text())
errors: list[str] = []

for scenario in ("disjoint", "contended", "contended_m1_stress_reference"):
    payload = summary.get(scenario)
    if not isinstance(payload, dict):
        errors.append(f"missing benchmark scenario '{scenario}'")
        continue
    ratio = payload.get("throughput_ratio_threaded_vs_canonical")
    p99 = payload.get("p99_latency_regression_percent")
    if ratio is None or float(ratio) < throughput_min:
        errors.append(
            f"{scenario}: throughput_ratio_threaded_vs_canonical={ratio} < {throughput_min}"
        )
    if p99 is None or float(p99) > p99_max:
        errors.append(f"{scenario}: p99_latency_regression_percent={p99} > {p99_max}")

lock_reduction = summary.get("lock_contention_reduction_vs_m1_stress_percent")
if lock_reduction is None or float(lock_reduction) < lock_min:
    errors.append(
        "lock_contention_reduction_vs_m1_stress_percent="
        f"{lock_reduction} < {lock_min}"
    )

if errors:
    for err in errors:
        print(f"FAIL {err}")
    raise SystemExit(1)

print(
    "OK   benchmark SLA thresholds satisfied "
    f"(throughput>={throughput_min}, p99<={p99_max}%, "
    f"lock-reduction>={lock_min}%)"
)
PY
}

# --- Main ---
case "${MODE}" in
  check)
    do_check
    ;;
  freeze)
    do_freeze
    ;;
  run)
    do_run
    ;;
  sla)
    do_sla
    ;;
  *)
    echo "error: unknown mode ${MODE}" >&2
    echo "Usage: $0 [check|freeze|run|sla]" >&2
    exit 2
    ;;
esac
