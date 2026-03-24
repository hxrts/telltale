#!/usr/bin/env bash
# Performance baseline management script.
# Usage:  ./scripts/ops/perf-baseline.sh [check|freeze|run|sla]
#
# Modes:
#   check   Verify baseline artifact integrity (default)
#   freeze  Capture baseline metrics and conformance artifacts
#   run     Run benchmark matrix across workloads
#   sla     Check performance SLA thresholds and CI gate ordering
set -euo pipefail

# ── Setup ──────────────────────────────────────────────────────────────
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

MODE="${1:-check}"

# Compute SHA-256 hash of a file (portable across Linux/macOS)
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

# ── Check Mode: Verify baseline artifact integrity ─────────────────────
do_check() {
  local ARTIFACT_DIR="${ROOT_DIR}/artifacts/v2/baseline"
  local SNAPSHOT_FILE="${ARTIFACT_DIR}/hash_snapshot.json"
  mkdir -p "${ARTIFACT_DIR}"

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

  local missing_artifacts=0
  for file in \
    "${ARTIFACT_DIR}/suite_manifest.json" \
    "${ARTIFACT_DIR}/metrics.json" \
    "${ARTIFACT_DIR}/conformance.json" \
    "${SNAPSHOT_FILE}"; do
    if [[ ! -f "${file}" ]]; then
      missing_artifacts=1
      break
    fi
  done

  if (( missing_artifacts == 1 )); then
    echo "INFO baseline artifacts missing; bootstrapping via freeze mode"
    do_freeze
  fi

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

# ── Freeze Mode: Capture baseline artifacts ────────────────────────────
do_freeze() {
  local ARTIFACT_DIR="${ROOT_DIR}/artifacts/v2/baseline"
  mkdir -p "${ARTIFACT_DIR}"

  echo "== Baseline Freeze =="
  echo "artifact dir: ${ARTIFACT_DIR}"

  cat > "${ARTIFACT_DIR}/suite_manifest.json" <<'JSON'
{
  "schema_version": 1,
  "benchmark_suite": {
    "capture_command": "cargo run -p telltale-protocol-machine --features multi-thread --example v2_baseline_capture -- --output artifacts/v2/baseline/metrics.json",
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
      "cargo test -p telltale-protocol-machine --test conformance_lean",
      "cargo test -p telltale-protocol-machine --test equivalence_lean",
      "cargo test -p telltale-protocol-machine --test differential_step_corpus"
    ],
    "threaded": [
      "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-protocol-machine --features multi-thread --test threaded_feature_contract",
      "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-protocol-machine --features multi-thread --test threaded_equivalence",
      "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-protocol-machine --features multi-thread --test threaded_lane_runtime"
    ]
  }
}
JSON

  echo "-> capturing benchmark/metrics artifact"
  cargo run -p telltale-protocol-machine --features multi-thread --example v2_baseline_capture -- \
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
    if run_test "${test_name}" cargo test -p telltale-protocol-machine --test "${test_name}"; then
      canonical_pass=$((canonical_pass + 1))
    fi
  done

  echo "-> running threaded conformance corpus"
  for test_name in threaded_feature_contract threaded_equivalence threaded_lane_runtime; do
    threaded_total=$((threaded_total + 1))
    if run_test "${test_name}" env TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-protocol-machine --features multi-thread --test "${test_name}"; then
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

# ── Run Mode: Run benchmark matrix ─────────────────────────────────────
do_run() {
  local OUT_DIR="${ROOT_DIR}/artifacts/v2/benchmark_matrix"
  local DISJOINT_OUT="${OUT_DIR}/disjoint.json"
  local CONTENDED_OUT="${OUT_DIR}/contended.json"
  local CONTENDED_M1_OUT="${OUT_DIR}/contended_m1_stress.json"
  local SUMMARY_OUT="${OUT_DIR}/summary.json"

  mkdir -p "${OUT_DIR}"

  echo "== Benchmark Matrix =="
  echo "-> disjoint workload"
  cargo run -p telltale-protocol-machine --example v2_baseline_capture --features multi-thread -- \
    --workload disjoint \
    --output "${DISJOINT_OUT}"

  echo "-> contended workload"
  cargo run -p telltale-protocol-machine --example v2_baseline_capture --features multi-thread -- \
    --workload contended \
    --output "${CONTENDED_OUT}"

  echo "-> contended M1-stress reference workload"
  cargo run -p telltale-protocol-machine --example v2_baseline_capture --features multi-thread -- \
    --workload contended \
    --tuning-profile m1_stress_reference \
    --output "${CONTENDED_M1_OUT}"

  # jq filter: summarize a single benchmark run
  local jq_summarize='
    def summarize:
      .canonical as $c | .threaded as $t |
      (if $c.throughput_steps_per_sec != 0 then
         $t.throughput_steps_per_sec / $c.throughput_steps_per_sec
       else 0.0 end) as $throughput_ratio |
      (if $c.p99_step_latency_us != 0 then
         (($t.p99_step_latency_us - $c.p99_step_latency_us) / $c.p99_step_latency_us) * 100.0
       else 0.0 end) as $p99_regression |
      {
        workload: .workload,
        throughput_ratio_threaded_vs_canonical: $throughput_ratio,
        p99_latency_regression_percent: $p99_regression,
        threaded_lock_contention_events_per_1k_steps: $t.lock_contention_events_per_1k_steps,
        threaded_mutex_lock_contention_events_per_1k_steps: $t.mutex_lock_contention_events_per_1k_steps,
        threaded_planner_conflict_events_per_1k_steps: $t.planner_conflict_events_per_1k_steps,
        canonical_mean_wave_width: $c.mean_wave_width,
        threaded_mean_wave_width: $t.mean_wave_width,
        threaded_max_wave_width: $t.max_wave_width
      };
    .[0] as $disjoint | .[1] as $contended | .[2] as $contended_m1 |
    ($contended_m1.threaded.lock_contention_events_per_1k_steps) as $m1_lock |
    ($contended.threaded.lock_contention_events_per_1k_steps) as $c_lock |
    {
      schema_version: 1,
      disjoint: ($disjoint | summarize),
      contended: ($contended | summarize),
      contended_m1_stress_reference: ($contended_m1 | summarize),
      lock_contention_reduction_vs_m1_stress_percent:
        (if $m1_lock > 0.0 then (($m1_lock - $c_lock) / $m1_lock) * 100.0
         else 100.0 end)
    }
  '

  local summary
  summary="$(jq -n --slurpfile d "${DISJOINT_OUT}" \
                    --slurpfile c "${CONTENDED_OUT}" \
                    --slurpfile m "${CONTENDED_M1_OUT}" \
                    '[$d[0], $c[0], $m[0]] | '"${jq_summarize}")"
  printf '%s\n' "${summary}" > "${SUMMARY_OUT}"
  printf '%s\n' "${summary}"

  echo "OK   wrote:"
  echo "  - ${DISJOINT_OUT}"
  echo "  - ${CONTENDED_OUT}"
  echo "  - ${CONTENDED_M1_OUT}"
  echo "  - ${SUMMARY_OUT}"
}

# ── SLA Mode: Check performance governance ─────────────────────────────
do_sla() {
  local JUSTFILE="${ROOT_DIR}/justfile"
  local SUMMARY_FILE="${ROOT_DIR}/artifacts/v2/benchmark_matrix/summary.json"
  mkdir -p "$(dirname "${SUMMARY_FILE}")"

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

  local line_capability line_parity line_perf_baseline line_bench
  line_capability="$(require_line "check-capability-gates" "^[[:space:]]+just check-capability-gates$")"
  line_parity="$(require_line "check-parity" "^[[:space:]]+just check-parity$")"
  line_perf_baseline="$(require_line "perf-baseline check" "^[[:space:]]+just perf-baseline check$")"
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
  check_before_bench "perf-baseline check" "${line_perf_baseline}"

  if (( errors > 0 )); then
    exit 1
  fi

  if [[ ! -f "${SUMMARY_FILE}" ]]; then
    echo "INFO benchmark summary missing; bootstrapping via run mode"
    do_run
  fi

  local THROUGHPUT_RATIO_MIN="${TT_SLA_THROUGHPUT_RATIO_MIN:-1.0}"
  local P99_REGRESSION_MAX_PERCENT="${TT_SLA_P99_REGRESSION_MAX_PERCENT:-15.0}"
  local LOCK_CONTENTION_REDUCTION_MIN_PERCENT="${TT_SLA_LOCK_CONTENTION_REDUCTION_MIN_PERCENT:-50.0}"

  local sla_result
  sla_result="$(jq -r \
    --argjson throughput_min "${THROUGHPUT_RATIO_MIN}" \
    --argjson p99_max "${P99_REGRESSION_MAX_PERCENT}" \
    --argjson lock_min "${LOCK_CONTENTION_REDUCTION_MIN_PERCENT}" '
    def check_scenario(scenario_key):
      .[scenario_key] as $payload |
      if ($payload | type) != "object" then
        ["missing benchmark scenario \u0027" + scenario_key + "\u0027"]
      else
        (if ($payload.throughput_ratio_threaded_vs_canonical == null) or
            ($payload.throughput_ratio_threaded_vs_canonical < $throughput_min) then
          [scenario_key + ": throughput_ratio_threaded_vs_canonical=" +
           ($payload.throughput_ratio_threaded_vs_canonical | tostring) +
           " < " + ($throughput_min | tostring)]
        else [] end) +
        (if ($payload.p99_latency_regression_percent == null) or
            ($payload.p99_latency_regression_percent > $p99_max) then
          [scenario_key + ": p99_latency_regression_percent=" +
           ($payload.p99_latency_regression_percent | tostring) +
           " > " + ($p99_max | tostring)]
        else [] end)
      end;

    (check_scenario("disjoint") +
     check_scenario("contended") +
     check_scenario("contended_m1_stress_reference")) as $scenario_errors |

    (.contended // {}) as $contended |
    (.contended_m1_stress_reference // {}) as $contended_m1 |
    ($contended.threaded_lock_contention_events_per_1k_steps) as $c_lock |
    ($contended_m1.threaded_lock_contention_events_per_1k_steps) as $m1_lock |
    .lock_contention_reduction_vs_m1_stress_percent as $lock_reduction |

    ($scenario_errors + (
      if ($c_lock == null) or ($m1_lock == null) then
        ["missing lock contention metrics in benchmark summary for SLA evaluation"]
      elif ($c_lock == 0) and ($m1_lock == 0) then
        []
      elif ($lock_reduction == null) or ($lock_reduction < $lock_min) then
        ["lock_contention_reduction_vs_m1_stress_percent=" +
         ($lock_reduction | tostring) + " < " + ($lock_min | tostring)]
      else [] end
    )) as $all_errors |

    if ($all_errors | length) > 0 then
      ($all_errors | map("FAIL " + .) | join("\n")) + "\n__EXIT_1__"
    else
      "OK   benchmark SLA thresholds satisfied " +
      "(throughput>=" + ($throughput_min | tostring) +
      ", p99<=" + ($p99_max | tostring) +
      "%, lock-reduction>=" + ($lock_min | tostring) + "%)"
    end
  ' "${SUMMARY_FILE}")"

  # Check for failure sentinel and split output
  if [[ "${sla_result}" == *"__EXIT_1__"* ]]; then
    printf '%s\n' "${sla_result%__EXIT_1__}"
    exit 1
  fi
  printf '%s\n' "${sla_result}"
}

# ── Main ───────────────────────────────────────────────────────────────
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
