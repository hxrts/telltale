#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARTIFACT_DIR="${ROOT_DIR}/artifacts/v2/baseline"

mkdir -p "${ARTIFACT_DIR}"

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
(
  cd "${ROOT_DIR}"
  cargo run -p telltale-vm --features multi-thread --example v2_baseline_capture -- \
    --output "${ARTIFACT_DIR}/metrics.json"
)

canonical_total=0
canonical_pass=0
threaded_total=0
threaded_pass=0

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
