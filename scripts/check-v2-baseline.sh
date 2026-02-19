#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARTIFACT_DIR="${ROOT_DIR}/artifacts/v2/baseline"
SNAPSHOT_FILE="${ARTIFACT_DIR}/hash_snapshot.json"

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

expected_metrics="$(read_snapshot_value "metrics_sha256")"
expected_conformance="$(read_snapshot_value "conformance_sha256")"
expected_suite="$(read_snapshot_value "suite_manifest_sha256")"

actual_metrics="$(hash_file "${ARTIFACT_DIR}/metrics.json")"
actual_conformance="$(hash_file "${ARTIFACT_DIR}/conformance.json")"
actual_suite="$(hash_file "${ARTIFACT_DIR}/suite_manifest.json")"

errors=0

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
