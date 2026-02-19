#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
JUSTFILE="${ROOT_DIR}/Justfile"

if [[ ! -f "${JUSTFILE}" ]]; then
  echo "error: Justfile not found at ${JUSTFILE}" >&2
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

line_envelope="$(require_line "check-envelope-conformance" "^[[:space:]]+just check-envelope-conformance$")"
line_byzantine="$(require_line "check-byzantine-conformance" "^[[:space:]]+just check-byzantine-conformance$")"
line_delegation="$(require_line "check-delegation-shard-gate" "^[[:space:]]+just check-delegation-shard-gate$")"
line_parity="$(require_line "check-vm-parity-suite" "^[[:space:]]+just check-vm-parity-suite$")"
line_v2_baseline="$(require_line "check-v2-baseline" "^[[:space:]]+just check-v2-baseline$")"
line_bench="$(require_line "bench-check" "^[[:space:]]+just bench-check$")"

errors=0

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

check_before_bench "check-envelope-conformance" "${line_envelope}"
check_before_bench "check-byzantine-conformance" "${line_byzantine}"
check_before_bench "check-delegation-shard-gate" "${line_delegation}"
check_before_bench "check-vm-parity-suite" "${line_parity}"
check_before_bench "check-v2-baseline" "${line_v2_baseline}"

if (( errors > 0 )); then
  exit 1
fi
