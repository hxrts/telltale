#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

checks=0
failures=0

run_check() {
  local name="$1"
  local cmd="$2"
  checks=$((checks + 1))
  echo "[parity-suite] ${name}"
  if eval "${cmd}"; then
    echo "[parity-suite] OK: ${name}"
  else
    failures=$((failures + 1))
    echo "[parity-suite] FAIL: ${name}" >&2
  fi
  echo
}

run_check "lean conformance corpus" \
  "cargo test -p telltale-vm --test conformance_lean"
run_check "lean equivalence corpus" \
  "cargo test -p telltale-vm --test equivalence_lean"
run_check "differential step corpus" \
  "cargo test -p telltale-vm --test differential_step_corpus"
run_check "bridge vm correspondence" \
  "cargo test -p telltale-lean-bridge --test vm_correspondence_tests"
run_check "bridge vm differential-step correspondence" \
  "cargo test -p telltale-lean-bridge --test vm_differential_step_tests"
run_check "threaded parity equivalence" \
  "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_equivalence"

echo "[parity-suite] Summary: ${checks} checks, ${failures} failures."

if (( failures > 0 )); then
  exit 1
fi
