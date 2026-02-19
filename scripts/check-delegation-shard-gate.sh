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
  echo "== ${name}"
  if eval "${cmd}"; then
    echo "OK   ${name}"
  else
    failures=$((failures + 1))
    echo "FAIL ${name}" >&2
  fi
  echo
}

run_check "cooperative transfer guard rejects non-delegation ownership mutation" \
  "cargo test -p telltale-vm test_transfer_rejects_delegation_guard_violation"
run_check "threaded transfer handoff emits delegation evidence" \
  "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_lane_runtime deterministic_transfer_handoff_uses_delegation_path"
run_check "threaded transfer guard rejects ambiguous ownership mutation" \
  "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread delegation_handoff_guard_rejects_ambiguous_endpoint_ownership"

echo "Summary: ${checks} checks, ${failures} failure(s)."
if (( failures > 0 )); then
  exit 1
fi
