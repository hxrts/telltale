#!/usr/bin/env bash
# Check that deprecated API patterns (old protocol machine constructors, scaffold flags)
# are not used in examples or benchmarks.
set -euo pipefail

cd "$(dirname "$0")/../.."

# ── Helpers ───────────────────────────────────────────────────────────

fail() {
  echo "tooling-convergence: $1" >&2
  exit 1
}

# Assert that a ripgrep pattern has zero matches in the given paths
check_no_match() {
  local pattern="$1"
  shift
  if rg -n "$pattern" "$@" -g '!target' >/tmp/telltale_tooling_convergence.$$ 2>/dev/null; then
    cat /tmp/telltale_tooling_convergence.$$ >&2
    rm -f /tmp/telltale_tooling_convergence.$$
    fail "found forbidden pattern: $pattern"
  fi
  rm -f /tmp/telltale_tooling_convergence.$$
}

# ── Deprecated Scaffold Flags ────────────────────────────────────────

check_no_match 'effect-scaffold out=' Justfile
check_no_match '--name' Justfile rust/effect-scaffold/src

# ── Retired Protocol Machine Constructors ──────────────────────────────────────────

check_no_match '\bThreadedVM\b' rust/protocol-machine/examples rust/protocol-machine/benches
check_no_match '\bVM::new\b' rust/protocol-machine/examples rust/protocol-machine/benches
check_no_match '\bVMConfig\b' rust/protocol-machine/examples rust/protocol-machine/benches
check_no_match 'load_choreography\(' rust/protocol-machine/examples rust/protocol-machine/benches

# ── Stale Justfile Description ───────────────────────────────────────

check_no_match 'EffectHandler stubs plus simulator harness test templates' Justfile

echo "tooling-convergence: ok"
