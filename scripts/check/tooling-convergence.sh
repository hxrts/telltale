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
check_no_match '--name' Justfile rust/choreography/src/bin/effect_scaffold.rs

# ── Retired Protocol Machine Constructors ──────────────────────────────────────────

check_no_match '\bThreadedVM\b' rust/machine/examples rust/machine/benches
check_no_match '\bVM::new\b' rust/machine/examples rust/machine/benches
check_no_match '\bVMConfig\b' rust/machine/examples rust/machine/benches
check_no_match 'load_choreography\(' rust/machine/examples rust/machine/benches

# ── Stale Justfile Description ───────────────────────────────────────

check_no_match 'EffectHandler stubs plus simulator harness test templates' Justfile

# ── Legacy Public Teaching Surfaces ──────────────────────────────────

check_no_match 'Program::new\(' \
  docs/02_getting_started.md \
  docs/03_architecture.md \
  docs/08_extensions.md \
  docs/09_effect_handlers.md \
  docs/28_examples.md \
  docs/29_wasm_guide.md

check_no_match 'compose race\b' docs examples
check_no_match 'compose fallback\b' docs examples
check_no_match 'compose quorum\(' docs examples

echo "tooling-convergence: ok"
