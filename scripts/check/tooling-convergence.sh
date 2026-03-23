#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

fail() {
  echo "tooling-convergence: $1" >&2
  exit 1
}

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

check_no_match 'effect-scaffold out=' Justfile
check_no_match '--name' Justfile rust/effect-scaffold/src
check_no_match '\bThreadedVM\b' rust/vm/examples rust/vm/benches
check_no_match '\bVM::new\b' rust/vm/examples rust/vm/benches
check_no_match '\bVMConfig\b' rust/vm/examples rust/vm/benches
check_no_match 'load_choreography\(' rust/vm/examples rust/vm/benches
check_no_match 'EffectHandler stubs plus simulator harness test templates' Justfile

echo "tooling-convergence: ok"
