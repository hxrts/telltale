#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

allowed_path() {
  local path="$1"
  case "$path" in
    rust/simulator/*) return 0 ;;
    docs/501_simulation_overview.md) return 0 ;;
    docs/502_simulation_runner.md) return 0 ;;
    docs/503_simulation_scenarios.md) return 0 ;;
    docs/504_simulation_fields.md) return 0 ;;
    docs/902_verification_inventory.md) return 0 ;;
    scripts/check/simulator-subsystem.sh) return 0 ;;
    *) return 1 ;;
  esac
}

collect_staged_paths() {
  git diff --cached --name-only --diff-filter=ACMR
}

subsystem_applies_to_paths() {
  local saw_any=0
  while IFS= read -r path; do
    [[ -z "$path" ]] && continue
    saw_any=1
    if ! allowed_path "$path"; then
      return 1
    fi
  done
  [[ "$saw_any" -eq 1 ]]
}

run_doc_checks() {
  local docs=()
  while IFS= read -r path; do
    [[ "$path" == docs/*.md ]] || continue
    docs+=("$path")
  done < <(collect_staged_paths)

  if [[ "${#docs[@]}" -eq 0 ]]; then
    return 0
  fi

  npx --yes markdown-link-check --config .github/config/markdown-link-check.json "${docs[@]}"
}

run_subsystem_checks() {
  cargo fmt -p telltale-simulator -- --check
  cargo check -p telltale-simulator --all-targets --all-features
  TMPDIR="${TMPDIR:-/tmp}" cargo test -p telltale-simulator --all-targets --all-features
  run_doc_checks
}

self_test() {
  printf '%s\n' "rust/simulator/src/runner.rs" "docs/501_simulation_overview.md" \
    | subsystem_applies_to_paths
  if printf '%s\n' "rust/simulator/src/runner.rs" "rust/runtime/src/lib.rs" \
    | subsystem_applies_to_paths; then
    echo "simulator-subsystem self-test failed: runtime path should be rejected" >&2
    exit 1
  fi
}

mode="${1:-run}"
case "$mode" in
  --applies-to-staged)
    if collect_staged_paths | subsystem_applies_to_paths; then
      exit 0
    fi
    exit 1
    ;;
  --self-test)
    self_test
    ;;
  run|--run)
    if ! collect_staged_paths | subsystem_applies_to_paths; then
      echo "staged changes are not restricted to the simulator subsystem" >&2
      exit 1
    fi
    run_subsystem_checks
    ;;
  *)
    echo "usage: $0 [run|--run|--applies-to-staged|--self-test]" >&2
    exit 2
    ;;
esac
