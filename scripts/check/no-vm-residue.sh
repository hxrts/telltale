#!/usr/bin/env bash
# Guard against reintroduction of architectural VM naming.
# Scans tracked source, docs, scripts, and tooling for forbidden patterns.
# WASM references are excluded.
set -uo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

errors=0

SELF_SCRIPT="scripts/check/no-vm-residue.sh"

check_pattern() {
  local label="$1"
  local pattern="$2"
  shift 2
  local hits
  hits="$(rg -n "$pattern" "$@" 2>/dev/null | grep -v "wasm\|WASM\|wasm_\|${SELF_SCRIPT}" || true)"
  if [[ -n "$hits" ]]; then
    echo "FAIL $label"
    echo "$hits" | head -10
    errors=$((errors + 1))
  else
    echo "OK   $label"
  fi
}

# Lean source
check_pattern "no Runtime.VM namespace in Lean" \
  'Runtime\.VM\b|Runtime/VM\b' \
  lean/ --type lean

check_pattern "no VM-prefixed definitions in Lean" \
  '\bVM[A-Z]' \
  lean/ --type lean

check_pattern "no vm_runner binary references in Lean" \
  '\bvm_runner\b' \
  lean/ --type lean

# Rust source
check_pattern "no telltale-vm crate name in Rust" \
  '\btelltale-vm\b|\btelltale_vm\b' \
  rust/ --type rust

check_pattern "no rust/vm/ path references" \
  'rust/vm/' \
  rust/ Cargo.toml justfile scripts/ docs/

check_pattern "no VM struct/type names in Rust" \
  '\bVMConfig\b|\bVMState\b|\bVMError\b|\bVMKernel\b|\bThreadedVM\b' \
  rust/ --type rust

# Cargo manifests
check_pattern "no telltale-vm in Cargo manifests" \
  '\btelltale-vm\b' \
  Cargo.toml rust/*/Cargo.toml

# Scripts and tooling
check_pattern "no old script names in Justfile" \
  'check-vm-placeholders|verify-lean-vm|verify-vm-correspondence|profile-vm[^-]' \
  justfile

# Docs (exclude generated book)
check_pattern "no old doc filenames referenced" \
  '12_vm_architecture|15_vm_simulation_overview|16_vm_simulation_runner|17_vm_simulation_scenarios|18_vm_simulation_materials' \
  docs/ --glob '!docs/book/**'

if (( errors > 0 )); then
  echo ""
  echo "vm residue guard failed: $errors pattern(s) found"
  exit 1
fi

echo "vm residue guard passed"
