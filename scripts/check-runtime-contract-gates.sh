#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CONTRACTS_FILE="${ROOT_DIR}/lean/Runtime/Proofs/CompileTime/RuntimeContracts.lean"
API_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/API.lean"
EXAMPLE_FILE="${ROOT_DIR}/lean/Runtime/Proofs/Examples/ComposedProofPack.lean"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

errors=0
checks=0

check() {
  local desc="$1"
  local cmd="$2"
  checks=$((checks + 1))
  if eval "${cmd}"; then
    echo "OK   ${desc}"
  else
    errors=$((errors + 1))
    echo "FAIL ${desc}"
  fi
}

echo "== Runtime Contract Gates =="

check "admission API requires runtime contracts for advanced modes" \
  "rg -q 'def requiresVMRuntimeContracts' '${CONTRACTS_FILE}' && \
   rg -q 'def admitVMRuntime' '${CONTRACTS_FILE}' && \
   rg -q 'theorem admitVMRuntime_requires_contracts' '${CONTRACTS_FILE}'"

check "determinism profile selection is capability-gated and validated" \
  "rg -q 'def determinismProfileSupported' '${CONTRACTS_FILE}' && \
   rg -q 'def requestDeterminismProfile' '${CONTRACTS_FILE}' && \
   rg -q 'canUseMixedDeterminismProfiles' '${CONTRACTS_FILE}'"

check "composed spaces provide deterministic minimal capability inventory API" \
  "rg -q 'def minimalCapabilities' '${API_FILE}' && \
   rg -q 'def composeProofSpaces' '${API_FILE}' && \
   rg -q 'def composedSpace' '${EXAMPLE_FILE}'"

if command -v lake >/dev/null 2>&1; then
  (
    cd "${ROOT_DIR}/lean"
    lake build Runtime.Proofs.CompileTime.RuntimeContracts \
      Runtime.Proofs.TheoremPack.API \
      Runtime.Proofs.Examples.ComposedProofPack >/dev/null
  )
  echo "OK   runtime contract gate modules type-check successfully"
elif command -v elan >/dev/null 2>&1; then
  (
    cd "${ROOT_DIR}"
    elan run leanprover/lean4:v4.26.0 lake --dir lean build \
      Runtime.Proofs.CompileTime.RuntimeContracts \
      Runtime.Proofs.TheoremPack.API \
      Runtime.Proofs.Examples.ComposedProofPack >/dev/null
  )
  echo "OK   runtime contract gate modules type-check successfully"
else
  echo "WARN skipping Lean type-check in runtime contract gates script (no lake/elan)"
fi

echo ""
echo "Summary: ${checks} checks, ${errors} failure(s)."
if (( errors > 0 )); then
  exit 1
fi
