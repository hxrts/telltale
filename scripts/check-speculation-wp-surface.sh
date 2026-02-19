#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

TARGET_FILES=(
  "${ROOT_DIR}/lean/Runtime/ProgramLogic/GhostState.lean"
  "${ROOT_DIR}/lean/Runtime/ProgramLogic/WPPair.lean"
  "${ROOT_DIR}/lean/Runtime/ProgramLogic/SessionWP.lean"
  "${ROOT_DIR}/lean/Runtime/ProgramLogic/FinalizationWP.lean"
  "${ROOT_DIR}/lean/Runtime/Adequacy/Adequacy.lean"
  "${ROOT_DIR}/lean/Runtime/Proofs/VM/Speculation.lean"
)

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

echo "== Speculation/WP Surface Conformance =="

for f in "${TARGET_FILES[@]}"; do
  if [[ ! -f "${f}" ]]; then
    echo "error: missing target file ${f}" >&2
    exit 2
  fi
done

PATTERN='(?i)\b(?:TODO|FIXME|TBD|placeholder|stub|unimplemented|WIP)\b'
HITS="$({
  rg -n --pcre2 "${PATTERN}" "${TARGET_FILES[@]}" || true
} | sed "s#${ROOT_DIR}/##" | sort -u)"

if [[ -n "${HITS}" ]]; then
  echo "FAIL speculation/WP target modules still contain placeholder markers:" >&2
  printf '%s\n' "${HITS}" >&2
  exit 1
fi

echo "OK   no placeholder/stub markers in speculation/WP target modules"

if command -v lake >/dev/null 2>&1; then
  (
    cd "${ROOT_DIR}/lean"
    lake build Runtime.ProgramLogic.WPPair Runtime.ProgramLogic.SessionWP \
      Runtime.ProgramLogic.FinalizationWP Runtime.Adequacy.Adequacy \
      Runtime.Proofs.VM.Speculation >/dev/null
  )
elif command -v elan >/dev/null 2>&1; then
  (
    cd "${ROOT_DIR}"
    elan run leanprover/lean4:v4.26.0 lake --dir lean build \
      Runtime.ProgramLogic.WPPair Runtime.ProgramLogic.SessionWP \
      Runtime.ProgramLogic.FinalizationWP Runtime.Adequacy.Adequacy \
      Runtime.Proofs.VM.Speculation >/dev/null
  )
else
  echo "WARN skipping Lean build check (no lake/elan found)"
fi

echo "OK   speculation/WP target modules build successfully"
