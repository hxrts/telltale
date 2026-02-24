#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="${ROOT_DIR}/lean"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

files="$(find "${LEAN_DIR}" -type f -name '*.lean' | wc -l | tr -d ' ')"
loc="$(find "${LEAN_DIR}" -type f -name '*.lean' -print0 | xargs -0 cat | wc -l | tr -d ' ')"
axioms="$( (rg -n '^[[:space:]]*axiom\\b' "${LEAN_DIR}" || true) | wc -l | tr -d ' ' )"
sorries="$( (rg -n '\\bsorry\\b' "${LEAN_DIR}" || true) | wc -l | tr -d ' ' )"

if [[ "${1:-}" == "--latex-row" ]]; then
  echo "Lean source statistics & ${files} files, ${loc} LOC, axioms: ${axioms}, unresolved proof holes (\\texttt{sorry}): ${sorries} \\\\"
  exit 0
fi

if [[ "${1:-}" == "--check" ]]; then
  shift
  if [[ "$#" -eq 0 ]]; then
    echo "usage: $0 --check <paper1.tex> [paper2.tex ...]" >&2
    exit 2
  fi
  expected="Lean source statistics & ${files} files, ${loc} LOC, axioms: ${axioms}, unresolved proof holes (\\texttt{sorry}): ${sorries} \\\\"
  for tex in "$@"; do
    if ! rg -Fq "${expected}" "${tex}"; then
      echo "error: stale stats row in ${tex}" >&2
      echo "expected: ${expected}" >&2
      exit 1
    fi
  done
  echo "paper lean stats rows are up to date."
  exit 0
fi

cat <<EOF
Lean stats snapshot
files : ${files}
loc   : ${loc}
axiom : ${axioms}
sorry : ${sorries}
EOF
