#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
METADATA_FILE="${ROOT_DIR}/paper/artifact_metadata.env"

ARTIFACT_DOI="DOI-UNSET"
if [[ -f "${METADATA_FILE}" ]]; then
  # shellcheck disable=SC1090
  source "${METADATA_FILE}"
fi

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

usage() {
  cat <<EOF
usage:
  $0 --print
  $0 --sync <paper1.tex> [paper2.tex ...]
  $0 --check <paper1.tex> [paper2.tex ...]
  $0 --check --strict-doi <paper1.tex> [paper2.tex ...]
EOF
}

format_commit_tex() {
  local hash="$1"
  local out=""
  local first=1
  while [[ -n "${hash}" ]]; do
    local chunk="${hash:0:16}"
    hash="${hash:16}"
    if [[ "${first}" -eq 1 ]]; then
      out="\\texttt{${chunk}}"
      first=0
    else
      out="${out}\\allowbreak\\texttt{${chunk}}"
    fi
  done
  printf '%s' "${out}"
}

CURRENT_COMMIT="$(git -C "${ROOT_DIR}" rev-parse HEAD)"
COMMIT_TEX="$(format_commit_tex "${CURRENT_COMMIT}")"
COMMIT_ROW="Pinned commit & ${COMMIT_TEX} \\\\"
DOI_ROW="Archival DOI & \\texttt{${ARTIFACT_DOI}} \\\\"
LEAN_ROW="$(bash "${ROOT_DIR}/scripts/ops/lean-stats.sh" --latex-row)"
COMMIT_ROW_AWK="$(printf '%s' "${COMMIT_ROW}" | sed 's/\\/\\\\/g')"
DOI_ROW_AWK="$(printf '%s' "${DOI_ROW}" | sed 's/\\/\\\\/g')"
LEAN_ROW_AWK="$(printf '%s' "${LEAN_ROW}" | sed 's/\\/\\\\/g')"

sync_one() {
  local tex="$1"
  local tmp
  tmp="$(mktemp)"

  awk \
    -v commit_row="${COMMIT_ROW_AWK}" \
    -v doi_row="${DOI_ROW_AWK}" \
    -v lean_row="${LEAN_ROW_AWK}" \
    '
      BEGIN {
        seen_commit=0;
        seen_doi=0;
        seen_lean=0;
      }
      /^[[:space:]]*Pinned commit[[:space:]]*&/ {
        print "\t\t" commit_row;
        seen_commit=1;
        next;
      }
      /^[[:space:]]*Archival DOI[[:space:]]*&/ {
        print "\t\t" doi_row;
        seen_doi=1;
        next;
      }
      /^[[:space:]]*Lean source statistics[[:space:]]*&/ {
        print "\t\t" lean_row;
        seen_lean=1;
        next;
      }
      { print }
      END {
        if (!seen_commit || !seen_doi || !seen_lean) {
          exit 2;
        }
      }
    ' "${tex}" > "${tmp}" || {
      rm -f "${tmp}"
      echo "error: failed to locate reproducibility rows in ${tex}" >&2
      exit 1
    }

  mv "${tmp}" "${tex}"
}

check_one() {
  local tex="$1"
  if ! rg -Fq "${COMMIT_ROW}" "${tex}"; then
    echo "error: stale pinned commit row in ${tex}" >&2
    echo "expected: ${COMMIT_ROW}" >&2
    exit 1
  fi
  if ! rg -Fq "${DOI_ROW}" "${tex}"; then
    echo "error: stale archival DOI row in ${tex}" >&2
    echo "expected: ${DOI_ROW}" >&2
    exit 1
  fi
  if ! rg -Fq "${LEAN_ROW}" "${tex}"; then
    echo "error: stale lean stats row in ${tex}" >&2
    echo "expected: ${LEAN_ROW}" >&2
    exit 1
  fi
}

if [[ "${1:-}" == "--print" ]]; then
  cat <<EOF
${COMMIT_ROW}
${DOI_ROW}
${LEAN_ROW}
EOF
  exit 0
fi

STRICT_DOI=0
if [[ "${1:-}" == "--check" ]]; then
  shift
  if [[ "${1:-}" == "--strict-doi" ]]; then
    STRICT_DOI=1
    shift
  fi
  if [[ "$#" -eq 0 ]]; then
    usage
    exit 2
  fi
  if [[ "${STRICT_DOI}" -eq 1 && "${ARTIFACT_DOI}" == "DOI-UNSET" ]]; then
    echo "error: strict DOI check failed (ARTIFACT_DOI=DOI-UNSET in ${METADATA_FILE})" >&2
    exit 1
  fi
  for tex in "$@"; do
    check_one "${tex}"
  done
  echo "paper reproducibility rows are up to date."
  exit 0
fi

if [[ "${1:-}" == "--sync" ]]; then
  shift
  if [[ "$#" -eq 0 ]]; then
    usage
    exit 2
  fi
  for tex in "$@"; do
    sync_one "${tex}"
  done
  echo "synchronized reproducibility rows in $*"
  exit 0
fi

usage
exit 2
