#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_FILE="${ROOT_DIR}/paper/artifact_manifest.json"
LOG_DIR="${ROOT_DIR}/artifacts/paper"
PAPER_DIR="${ROOT_DIR}/paper/build"

hash_file() {
  local path="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "${path}" | awk '{print $1}'
    return
  fi
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "${path}" | awk '{print $1}'
    return
  fi
  echo "error: sha256 tool not found (need sha256sum or shasum)" >&2
  exit 2
}

json_escape() {
  printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g'
}

tool_version() {
  local cmd="$1"
  local fallback="$2"
  if command -v "${cmd}" >/dev/null 2>&1; then
    "${cmd}" --version 2>/dev/null | head -n 1 || true
  else
    printf '%s' "${fallback}"
  fi
}

LEAN_TOOLCHAIN="$(cat "${ROOT_DIR}/lean-toolchain" 2>/dev/null || echo "unavailable")"
RUST_TOOLCHAIN="$(cat "${ROOT_DIR}/rust-toolchain" 2>/dev/null || echo "unavailable")"
COMMIT="$(git -C "${ROOT_DIR}" rev-parse HEAD)"
DIRTY="false"
if ! git -C "${ROOT_DIR}" diff --quiet || ! git -C "${ROOT_DIR}" diff --cached --quiet; then
  DIRTY="true"
fi

mkdir -p "$(dirname "${OUT_FILE}")"

paper_hash_or_null() {
  local file="$1"
  if [[ -f "${file}" ]]; then
    printf '"%s"' "$(hash_file "${file}")"
  else
    printf 'null'
  fi
}

LOG_JSON=""
if [[ -d "${LOG_DIR}" ]]; then
  while IFS= read -r log_file; do
    base="$(basename "${log_file}")"
    hash="$(hash_file "${log_file}")"
    if [[ -n "${LOG_JSON}" ]]; then
      LOG_JSON="${LOG_JSON},"
    fi
    LOG_JSON="${LOG_JSON}\"$(json_escape "${base}")\":\"${hash}\""
  done < <(find "${LOG_DIR}" -maxdepth 1 -type f -name '*.log' | LC_ALL=C sort)
fi

if [[ -z "${LOG_JSON}" ]]; then
  LOG_JSON="\"_none\":\"no-log-files-found\""
fi

cat > "${OUT_FILE}" <<EOF
{
  "schema_version": 1,
  "generated_at_utc": "$(date -u +"%Y-%m-%dT%H:%M:%SZ")",
  "repository": "https://github.com/hxrts/telltale",
  "commit": "${COMMIT}",
  "dirty_worktree": ${DIRTY},
  "toolchains": {
    "lean_toolchain_file": "$(json_escape "${LEAN_TOOLCHAIN}")",
    "rust_toolchain_file": "$(json_escape "${RUST_TOOLCHAIN}")",
    "lake_version": "$(json_escape "$(tool_version lake unavailable)")",
    "lean_version": "$(json_escape "$(tool_version lean unavailable)")",
    "rustc_version": "$(json_escape "$(tool_version rustc unavailable)")",
    "pdflatex_version": "$(json_escape "$(tool_version pdflatex unavailable)")"
  },
  "artifacts": {
    "paper1_pdf_sha256": $(paper_hash_or_null "${PAPER_DIR}/paper1.pdf"),
    "paper2_pdf_sha256": $(paper_hash_or_null "${PAPER_DIR}/paper2.pdf"),
    "paper3_pdf_sha256": $(paper_hash_or_null "${PAPER_DIR}/paper3.pdf")
  },
  "log_sha256": {
    ${LOG_JSON}
  }
}
EOF

echo "wrote ${OUT_FILE}"
