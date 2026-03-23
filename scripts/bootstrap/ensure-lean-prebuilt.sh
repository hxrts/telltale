#!/usr/bin/env bash
# Ensure repo-owned Lean entrypoints reuse pinned local dependency builds and
# hydrated package caches instead of rebuilding dependency trees from source.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LEAN_DIR="${ROOT_DIR}/lean"
PINS_FILE="${LEAN_DIR}/dependency_pins.json"
DEPENDENCY_BOOTSTRAP="${ROOT_DIR}/scripts/bootstrap/dependency-checkouts.sh"

if [[ ! -f "${LEAN_DIR}/lakefile.lean" ]]; then
  echo "error: missing Lean package at ${LEAN_DIR}/lakefile.lean" >&2
  exit 2
fi

if [[ ! -f "${PINS_FILE}" ]]; then
  echo "error: missing dependency pins file: ${PINS_FILE}" >&2
  exit 2
fi

if ! command -v jq >/dev/null 2>&1; then
  echo "error: jq is required but not found on PATH" >&2
  exit 2
fi

dependency_bootstrap_needed=0
while IFS= read -r dep; do
  name="$(jq -r '.name' <<< "${dep}")"
  checkout="$(jq -r '.path' <<< "${dep}")"
  revision="$(jq -r '.revision' <<< "${dep}")"

  if [[ ! -d "${checkout}/.git" ]]; then
    dependency_bootstrap_needed=1
    break
  fi

  actual="$(git -C "${checkout}" rev-parse HEAD 2>/dev/null || true)"
  if [[ "${actual}" != "${revision}" ]]; then
    dependency_bootstrap_needed=1
    break
  fi
done < <(jq -c '.dependencies[]' "${PINS_FILE}")

mathlib_path="$(jq -r '.dependencies[] | select(.name == "mathlib4") | .path' "${PINS_FILE}")"
mathlib_marker="${mathlib_path}/.lake/build/lib/lean/Mathlib.olean"
if [[ ! -f "${mathlib_marker}" ]]; then
  dependency_bootstrap_needed=1
fi

if (( dependency_bootstrap_needed )); then
  "${DEPENDENCY_BOOTSTRAP}"
else
  echo "OK   pinned local Lean dependency checkouts already present"
  echo "OK   mathlib4 cache present at ${mathlib_marker}"
fi

iris_path="$(jq -r '.dependencies[] | select(.name == "iris-lean") | .path' "${PINS_FILE}")"
if ! find "${iris_path}/.lake/build/lib/lean" -type f -name '*.olean' -print -quit 2>/dev/null | grep -q .; then
  echo "error: missing prebuilt iris-lean oleans under ${iris_path}/.lake/build/lib/lean" >&2
  echo "hint: build the pinned local iris checkout once, then rerun this command" >&2
  exit 1
fi
echo "OK   iris-lean local build artifacts present under ${iris_path}/.lake/build/lib/lean"

package_cache_markers=(
  "${LEAN_DIR}/.lake/packages/batteries/.lake/build/lib/lean/Batteries.olean"
  "${LEAN_DIR}/.lake/packages/aesop/.lake/build/lib/lean/Aesop.olean"
)

package_cache_missing=0
for marker in "${package_cache_markers[@]}"; do
  if [[ ! -f "${marker}" ]]; then
    package_cache_missing=1
    break
  fi
done

if (( package_cache_missing )); then
  echo "sync Lean package caches: fetching prebuilt oleans with \`lake exe cache get\`"
  (
    cd "${LEAN_DIR}"
    lake exe cache get
  )
fi

for marker in "${package_cache_markers[@]}"; do
  if [[ ! -f "${marker}" ]]; then
    echo "error: expected Lean package cache marker missing after hydration: ${marker}" >&2
    exit 1
  fi
done
echo "OK   Lean package caches are ready under ${LEAN_DIR}/.lake/packages"
