#!/usr/bin/env bash
# Validate that Lean dependency checkouts match pinned revisions
# recorded in lean/dependency_pins.json.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PINS_FILE="${ROOT_DIR}/lean/dependency_pins.json"

# ── Load Pins File ────────────────────────────────────────────────────

if [[ ! -f "${PINS_FILE}" ]]; then
  echo "error: missing dependency pins file: ${PINS_FILE}" >&2
  exit 2
fi

dep_count="$(jq '.dependencies | if type == "array" then length else 0 end' "${PINS_FILE}")"
if [[ "${dep_count}" -eq 0 ]]; then
  echo "error: dependency_pins.json must define non-empty dependencies" >&2
  exit 1
fi

# ── Verify Each Dependency ─────────────────────────────────────────────

errors=()

for i in $(seq 0 $((dep_count - 1))); do
  name="$(jq -r ".dependencies[$i].name // empty" "${PINS_FILE}")"
  path="$(jq -r ".dependencies[$i].path // empty" "${PINS_FILE}")"
  expected="$(jq -r ".dependencies[$i].revision // empty" "${PINS_FILE}")"

  if [[ -z "${name}" || -z "${path}" || -z "${expected}" ]]; then
    entry="$(jq -c ".dependencies[$i]" "${PINS_FILE}")"
    errors+=("invalid dependency pin entry: ${entry}")
    continue
  fi

  if [[ ! -e "${path}" ]]; then
    errors+=("${name}: missing checkout at ${path}")
    continue
  fi

  if ! actual="$(git -C "${path}" rev-parse HEAD 2>&1)"; then
    errors+=("${name}: failed to read git revision (${actual})")
    continue
  fi

  actual="${actual%"${actual##*[![:space:]]}"}"

  if [[ "${actual}" != "${expected}" ]]; then
    errors+=("${name}: expected ${expected}, found ${actual}")
  else
    echo "OK   ${name} pinned at ${actual}"
  fi
done

# ── Report ────────────────────────────────────────────────────────────

if [[ ${#errors[@]} -gt 0 ]]; then
  for error in "${errors[@]}"; do
    echo "FAIL ${error}"
  done
  exit 1
fi
