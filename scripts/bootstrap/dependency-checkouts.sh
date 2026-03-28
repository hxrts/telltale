#!/usr/bin/env bash
# Clone or update Lean dependency checkouts (mathlib4, iris-lean) to pinned
# revisions from dependency_pins.json. Ensures mathlib cache is present.
set -euo pipefail

# ── Configuration ─────────────────────────────────────────────────────

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PINS_FILE="${ROOT_DIR}/lean/dependency_pins.json"

# ── Prerequisites ─────────────────────────────────────────────────────

if [[ ! -f "${PINS_FILE}" ]]; then
  echo "error: missing dependency pins file: ${PINS_FILE}" >&2
  exit 2
fi

if ! command -v jq &>/dev/null; then
  echo "error: jq is required but not found on PATH" >&2
  exit 2
fi

# ── Repository Mapping ────────────────────────────────────────────────

# Resolve dependency name to its git remote URL.
repo_for_name() {
  case "$1" in
    mathlib4)   echo "https://github.com/leanprover-community/mathlib4.git" ;;
    iris-lean)  echo "https://github.com/hxrts/iris-lean.git" ;;
    *)          return 1 ;;
  esac
}

# ── Mathlib Cache ─────────────────────────────────────────────────────

# Fetch prebuilt oleans if the cache marker is absent.
ensure_mathlib_cache() {
  local checkout="$1"
  local marker="${checkout}/.lake/build/lib/lean/Mathlib.olean"

  if [[ -f "${marker}" ]]; then
    echo "OK   mathlib4 cache present at ${marker}"
    return
  fi

  echo "sync mathlib4 cache: fetching prebuilt oleans with \`lake exe cache get\`"
  if ! (cd "${checkout}" && lake exe cache get); then
    echo "error: failed to fetch prebuilt mathlib4 cache; run \`cd /Users/hxrts/projects/lean_common/mathlib4 && lake exe cache get\` after resolving the local issue" >&2
    exit 1
  fi

  if [[ ! -f "${marker}" ]]; then
    echo "error: \`lake exe cache get\` completed but Mathlib.olean is still missing at ${marker}" >&2
    exit 1
  fi

  echo "OK   mathlib4 cache ready at ${marker}"
}

# ── iris-lean Build Artifacts ─────────────────────────────────────────

ensure_iris_build() {
  local checkout="$1"

  if find "${checkout}/.lake/build/lib/lean" -type f -name '*.olean' -print -quit 2>/dev/null | grep -q .; then
    echo "OK   iris-lean build artifacts present under ${checkout}/.lake/build/lib/lean"
    return
  fi

  echo "build iris-lean: compiling pinned dependency with \`lake build Iris\`"
  local attempts=0
  local max_attempts=3
  local ok=0
  while [[ "${attempts}" -lt "${max_attempts}" ]]; do
    attempts=$((attempts + 1))
    if (cd "${checkout}" && lake build Iris); then
      ok=1
      break
    fi
    if [[ "${attempts}" -lt "${max_attempts}" ]]; then
      echo "warning: iris-lean build attempt ${attempts}/${max_attempts} failed; cleaning packages and retrying in 10s"
      rm -rf "${checkout}/.lake/packages"
      sleep 10
    fi
  done
  if [[ "${ok}" -ne 1 ]]; then
    echo "error: failed to build iris-lean at ${checkout} after ${max_attempts} attempts; run \`cd ${checkout} && lake build Iris\` after resolving the local issue" >&2
    exit 1
  fi

  if ! find "${checkout}/.lake/build/lib/lean" -type f -name '*.olean' -print -quit 2>/dev/null | grep -q .; then
    echo "error: \`lake build Iris\` completed but iris-lean oleans are still missing under ${checkout}/.lake/build/lib/lean" >&2
    exit 1
  fi

  echo "OK   iris-lean build artifacts ready under ${checkout}/.lake/build/lib/lean"
}

# ── Validate Dependencies Array ───────────────────────────────────────

dep_count="$(jq -r '.dependencies | if type == "array" then length else -1 end' "${PINS_FILE}")"
if [[ "${dep_count}" -le 0 ]]; then
  echo "error: dependency_pins.json must define non-empty dependencies" >&2
  exit 1
fi

# ── Iterate Dependencies ──────────────────────────────────────────────

for i in $(seq 0 $(( dep_count - 1 ))); do
  name="$(jq -r ".dependencies[$i].name // empty" "${PINS_FILE}")"
  path="$(jq -r ".dependencies[$i].path // empty" "${PINS_FILE}")"
  revision="$(jq -r ".dependencies[$i].revision // empty" "${PINS_FILE}")"

  if [[ -z "${name}" || -z "${path}" || -z "${revision}" ]]; then
    entry="$(jq -c ".dependencies[$i]" "${PINS_FILE}")"
    echo "error: invalid dependency pin entry: ${entry}" >&2
    exit 1
  fi

  repo="$(repo_for_name "${name}")" || {
    echo "error: missing repository mapping for dependency '${name}'" >&2
    exit 1
  }

  checkout="${path}"
  mkdir -p "$(dirname "${checkout}")"

  if [[ -d "${checkout}/.git" ]]; then
    actual="$(git -C "${checkout}" rev-parse HEAD 2>/dev/null || true)"
    if [[ "${actual}" == "${revision}" ]]; then
      echo "OK   ${name} already at pinned revision ${revision}"
    else
      echo "sync ${name}: fetching pinned revision ${revision}"
      git -C "${checkout}" fetch --depth=1 origin "${revision}"
      git -C "${checkout}" checkout --detach "${revision}"
    fi
  else
    echo "clone ${name}: ${repo} -> ${checkout}"
    git clone --filter=blob:none "${repo}" "${checkout}"
    git -C "${checkout}" fetch --depth=1 origin "${revision}"
    git -C "${checkout}" checkout --detach "${revision}"
  fi

  actual="$(git -C "${checkout}" rev-parse HEAD)"
  if [[ "${actual}" != "${revision}" ]]; then
    echo "error: ${name} pinned checkout mismatch: expected ${revision}, got ${actual}" >&2
    exit 1
  fi
  echo "OK   ${name} pinned at ${actual}"

  if [[ "${name}" == "mathlib4" ]]; then
    ensure_mathlib_cache "${checkout}"
  elif [[ "${name}" == "iris-lean" ]]; then
    ensure_iris_build "${checkout}"
  fi
done
