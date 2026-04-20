#!/usr/bin/env bash
# Ensure the Lean package has its Mathlib olean cache hydrated.
#
# Mathlib is referenced via a pinned git commit. lake exe cache get downloads
# prebuilt .olean files from cache.leanprover.community keyed by that commit,
# so Mathlib is never rebuilt from source.
#
# Iris and Paco are compiled once and cached in .lake/; they are much smaller
# than Mathlib and have no public olean cache.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LEAN_DIR="${ROOT_DIR}/lean"
IRIS_LINTER_ARGS='moreLeanArgs = ["-Dlinter.unusedSectionVars=false", "-Dlinter.unusedVariables=false"]'

if [[ ! -f "${LEAN_DIR}/lakefile.lean" ]]; then
  echo "error: missing ${LEAN_DIR}/lakefile.lean" >&2
  exit 2
fi

if ! command -v lake >/dev/null 2>&1; then
  echo "error: lake not on PATH — run this script from inside 'nix develop'" >&2
  exit 2
fi

ensure_iris_linter_config() {
  local config_path="$1"
  local config_dir
  local config_name

  config_dir="$(dirname "${config_path}")"
  config_name="$(basename "${config_path}")"

  if [[ ! -f "${config_path}" ]]; then
    echo "error: missing iris package config: ${config_path}" >&2
    exit 1
  fi

  if ! grep -Fq "${IRIS_LINTER_ARGS}" "${config_path}"; then
    perl -0pi -e '
      my $line = qq{'"${IRIS_LINTER_ARGS}"'\n};
      if ($_ !~ /moreLeanArgs = \["-Dlinter\.unusedSectionVars=false", "-Dlinter\.unusedVariables=false"\]/) {
        if (!s/\n\[\[require\]\]/\n$line\n[[require]]/) {
          $_ .= "\n$line";
        }
      }
    ' "${config_path}"
  fi

  if [[ -d "${config_dir}/.git" ]]; then
    git -C "${config_dir}" update-index --assume-unchanged "${config_name}"
  fi
}

package_config_path() {
  local package_name="$1"
  local package_dir=".lake/packages/${package_name}"
  local config_path

  for config_path in \
    "${package_dir}/lakefile.toml" \
    "${package_dir}/lakefile.lean"
  do
    if [[ -f "${config_path}" ]]; then
      printf '%s\n' "${config_path}"
      return 0
    fi
  done

  return 1
}

cd "${LEAN_DIR}"

# Step 1: generate or refresh lake-manifest.json.
manifest_needs_refresh=0
if [[ ! -f "lake-manifest.json" ]]; then
  manifest_needs_refresh=1
elif jq -e '
  .packages[]
  | select((.name == "mathlib" or .name == "iris") and .type == "path")
' lake-manifest.json >/dev/null 2>&1; then
  manifest_needs_refresh=1
fi

if [[ "${manifest_needs_refresh}" -eq 1 ]]; then
  echo "== lake update (refreshing lake-manifest.json) =="
  lake update
else
  echo "OK   lake-manifest.json present"
fi

if ! iris_config_path="$(package_config_path "iris")"; then
  echo "== lake update (materializing missing package checkout: iris) =="
  lake update
  if ! iris_config_path="$(package_config_path "iris")"; then
    echo "error: missing iris package config under .lake/packages/iris" >&2
    exit 1
  fi
fi

if ! package_config_path "mathlib" >/dev/null 2>&1; then
  echo "== lake update (materializing missing package checkout: mathlib) =="
  lake update
  if ! package_config_path "mathlib" >/dev/null 2>&1; then
    echo "error: missing mathlib package config under .lake/packages/mathlib" >&2
    exit 1
  fi
fi

ensure_iris_linter_config "${iris_config_path}"

# Step 2: fetch prebuilt Mathlib oleans from cache.leanprover.community.
# The cache key is the exact mathlib commit pinned in lake-manifest.json.
MATHLIB_MARKER=".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
if [[ ! -f "${MATHLIB_MARKER}" ]]; then
  echo "== lake exe cache get (fetching prebuilt Mathlib oleans) =="
  lake exe cache get
else
  echo "OK   Mathlib olean cache present"
fi

if [[ ! -f "${MATHLIB_MARKER}" ]]; then
  echo "error: Mathlib olean marker missing after cache fetch" >&2
  echo "  expected: ${LEAN_DIR}/${MATHLIB_MARKER}" >&2
  echo "hint: try 'lake exe cache get' manually inside lean/" >&2
  exit 1
fi

echo "== Lean prebuilt cache ready — run 'lake build' to compile telltale =="
