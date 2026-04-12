#!/usr/bin/env bash
# Validate workspace crate dependency ordering: no crate may depend on a
# higher-layer crate. Uses cargo metadata + jq.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

# ── Prerequisites ─────────────────────────────────────────────────────
if ! command -v jq >/dev/null 2>&1; then
  echo "error: jq is required" >&2
  exit 2
fi

if ! command -v cargo >/dev/null 2>&1; then
  echo "error: cargo is required" >&2
  exit 2
fi

echo "Checking TellTale dependency-layer ordering..."
echo

# ── Layer Map ─────────────────────────────────────────────────────────
# Crate name -> layer number. Lower layers must not depend on higher ones.
crate_layer() {
  case "$1" in
    telltale-types) echo 1 ;;
    telltale-theory|telltale-language|telltale-macros) echo 2 ;;
    telltale-machine|telltale-search) echo 3 ;;
    telltale-runtime|telltale-bridge|telltale-simulator|telltale-transport|telltale|telltale-lints) echo 4 ;;
    telltale-viewer|telltale-ui|telltale-web) echo 5 ;;
    *) echo "" ;;
  esac
}

# ── Cargo Metadata ────────────────────────────────────────────────────
metadata="$(cargo metadata --no-deps --format-version 1)"

workspace_members="$(echo "$metadata" | jq -r '.workspace_members[]')"

# Get workspace package names
pkg_names="$(echo "$metadata" | jq -r --argjson members "$(echo "$metadata" | jq '.workspace_members')" '
  [.packages[] | select(.id as $id | $members | index($id))] | .[].name
')"

# Dependency edges: pkg_name<TAB>dep_name for local, non-dev deps
dep_edges="$(echo "$metadata" | jq -r --argjson members "$(echo "$metadata" | jq '.workspace_members')" '
  .packages[]
  | select(.id as $id | $members | index($id))
  | .name as $pkg
  | .dependencies[]
  | select(.source == null)
  | select(.kind == null)
  | "\($pkg)\t\(.name)"
')"

# ── Validate Layer Assignments ─────────────────────────────────────────
errors=()
unknown=()
pkg_count=0

# Check each workspace package is in the layer map
while IFS= read -r pkg_name; do
  [[ -z "$pkg_name" ]] && continue
  pkg_count=$((pkg_count + 1))
  if [[ -z "$(crate_layer "$pkg_name")" ]]; then
    unknown+=("package_not_layered=${pkg_name}")
  fi
done <<< "$pkg_names"

# ── Check Dependency Edges ─────────────────────────────────────────────
while IFS=$'\t' read -r pkg_name dep_name; do
  [[ -z "$pkg_name" ]] && continue

  # Skip if the package itself is not in the layer map (already reported above)
  pkg_layer="$(crate_layer "$pkg_name")"
  if [[ -z "$pkg_layer" ]]; then
    continue
  fi

  dep_layer="$(crate_layer "$dep_name")"
  if [[ -z "$dep_layer" ]]; then
    unknown+=("${pkg_name} -> ${dep_name}")
    continue
  fi

  if (( dep_layer > pkg_layer )); then
    errors+=("${pkg_name}(L${pkg_layer}) -> ${dep_name}(L${dep_layer})")
  fi
done <<< "$dep_edges"

# ── Report ────────────────────────────────────────────────────────────
if (( ${#unknown[@]} > 0 )); then
  mapfile -t unknown_sorted < <(printf '%s\n' "${unknown[@]}" | sort -u)
else
  unknown_sorted=()
fi

# Sort errors for stable output
if (( ${#errors[@]} > 0 )); then
  mapfile -t errors_sorted < <(printf '%s\n' "${errors[@]}" | sort)
else
  errors_sorted=()
fi

if (( ${#unknown_sorted[@]} > 0 )); then
  echo "Dependency layer check failed: unmapped local dependencies detected."
  echo "Add these crates to the layer map:"
  for item in "${unknown_sorted[@]}"; do
    echo "  - ${item}"
  done
  echo
fi

if (( ${#errors_sorted[@]} > 0 )); then
  echo "Dependency layer check failed: forbidden upward dependency found."
  for item in "${errors_sorted[@]}"; do
    echo "  - ${item}"
  done
  echo
fi

if (( ${#unknown_sorted[@]} > 0 || ${#errors_sorted[@]} > 0 )); then
  total=$(( ${#errors_sorted[@]} + ${#unknown_sorted[@]} ))
  echo "dependency-layer violations: ${total}"
  exit 1
fi

echo "dependency-layer check passed"
echo "checked ${pkg_count} workspace packages"
