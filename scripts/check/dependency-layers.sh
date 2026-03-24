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
declare -A layer_of=(
  # Foundation
  ["telltale-types"]=1
  # Core algorithm and macro layer
  ["telltale-theory"]=2
  ["telltale-macros"]=2
  # Runtime/verification
  ["telltale-machine"]=3
  # Session tooling, transport, and facade layer
  ["telltale-choreography"]=4
  ["telltale-lean-bridge"]=4
  ["telltale-simulator"]=4
  ["telltale-transport"]=4
  ["telltale"]=4
  # Internal support utility
  ["telltale-lints"]=4
)

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
  if [[ -z "${layer_of[$pkg_name]+x}" ]]; then
    unknown+=("package_not_layered=${pkg_name}")
  fi
done <<< "$pkg_names"

# ── Check Dependency Edges ─────────────────────────────────────────────
while IFS=$'\t' read -r pkg_name dep_name; do
  [[ -z "$pkg_name" ]] && continue

  # Skip if the package itself is not in the layer map (already reported above)
  if [[ -z "${layer_of[$pkg_name]+x}" ]]; then
    continue
  fi

  pkg_layer="${layer_of[$pkg_name]}"

  if [[ -z "${layer_of[$dep_name]+x}" ]]; then
    unknown+=("${pkg_name} -> ${dep_name}")
    continue
  fi

  dep_layer="${layer_of[$dep_name]}"

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
