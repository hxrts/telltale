#!/usr/bin/env bash
# Keep telltale-search generic and independent of simulator/viewer/application
# layers.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

fail=0

check_no_hits() {
  local pattern="$1"
  shift
  local paths=("$@")
  local hits
  hits="$(rg -n "$pattern" "${paths[@]}" || true)"
  if [[ -n "$hits" ]]; then
    echo "search boundary violation for pattern: $pattern" >&2
    echo "$hits" >&2
    fail=1
  fi
}

check_has_hits() {
  local pattern="$1"
  local path="$2"
  if ! rg -q "$pattern" "$path"; then
    echo "expected to find '$pattern' in $path" >&2
    fail=1
  fi
}

check_no_hits 'telltale-simulator|telltale-viewer|telltale-ui|telltale-web|dioxus' rust/search
check_no_hits 'Bluetooth|bluetooth|BLE|mesh router|radio interference|RF' rust/search docs/507_session_graph_search.md
check_has_hits 'telltale-search' docs/507_session_graph_search.md
check_has_hits 'downstream' docs/507_session_graph_search.md
check_has_hits 'optional' docs/507_session_graph_search.md
check_has_hits 'generic' docs/507_session_graph_search.md

if [[ "$fail" -ne 0 ]]; then
  exit 1
fi

echo "search-boundaries: clean"
