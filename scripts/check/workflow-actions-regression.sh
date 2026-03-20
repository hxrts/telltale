#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

tmp_root="${TMPDIR:-/tmp}"
if [[ ! -d "$tmp_root" ]]; then
  tmp_root="/tmp"
fi

tmpdir="$(TMPDIR="$tmp_root" mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

cat > "$tmpdir/bad.yml" <<'EOF'
name: Bad
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: leanprover/lean4-action@v1
EOF

if WORKFLOW_ACTIONS_DIR="$tmpdir" ./scripts/check/workflow-actions.sh >"$tmpdir/output.log" 2>&1; then
  echo "error: workflow action regression check unexpectedly passed" >&2
  cat "$tmpdir/output.log" >&2
  exit 1
fi

grep -q "unresolved GitHub Action reference leanprover/lean4-action@v1" "$tmpdir/output.log"
