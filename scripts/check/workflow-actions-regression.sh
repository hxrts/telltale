#!/usr/bin/env bash
# Regression test: verify workflow-actions.sh correctly rejects an
# intentionally bad action reference.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

# ── Setup Temp Workflow ───────────────────────────────────────────────

tmp_root="${TMPDIR:-/tmp}"
if [[ ! -d "$tmp_root" ]]; then
  tmp_root="/tmp"
fi

tmpdir="$(TMPDIR="$tmp_root" mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

# Craft a workflow with a known-bad action ref
cat > "$tmpdir/bad.yml" <<'EOF'
name: Bad
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: leanprover/lean4-action@v1
EOF

# ── Assert Rejection ──────────────────────────────────────────────────

# The check script must fail on the bad ref
if WORKFLOW_ACTIONS_DIR="$tmpdir" ./scripts/check/workflow-actions.sh >"$tmpdir/output.log" 2>&1; then
  echo "error: workflow action regression check unexpectedly passed" >&2
  cat "$tmpdir/output.log" >&2
  exit 1
fi

# Confirm the expected error message appears
grep -q "unresolved GitHub Action reference leanprover/lean4-action@v1" "$tmpdir/output.log"
