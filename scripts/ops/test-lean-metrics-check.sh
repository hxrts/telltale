#!/usr/bin/env bash
# Check mode must accept unchanged historical metrics and never mutate input.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_tmp_root="${TMPDIR:-/tmp}"
[[ -d "$test_tmp_root" ]] || test_tmp_root=/tmp
fixture="$(TMPDIR="$test_tmp_root" mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
mkdir -p "$fixture/scripts/ops" "$fixture/lean/SessionTypes"
cp "$repo_root/scripts/ops/sync-lean-metrics.sh" "$fixture/scripts/ops/"
printf 'def fixture : Nat := 1\n' > "$fixture/lean/SessionTypes/Fixture.lean"
cat > "$fixture/lean/CODE_MAP.md" <<'EOF'
# Lean test map
<!-- GENERATED_METRICS:BEGIN -->
**Last Updated:** 2000-01-01
<!-- GENERATED_METRICS:END -->
<!-- GENERATED_OVERVIEW_TABLE:BEGIN -->
<!-- GENERATED_OVERVIEW_TABLE:END -->
EOF
bash "$fixture/scripts/ops/sync-lean-metrics.sh" >/dev/null
sed 's/^\*\*Last Updated:\*\* .*/**Last Updated:** 2000-01-01/' \
  "$fixture/lean/CODE_MAP.md" > "$fixture/expected.md"
cp "$fixture/expected.md" "$fixture/lean/CODE_MAP.md"
bash "$fixture/scripts/ops/sync-lean-metrics.sh" --check >/dev/null
cmp "$fixture/expected.md" "$fixture/lean/CODE_MAP.md"
printf 'def drift : Nat := 2\n' >> "$fixture/lean/SessionTypes/Fixture.lean"
if bash "$fixture/scripts/ops/sync-lean-metrics.sh" --check > "$fixture/drift.log" 2>&1; then
  echo 'error: stale Lean counts passed check mode' >&2
  exit 1
fi
grep -Fq 'Lean metrics are stale' "$fixture/drift.log"
cmp "$fixture/expected.md" "$fixture/lean/CODE_MAP.md"
echo 'Lean metrics check: historical dates and read-only drift rejection verified.'
