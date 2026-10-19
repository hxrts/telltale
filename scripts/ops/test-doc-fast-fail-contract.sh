#!/usr/bin/env bash
# Exercise the actual cheap gate without compiling any assurance/build targets.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
selected_justfile="${1:-$repo_root/justfile}"
real_just=$(command -v just)
fixture=$(mktemp -d "${TMPDIR:-/tmp}/telltale-doc-fast-fail.XXXXXX")
trap 'rm -rf "$fixture"' EXIT
mkdir "$fixture/bin"
cat > "$fixture/bin/just" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ $# == 1 ]] || exit 2
case "$1" in
  check-doc-quality|check-doc-links-ci|check-docs-as-contract|check-docs-semantic-drift|check-docs-index|check-verification-inventory) ;;
  *) exit 2 ;;
esac
printf '%s\n' "$1" >> "$DOC_GATE_LOG"
if [[ "$1" == check-doc-quality ]]; then exit "${DOC_GATE_FAIL:-0}"; fi
SH
chmod +x "$fixture/bin/just"
export PATH="$fixture/bin:$PATH" DOC_GATE_LOG="$fixture/calls"
"$real_just" --justfile "$selected_justfile" --working-directory "$repo_root" check-doc-fast-fail > "$fixture/output" 2>&1
cat > "$fixture/expected" <<'EXPECTED'
check-doc-quality
check-doc-links-ci
check-docs-as-contract
check-docs-semantic-drift
check-docs-index
check-verification-inventory
EXPECTED
cmp "$fixture/expected" "$DOC_GATE_LOG"
: > "$DOC_GATE_LOG"
result=0
DOC_GATE_FAIL=17 "$real_just" --justfile "$selected_justfile" --working-directory "$repo_root" check-doc-fast-fail > "$fixture/output" 2>&1 || result=$?
[[ "$result" == 17 ]]
printf '%s\n' check-doc-quality > "$fixture/expected"
cmp "$fixture/expected" "$DOC_GATE_LOG"
echo 'doc fast-fail: prose precedes other gates; original failure stops the lane'
