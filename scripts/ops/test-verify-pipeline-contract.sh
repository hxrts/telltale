#!/usr/bin/env bash
# Exercise the actual Verify run blocks with fake just; no assurance/build runs.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
workflow="${1:-$repo_root/.github/workflows/verify.yml}"
fixture="$(mktemp -d "${TMPDIR:-/tmp}/telltale-verify-pipeline.XXXXXX")"
trap 'rm -rf "$fixture"' EXIT
mkdir "$fixture/bin"
cat > "$fixture/bin/just" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ $# == 1 ]] || exit 2
case "$1" in check-pr-critical|check-parity|check-deep-assurance) ;; *) exit 2 ;; esac
printf 'original %s failure\n' "$1"
printf 'original %s diagnostic\n' "$1" >&2
exit "${VERIFY_FIXTURE_STATUS:-0}"
SH
chmod +x "$fixture/bin/just"
# Extract the real YAML literal run blocks, then execute those exact commands.
awk -v out="$fixture" '
function flush() {
  if (block ~ /[|] tee artifacts\//) {
    count++
    if (first != "set -euo pipefail") exit 1
    print block > (out "/step-" count ".sh")
  }
  block=""; first=""; active=0
}
/^        run: [|]$/ { flush(); active=1; next }
active && /^          / {
  line=substr($0,11); if (first == "" && line != "") first=line
  block=block line "\n"; next
}
active { flush() }
END { flush(); if (count != 5) exit 1 }
' "$workflow"
[[ $(grep -c 'sudo apt-get update && sudo apt-get install -y ripgrep' "$workflow") == 2 ]] || exit 1
[[ $(awk '/- name: Upload .*artifacts/ { getline; if ($0 == "        if: always()") n++ } END { print n+0 }' "$workflow") == 2 ]] || exit 1
for step in 1 2 3 4 5; do
  mkdir "$fixture/run-$step"
  status=0
  (cd "$fixture/run-$step"; PATH="$fixture/bin:$PATH" VERIFY_FIXTURE_STATUS=17 \
    "$BASH" -e "$fixture/step-$step.sh") > "$fixture/failure-$step.log" 2>&1 || status=$?
  [[ "$status" == 17 ]] || exit 1
  grep -q 'original .* failure' "$fixture/run-$step"/artifacts/*.log
  grep -q 'original .* diagnostic' "$fixture/run-$step"/artifacts/*.log
  (cd "$fixture/run-$step"; PATH="$fixture/bin:$PATH" VERIFY_FIXTURE_STATUS=0 \
    "$BASH" -e "$fixture/step-$step.sh") > "$fixture/success-$step.log" 2>&1
  printf 'Verify pipeline %s: original17 retained, stdout+stderr artifact retained, success0\n' "$step"
done
printf 'Verify: five strict pipelines; both jobs install rg; both failure uploads always run\n'
