#!/usr/bin/env bash
# Exercise conformance failure propagation without compiling benchmark targets.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
sandbox="$(mktemp -d)"
trap 'rm -rf "$sandbox"' EXIT
mkdir -p "$sandbox/scripts/ops" "$sandbox/bin"
cp "$repo_root/scripts/ops/perf-baseline.sh" "$sandbox/scripts/ops/"
for target in conformance_lean equivalence_lean differential_step_corpus \
  threaded_contract threaded_equivalence threaded_lane_runtime; do
  test -f "$repo_root/rust/machine/tests/$target.rs"
done
cat > "$sandbox/bin/cargo" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
mode="$1"
shift
if [[ "$mode" == run ]]; then
  while (( $# )); do
    if [[ "$1" == --output ]]; then
      printf '{"envelope_diff_artifact":{}}\n' > "$2"
      exit 0
    fi
    shift
  done
  exit 2
fi
test "$mode" == test
while (( $# )); do
  if [[ "$1" == --test ]]; then
    target="$2"
    case "$target" in
      conformance_lean|equivalence_lean|differential_step_corpus|\
      threaded_contract|threaded_equivalence|threaded_lane_runtime) ;;
      *) exit 2 ;;
    esac
    [[ "$target" != "${BASELINE_TEST_FAIL_TARGET:-}" ]]
    exit
  fi
  shift
done
exit 2
SH
chmod +x "$sandbox/bin/cargo"
export PATH="$sandbox/bin:$PATH"
baseline="$sandbox/artifacts/v2/baseline"
for target in conformance_lean threaded_contract; do
  rm -rf "$baseline"
  if BASELINE_TEST_FAIL_TARGET="$target" bash \
    "$sandbox/scripts/ops/perf-baseline.sh" freeze > "$sandbox/output" 2>&1; then
    echo "failed conformance target was accepted: $target" >&2
    exit 1
  fi
  test -f "$baseline/conformance.json"
  test ! -f "$baseline/hash_snapshot.json"
done
rm -rf "$baseline"
bash "$sandbox/scripts/ops/perf-baseline.sh" freeze > "$sandbox/output" 2>&1
bash "$sandbox/scripts/ops/perf-baseline.sh" check > "$sandbox/output" 2>&1
# A matching hash must not bless a captured failed corpus.
jq '.threaded.passed = 2 | .threaded.pass_rate = 0.667' \
  "$baseline/conformance.json" > "$sandbox/failed.json"
mv "$sandbox/failed.json" "$baseline/conformance.json"
if command -v sha256sum >/dev/null 2>&1; then
  failed_hash="$(sha256sum "$baseline/conformance.json" | awk '{print $1}')"
else
  failed_hash="$(shasum -a 256 "$baseline/conformance.json" | awk '{print $1}')"
fi
jq --arg digest "$failed_hash" '.conformance_sha256 = $digest' \
  "$baseline/hash_snapshot.json" > "$sandbox/snapshot.json"
mv "$sandbox/snapshot.json" "$baseline/hash_snapshot.json"
if bash "$sandbox/scripts/ops/perf-baseline.sh" check > "$sandbox/output" 2>&1; then
  echo "matching hash accepted a failed conformance corpus" >&2
  exit 1
fi
echo "Performance baseline conformance failure guards passed"
