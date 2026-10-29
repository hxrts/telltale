#!/usr/bin/env bash
# Dispatch contract only; real compiler/cache-hit acceptance is separate.
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
temporary=$(mktemp -d)
trap 'rm -rf "$temporary"' EXIT
export TELLTALE_DISPATCH_RECORD="$temporary/record"
cat > "$temporary/cargo" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "${0##*/}" "${RUSTC_WRAPPER-unset}" "$@" > "$TELLTALE_DISPATCH_RECORD"
exit "${TELLTALE_DISPATCH_EXIT:-0}"
SH
cp "$temporary/cargo" "$temporary/clippy"
cp "$temporary/cargo" "$temporary/fmt"
chmod +x "$temporary/cargo" "$temporary/clippy" "$temporary/fmt"
export TELLTALE_NIX_CARGO_BIN="$temporary/cargo"
export TELLTALE_NIX_CLIPPY_BIN="$temporary/clippy"
export TELLTALE_NIX_FMT_BIN="$temporary/fmt"
unset TELLTALE_NO_SCCACHE CARGO_INCREMENTAL TELLTALE_DISPATCH_EXIT
export RUSTC_WRAPPER=/chosen/bin/sccache
check_record() {
  printf '%s\n' "$@" > "$temporary/expected"
  cmp "$temporary/expected" "$TELLTALE_DISPATCH_RECORD"
}
bash "$root/scripts/dev/cargo-in-nix.sh" check --message-format=json 'two words'
check_record cargo /chosen/bin/sccache check --message-format=json 'two words'
bash "$root/scripts/dev/cargo-in-nix.sh" clippy --all-targets -- -D warnings
check_record clippy /chosen/bin/sccache clippy --all-targets -- -D warnings
bash "$root/scripts/dev/cargo-in-nix.sh" fmt --all -- --check
check_record fmt /chosen/bin/sccache fmt --all -- --check
TELLTALE_NO_SCCACHE=1 bash "$root/scripts/dev/cargo-in-nix.sh" check
check_record cargo unset check
CARGO_INCREMENTAL=1 bash "$root/scripts/dev/cargo-in-nix.sh" check
check_record cargo unset check
RUSTC_WRAPPER=/caller/custom-wrapper TELLTALE_NO_SCCACHE=1 \
  bash "$root/scripts/dev/cargo-in-nix.sh" check
check_record cargo /caller/custom-wrapper check
status=0
TELLTALE_DISPATCH_EXIT=31 bash "$root/scripts/dev/cargo-in-nix.sh" check || status=$?
[[ $status == 31 ]]
status=0
TELLTALE_DISPATCH_EXIT=32 bash "$root/scripts/dev/cargo-in-nix.sh" clippy || status=$?
[[ $status == 32 ]]
status=0
TELLTALE_DISPATCH_EXIT=33 bash "$root/scripts/dev/cargo-in-nix.sh" fmt || status=$?
[[ $status == 33 ]]
env -u RUSTC_WRAPPER bash "$root/scripts/dev/cargo-in-nix.sh" --version
check_record cargo unset --version
echo 'Cargo/Clippy/fmt dispatch fixtures: OK (10 cases; no compiler/cache-hit claim)'
