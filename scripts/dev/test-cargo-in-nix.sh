#!/usr/bin/env bash
# Dispatch contract only; real compiler/cache-hit acceptance is separate.
set -euo pipefail
: "${TOOLKIT_CARGO_DISPATCH_BIN:?enter the Telltale Nix shell for the selected Toolkit dispatcher}"
[[ $TOOLKIT_CARGO_DISPATCH_BIN == /* && -x $TOOLKIT_CARGO_DISPATCH_BIN ]] || exit 2
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
temporary=$(mktemp -d)
trap 'rm -rf "$temporary"' EXIT
export TELLTALE_DISPATCH_RECORD="$temporary/record"
cat > "$temporary/cargo" <<'SH'
#!/usr/bin/env bash
printf '%s' "${CARGO_TOOLKIT_APPLE_DEPLOYMENT_V1-ABSENT}" > "$TELLTALE_DISPATCH_RECORD.key"
printf '%s\n' "${0##*/}" "${RUSTC_WRAPPER-unset}" "$@" > "$TELLTALE_DISPATCH_RECORD"
if [[ ${TELLTALE_DISPATCH_STREAMS:-0} == 1 ]]; then
  printf 'native stdout\000tail\n'
  printf 'native stderr\000tail\n' >&2
fi
exit "${TELLTALE_DISPATCH_EXIT:-0}"
SH
cp "$temporary/cargo" "$temporary/clippy"
cp "$temporary/cargo" "$temporary/fmt"
chmod +x "$temporary/cargo" "$temporary/clippy" "$temporary/fmt"
export TELLTALE_NIX_CARGO_BIN="$temporary/cargo"
export TELLTALE_NIX_CLIPPY_BIN="$temporary/clippy"
export TELLTALE_NIX_FMT_BIN="$temporary/fmt"
unset TELLTALE_NO_SCCACHE CARGO_INCREMENTAL TELLTALE_DISPATCH_EXIT
mkdir -p "$temporary/selected" "$temporary/caller"
cp "$temporary/cargo" "$temporary/selected/sccache"
cp "$temporary/cargo" "$temporary/caller/sccache"
export TELLTALE_NIX_SCCACHE_BIN="$temporary/selected/sccache"
export RUSTC_WRAPPER="$TELLTALE_NIX_SCCACHE_BIN"
check_record() {
  printf '%s\n' "$@" > "$temporary/expected"
  if ! cmp "$temporary/expected" "$TELLTALE_DISPATCH_RECORD"; then
    printf 'expected:\n'; cat "$temporary/expected"
    printf 'actual:\n'; cat "$TELLTALE_DISPATCH_RECORD"
    return 1
  fi
}
bash "$root/scripts/dev/cargo-in-nix.sh" check --message-format=json 'two words'
check_record cargo "$TELLTALE_NIX_SCCACHE_BIN" check --message-format=json 'two words'
bash "$root/scripts/dev/cargo-in-nix.sh" clippy --all-targets -- -D warnings
check_record clippy "$TELLTALE_NIX_SCCACHE_BIN" clippy --all-targets -- -D warnings
bash "$root/scripts/dev/cargo-in-nix.sh" fmt --all -- --check
check_record fmt "$TELLTALE_NIX_SCCACHE_BIN" fmt --all -- --check
TELLTALE_NO_SCCACHE=1 bash "$root/scripts/dev/cargo-in-nix.sh" check
check_record cargo unset check
CARGO_INCREMENTAL=1 bash "$root/scripts/dev/cargo-in-nix.sh" check
check_record cargo unset check
RUSTC_WRAPPER=/caller/custom-wrapper TELLTALE_NO_SCCACHE=1 \
  bash "$root/scripts/dev/cargo-in-nix.sh" check
check_record cargo /caller/custom-wrapper check
# A matching suffix or basename cannot identify the selected cache executable.
for caller_wrapper in /caller/custom-sccache /caller/sccache; do
  RUSTC_WRAPPER="$caller_wrapper" TELLTALE_NO_SCCACHE=1 \
    bash "$root/scripts/dev/cargo-in-nix.sh" check
  check_record cargo "$caller_wrapper" check
  RUSTC_WRAPPER="$caller_wrapper" CARGO_INCREMENTAL=1 \
    bash "$root/scripts/dev/cargo-in-nix.sh" check
  check_record cargo "$caller_wrapper" check
done
# Bare names are recognized only when PATH resolves to the selected executable.
for bypass in TELLTALE_NO_SCCACHE CARGO_INCREMENTAL; do
  env "$bypass=1" PATH="$temporary/selected:$PATH" RUSTC_WRAPPER=sccache \
    bash "$root/scripts/dev/cargo-in-nix.sh" check
  check_record cargo unset check
  env "$bypass=1" PATH="$temporary/caller:$PATH" RUSTC_WRAPPER=sccache \
    bash "$root/scripts/dev/cargo-in-nix.sh" check
  check_record cargo sccache check
done
# Native status and both output byte streams survive every route unchanged.
printf 'native stdout\000tail\n' > "$temporary/expected.stdout"
printf 'native stderr\000tail\n' > "$temporary/expected.stderr"
for route in cargo clippy fmt; do
  case "$route" in cargo) argument=check; expected_status=31 ;; clippy) argument=clippy; expected_status=32 ;; fmt) argument=fmt; expected_status=33 ;; esac
  status=0
  TELLTALE_DISPATCH_EXIT="$expected_status" TELLTALE_DISPATCH_STREAMS=1 \
    bash "$root/scripts/dev/cargo-in-nix.sh" "$argument" '' 'two words' \
    > "$temporary/actual.stdout" 2> "$temporary/actual.stderr" || status=$?
  [[ "$status" == "$expected_status" ]]
  check_record "$route" "$TELLTALE_NIX_SCCACHE_BIN" "$argument" '' 'two words'
  cmp "$temporary/expected.stdout" "$temporary/actual.stdout"
  cmp "$temporary/expected.stderr" "$temporary/actual.stderr"
done
# An explicitly empty wrapper is caller configuration, never the shell default.
RUSTC_WRAPPER='' bash "$root/scripts/dev/cargo-in-nix.sh" check
check_record cargo '' check
for bypass in TELLTALE_NO_SCCACHE CARGO_INCREMENTAL; do
  env "$bypass=1" RUSTC_WRAPPER='' bash "$root/scripts/dev/cargo-in-nix.sh" check
  check_record cargo '' check
done
env -u RUSTC_WRAPPER bash "$root/scripts/dev/cargo-in-nix.sh" --version
check_record cargo unset --version
echo 'Cargo/Clippy/fmt dispatch fixtures: OK (21 cases; no compiler/cache-hit claim)'

# Actual shared owner projection survives this adapter; do not duplicate its key logic.
MACOSX_DEPLOYMENT_TARGET=11.0 CARGO_TOOLKIT_APPLE_DEPLOYMENT_V1=poison \
  bash "$root/scripts/dev/cargo-in-nix.sh" check
cp "$TELLTALE_DISPATCH_RECORD.key" "$temporary/key11"
[[ $(cat "$temporary/key11") != poison && $(cat "$temporary/key11") != ABSENT ]]
MACOSX_DEPLOYMENT_TARGET=14.0 bash "$root/scripts/dev/cargo-in-nix.sh" check
key_status=0
cmp -s "$temporary/key11" "$TELLTALE_DISPATCH_RECORD.key" || key_status=$?
[[ $key_status == 1 ]]
MACOSX_DEPLOYMENT_TARGET=11.0 bash "$root/scripts/dev/cargo-in-nix.sh" check
cmp "$temporary/key11" "$TELLTALE_DISPATCH_RECORD.key"
echo 'Shared Toolkit integration: OK (3 cases; actual selected helper, no cache-hit claim)'
