#!/usr/bin/env bash
# Real hook shell, fake Cargo only. No compiler/dependency/build invocation.
set -euo pipefail
hook=${1:-$(cd "$(dirname "$0")/.." && pwd)/.githooks/pre-commit}
[[ -f $hook ]]
hook=$(cd "$(dirname "$hook")" && printf '%s/%s\n' "$PWD" "${hook##*/}")
fixture=$(mktemp -d)
trap 'rm -rf "$fixture"' EXIT
mkdir -p "$fixture/bin" "$fixture/repo/crates/fixture/src"
printf 'fn main() {}\n' > "$fixture/repo/crates/fixture/src/lib.rs"
printf '[package]\nname = "fixture"\n' > "$fixture/repo/crates/fixture/Cargo.toml"
cat > "$fixture/bin/git" <<'TOOL'
#!/usr/bin/env bash
case $1 in
 diff) printf 'crates/fixture/src/lib.rs\n' ;;
 check-ignore) exit 1 ;;
 *) exit 91 ;;
esac
TOOL
cat > "$fixture/bin/python" <<'TOOL'
#!/usr/bin/env bash
cat >/dev/null
printf 'fixture\n'
TOOL
cat > "$fixture/bin/cargo" <<'TOOL'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$CALLS"
case $1 in
 run) exit 1 ;; # Existing applicability probe selects ordinary staged-crate path.
 metadata) printf '{"packages":[{"name":"fixture"}]}\n' ;;
 fmt|check)
  printf '%s output first\n%s output last\n' "$1" "$1"
  printf '%s error first\n%s error last\n' "$1" "$1" >&2
  if [[ $1 == fmt ]]; then exit "$FMT_STATUS"; else exit "$CHECK_STATUS"; fi ;;
 *) exit 92 ;;
esac
TOOL
chmod +x "$fixture/bin/"*
export PATH="$fixture/bin:$PATH"
export CALLS="$fixture/calls" FMT_STATUS=0 CHECK_STATUS=0
run_case() {
 local name=$1 expected=$2 status=0
 : > "$CALLS"
 (cd "$fixture/repo" && "$BASH" "$hook") > "$fixture/$name.stdout" 2> "$fixture/$name.stderr" || status=$?
 [[ $status == "$expected" ]] || { printf '%s expected=%s actual=%s\n' "$name" "$expected" "$status" >&2; cat "$fixture/$name.stdout" "$fixture/$name.stderr" >&2; return 1; }
 grep -Fxq 'Checking formatting... fmt output first' "$fixture/$name.stdout"
 grep -Fxq 'fmt output last' "$fixture/$name.stdout"
 printf 'fmt error first\nfmt error last\n' > "$fixture/expected.stderr"
 if (( FMT_STATUS == 0 )); then
  grep -Fxq 'Checking compilation... check output first' "$fixture/$name.stdout"
  grep -Fxq 'check output last' "$fixture/$name.stdout"
  printf 'check error first\ncheck error last\n' >> "$fixture/expected.stderr"
 else
  if grep -q '^check ' "$CALLS"; then echo 'compile ran after failed fmt' >&2; return 1; fi
 fi
 cmp "$fixture/expected.stderr" "$fixture/$name.stderr"
 printf 'PASS %s native_status=%s stdout_lines_preserved stderr_bytes_equal\n' "$name" "$status"
}
FMT_STATUS=37 CHECK_STATUS=0 run_case fmt_failure 37
FMT_STATUS=0 CHECK_STATUS=23 run_case compiler_failure 23
FMT_STATUS=0 CHECK_STATUS=0 run_case success 0
