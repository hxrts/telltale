#!/usr/bin/env bash
# Focused host controls only: no Lean elaboration or compiler invocation.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd -P)
shared=${LEAN_BUILDER_TEST_ROOT:-$root/../lean-builder}
project_only=0
case ${1:-} in
 --project-only) project_only=1; shift ;;
 '') ;;
 *) echo 'usage: test-lean-host-custody.sh [--project-only]' >&2; exit 2 ;;
esac
[[ $# == 0 ]] || exit 2
python=${PYTHON:-python3}
fail() { echo "FAIL expected custody boundary: $*" >&2; exit 1; }
(( project_only != 0 )) || [[ -x "$shared/scripts/run-lean-build.py" && -x "$shared/target/release/lean-builder" ]] || fail 'selected real shared wrapper/binary unavailable'
scratch=$(mktemp -d)
owner=''; pending_owner=0; release_fd=''
cleanup() {
 status=$?; trap - EXIT
 if (( pending_owner != 0 )); then
   # Resume the original controlled child instead of signaling a possibly reaped
   # numeric PID. Our retained RDWR FIFO endpoint makes this write nonblocking.
   printf 'diagnostic-release\n' >&"$release_fd"
   original_cleanup=0; wait "$owner" || original_cleanup=$?
   printf 'original pending owner native=%s\n' "$original_cleanup" >&2
 fi
 if [[ -n $release_fd ]]; then exec {release_fd}>&-; fi
 if (( status != 0 )); then echo "failed custody fixture retained:$scratch" >&2; exit "$status"; fi
 rm -rf "$scratch"
}
trap cleanup EXIT
mkdir -p "$scratch/project/tools" "$scratch/project/lean" "$scratch/stub"
cp "$root/tools/run_lean_build.py" "$scratch/project/tools/run_lean_build.py"
launcher="$scratch/project/tools/run_lean_build.py"
cd "$scratch/project"
export TELLTALE_LOCAL_LAKE_LOCK="$scratch/project/lean/project.lock"
export LEAN_BUILDER_BUILD_PROTOCOL_VERSION=1 LEAN_NUM_THREADS=1
export LEAN_BUILDER_BUILD_BUDGET_DIR="$scratch/budget" LEAN_BUILDER_LAKE_LOCK_DIR="$scratch/shared-lake"
export LEAN_BUILDER_BUILD_CAPACITY_MIB=11264 LEAN_BUILDER_BUILD_RESERVE_MIB=4096
export LEAN_BUILDER_BUILD_FIXED_OVERHEAD_MIB=1024 LEAN_BUILDER_BUILD_WORKER_WEIGHT_MIB=5120
export LEAN_BUILDER_BUILD_SAFETY_MARGIN_PERCENT=25
unset LEAN_BUILDER_LAKE_LOCK_HELD TELLTALE_LEAN_CUSTODY_MODE
export LEAN_BUILDER_BUILD_WRAPPER="$shared/scripts/run-lean-build.py"
export LEAN_BUILDER_BIN="$shared/target/release/lean-builder"
if (( project_only != 0 )); then
 # Protocol selection only; these stand-ins never attest shared custody.
 protocol_fixture=$(command -v "$python")
 export LEAN_BUILDER_BUILD_WRAPPER="$protocol_fixture" LEAN_BUILDER_BIN="$protocol_fixture"
fi
export PROBE_MARKER="$scratch/probe-marker"
expect() {
 local expected=$1 actual=0; shift
 "$@" > "$scratch/stdout" 2> "$scratch/stderr" || actual=$?
 [[ $actual == "$expected" ]] || { cat "$scratch/stderr" >&2; fail "native status expected=$expected actual=$actual"; }
}
[[ $("$python" "$launcher" --custody-mode --label selected -- true) == shared ]] || fail shared-mode
[[ ! -e $TELLTALE_LOCAL_LAKE_LOCK ]] || fail mode-probe-acquired-writer
[[ $(LEAN_BUILDER_BIN="$scratch/missing" "$python" "$launcher" --custody-mode --label selected -- true) == native ]] || fail degraded-mode
[[ ! -e $TELLTALE_LOCAL_LAKE_LOCK ]] || fail degraded-probe-acquired-writer
expect 78 env LEAN_BUILDER_BIN="$scratch/missing" TELLTALE_LEAN_CUSTODY_MODE=shared "$python" "$launcher" --label changed -- /bin/sh -c 'touch "$PROBE_MARKER"'
grep -Fx 'Lean cancellation configuration changed before original launch' "$scratch/stderr" >/dev/null || fail mode-rejection-cause
[[ ! -e $PROBE_MARKER && ! -e $TELLTALE_LOCAL_LAKE_LOCK ]] || fail rejected-body-entered
expect 41 env LEAN_BUILDER_BIN="$scratch/missing" "$python" "$launcher" --label native -- /bin/sh -c 'printf original-out; printf original-err >&2; exit 41'
[[ $(cat "$scratch/stdout") == original-out ]] || fail native-stdout
grep -F original-err "$scratch/stderr" >/dev/null || fail native-stderr
grep -F 'machine-wide exclusion is unavailable' "$scratch/stderr" >/dev/null || fail announced-degraded
cat > "$scratch/stub/wrapper" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ $1 == --required-child-custody-version && $2 == 1 && $3 == --pass-fd ]] || exit 78
fd=$4; [[ $fd =~ ^[0-9]+$ && -e /dev/fd/$fd ]] || exit 78
# Prove this is the actual kernel writer lock rather than a similarly valued ID.
python3 - "$fd" <<'PY'
import os,sys
held=os.fstat(int(sys.argv[1])); original=os.stat(os.environ['TELLTALE_LOCAL_LAKE_LOCK'])
assert (held.st_dev,held.st_ino)==(original.st_dev,original.st_ino)
PY
while [[ $1 != -- ]]; do shift; done; shift
exec "$@"
SH
chmod +x "$scratch/stub/wrapper"
expect 41 env LEAN_BUILDER_BUILD_WRAPPER="$scratch/stub/wrapper" "$python" "$launcher" --label inherited -- /bin/sh -c 'printf inherited; exit 41'
[[ $(cat "$scratch/stdout") == inherited ]] || fail retained-original-fd
if (( project_only == 0 )); then
expect 41 "$python" "$launcher" --label actual-native -- /bin/sh -c 'printf actual-shared; exit 41'
[[ $(cat "$scratch/stdout") == actual-shared ]] || fail actual-shared-native
# Actual selected shared chain, original child readiness, direct outer TERM,
# native original error41 and physical lock reacquisition after that wait.
mkfifo "$scratch/ready" "$scratch/release"
export READY="$scratch/ready" RELEASE="$scratch/release" ACK="$scratch/ack"
exec {release_fd}<> "$scratch/release"
cat > "$scratch/pending" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
trap 'printf original-terminated > "$ACK"; exit 41' TERM
printf '%s\n' "$$" > "$READY"
IFS= read -r original < "$RELEASE"
printf original-released > "$ACK"
exit 41
SH
chmod +x "$scratch/pending"
"$python" "$launcher" --label actual-term -- "$scratch/pending" > "$scratch/term.stdout" 2> "$scratch/term.stderr" &
owner=$!; pending_owner=1
IFS= read -r original < "$scratch/ready"
[[ $original =~ ^[0-9]+$ ]] || fail actual-child-identity
"$python" - <<'PY'
import fcntl,os
with open(os.environ['TELLTALE_LOCAL_LAKE_LOCK'],'a+') as lock:
 try: fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 except BlockingIOError: pass
 else: raise SystemExit('original writer lease not held while child pending')
PY
kill -TERM "$owner"
status=0; wait "$owner" || status=$?
pending_owner=0
[[ $status == 41 && $(cat "$scratch/ack") == original-terminated ]] || fail original-term-status-and-ack
"$python" - <<'PY'
import fcntl,os
with open(os.environ['TELLTALE_LOCAL_LAKE_LOCK'],'a+') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
PY
fi
mkdir -p "$scratch/project/scripts/lean" "$scratch/bin"
cat > "$scratch/bin/lake" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
python3 - <<'PYTHON'
import fcntl,os
with open(os.environ['TELLTALE_LOCAL_LAKE_LOCK'],'a+') as lock:
 try: fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 except BlockingIOError: pass
 else: raise SystemExit('source-backed command did not inherit original writer lease')
PYTHON
printf '%s\n' "$@"
SH
chmod +x "$scratch/bin/lake"
for operation in runner validator; do
 cp "$root/scripts/lean/protocol-machine-$operation.sh" "$scratch/project/scripts/lean/"
 expect 0 env PATH="$scratch/bin:$PATH" LEAN_BUILDER_BIN="$scratch/missing" \
  TELLTALE_LEAN_CUSTODY_MODE=native bash "$scratch/project/scripts/lean/protocol-machine-$operation.sh" original-argument
 if [[ $operation == runner ]]; then source_name=ProtocolMachineRunner; else source_name=ProtocolMachineValidator; fi
 printf '%s\n' env lean --run "Runtime/Tests/$source_name.lean" original-argument > "$scratch/expected"
 cmp "$scratch/expected" "$scratch/stdout"
 grep -F 'machine-wide exclusion is unavailable' "$scratch/stderr" >/dev/null || fail source-fallback-bypassed-project-launcher
done
# Exercise the INSTALLED seed hook: original command, cwd, native failure and
# writer custody travel through its actual recipe and project launcher.
cp "$root/justfile" "$scratch/project/justfile"
cp "$root/lean/lean-toolchain" "$scratch/project/lean/lean-toolchain"
cat > "$scratch/bin/seed-probe" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ $PWD == "$EXPECTED_SEED_CWD" ]]
[[ $# == 2 && $1 == 'first original' && $2 == 'second-original' ]]
python3 - <<'PYTHON'
import fcntl,os
with open(os.environ['TELLTALE_LOCAL_LAKE_LOCK'],'a+') as lock:
 try: fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 except BlockingIOError: pass
 else: raise SystemExit('installed seed hook did not retain original writer lock')
PYTHON
printf original-seed-hook
exit 41
SH
chmod +x "$scratch/bin/seed-probe"
expect 41 env PATH="$scratch/bin:$PATH" EXPECTED_SEED_CWD="$scratch/project/lean" \
 LEAN_BUILDER_BIN="$scratch/missing" TELLTALE_LEAN_CUSTODY_MODE=native \
 just --justfile "$scratch/project/justfile" _with-lake-lock original-label "seed-probe 'first original' second-original"
[[ $(cat "$scratch/stdout") == original-seed-hook ]] || fail installed-seed-hook-output
if (( project_only != 0 )); then
 printf '%s\n' 'PASS eight project protocol controls; real shared custody unsupported in this mode'
else
printf '%s\n' 'PASS ten host controls: shared/degraded pure probes, exact refusal, native41, actual FD, real shared41, acknowledged real shared TERM41, both source-backed producers'
fi
