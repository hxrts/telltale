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
# Controlled canonical Git/common-dir provider for the copied fixture project.
mkdir -p "$scratch/project/.git" "$scratch/cache"
cat > "$scratch/stub/git" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ $# == 4 && $1 == -C && $3 == rev-parse && $4 == --git-common-dir ]] || exit 89
if [[ ${ORIGINAL_GIT_STATUS:-0} != 0 ]]; then echo original-git-preflight-error >&2; exit "$ORIGINAL_GIT_STATUS"; fi
printf '.git\n'
SH
chmod +x "$scratch/stub/git"
export PATH="$scratch/stub:$PATH" LAKE_CACHE_DIR="$scratch/cache"
export TELLTALE_LEAN_SOURCE_IDENTITY=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
command -v ps >/dev/null || fail 'selected v2 measurement provider ps unavailable'
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
# Execute the maintained .envrc with controlled direnv hooks. It selects3
# threads. Protocol1 must preserve that original development/caller contract.
use() { [[ $1 == flake ]]; }
watch_file() { [[ $1 == lean/lean-toolchain ]]; }
source "$root/.envrc"
[[ $LEAN_NUM_THREADS == 3 ]] || fail actual-envrc-thread-setting
cat > "$scratch/stub/v1-wrapper" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ $1 == --required-child-custody-version && $2 == 1 && $3 == --pass-fd ]]
[[ $5 == --label && $7 == --desired-count && $8 == "$EXPECTED_V1_DESIRED" && $9 == --floor && ${10} == 2 && ${11} == -- ]]
[[ $# == 14 ]]
while [[ $1 != -- ]]; do shift; done; shift
exec "$@"
SH
chmod +x "$scratch/stub/v1-wrapper"
expect 0 env EXPECTED_V1_DESIRED=3 LEAN_BUILDER_BUILD_DESIRED_COUNT=3 LEAN_BUILDER_BUILD_FLOOR=2 LEAN_BUILDER_BUILD_WRAPPER="$scratch/stub/v1-wrapper" "$python" "$launcher" --label original-v1 -- /bin/sh -c 'printf "%s" "$LEAN_NUM_THREADS"'
[[ $(cat "$scratch/stdout") == 3 ]] || fail original-v1-envrc-worker
expect 0 env EXPECTED_V1_DESIRED=4 LEAN_NUM_THREADS=4 LEAN_BUILDER_BUILD_DESIRED_COUNT=4 LEAN_BUILDER_BUILD_FLOOR=2 LEAN_BUILDER_BUILD_WRAPPER="$scratch/stub/v1-wrapper" "$python" "$launcher" --label override-v1 -- /bin/sh -c 'printf "%s" "$LEAN_NUM_THREADS"'
[[ $(cat "$scratch/stdout") == 4 ]] || fail original-v1-caller-override
expect 0 env LEAN_BUILDER_BIN="$scratch/missing" "$python" "$launcher" --label original-v1-native -- /bin/sh -c 'printf "%s" "$LEAN_NUM_THREADS"'
[[ $(cat "$scratch/stdout") == 3 ]] || fail original-v1-native-worker
if (( project_only == 0 )); then
 expect 41 env LEAN_BUILDER_BUILD_DESIRED_COUNT=3 LEAN_BUILDER_BUILD_FLOOR=2 "$python" "$launcher" --label original-v1-real -- /bin/sh -c 'printf "original-v1-granted:%s" "$LEAN_NUM_THREADS"; exit 41'
 [[ $(cat "$scratch/stdout") == original-v1-granted:2 ]] || fail actual-v1-granted-worker
fi
# Canonical one-worker8168 campaign explicitly selects budget protocol2.
export LEAN_BUILDER_BUILD_PROTOCOL_VERSION=2 LEAN_NUM_THREADS=1
cat > "$scratch/stub/wrapper" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ $1 == --required-child-custody-version && $2 == 1 && $3 == --pass-fd ]] || exit 78
fd=$4; [[ $fd =~ ^[0-9]+$ && -e /dev/fd/$fd ]] || exit 78
# Prove BOTH actual original descriptors and the existing v2 request schema.
python3 - "$@" <<'PY'
import os,sys,json,hashlib
args=sys.argv[1:]; fd=int(args[args.index('--pass-fd')+1])
held=os.fstat(fd); original=os.stat(os.environ['TELLTALE_LOCAL_LAKE_LOCK'])
assert (held.st_dev,held.st_ino)==(original.st_dev,original.st_ino)
assert args[args.index('--protocol-version')+1]=='2'
path=args[args.index('--resource-request')+1]; request_fd=int(path.rsplit('/',1)[1])
assert request_fd!=fd and args.count('--pass-fd')==2
assert str(request_fd) in [args[i+1] for i,a in enumerate(args) if a=='--pass-fd']
assert os.fstat(request_fd).st_nlink==0
with open(path) as source: request=json.load(source)
assert request['schema']=='lean-builder-resource-request-v2'
assert request['requested_mib']==request['hard_cap_mib']==8168
assert request['source_identity']==os.environ['TELLTALE_LEAN_SOURCE_IDENTITY']
worktree=os.path.realpath(os.getcwd()); scoped=lambda p:hashlib.sha256(os.path.realpath(p).encode()).hexdigest()[:16]
assert request['worktree']==worktree
assert request['reads']==sorted([f"worktree:{scoped(worktree)}:source",f"shared-cache:{scoped(os.environ['LAKE_CACHE_DIR'])}:maintenance"])
assert request['writes']==sorted([f"worktree:{scoped(worktree)}:lake-build",f"worktree:{scoped(worktree)}:generated-metadata",f"worktree:{scoped(worktree)}:audit-results",f"repository:{scoped(worktree+'/.git')}:legacy-global-writer"])
PY
while [[ $1 != -- ]]; do shift; done; shift
exec "$@"
SH
chmod +x "$scratch/stub/wrapper"
expect 41 env LEAN_BUILDER_BUILD_WRAPPER="$scratch/stub/wrapper" "$python" "$launcher" --label inherited -- /bin/sh -c 'printf inherited; exit 41'
[[ $(cat "$scratch/stdout") == inherited ]] || fail retained-original-fd
# Negative controls start from the admitted positive profile above.
for variable in LEAN_NUM_THREADS LEAN_BUILDER_BUILD_DESIRED_COUNT LEAN_BUILDER_BUILD_FLOOR; do
 expect 78 env "$variable=2" "$python" "$launcher" --label rejected-worker -- /bin/sh -c 'touch "$PROBE_MARKER"'
 grep -Fx "original one-worker profile required: $variable" "$scratch/stderr" >/dev/null || fail original-worker-cause
 [[ ! -e $PROBE_MARKER ]] || fail rejected-worker-body
 done
expect 78 env LEAN_BUILDER_BIN="$scratch/missing" LEAN_BUILDER_BUILD_CAPACITY_MIB=8167 "$python" "$launcher" --label insufficient -- /bin/sh -c 'touch "$PROBE_MARKER"'
grep -F 'original degraded resource profile does not fit' "$scratch/stderr" >/dev/null || fail degraded-capacity-cause
[[ ! -e $PROBE_MARKER ]] || fail insufficient-body
expect 78 env LEAN_BUILDER_BUILD_PROTOCOL_VERSION=3 "$python" "$launcher" --label incompatible -- /bin/sh -c 'touch "$PROBE_MARKER"'
grep -Fx 'incompatible build-budget protocol 3' "$scratch/stderr" >/dev/null || fail incompatible-cause
[[ ! -e $PROBE_MARKER ]] || fail unsupported-body
cat > "$scratch/stub/refusal" <<'SH'
#!/usr/bin/env bash
printf 'original-v2-refusal\n' >&2
exit 43
SH
chmod +x "$scratch/stub/refusal"
expect 43 env LEAN_BUILDER_BUILD_WRAPPER="$scratch/stub/refusal" "$python" "$launcher" --label refused -- /bin/sh -c 'touch "$PROBE_MARKER"'
grep -Fx original-v2-refusal "$scratch/stderr" >/dev/null || fail native-v2-refusal-cause
[[ ! -e $PROBE_MARKER ]] || fail refusal-retried-native
expect 78 env LEAN_BUILDER_BIN="$scratch/missing" LEAN_BUILDER_BUILD_RESERVE_MIB=4095 "$python" "$launcher" --label insufficient-reserve -- /bin/sh -c 'touch "$PROBE_MARKER"'
grep -F 'original degraded resource profile does not fit' "$scratch/stderr" >/dev/null || fail original-reserve-cause
[[ ! -e $PROBE_MARKER ]] || fail reserve-body
expect 78 env -u LEAN_BUILDER_BUILD_CAPACITY_MIB LEAN_BUILDER_BIN="$scratch/missing" "$python" "$launcher" --label unknown-capacity -- /bin/sh -c 'touch "$PROBE_MARKER"'
grep -Fx 'original degraded resource capacity is unknown' "$scratch/stderr" >/dev/null || fail unknown-capacity-cause
[[ ! -e $PROBE_MARKER ]] || fail unknown-capacity-body
expect 78 env TELLTALE_LEAN_SOURCE_IDENTITY=invalid "$python" "$launcher" --label invalid-source -- /bin/sh -c 'touch "$PROBE_MARKER"'
grep -Fx 'source identity must be the original admission fingerprint' "$scratch/stderr" >/dev/null || fail source-identity-cause
[[ ! -e $PROBE_MARKER ]] || fail source-identity-body
mkdir "$scratch/no-ps"
selected_python=$(command -v "$python")
expect 78 env PATH="$scratch/no-ps" "$selected_python" "$launcher" --label missing-ps -- /bin/sh -c 'touch "$PROBE_MARKER"'
grep -Fx 'original v2 process measurement provider ps unavailable' "$scratch/stderr" >/dev/null || fail missing-ps-cause
[[ ! -e $PROBE_MARKER ]] || fail measurement-body
expect 41 env ORIGINAL_GIT_STATUS=41 "$python" "$launcher" --label original-git-error -- /bin/sh -c 'touch "$PROBE_MARKER"'
grep -Fx original-git-preflight-error "$scratch/stderr" >/dev/null || fail original-git-cause
[[ ! -e $PROBE_MARKER ]] || fail git-error-body
if (( project_only == 0 )); then
expect 41 "$python" "$launcher" --label actual-native -- /bin/sh -c 'printf actual-shared; exit 41'
[[ $(cat "$scratch/stdout") == actual-shared ]] || fail actual-shared-native
# The v2 request does not rewrite or bypass the original v1 compatibility config.
expect 1 env LEAN_BUILDER_BUILD_WORKER_WEIGHT_MIB=7144 "$python" "$launcher" --label incompatible-ledger -- /bin/sh -c 'touch "$PROBE_MARKER"'
grep -F 'coordination configuration mismatch' "$scratch/stdout" >/dev/null || fail original-ledger-refusal-cause
grep -F '"worker_weight_mib":5120' "$scratch/stdout" >/dev/null || fail original-ledger-config
grep -F '"worker_weight_mib":7144' "$scratch/stdout" >/dev/null || fail original-request-config
[[ ! -e $PROBE_MARKER ]] || fail ledger-refusal-retried-native
# Actual selected shared chain, original child readiness, direct outer TERM,
# native original error41 and physical lock reacquisition after that wait.
mkfifo "$scratch/ready" "$scratch/release"
export READY="$scratch/ready" RELEASE="$scratch/release" ACK="$scratch/ack"
exec {release_fd}<> "$scratch/release"
cat > "$scratch/pending" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
trap 'printf "original-terminated:%s" "$$" > "$ACK"; exit 41' TERM
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
# Select the actual admitted operation and retain its original lease object.
lease_path=$("$python" - <<'PY'
import json,os,pathlib
root=pathlib.Path(os.environ['LEAN_BUILDER_BUILD_BUDGET_DIR'])
rows=[json.loads(p.read_text()) for p in root.glob('holder-*.json')]
rows=[r for r in rows if r['label']=='actual-term']
assert len(rows)==1
row=rows[0]
assert row['protocol_version']==2 and row['granted_count']==1
assert row['admitted_mib']==row['hard_cap_mib']==8168
assert row['worktree']==str(pathlib.Path.cwd().resolve())
lease=row['lease']; assert pathlib.Path(lease).name==lease
print(root/lease)
PY
)
exec {lease_fd}< "$lease_path"
"$python" - "$lease_fd" <<'PY'
import fcntl,sys
try: fcntl.flock(int(sys.argv[1]),fcntl.LOCK_EX|fcntl.LOCK_NB)
except BlockingIOError: pass
else: raise SystemExit('original operation memory lease is not held')
PY
kill -TERM "$owner"
status=0; wait "$owner" || status=$?
pending_owner=0
# v2 deliberately classifies outer cancellation as143. Retain BOTH outcomes.
[[ $status == 143 && $(cat "$scratch/ack") == "original-terminated:$original" ]] || fail original-term-status-and-ack
"$python" - "$scratch/project/.lake/build/lean-builder/timings.jsonl" <<'PY'
import json,sys
rows=[json.loads(line) for line in open(sys.argv[1])]
rows=[r for r in rows if r['label']=='actual-term']
assert len(rows)==1 and rows[0]['format']=='lean-builder-lake-timings-v1'
assert rows[0]['status']==41
PY
[[ $(grep -Fxc '  cleanup_complete: True' "$scratch/term.stderr") == 1 ]] || fail actual-cleanup-outcome
[[ $(grep -Fxc '  exit_status: 143' "$scratch/term.stderr") == 1 ]] || fail actual-cancellation-outcome
"$python" - "$lease_fd" <<'PY'
import fcntl,sys
fcntl.flock(int(sys.argv[1]),fcntl.LOCK_EX|fcntl.LOCK_NB)
PY
exec {lease_fd}>&-
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
 printf '%s\n' 'PASS twenty-two project protocol controls; real shared custody unsupported in this mode'
else
printf '%s\n' 'PASS twenty-six host controls: shared/degraded pure probes, exact refusal, native41, actual FD, real shared41, outer TERM143 with retained original41 and acknowledged settlement, both source-backed producers'
fi
