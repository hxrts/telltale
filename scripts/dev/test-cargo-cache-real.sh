#!/usr/bin/env bash
# Explicit optional native Darwin probe; existing budget owner retains group custody.
set -euo pipefail
[[ $# == 1 && -n ${AURA_BUILD_BUDGET_HELD:-} ]] || { echo 'usage under build-budget: test-cargo-in-nix-real.sh NEW_EVIDENCE' >&2; exit 2; }
[[ $(uname -s) == Darwin ]] || { echo 'native Darwin startup-notify fixture unsupported here' >&2; exit 2; }
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
source "$repo/scripts/dev/cache-real-provider.sh"
[[ $cache_real_cargo == /nix/store/* && $cache_real_sccache == /nix/store/* ]] || exit 2
[[ $($cache_real_sccache --version) == 'sccache 0.11.0' && $(rustc --version) == 'rustc 1.99.1 '* ]] || exit 2
timeout_bin=$(command -v timeout)
[[ $timeout_bin == /nix/store/* && $($timeout_bin --version) == *'GNU coreutils'* ]] || { echo 'selected GNU timeout required' >&2; exit 2; }
# Inspect objects using already-installed native tools; never invoke xcrun or an installer.
developer=$(/usr/bin/env -u DEVELOPER_DIR /usr/bin/xcode-select -p) || exit "$?"
[[ $developer == /* && -d $developer && -x $developer/usr/bin/ar && -x $developer/usr/bin/otool ]] || {
 echo 'installed selected CLT ar/otool required; no installation attempted' >&2; exit 2;
}
ar_bin=$developer/usr/bin/ar
otool_bin=$developer/usr/bin/otool
command -v b3sum >/dev/null || { echo 'selected BLAKE3 tool required' >&2; exit 2; }
for variable in "${!MACOSX_DEPLOYMENT_TARGET_@}"; do
 case $variable in MACOSX_DEPLOYMENT_TARGET_*) echo 'role-suffixed deployment override unsupported in controlled probe' >&2; exit 2;; esac
done
# BEGIN pure object observation contracts
select_probe_artifact() {
 local stream=$1 manifest=$2 package=$3
 jq -es --arg manifest "$manifest" --arg package "$package" '
 if ([.[]|select(.reason=="build-finished")]|length)!=1
   or .[-1].reason!="build-finished" or .[-1].success!=true
 then error("original Cargo stream lacks unique successful terminal record") else
 [.[]|select(.reason=="compiler-artifact" and .package_id==$package
   and .manifest_path==$manifest and .target.name=="cache_probe"
   and .target.kind==["lib"] and .target.crate_types==["lib"]
   and .profile.test==false and .features==[])] as $a
 | if ($a|length)!=1 then error("expected exactly one original probe artifact") else
 $a[0] as $p | [$p.filenames[]|select(endswith(".rlib"))] as $r
 | if ($r|length)!=1 or ($p|has("executable")|not) or $p.executable!=null or $p.fresh!=false
   then error("probe requires one newly requested rlib and explicit null executable")
   else {artifact:$p,rlib:$r[0]} end end end' "$stream"
}
verify_object_minos() {
 local dump=$1 expected=$2
 awk -v expected="$expected" '
 $1=="cmd" { selected=($2=="LC_BUILD_VERSION"); if(selected) builds++ }
 selected && $1=="platform" { platforms++;if($2!="1" && $2!="macos") bad=1 }
 selected && $1=="minos" { versions++;if($2!=expected) bad=1 }
 END {if(!builds || platforms!=builds || versions!=builds || bad) exit 1;
      printf "verified_build_versions=%d minos=%s\n",builds,expected}' "$dump"
}
archive_member_kind() {
 case $1 in
  '__.SYMDEF'|'__.SYMDEF SORTED') printf 'index\n';;
  lib.rmeta) printf 'metadata\n';;
  lib.rmeta-link) printf 'object\n';;
  *) [[ $1 =~ ^[A-Za-z0-9_][A-Za-z0-9_.-]*\.o$ ]] || return 1
     printf 'object\n';;
 esac
}
# END pure object observation contracts
mkdir "$1"
evidence=$(cd "$1" && pwd -P)
private=$(mktemp -d /tmp/sc-real.XXXXXX)
chmod 700 "$private"
server='' notifier=''
cleanup() {
 local primary=$? native=0 failure=0
 trap - EXIT
 for child in "$server" "$notifier"; do
  [[ -n $child ]] || continue
  if kill -0 "$child" 2>/dev/null; then kill -TERM "$child" || { native=$?; echo "independent TERM failure: $native" >&2 || :; (( failure != 0 )) || failure=$native; }; fi
  native=0
  wait "$child" || native=$?
  # Select an already-observed child cause before fallible evidence publication.
  if (( native != 0 && native != 143 )); then (( failure != 0 )) || failure=$native; fi
  printf 'original_child=%s actual_wait_status=%s primary=%s\n' "$child" "$native" "$primary" >> "$evidence/child-waits.txt" || { local publication=$?; printf 'independent child-wait publication failure: %s\n' "$publication" >&2 || :; (( failure != 0 )) || failure=$publication; }
  # TERM143 is expected settlement after requesting shutdown, not success inferred from stop reply.
 done
 if (( primary != 0 || failure != 0 )); then
  printf 'failed_private_artifacts=%s\n' "$private" >> "$evidence/retained-private.txt" || { native=$?; printf 'independent retention publication failure: %s\n' "$native" >&2 || :; (( failure != 0 )) || failure=$native; }
  echo "failed private fixture retained: $private" >&2 || :
 else
  rm -rf -- "$private" || { native=$?; echo "independent private cleanup failure: $native" >&2 || :; (( failure != 0 )) || failure=$native; }
 fi
 (( primary != 0 )) || primary=$failure
 exit "$primary"
}
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
# Deliberately isolate config; never operate on a user's cache or daemon.
for variable in "${!SCCACHE_@}" "${!CARGO_PROFILE_@}" "${!CARGO_TARGET_@}" "${!CARGO_BUILD_@}"; do unset "$variable"; done
unset CARGO_ENCODED_RUSTFLAGS RUSTC_WORKSPACE_WRAPPER "$cache_real_optout_key"
export SCCACHE_DIR="$private/cache" SCCACHE_SERVER_UDS="$private/server" SCCACHE_NO_DAEMON=1 SCCACHE_CACHE_SIZE=64M
export CARGO_HOME="$private/cargo-home" CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS=1 RUSTFLAGS=''
export RUSTC_WRAPPER="$cache_real_sccache" RUSTC
RUSTC=$(command -v rustc)
[[ $RUSTC == /nix/store/* ]] || exit 2
# Refuse ancestor Cargo configuration rather than permit target/wrapper redirection.
physical=$(cd "$private" && pwd -P)
ancestor=$physical
while :; do
 [[ ! -e $ancestor/.cargo/config && ! -e $ancestor/.cargo/config.toml ]] || { echo 'ancestor Cargo config unsupported' >&2; exit 2; }
 [[ $ancestor != / ]] || break
 ancestor=${ancestor%/*}; [[ -n $ancestor ]] || ancestor=/
done
mkdir -p "$private/project/src"
printf '[package]\nname="cache_probe"\nversion="0.0.0"\nedition="2021"\n' > "$private/project/Cargo.toml"
printf 'pub fn answer() -> u32 { 42 }\n' > "$private/project/src/lib.rs"
cp "$private/project/src/lib.rs" "$evidence/probe-source.rs"
cp "$private/project/Cargo.toml" "$evidence/probe-manifest.toml"
jq -nc --arg cargo "$cache_real_cargo" --arg rustc "$RUSTC" --arg cache "$cache_real_sccache" --arg developer "${DEVELOPER_DIR-}" --arg sdk "${SDKROOT-}" --arg cc "${CC-}" '{cargo:$cargo,rustc:$rustc,sccache:$cache,original_developer_dir:$developer,original_sdkroot:$sdk,original_cc:$cc,incremental:0,cache_scope:"private",startup:"0.11 internal foreground; native Darwin nc notification"}' > "$evidence/providers.json"
printf '%s\n' "$developer" "$ar_bin" "$otool_bin" > "$evidence/native-object-tools.txt"
b3sum "$ar_bin" "$otool_bin" > "$evidence/native-object-tools.b3"
"$cache_real_cargo" generate-lockfile --offline --manifest-path "$private/project/Cargo.toml"
env RUSTC_WRAPPER= "$cache_real_cargo" metadata --offline --no-deps --format-version 1 --manifest-path "$private/project/Cargo.toml" > "$evidence/probe-metadata.json"
probe_package=$(jq -er --arg manifest "$private/project/Cargo.toml" '
 [.packages[]|select(.manifest_path==$manifest and .name=="cache_probe" and .version=="0.0.0")]
 | if length==1 then .[0].id else error("original probe package is not unique") end' "$evidence/probe-metadata.json")
# Native nc receives the real sccache startup-notify stream; no Python helper.
"$timeout_bin" --foreground 20s /usr/bin/nc -l -U "$private/notify" < /dev/null > "$evidence/startup-notification.bin" 2> "$evidence/notify.stderr" &
notifier=$!
start=$SECONDS
while [[ ! -S $private/notify ]]; do
 kill -0 "$notifier" || { wait "$notifier"; exit 1; }
 (( SECONDS - start < 20 )) || { echo 'notification listener readiness failure' >&2; exit 1; }
 sleep 0.02
done
SCCACHE_START_SERVER=1 SCCACHE_STARTUP_NOTIFY="$private/notify" "$cache_real_sccache" > "$evidence/server.log" 2>&1 &
server=$!
# Receiver terminates on actual original sender EOF. No timeout widening or stop-reply inference.
notification_status=0
wait "$notifier" || notification_status=$?
printf 'notification_original_child=%s actual_wait_status=%s\n' "$notifier" "$notification_status" >> "$evidence/child-waits.txt"
notifier=''
(( notification_status == 0 )) || exit "$notification_status"
[[ -s $evidence/startup-notification.bin && -S $private/server ]] && kill -0 "$server"
stats() {
 kill -0 "$server" || { echo 'original foreground server exited' >&2; return 1; }
 "$cache_real_sccache" --show-stats --stats-format json > "$evidence/$1.json"
 jq -e '.stats.compile_requests | type=="number"' "$evidence/$1.json" > /dev/null
}
compile() {
 local label=$1 expected=$2 actual=0; shift 2
 rm -rf -- "$private/project/target"
 (cd "$private/project"; env "$@" bash "$repo/scripts/dev/cargo-in-nix.sh" build --offline --locked --manifest-path "$private/project/Cargo.toml" --message-format=json) > "$evidence/$label.stdout" 2> "$evidence/$label.stderr" || actual=$?
 [[ $actual == "$expected" ]] || { printf '%s native=%s expected=%s\n' "$label" "$actual" "$expected" >&2; return 1; }
 kill -0 "$server" || { echo 'original server failed; fallback cannot establish acceptance' >&2; return 1; }
}
observe_probe() {
 local label=$1 expected=$2 rlib member kind objects=0
 select_probe_artifact "$evidence/$label.stdout" "$private/project/Cargo.toml" "$probe_package" > "$evidence/$label-artifact.json"
 rlib=$(jq -er '.rlib' "$evidence/$label-artifact.json")
 [[ $rlib == "$private/project/target/debug/"*.rlib && -f $rlib && ! -L $rlib ]] || return 1
 [[ "$(cd "$(dirname "$rlib")" && pwd -P)/" == "$physical/project/target/debug/"* ]] || return 1
 cp -p "$rlib" "$evidence/$label.rlib"
 cmp "$rlib" "$evidence/$label.rlib"
 b3sum "$rlib" "$evidence/$label.rlib" > "$evidence/$label-rlib.b3"
 env DEVELOPER_DIR="$developer" "$ar_bin" -t "$evidence/$label.rlib" > "$evidence/$label-members.txt"
 jq -Rse 'split("\n") as $lines | $lines[-1]=="" and
   ($lines[:-1]|length)==($lines[:-1]|unique|length)' "$evidence/$label-members.txt" >/dev/null
 mkdir "$evidence/$label-objects"
 while IFS= read -r member; do
  kind=$(archive_member_kind "$member") || { echo "unsupported probe archive member: $member" >&2; return 1; }
  [[ $kind == object ]] || continue
  (cd "$evidence/$label-objects"; env DEVELOPER_DIR="$developer" "$ar_bin" -x "$evidence/$label.rlib" "$member")
  env DEVELOPER_DIR="$developer" "$otool_bin" -l "$evidence/$label-objects/$member" > "$evidence/$label-objects/$member.load-commands"
  verify_object_minos "$evidence/$label-objects/$member.load-commands" "$expected" || {
   echo "original $label object $member lacks expected LC_BUILD_VERSION minos $expected" >&2; return 1;
  }
  objects=$((objects+1))
 done < "$evidence/$label-members.txt"
 (( objects > 0 )) || { echo 'probe archive has no observed Mach-O objects' >&2; return 1; }
 printf 'original_artifact=%s objects=%s expected_minos=%s\n' "$rlib" "$objects" "$expected" > "$evidence/$label-object-result.txt"
}
stats before
compile cold 0 MACOSX_DEPLOYMENT_TARGET=11.0
stats cold-stats
observe_probe cold 11.0
compile repeat 0 MACOSX_DEPLOYMENT_TARGET=11.0
stats repeat-stats
observe_probe repeat 11.0
cmp "$evidence/cold.rlib" "$evidence/repeat.rlib"
jq -en --slurpfile before "$evidence/before.json" --slurpfile cold "$evidence/cold-stats.json" --slurpfile repeat "$evidence/repeat-stats.json" '
 def count: [..|numbers]|add // 0;
 ($cold[0].stats.cache_misses|count)>($before[0].stats.cache_misses|count)
 and ($repeat[0].stats.cache_hits|count)>($cold[0].stats.cache_hits|count)' >/dev/null
compile deployment14 0 MACOSX_DEPLOYMENT_TARGET=14.0
stats deployment14-stats
observe_probe deployment14 14.0
compile return11 0 MACOSX_DEPLOYMENT_TARGET=11.0
stats return11-stats
observe_probe return11 11.0
cmp "$evidence/cold.rlib" "$evidence/return11.rlib"
jq -en --slurpfile prior "$evidence/repeat-stats.json" --slurpfile changed "$evidence/deployment14-stats.json" --slurpfile returned "$evidence/return11-stats.json" '
 def rust($s;$kind): ($s.stats[$kind].counts.Rust // 0) as $n
   | if ($n|type)!="number" or $n<0 or ($n|floor)!=$n then error("invalid native Rust cache count") else $n end;
 rust($changed[0];"cache_misses")==rust($prior[0];"cache_misses")+1
 and rust($changed[0];"cache_hits")==rust($prior[0];"cache_hits")
 and rust($returned[0];"cache_hits")==rust($changed[0];"cache_hits")+1
 and rust($returned[0];"cache_misses")==rust($changed[0];"cache_misses")' >/dev/null
for variant in incremental optout; do
 if [[ $variant == incremental ]]; then compile "$variant" 0 CARGO_INCREMENTAL=1; else compile "$variant" 0 "$cache_real_optout_key=1"; fi
 stats "$variant-stats"
 jq -en --slurpfile prior "$evidence/return11-stats.json" --slurpfile current "$evidence/$variant-stats.json" '$prior[0].stats.compile_requests==$current[0].stats.compile_requests' >/dev/null
done
printf '#!/bin/sh\nprintf "custom\\n" >> "$CUSTOM_CAPTURE"\nexec "$@"\n' > "$private/custom-wrapper"
chmod +x "$private/custom-wrapper"
compile custom 0 "$cache_real_optout_key=1" RUSTC_WRAPPER="$private/custom-wrapper" CUSTOM_CAPTURE="$private/custom-capture"
[[ -s $private/custom-capture ]]
stats custom-stats
jq -en --slurpfile prior "$evidence/return11-stats.json" --slurpfile current "$evidence/custom-stats.json" '$prior[0].stats.compile_requests==$current[0].stats.compile_requests' >/dev/null
printf 'deliberately invalid Rust\n' > "$private/project/src/lib.rs"
compile native-rust-error 101 "$cache_real_optout_key=1"
printf '#!/bin/sh\nexit 37\n' > "$private/native37"
chmod +x "$private/native37"
native=0
env "$cache_real_cargo_key=$private/native37" bash "$repo/scripts/dev/cargo-in-nix.sh" build || native=$?
[[ $native == 37 ]]
printf '%s\n' 'PASS actual private cold miss/repeat hit; deployment11/14/11 Rust miss/hit with every Mach-O minos checked; incremental/optout/custom bypass; actual Rust101; dispatcher37' > "$evidence/result.txt"
