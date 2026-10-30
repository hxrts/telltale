#!/usr/bin/env bash
# Exercise the maintained bootstrap's selected roots, without network or builds.
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
mkdir -p "$scratch/project/scripts/bootstrap" "$scratch/project/lean" "$scratch/bin" "$scratch/caller"
cp "$root/scripts/bootstrap/dependency-checkouts.sh" "$scratch/project/scripts/bootstrap/"
cp "$root/lean/dependency_pins.json" "$scratch/project/lean/"
export SELECTED_PROJECT="$scratch/project" GIT_LOG="$scratch/git.log"
: > "$GIT_LOG"
for name in mathlib iris; do mkdir -p "$SELECTED_PROJECT/lean/.lake/packages/$name/.git"; done
mkdir -p "$SELECTED_PROJECT/lean/.lake/packages/mathlib/.lake/build/lib/lean"
touch "$SELECTED_PROJECT/lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
mkdir -p "$SELECTED_PROJECT/lean/.lake/packages/iris/Iris/.lake/build/lib/lean"
touch "$SELECTED_PROJECT/lean/.lake/packages/iris/Iris/lakefile.toml"
touch "$SELECTED_PROJECT/lean/.lake/packages/iris/Iris/.lake/build/lib/lean/Fixture.olean"
cat > "$scratch/bin/git" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ $# == 4 && $1 == -C && $3 == rev-parse && $4 == HEAD ]] || exit 89
case $2 in
 "$SELECTED_PROJECT/lean/.lake/packages/mathlib") name=mathlib4 ;;
 "$SELECTED_PROJECT/lean/.lake/packages/iris") name=iris-lean ;;
 *) echo 'foreign checkout selected' >&2; exit 88 ;;
esac
printf '%s\n' "$2" >> "$GIT_LOG"
jq -r --arg name "$name" '.dependencies[] | select(.name==$name) | .revision' "$SELECTED_PROJECT/lean/dependency_pins.json"
SH
cat > "$scratch/bin/lake" <<'SH'
#!/usr/bin/env bash
echo 'unexpected Lean build/cache command' >&2
exit 87
SH
chmod +x "$scratch/bin/git" "$scratch/bin/lake"
cd "$scratch/caller"
PATH="$scratch/bin:$PATH" bash "$SELECTED_PROJECT/scripts/bootstrap/dependency-checkouts.sh"
printf '%s\n' "$SELECTED_PROJECT/lean/.lake/packages/mathlib" "$SELECTED_PROJECT/lean/.lake/packages/mathlib" "$SELECTED_PROJECT/lean/.lake/packages/iris" "$SELECTED_PROJECT/lean/.lake/packages/iris" > "$scratch/expected"
cmp "$scratch/expected" "$GIT_LOG"
printf '%s\n' 'Dependency bootstrap: original repository roots and revisions from foreign cwd; no fetch/checkout/build'
