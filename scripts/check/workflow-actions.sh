#!/usr/bin/env bash
# Scan GitHub workflow YAML files for action references and verify each
# remote ref resolves via git ls-remote.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

WORKFLOW_DIR="${WORKFLOW_ACTIONS_DIR:-.github/workflows}"
refs_file="$(mktemp)"
trap 'rm -f "$refs_file"' EXIT

# ── Collect Action References ─────────────────────────────────────────

for workflow in "$WORKFLOW_DIR"/*.yml; do
  [[ -f "$workflow" ]] || continue
  lineno=0
  while IFS= read -r line; do
    lineno=$((lineno + 1))
    # Match lines like:  - uses: owner/repo@ref  or  uses: owner/repo@ref
    if [[ "$line" =~ ^[[:space:]]*(- )?uses:[[:space:]]*([^[:space:]#]+) ]]; then
      spec="${BASH_REMATCH[2]}"
      # Skip local actions and docker references
      [[ "$spec" == ./* || "$spec" == docker://* ]] && continue
      if [[ "$spec" != *@* ]]; then
        echo "${workflow}:${lineno}: malformed action reference without @ref: ${spec}" >&2
        exit 1
      fi
      printf '%s\t%s:%s\n' "$spec" "$workflow" "$lineno" >>"$refs_file"
    fi
  done < "$workflow"
done

# ── Resolve Remote Refs ────────────────────────────────────────────────

# Check whether a tag or branch exists on the remote repository
remote_ref_exists() {
  local repo="$1" ref="$2"
  GIT_TERMINAL_PROMPT=0 git \
    -c credential.helper= \
    -c core.askPass= \
    -c credential.interactive=never \
    ls-remote --exit-code \
    "https://github.com/${repo}.git" \
    "refs/tags/${ref}" "refs/heads/${ref}" \
    >/dev/null 2>&1
}

# Verify every collected action spec resolves to a real tag or branch
errors=()
while IFS= read -r spec; do
  ref="${spec##*@}"
  repo="${spec%@*}"
  if ! remote_ref_exists "$repo" "$ref"; then
    locations="$(
      awk -F '\t' -v target="$spec" '$1 == target { print $2 }' "$refs_file" \
        | paste -sd ', ' -
    )"
    errors+=("${locations}: unresolved GitHub Action reference ${spec}")
  fi
done < <(cut -f1 "$refs_file" | sort -u)

# ── Report ────────────────────────────────────────────────────────────

if [[ ${#errors[@]} -gt 0 ]]; then
  for err in "${errors[@]}"; do
    echo "$err" >&2
  done
  exit 1
fi

resolved_count="$(cut -f1 "$refs_file" | sort -u | wc -l | tr -d ' ')"
echo "workflow action check passed (${resolved_count} remote action reference(s) resolved)"
