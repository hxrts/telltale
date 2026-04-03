#!/usr/bin/env bash
# Validate all docs/ link references across the repo: check targets exist,
# detect work/ links, verify SUMMARY.md completeness, check link text matches
# target titles.
set -uo pipefail

# ── Prerequisites ─────────────────────────────────────────────────────
if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

if ! command -v git >/dev/null 2>&1; then
  echo "error: git is required" >&2
  exit 2
fi

if [[ "${1:-}" != "" ]]; then
  echo "usage: $0"
  exit 2
fi

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

if [[ ! -d docs ]]; then
  echo "error: docs directory not found at docs/" >&2
  exit 2
fi

# ── State ─────────────────────────────────────────────────────────────

SCAN_ROOTS=(docs rust lean scripts .github)
ROOT_FILES=(README.md CLAUDE.md)

declare -A SEEN=()
checked=0
missing=()
outside=()
work_links=()
summary_errors=()
title_mismatches=()
missing_scripts=()

# ── Helpers ───────────────────────────────────────────────────────────

# Strip whitespace, quotes, brackets, query strings, and anchors.
sanitize() {
  local t="$1"

  # strip surrounding whitespace and <>\"'
  t="${t#"${t%%[![:space:]]*}"}"
  t="${t%"${t##*[![:space:]]}"}"
  t="${t#[<\"\']*}"
  t="${t%[>\"\']*}"

  if [[ -z "$t" ]]; then
    echo ""
    return
  fi

  # unwrap [docs/...] bracket references
  if [[ "$t" == "["*"]" ]]; then
    local inner="${t:1:${#t}-2}"
    if [[ "$inner" == *docs/* ]]; then
      t="$inner"
    fi
  fi

  # take first space-delimited token (strips title text)
  t="${t%% *}"
  # strip query string
  t="${t%%\?*}"
  # strip anchor
  t="${t%%#*}"

  # strip trailing punctuation .,:;)
  while [[ -n "$t" && "${t: -1}" =~ [.,:';)'] ]]; do
    t="${t%?}"
  done

  echo "$t"
}

# Return true for http/https/mailto/anchor-only links.
is_external() {
  local lower
  lower="$(echo "$1" | tr '[:upper:]' '[:lower:]')"
  case "$lower" in
    http://*|https://*|mailto:*|\#*) return 0 ;;
    *) return 1 ;;
  esac
}

# Resolve a relative link to a normalized path. Prints "STATUS:PATH".
resolve_path() {
  local source="$1" candidate="$2"

  local resolved
  if [[ "$candidate" == /docs/* ]]; then
    resolved="${candidate:1}"
  elif [[ "$candidate" == docs/* ]]; then
    resolved="$candidate"
  else
    local parent
    parent="$(dirname "$source")"
    resolved="$parent/$candidate"
  fi

  # normalise (collapse ../ and ./ segments)
  local IFS='/'
  local -a parts=()
  local seg
  for seg in $resolved; do
    if [[ "$seg" == ".." ]]; then
      if [[ ${#parts[@]} -gt 0 ]]; then
        unset 'parts[${#parts[@]}-1]'
      else
        echo "outside_root:"
        return
      fi
    elif [[ "$seg" != "." && -n "$seg" ]]; then
      parts+=("$seg")
    fi
  done

  local normalised
  normalised="$(printf '%s/' "${parts[@]}")"
  normalised="${normalised%/}"

  if [[ "$normalised" != docs && "$normalised" != docs/* ]]; then
    # Relative paths resolved from non-docs directories (e.g. rust/machine/tests/)
    # may normalise to prefix/docs/file.md — extract the docs/ suffix.
    if [[ "$normalised" == */docs/* ]]; then
      normalised="docs/${normalised#*/docs/}"
    else
      echo "outside_docs:"
      return
    fi
  fi

  echo "ok:$normalised"
}

# Validate that a link target resolves to an existing file.
check_target() {
  local source="$1" line_no="$2" raw_target="$3"

  [[ -z "$raw_target" ]] && return

  local candidate
  candidate="$(sanitize "$raw_target")"
  [[ -z "$candidate" ]] && return
  is_external "$candidate" && return

  # only care about targets mentioning docs/
  if [[ "$candidate" != *docs/* && "$candidate" != /docs/* ]]; then
    return
  fi

  # dedup
  local key="$source:$line_no:$candidate"
  if [[ -n "${SEEN[$key]:-}" ]]; then
    return
  fi
  SEEN[$key]=1

  local resolve_result
  resolve_result="$(resolve_path "$source" "$candidate")"
  local status="${resolve_result%%:*}"
  local rel="${resolve_result#*:}"

  case "$status" in
    outside_root)
      outside+=("$source:$line_no: docs reference escapes repo root: $candidate")
      return
      ;;
    outside_docs)
      outside+=("$source:$line_no: docs reference outside docs/: $candidate")
      return
      ;;
  esac

  # Skip generated/build-output paths that may not exist at check time.
  case "$rel" in
    docs/SUMMARY.md|docs/book|docs/book/*) ;;
    *)
      if [[ ! -e "$rel" ]]; then
        missing+=("$source:$line_no: missing docs target: $candidate -> $rel")
        return
      fi
      ;;
  esac

  checked=$((checked + 1))
}

# Flag links that point into the untracked work/ directory.
check_work_link() {
  local source="$1" line_no="$2" raw_target="$3"

  [[ -z "$raw_target" ]] && return

  local candidate
  candidate="$(sanitize "$raw_target")"
  [[ -z "$candidate" ]] && return
  is_external "$candidate" && return

  if [[ "$candidate" == work/* || "$candidate" == */work/* ]]; then
    work_links+=("$source:$line_no: link to work/ directory: $candidate")
  fi
}

# Read the first H1 from a markdown file (cached).
declare -A TITLE_CACHE=()

get_title() {
  local md_path="$1"
  if [[ -n "${TITLE_CACHE[$md_path]+x}" ]]; then
    echo "${TITLE_CACHE[$md_path]}"
    return
  fi
  local title=""
  if [[ -f "$md_path" ]]; then
    title="$(sed -n 's/^# //p' "$md_path" | head -n 1)"
  fi
  TITLE_CACHE[$md_path]="$title"
  echo "$title"
}

# Verify that link text matches the target file's H1 title.
check_link_title() {
  local source="$1" line_no="$2" link_text="$3" raw_target="$4"

  # only check .md targets
  local target_file="${raw_target%%#*}"
  target_file="${target_file%%\?*}"
  target_file="${target_file#"${target_file%%[![:space:]]*}"}"
  target_file="${target_file%"${target_file##*[![:space:]]}"}"

  [[ "$target_file" == *.md ]] || return
  is_external "$raw_target" && return

  # resolve relative to source
  local resolved
  resolved="$(dirname "$source")/$target_file"
  [[ -f "$resolved" ]] || return

  local title
  title="$(get_title "$resolved")"
  if [[ -n "$title" && "$link_text" != "$title" ]]; then
    title_mismatches+=("$source:$line_no: link text '$link_text' does not match title '$title' for $target_file")
  fi
}

# Extract "LINE_NO:TARGET" for every markdown link in the file.
extract_markdown_targets() {
  rg -n -o '\[[^\]]+\]\(([^)]+)\)' -r '$1' "$1" 2>/dev/null || true
}

# Extract "LINE_NO|TEXT|TARGET" for every markdown link.
extract_markdown_links_with_text() {
  perl -ne 'while (/\[([^\]]+)\]\(([^)]+)\)/g) { print "$.|$1|$2\n"; }' "$1" 2>/dev/null || true
}

# Extract "LINE_NO:TARGET" for bare docs/ path references.
extract_bare_docs_refs() {
  if rg --pcre2-version >/dev/null 2>&1; then
    rg -n -o --pcre2 '(?<![A-Za-z0-9_./-])((?:\.\.?/)*docs/[A-Za-z0-9._/-]+)' -r '$1' "$1" 2>/dev/null || true
  else
    rg -n -o '(?:^|[^A-Za-z0-9_./-])((?:\.\.?/)*docs/[A-Za-z0-9._/-]+)' -r '$1' "$1" 2>/dev/null || true
  fi
}

# Process a single file: check all link targets, work/ refs, and titles.
process_file() {
  local source="$1"
  local is_md=0
  local is_docs_md=0
  [[ "$source" == *.md ]] && is_md=1
  [[ "$source" == docs/*.md ]] && is_docs_md=1

  # ── Markdown link targets ──────────────────────────────────────────

  local line_no target

  while IFS=: read -r line_no target; do
    [[ -z "$line_no" ]] && continue

    # check_target only if the line mentions docs/
    if [[ "$target" == *docs/* || "$target" == */docs/* ]]; then
      check_target "$source" "$line_no" "$target"
    fi

    # work/ link check for .md files
    if [[ $is_md -eq 1 ]]; then
      check_work_link "$source" "$line_no" "$target"
    fi
  done < <(extract_markdown_targets "$source")

  # ── Bare docs/ path references ─────────────────────────────────────

  while IFS=: read -r line_no target; do
    [[ -z "$line_no" ]] && continue
    check_target "$source" "$line_no" "$target"
  done < <(extract_bare_docs_refs "$source")

  # ── Link title matching and script refs (docs/*.md only) ───────────

  if [[ $is_docs_md -eq 1 ]]; then
    local link_text link_target
    while IFS='|' read -r line_no link_text link_target; do
      [[ -z "$line_no" ]] && continue
      check_link_title "$source" "$line_no" "$link_text" "$link_target"
    done < <(extract_markdown_links_with_text "$source")

    # Check script references
    while IFS=: read -r line_no script_name; do
      [[ -z "$script_name" ]] && continue
      if [[ ! -f "scripts/$script_name" ]]; then
        missing_scripts+=("$source:$line_no: missing script reference scripts/$script_name")
      fi
    done < <(rg -n -o '\bscripts/([A-Za-z0-9_.-]+\.sh)\b' -r '$1' "$source" 2>/dev/null || true)
  fi
}

# ── Scan Directories ──────────────────────────────────────────────────

for scan_root in "${SCAN_ROOTS[@]}"; do
  [[ -e "$scan_root" ]] || continue

  while IFS= read -r -d '' raw_file; do
    [[ -z "$raw_file" ]] && continue
    [[ -f "$raw_file" ]] || continue

    # skip work/archive paths
    if [[ "$raw_file" == *work/*archive/* || "$raw_file" == *work/archive/* ]]; then
      continue
    fi

    process_file "$raw_file"
  done < <(rg -l -0 'docs/|\.\.\/' "$scan_root" 2>/dev/null || true)
done

# ── Scan Root Files ───────────────────────────────────────────────────

for rel_name in "${ROOT_FILES[@]}"; do
  [[ -f "$rel_name" ]] || continue
  process_file "$rel_name"
done

# ── SUMMARY.md Completeness ───────────────────────────────────────────

if [[ -f docs/SUMMARY.md ]]; then
  declare -A summary_targets=()
  while IFS=: read -r _ target; do
    [[ -z "$target" ]] && continue
    target="${target%%#*}"
    target="${target%%\?*}"
    target="${target#"${target%%[![:space:]]*}"}"
    target="${target%"${target##*[![:space:]]}"}"
    [[ -n "$target" ]] && summary_targets[$target]=1
  done < <(rg -n -o '\[[^\]]+\]\(([^)]+)\)' -r '$1' docs/SUMMARY.md 2>/dev/null || true)

  for md in docs/*.md; do
    [[ -f "$md" ]] || continue
    local_name="$(basename "$md")"
    [[ "$local_name" == "SUMMARY.md" ]] && continue
    if [[ -z "${summary_targets[$local_name]:-}" ]]; then
      summary_errors+=("docs/SUMMARY.md: missing link to $local_name")
    fi
  done
fi

# ── Report ────────────────────────────────────────────────────────────

has_errors=0

if [[ ${#outside[@]} -gt 0 ]]; then
  has_errors=1
  echo "docs link check failed: references outside docs root"
  for entry in "${outside[@]}"; do
    echo "  - $entry"
  done
fi

if [[ ${#missing[@]} -gt 0 ]]; then
  has_errors=1
  echo "docs link check failed: missing targets"
  for entry in "${missing[@]}"; do
    echo "  - $entry"
  done
fi

if [[ ${#work_links[@]} -gt 0 ]]; then
  has_errors=1
  echo "docs link check failed: links to work/ directory"
  for entry in "${work_links[@]}"; do
    echo "  - $entry"
  done
fi

if [[ ${#summary_errors[@]} -gt 0 ]]; then
  has_errors=1
  echo "docs link check failed: SUMMARY.md incomplete"
  for entry in "${summary_errors[@]}"; do
    echo "  - $entry"
  done
  echo "hint: run \`just summary\` to regenerate SUMMARY.md"
fi

if [[ ${#title_mismatches[@]} -gt 0 ]]; then
  has_errors=1
  echo "docs link check failed: link text does not match target title"
  for entry in "${title_mismatches[@]}"; do
    echo "  - $entry"
  done
fi

if [[ ${#missing_scripts[@]} -gt 0 ]]; then
  has_errors=1
  echo "docs link check failed: missing script references"
  for entry in "${missing_scripts[@]}"; do
    echo "  - $entry"
  done
fi

if [[ $has_errors -ne 0 ]]; then
  total=$(( ${#outside[@]} + ${#missing[@]} + ${#work_links[@]} + ${#summary_errors[@]} + ${#title_mismatches[@]} + ${#missing_scripts[@]} ))
  echo "docs link check found $total issue(s)"
  exit 1
fi

echo "docs link check passed ($checked unique docs reference(s) checked)"
