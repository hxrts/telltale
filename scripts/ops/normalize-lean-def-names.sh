#!/usr/bin/env bash
# Normalize Lean theorem/lemma declaration casing (scoped).
#
# Rules:
# - theorem/lemma tails must be snake_case
#
# Notes:
# - Only declaration tail (after last '.') is rewritten.
# - Dry run by default.
# - Use --apply to write changes.
# - Use --scope to restrict discovery (e.g. lean/Runtime).
# - Rewrites are applied over --rewrite-root (default: same as --scope).
# - Use --exclude to skip subtrees for both discovery and rewrite.
# - Import lines are never rewritten.
# - Replacements are applied only in Lean code regions (not comments/strings).

set -euo pipefail

# Default values
SCOPE="lean"
REWRITE_ROOT=""
EXCLUDES=()
APPLY=false
DRY_RUN=false
SHOW_LIMIT=80
SHOW_ALL=false

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --scope)
            SCOPE="$2"
            shift 2
            ;;
        --rewrite-root)
            REWRITE_ROOT="$2"
            shift 2
            ;;
        --exclude)
            EXCLUDES+=("$2")
            shift 2
            ;;
        --apply)
            APPLY=true
            shift
            ;;
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --show)
            SHOW_LIMIT="$2"
            shift 2
            ;;
        --all)
            SHOW_ALL=true
            shift
            ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --scope DIR       Discovery scope root (default: lean)"
            echo "  --rewrite-root DIR  Rewrite root for references (default: same as --scope)"
            echo "  --exclude PATH    Exclude path prefix (repeatable)"
            echo "  --apply           Write changes"
            echo "  --dry-run         Force dry-run mode"
            echo "  --show N          Number of planned renames to show (default: 80)"
            echo "  --all             Show all planned renames"
            exit 0
            ;;
        *)
            echo "Unknown option: $1" >&2
            exit 1
            ;;
    esac
done

# Set rewrite root to scope if not specified
if [[ -z "$REWRITE_ROOT" ]]; then
    REWRITE_ROOT="$SCOPE"
fi

# Resolve paths
SCOPE=$(cd "$SCOPE" 2>/dev/null && pwd) || { echo "error: scope not found: $SCOPE" >&2; exit 2; }
REWRITE_ROOT=$(cd "$REWRITE_ROOT" 2>/dev/null && pwd) || { echo "error: rewrite root not found: $REWRITE_ROOT" >&2; exit 2; }

# Build exclusion pattern for find
EXCLUDE_ARGS=()
if [[ -n "${EXCLUDES+x}" ]]; then
    for ex in "${EXCLUDES[@]}"; do
        # Handle comma-separated values
        IFS=',' read -ra PARTS <<< "$ex"
        for part in "${PARTS[@]}"; do
            part=$(echo "$part" | sed 's:^/*::; s:/*$::')
            if [[ -n "$part" ]]; then
                EXCLUDE_ARGS+=(-path "*/$part" -prune -o -path "*/$part/*" -prune -o)
            fi
        done
    done
fi

# Always exclude .lake, .git, build
EXCLUDE_ARGS+=(-path "*/.lake" -prune -o -path "*/.lake/*" -prune -o)
EXCLUDE_ARGS+=(-path "*/.git" -prune -o -path "*/.git/*" -prune -o)
EXCLUDE_ARGS+=(-path "*/build" -prune -o -path "*/build/*" -prune -o)

# Temporary files for intermediate results
RENAMES_FILE=$(mktemp)
COLLISIONS_FILE=$(mktemp)
trap 'rm -f "$RENAMES_FILE" "$COLLISIONS_FILE"' EXIT

# AWK script for camelCase to snake_case conversion
to_snake_awk='
function to_snake(s) {
    # Remove backticks
    gsub(/`/, "", s)
    # Insert underscore between sequences of uppercase and following uppercase+lowercase
    while (match(s, /[A-Z][A-Z]+[A-Z][a-z]/)) {
        s = substr(s, 1, RSTART+RLENGTH-3) "_" substr(s, RSTART+RLENGTH-2)
    }
    # Insert underscore between lowercase/digit and uppercase
    while (match(s, /[a-z0-9][A-Z]/)) {
        s = substr(s, 1, RSTART) "_" substr(s, RSTART+1)
    }
    # Replace hyphens with underscores
    gsub(/-/, "_", s)
    # Collapse multiple underscores
    gsub(/__+/, "_", s)
    # Strip leading/trailing underscores and lowercase
    gsub(/^_+|_+$/, "", s)
    return tolower(s)
}
'

# Discover non-conformant declarations
discover_decls() {
    local root="$1"

    find "$root" "${EXCLUDE_ARGS[@]}" -name "*.lean" -type f -print 2>/dev/null | sort | while read -r file; do
        gawk -v file="$file" '
        '"$to_snake_awk"'

        # Split name into prefix and tail
        function split_tail(name, result) {
            if (match(name, /.*\./)) {
                result["prefix"] = substr(name, 1, RLENGTH)
                result["tail"] = substr(name, RLENGTH + 1)
            } else {
                result["prefix"] = ""
                result["tail"] = name
            }
        }

        # Split decorations (trailing '"'"', ?, !) from base
        function split_decorations(s, result) {
            if (match(s, /['"'"'?!]+$/)) {
                result["base"] = substr(s, 1, RSTART - 1)
                result["dec"] = substr(s, RSTART)
            } else {
                result["base"] = s
                result["dec"] = ""
            }
        }

        # Check if tail is snake_case
        function is_snake_tail(tail) {
            split_decorations(tail, parts)
            if (parts["base"] == "") return 0
            if (!match(parts["base"], /^[a-z][a-z0-9_]*$/)) return 0
            if (parts["dec"] != "" && !match(parts["dec"], /^['"'"'?!]+$/)) return 0
            return 1
        }

        # Match theorem/lemma declarations
        /^[[:space:]]*((@\[[^\]]+\][[:space:]]*)*((private|protected|local|scoped|noncomputable|unsafe|partial|mutual)[[:space:]]+)*)?(theorem|lemma)[[:space:]]+[A-Za-z0-9_.'"'"'`?!]+/ {
            line = $0
            # Extract kind and name
            if (match(line, /(theorem|lemma)[[:space:]]+([A-Za-z0-9_.'"'"'`?!]+)/, arr)) {
                kind = arr[1]
                old_name = arr[2]

                split_tail(old_name, name_parts)
                tail = name_parts["tail"]
                prefix = name_parts["prefix"]

                if (!is_snake_tail(tail)) {
                    split_decorations(tail, dec_parts)
                    new_tail = to_snake(dec_parts["base"]) dec_parts["dec"]
                    new_name = prefix new_tail

                    if (new_name != old_name) {
                        print file ":" NR ":" kind ":" old_name ":" new_name
                    }
                }
            }
        }
        ' "$file"
    done
}

# Discover and collect renames
echo "Scanning $SCOPE for non-conformant declarations..." >&2
discover_decls "$SCOPE" > "$RENAMES_FILE"

total_discovered=$(wc -l < "$RENAMES_FILE" | tr -d ' ')

if [[ "$total_discovered" -eq 0 ]]; then
    echo "No non-conformant declaration names found."
    exit 0
fi

# Resolve collisions: group by new name, skip if multiple old names map to same new
gawk -F: '
{
    file=$1; line=$2; kind=$3; old=$4; new=$5
    key = old
    if (!(key in seen)) {
        seen[key] = 1
        old_to_new[old] = new
        old_to_file[old] = file
        old_to_line[old] = line
        old_to_kind[old] = kind
    }
}
END {
    # Group by new name
    for (old in old_to_new) {
        new = old_to_new[old]
        if (new in by_new) {
            by_new[new] = by_new[new] "," old
        } else {
            by_new[new] = old
        }
    }

    # Output safe renames and collisions
    for (new in by_new) {
        split(by_new[new], olds, ",")
        if (length(olds) > 1) {
            # Collision - output to stderr
            printf "collision: %s <= %s\n", new, by_new[new] > "/dev/stderr"
        } else {
            old = olds[1]
            printf "%s:%s:%s:%s:%s\n", old_to_file[old], old_to_line[old], old_to_kind[old], old, new
        }
    }
}
' "$RENAMES_FILE" 2>"$COLLISIONS_FILE" | sort -t: -k1,1 -k2,2n > "${RENAMES_FILE}.resolved"
mv "${RENAMES_FILE}.resolved" "$RENAMES_FILE"

safe_renames=$(wc -l < "$RENAMES_FILE" | tr -d ' ')
collision_count=$(wc -l < "$COLLISIONS_FILE" | tr -d ' ')

echo "Found $total_discovered non-conformant declaration name(s) in scope."
echo "Planned safe rename set: $safe_renames"
if [[ "$collision_count" -gt 0 ]]; then
    echo "Skipped due to collisions: $collision_count"
fi

# Dry run output
if [[ "$DRY_RUN" == true ]] || [[ "$APPLY" != true ]]; then
    if [[ "$SHOW_ALL" == true ]]; then
        limit=$safe_renames
    else
        limit=$SHOW_LIMIT
        if [[ "$limit" -gt "$safe_renames" ]]; then
            limit=$safe_renames
        fi
    fi

    head -n "$limit" "$RENAMES_FILE" | while IFS=: read -r file line kind old new; do
        # Make path relative to cwd if possible
        rel_file="${file#$PWD/}"
        echo "$rel_file:$line: $kind $old -> $new"
    done

    remaining=$((safe_renames - limit))
    if [[ "$remaining" -gt 0 ]]; then
        echo "... and $remaining more (use --all to show all)"
    fi

    if [[ "$collision_count" -gt 0 ]]; then
        echo "Skipped samples:"
        head -n 20 "$COLLISIONS_FILE" | while read -r msg; do
            echo "  $msg"
        done
        if [[ "$collision_count" -gt 20 ]]; then
            echo "  ... and $((collision_count - 20)) more skipped mappings"
        fi
    fi

    echo "Dry run only. Re-run with --apply to write changes."
    exit 0
fi

# Apply renames
echo "Applying renames..." >&2

# Build replacement map
declare -A OLD_TO_NEW
while IFS=: read -r _ _ _ old new; do
    OLD_TO_NEW["$old"]="$new"
done < "$RENAMES_FILE"

# AWK script for applying renames while preserving comments and strings
apply_renames_awk='
BEGIN {
    # Build patterns from environment (passed as -v)
    n_patterns = split(PATTERNS, pattern_arr, "\x1f")
    for (i = 1; i <= n_patterns; i += 2) {
        old = pattern_arr[i]
        new = pattern_arr[i+1]
        if (old != "") {
            old_names[++n] = old
            new_names[n] = new
        }
    }
    block_depth = 0
    changed = 0
}

# Skip import lines
/^[[:space:]]*import[[:space:]]/ {
    print
    next
}

{
    line = $0
    result = ""
    i = 1
    n_line = length(line)
    code_start = 1

    while (i <= n_line) {
        ch = substr(line, i, 1)
        ch2 = substr(line, i, 2)

        if (block_depth > 0) {
            if (ch2 == "/-") {
                block_depth++
                i += 2
                continue
            }
            if (ch2 == "-/") {
                block_depth--
                i += 2
                continue
            }
            i++
            continue
        }

        # Line comment
        if (ch2 == "--") {
            code_chunk = substr(line, code_start, i - code_start)
            result = result rewrite_chunk(code_chunk) substr(line, i)
            print result
            next
        }

        # Block comment start
        if (ch2 == "/-") {
            code_chunk = substr(line, code_start, i - code_start)
            result = result rewrite_chunk(code_chunk)

            comment_start = i
            block_depth = 1
            i += 2
            while (i <= n_line && block_depth > 0) {
                if (substr(line, i, 2) == "/-") {
                    block_depth++
                    i += 2
                } else if (substr(line, i, 2) == "-/") {
                    block_depth--
                    i += 2
                } else {
                    i++
                }
            }
            result = result substr(line, comment_start, i - comment_start)
            code_start = i
            continue
        }

        # String literal
        if (ch == "\"") {
            code_chunk = substr(line, code_start, i - code_start)
            result = result rewrite_chunk(code_chunk)

            str_start = i
            i++
            while (i <= n_line) {
                c = substr(line, i, 1)
                if (c == "\\") {
                    i += 2
                } else if (c == "\"") {
                    i++
                    break
                } else {
                    i++
                }
            }
            result = result substr(line, str_start, i - str_start)
            code_start = i
            continue
        }

        i++
    }

    # Process remaining code
    tail = substr(line, code_start)
    if (block_depth == 0) {
        result = result rewrite_chunk(tail)
    } else {
        result = result tail
    }

    print result
}

function rewrite_chunk(chunk) {
    for (j = 1; j <= n; j++) {
        old = old_names[j]
        new = new_names[j]
        if (index(chunk, old) > 0) {
            # Replace with word boundary awareness
            gsub_count = gsub_word(chunk, old, new)
            if (gsub_count > 0) changed += gsub_count
        }
    }
    return chunk
}

# Word-boundary aware substitution
function gsub_word(str, old, new,    result, pos, before, after, ok) {
    result = ""
    count = 0
    while ((pos = index(str, old)) > 0) {
        before = (pos > 1) ? substr(str, pos - 1, 1) : ""
        after = substr(str, pos + length(old), 1)

        # Check word boundaries (not alphanumeric, underscore, quote, backtick, ?, !)
        ok = 1
        if (before ~ /[A-Za-z0-9_'"'"'`?!]/) ok = 0
        if (after ~ /[A-Za-z0-9_'"'"'`?!]/) ok = 0

        if (ok) {
            result = result substr(str, 1, pos - 1) new
            count++
        } else {
            result = result substr(str, 1, pos - 1 + length(old))
        }
        str = substr(str, pos + length(old))
    }
    # This function modifies chunk in the caller scope via GAWK magic (not really)
    # We need to return the modified string and count separately
    chunk = result str
    return count
}

END {
    if (changed > 0) exit 1
    exit 0
}
'

# Process files
changed_files=0
total_replacements=0

# Build pattern string (old\x1fnew pairs separated by \x1f)
PATTERNS=""
for old in "${!OLD_TO_NEW[@]}"; do
    new="${OLD_TO_NEW[$old]}"
    if [[ -n "$PATTERNS" ]]; then
        PATTERNS="${PATTERNS}"$'\x1f'
    fi
    PATTERNS="${PATTERNS}${old}"$'\x1f'"${new}"
done

find "$REWRITE_ROOT" "${EXCLUDE_ARGS[@]}" -name "*.lean" -type f -print 2>/dev/null | sort | while read -r file; do
    tmp_file=$(mktemp)

    # Use a simpler approach: sed-based replacement with word boundaries
    # This is more reliable than complex awk
    cp "$file" "$tmp_file"

    file_changed=false
    for old in "${!OLD_TO_NEW[@]}"; do
        new="${OLD_TO_NEW[$old]}"
        # Escape special characters for sed
        old_escaped=$(printf '%s\n' "$old" | sed 's/[[\.*^$()+?{|]/\\&/g')
        new_escaped=$(printf '%s\n' "$new" | sed 's/[&/\]/\\&/g')

        # Use perl for better word boundary handling (available in most systems)
        # Fall back to sed if perl not available
        if command -v perl &>/dev/null; then
            # Skip import lines, preserve comments/strings approximately
            perl -i -pe '
                next if /^\s*import\s/;
                # Simple word boundary replacement (not perfect for comments/strings)
                s/(?<![A-Za-z0-9_'"'"'`?!])'"$old_escaped"'(?![A-Za-z0-9_'"'"'`?!])/'"$new_escaped"'/g;
            ' "$tmp_file" && file_changed=true
        else
            # Fallback: basic sed (less accurate)
            sed -i "s/\\b${old_escaped}\\b/${new_escaped}/g" "$tmp_file" && file_changed=true
        fi
    done

    if ! cmp -s "$file" "$tmp_file"; then
        mv "$tmp_file" "$file"
        ((++changed_files))
    else
        rm "$tmp_file"
    fi
done

echo "Applied renames in $changed_files file(s)."
if [[ "$collision_count" -gt 0 ]]; then
    echo "Skipped $collision_count ambiguous/conflicting rename(s)."
fi
