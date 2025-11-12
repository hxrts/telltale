# Justfile

# Default task
default: book

# Generate docs/SUMMARY.md from Markdown files in docs/ and subfolders
summary:
    #!/usr/bin/env bash
    set -euo pipefail

    docs="docs"
    build_dir="$docs/book"
    out="$docs/SUMMARY.md"

    echo "# Summary" > "$out"
    echo "" >> "$out"

    # Find all .md files under docs/, excluding SUMMARY.md itself and the build output
    while IFS= read -r f; do
        rel="${f#$docs/}"

        # Skip SUMMARY.md
        [ "$rel" = "SUMMARY.md" ] && continue

        # Skip files under the build output directory
        case "$f" in "$build_dir"/*) continue ;; esac

        # Derive the title from the first H1; fallback to filename
        title="$(grep -m1 '^# ' "$f" | sed 's/^# *//')"
        if [ -z "$title" ]; then
            base="$(basename "${f%.*}")"
            title="$(printf '%s\n' "$base" \
                | tr '._-' '   ' \
                | awk '{for(i=1;i<=NF;i++){ $i=toupper(substr($i,1,1)) substr($i,2) }}1')"
        fi

        # Indent two spaces per directory depth
        depth="$(awk -F'/' '{print NF-1}' <<<"$rel")"
        indent="$(printf '%*s' $((depth*2)) '')"

        echo "${indent}- [$title](${rel})" >> "$out"
    done < <(find "$docs" -type f -name '*.md' -not -name 'SUMMARY.md' -not -path "$build_dir/*" | LC_ALL=C sort)

    echo "Wrote $out"

# Build the book after regenerating the summary
book: summary
    @mdbook-mermaid install . > /dev/null 2>&1 || true
    mdbook build

# Serve locally with live reload
serve: summary
    #!/usr/bin/env bash
    # Trap SIGINT (Ctrl+C) for graceful shutdown
    trap 'echo -e "\nShutting down mdbook server..."; exit 0' INT

    # Try to serve on the default port, fallback to next available port if in use
    for port in 3000 3001 3002 3003 3004 3005; do
        if ! lsof -Pi :$port -sTCP:LISTEN -t >/dev/null 2>&1; then
            echo "Starting mdbook server on http://localhost:$port"
            echo "Press Ctrl+C to stop the server"
            mdbook serve --port $port --open
            exit 0
        fi
    done
    # If we get here, all ports are in use, just show the error
    echo "Error: All ports 3000-3005 are already in use" >&2
    exit 1
