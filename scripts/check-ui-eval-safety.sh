#!/usr/bin/env bash
set -euo pipefail

violations="$(
  rg -n '\beval\s*\(' rust/ui rust/web --glob '*.rs' \
    | rg -v 'rust/ui/src/components.rs:[0-9]+:\s*let _ = eval\(&script\);' \
    || true
)"

if [[ -n "$violations" ]]; then
  cat >&2 <<'MSG'
Unsafe UI eval usage found.

Only rust/ui/src/components.rs::call_js may invoke dioxus::document::eval,
and it must pass JSON-encoded arguments through the local script variable.
MSG
  printf '%s\n' "$violations" >&2
  exit 1
fi
