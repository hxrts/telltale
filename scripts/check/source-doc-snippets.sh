#!/usr/bin/env bash
set -euo pipefail

cargo test -p telltale-runtime --test source_doc_snippets -- --nocapture
echo "source-doc-snippets: ok"
