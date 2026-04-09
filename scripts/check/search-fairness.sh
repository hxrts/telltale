#!/usr/bin/env bash
# Keep the Lean-backed search fairness theorem surface, parity fixture, and
# inventory gate aligned.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

artifact_path="$(./scripts/ops/export-search-theorem-pack.sh)"
[[ -f "$artifact_path" ]] || {
  echo "error: missing search theorem-pack export ${artifact_path}" >&2
  exit 1
}
vector_path="$(./scripts/ops/export-search-vectors.sh)"
[[ -f "$vector_path" ]] || {
  echo "error: missing search vector export ${vector_path}" >&2
  exit 1
}
recovery_vector_path="$(./scripts/ops/export-search-recovery-vectors.sh)"
[[ -f "$recovery_vector_path" ]] || {
  echo "error: missing search recovery vector export ${recovery_vector_path}" >&2
  exit 1
}

lake --dir lean build Runtime.Proofs.Search.API search_parity_runner
cargo test -p telltale-search --test search_lean -- --nocapture
cargo test -p telltale-search --test search_vectors -- --nocapture
cargo test -p telltale-search --test search_vectors --features multi-thread -- --nocapture
cargo test -p telltale-search --test search_recovery_vectors -- --nocapture
./scripts/check/verification-inventory.sh

echo "search-fairness: clean"
