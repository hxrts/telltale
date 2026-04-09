#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

output_dir="${ROOT_DIR}/target/search-artifacts"
output_path="${output_dir}/search-recovery-vectors-v1.json"

mkdir -p "${output_dir}"
cargo run --quiet -p telltale-search --example export_recovery_vectors > "${output_path}"

printf '%s\n' "${output_path}"
