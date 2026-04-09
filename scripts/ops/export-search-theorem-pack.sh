#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

out_dir="${ROOT_DIR}/target/search-theorem-pack"
out_file="${out_dir}/search-theorem-pack.json"
mkdir -p "${out_dir}"

cargo run -q -p telltale-search --example export_theorem_pack > "${out_file}"

echo "${out_file}"
