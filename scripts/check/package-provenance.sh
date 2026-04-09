#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

source "${ROOT_DIR}/scripts/lib/release-packages.sh"

manifest_path="${ROOT_DIR}/target/package-artifact-tarballs/provenance.json"

hash_file() {
  local path="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "${path}" | awk '{print $1}'
  else
    shasum -a 256 "${path}" | awk '{print $1}'
  fi
}

extract_manifest_version() {
  local manifest="$1"
  awk '
    /^\[package\]/ { in_package = 1; next }
    /^\[/ { in_package = 0 }
    in_package && $1 == "version" {
      gsub(/ /, "", $0)
      sub(/^version="/, "", $0)
      sub(/"$/, "", $0)
      print $0
      exit
    }
  ' "${manifest}"
}

if [[ ! -f "${manifest_path}" ]]; then
  echo "package-provenance: missing packaged artifact manifest; generating it first" >&2
  "${ROOT_DIR}/scripts/check/package-artifacts.sh"
fi

[[ -f "${manifest_path}" ]] || {
  echo "error: missing provenance manifest ${manifest_path} after package-artifacts.sh" >&2
  exit 1
}

workspace_version="$(extract_manifest_version "${ROOT_DIR}/Cargo.toml")"
git_head="$(git rev-parse HEAD)"

export PACKAGE_PROVENANCE_MANIFEST="${manifest_path}"
export PACKAGE_PROVENANCE_VERSION="${workspace_version}"
export PACKAGE_PROVENANCE_HEAD="${git_head}"
export PACKAGE_PROVENANCE_WASM_LOCK_SHA256="$(hash_file "${WASM_EXAMPLE_LOCK_PATH}")"
export PACKAGE_PROVENANCE_SEARCH_THEOREM_PACK_PATH="$(./scripts/ops/export-search-theorem-pack.sh)"
export PACKAGE_PROVENANCE_SEARCH_VECTORS_PATH="$(./scripts/ops/export-search-vectors.sh)"
export PACKAGE_PROVENANCE_SEARCH_RECOVERY_VECTORS_PATH="$(./scripts/ops/export-search-recovery-vectors.sh)"
python3 - <<'PY'
import json
import os
import pathlib
import subprocess
import sys

root = pathlib.Path.cwd()
manifest_path = pathlib.Path(os.environ["PACKAGE_PROVENANCE_MANIFEST"])
workspace_version = os.environ["PACKAGE_PROVENANCE_VERSION"]
git_head = os.environ["PACKAGE_PROVENANCE_HEAD"]
wasm_lock_sha256 = os.environ["PACKAGE_PROVENANCE_WASM_LOCK_SHA256"]
search_theorem_pack_path = pathlib.Path(os.environ["PACKAGE_PROVENANCE_SEARCH_THEOREM_PACK_PATH"])
search_vectors_path = pathlib.Path(os.environ["PACKAGE_PROVENANCE_SEARCH_VECTORS_PATH"])
search_recovery_vectors_path = pathlib.Path(
    os.environ["PACKAGE_PROVENANCE_SEARCH_RECOVERY_VECTORS_PATH"]
)

manifest = json.loads(manifest_path.read_text())

def sha256(path: pathlib.Path) -> str:
    if subprocess.run(["which", "sha256sum"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0:
        return subprocess.check_output(["sha256sum", str(path)], text=True).split()[0]
    return subprocess.check_output(["shasum", "-a", "256", str(path)], text=True).split()[0]

errors: list[str] = []

if manifest.get("workspace_version") != workspace_version:
    errors.append(
        f"workspace_version mismatch: {manifest.get('workspace_version')} != {workspace_version}"
    )
if manifest.get("git_head") != git_head:
    errors.append(f"git_head mismatch: {manifest.get('git_head')} != {git_head}")
if manifest.get("wasm_example_lock_sha256") != wasm_lock_sha256:
    errors.append("wasm_example_lock_sha256 mismatch")

artifact_dir = manifest_path.parent
for entry in manifest.get("tarballs", []):
    tarball = artifact_dir / entry["file"]
    if not tarball.is_file():
        errors.append(f"missing tarball {tarball}")
        continue
    actual_sha = sha256(tarball)
    if actual_sha != entry.get("sha256"):
        errors.append(f"sha256 mismatch for {tarball.name}")
    actual_size = tarball.stat().st_size
    if actual_size != entry.get("size_bytes"):
        errors.append(f"size mismatch for {tarball.name}")

resource_files = {
    "telltale:README.md": root / "README.md",
    "telltale-runtime:README.md": root / "README.md",
    "telltale-runtime:src/compiler/choreography.pest": root / "rust/runtime/src/compiler/choreography.pest",
    "telltale-bridge:README.md": root / "README.md",
    "examples/wasm/README.md": root / "examples/wasm/README.md",
    "examples/wasm/harness.sh": root / "examples/wasm/harness.sh",
    "telltale-search:search-theorem-pack.json": search_theorem_pack_path,
    "telltale-search:search-vectors-v1.json": search_vectors_path,
    "telltale-search:search-recovery-vectors-v1.json": search_recovery_vectors_path,
}

recorded_resources = manifest.get("resource_hashes", {})
for key, path in resource_files.items():
    actual = sha256(path)
    if recorded_resources.get(key) != actual:
        errors.append(f"resource hash mismatch for {key}")

if errors:
    for error in errors:
        print(f"error: {error}", file=sys.stderr)
    sys.exit(1)
PY

echo "package-provenance: ok"
