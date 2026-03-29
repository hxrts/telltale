#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

source "${ROOT_DIR}/scripts/lib/release-packages.sh"

require_command() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "error: $1 is required" >&2
    exit 2
  }
}

extract_manifest_version() {
  local manifest_path="$1"
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
  ' "${manifest_path}"
}

extract_manifest_rust_version() {
  local manifest_path="$1"
  awk '
    /^\[package\]/ { in_package = 1; next }
    /^\[/ { in_package = 0 }
    in_package && $1 == "rust-version" {
      gsub(/ /, "", $0)
      sub(/^rust-version="/, "", $0)
      sub(/"$/, "", $0)
      print $0
      exit
    }
  ' "${manifest_path}"
}

extract_lockfile_version() {
  local lockfile_path="$1"
  local package="$2"
  awk -v package="${package}" '
    /^\[\[package\]\]$/ { in_target = 0; next }
    /^name = "/ {
      current = $0
      sub(/^name = "/, "", current)
      sub(/"$/, "", current)
      in_target = (current == package)
      next
    }
    in_target && /^version = "/ {
      version = $0
      sub(/^version = "/, "", version)
      sub(/"$/, "", version)
      print version
      exit
    }
  ' "${lockfile_path}"
}

workspace_version="$(extract_manifest_version "${ROOT_DIR}/Cargo.toml")"
workspace_rust_version="$(extract_manifest_rust_version "${ROOT_DIR}/Cargo.toml")"
package_target_dir="${ROOT_DIR}/target/package-artifact-audit"
saved_tarball_dir="${ROOT_DIR}/target/package-artifact-tarballs"

require_command cargo
require_command python3
require_command tar
require_command rg

echo "== validate publishable crate versions =="
for package in "${RELEASE_PACKAGES[@]}"; do
  manifest="$(manifest_path "${package}")"
  manifest_version="$(extract_manifest_version "${manifest}")"
  if [[ "${manifest_version}" != "${workspace_version}" ]]; then
    echo "error: version mismatch for ${package}: ${manifest_version} != ${workspace_version}" >&2
    exit 1
  fi
done

echo "== validate wasm example lockfile =="
[[ -f "${WASM_EXAMPLE_LOCK_PATH}" ]] || {
  echo "error: missing ${WASM_EXAMPLE_LOCK_PATH}" >&2
  exit 1
}
for package in "${WASM_EXAMPLE_LOCK_PACKAGES[@]}"; do
  lock_version="$(extract_lockfile_version "${WASM_EXAMPLE_LOCK_PATH}" "${package}")"
  [[ -n "${lock_version}" ]] || {
    echo "error: missing ${package} entry in ${WASM_EXAMPLE_LOCK_PATH}" >&2
    exit 1
  }
  if [[ "${lock_version}" != "${workspace_version}" ]]; then
    echo "error: ${WASM_EXAMPLE_LOCK_PATH} is stale for ${package}: ${lock_version} != ${workspace_version}" >&2
    exit 1
  fi
done

echo "== check resolved dependency rust-version compatibility =="
python3 - <<'PY'
import json
import pathlib
import subprocess
import sys

root = pathlib.Path.cwd()
sys.path.insert(0, str(root))

release_packages = [
    "telltale-types",
    "telltale-language",
    "telltale-theory",
    "telltale-macros",
    "telltale-machine",
    "telltale",
    "telltale-runtime",
    "telltale-transport",
    "telltale-simulator",
    "telltale-bridge",
]

manifest_paths = {
    "telltale-types": "rust/types/Cargo.toml",
    "telltale-language": "rust/language/Cargo.toml",
    "telltale-theory": "rust/theory/Cargo.toml",
    "telltale-macros": "rust/macros/Cargo.toml",
    "telltale-machine": "rust/machine/Cargo.toml",
    "telltale": "Cargo.toml",
    "telltale-runtime": "rust/runtime/Cargo.toml",
    "telltale-transport": "rust/transport/Cargo.toml",
    "telltale-simulator": "rust/simulator/Cargo.toml",
    "telltale-bridge": "rust/bridge/Cargo.toml",
}

def parse_version(raw: str):
    raw = raw.strip()
    if not raw:
        return None
    core = raw.split("-", 1)[0]
    parts = [int(part) for part in core.split(".")]
    while len(parts) < 3:
        parts.append(0)
    return tuple(parts[:3])

def manifest_rust_version(path: pathlib.Path) -> str | None:
    in_package = False
    for line in path.read_text().splitlines():
        stripped = line.strip()
        if stripped == "[package]":
            in_package = True
            continue
        if stripped.startswith("[") and stripped != "[package]":
            in_package = False
        if in_package and stripped.startswith("rust-version"):
            return stripped.split("=", 1)[1].strip().strip('"')
    return None

metadata = json.loads(
    subprocess.check_output(
        ["cargo", "metadata", "--format-version", "1", "--locked"],
        text=True,
    )
)
packages = metadata["packages"]

def lookup_package(name: str, version: str):
    for pkg in packages:
        if pkg["name"] == name and pkg["version"] == version:
            return pkg
    return None

errors: list[str] = []

for package_name in release_packages:
    manifest = (root / manifest_paths[package_name]).resolve()
    package_msrv_raw = manifest_rust_version(manifest) or manifest_rust_version(root / "Cargo.toml")
    package_msrv = parse_version(package_msrv_raw or "")
    tree_lines = subprocess.check_output(
        ["cargo", "tree", "-p", package_name, "-e", "normal,build", "--prefix", "none", "--format", "{p}"],
        text=True,
    ).splitlines()
    seen: set[tuple[str, str]] = set()
    for line in tree_lines:
        line = line.strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) < 2:
            continue
        dep_name, dep_version = parts[0], parts[1]
        if (dep_name, dep_version) in seen:
            continue
        seen.add((dep_name, dep_version))
        pkg = lookup_package(dep_name, dep_version)
        if pkg is None:
            continue
        dep_msrv_raw = pkg.get("rust_version")
        if dep_msrv_raw and package_msrv and parse_version(dep_msrv_raw) > package_msrv:
            errors.append(
                f"{package_name} (rust-version {package_msrv_raw}) resolves dependency "
                f"{pkg['name']}@{pkg['version']} requiring rust-version {dep_msrv_raw}"
            )

if errors:
    for err in errors:
        print(f"error: {err}", file=sys.stderr)
    sys.exit(1)
PY

echo "== cargo publish --dry-run --locked for every release crate =="
rm -rf "${package_target_dir}" "${saved_tarball_dir}"
mkdir -p "${package_target_dir}" "${saved_tarball_dir}"
for package in "${RELEASE_PACKAGES[@]}"; do
  package_target_dir_run="${package_target_dir}/${package}"
  rm -rf "${package_target_dir_run}"
  mkdir -p "${package_target_dir_run}"
  echo "-- cargo publish -p ${package} --dry-run --locked --allow-dirty"
  CARGO_TARGET_DIR="${package_target_dir_run}" \
    cargo publish -p "${package}" --dry-run --locked --allow-dirty

  tarball="${package_target_dir_run}/package/${package}-${workspace_version}.crate"
  [[ -f "${tarball}" ]] || {
    echo "error: missing tarball ${tarball}" >&2
    exit 1
  }

  case "${package}" in
    telltale|telltale-runtime|telltale-bridge)
      cp "${tarball}" "${saved_tarball_dir}/"
      ;;
  esac

  rm -rf "${package_target_dir_run}"
done

tarball_path() {
  local package="$1"
  echo "${saved_tarball_dir}/${package}-${workspace_version}.crate"
}

assert_tarball_contains() {
  local package="$1"
  local needle="$2"
  local tarball
  tarball="$(tarball_path "${package}")"
  [[ -f "${tarball}" ]] || {
    echo "error: missing tarball ${tarball}" >&2
    exit 1
  }
  tar -tf "${tarball}" | grep -Fq "/${needle}" || {
    echo "error: ${package} tarball missing ${needle}" >&2
    exit 1
  }
}

smoke_packaged_crate() {
  local package="$1"
  shift
  local tarball tmpdir crate_root
  tarball="$(tarball_path "${package}")"
  tmpdir="$(mktemp -d)"
  tar -xf "${tarball}" -C "${tmpdir}"
  crate_root="${tmpdir}/${package}-${workspace_version}"
  (
    cd "${crate_root}"
    CARGO_TARGET_DIR="${tmpdir}/target" "$@"
  )
  rm -rf "${tmpdir}"
}

echo "== verify packaged resource presence =="
assert_tarball_contains telltale "README.md"
assert_tarball_contains telltale-runtime "README.md"
assert_tarball_contains telltale-runtime "src/compiler/choreography.pest"
assert_tarball_contains telltale-bridge "README.md"
[[ -f "${ROOT_DIR}/examples/wasm/README.md" ]] || {
  echo "error: missing examples/wasm/README.md" >&2
  exit 1
}
[[ -f "${ROOT_DIR}/examples/wasm/harness.sh" ]] || {
  echo "error: missing examples/wasm/harness.sh" >&2
  exit 1
}

echo "== smoke check packaged telltale crate =="
smoke_packaged_crate telltale cargo check --lib --features full
smoke_packaged_crate telltale cargo check --lib --target wasm32-unknown-unknown --features wasm

echo "== smoke check packaged telltale-runtime crate =="
smoke_packaged_crate telltale-runtime cargo check --lib --all-features

echo "== smoke check packaged telltale-bridge crate =="
smoke_packaged_crate telltale-bridge cargo check --lib --all-features

echo "package-artifacts: ok"
