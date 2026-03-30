#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

tmp_root="${TMPDIR:-/tmp}"
if [[ ! -d "${tmp_root}" ]]; then
  export TMPDIR="/tmp"
fi

source "${ROOT_DIR}/scripts/lib/release-packages.sh"

require_command() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "error: $1 is required" >&2
    exit 2
  }
}

hash_file() {
  local path="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "${path}" | awk '{print $1}'
  else
    shasum -a 256 "${path}" | awk '{print $1}'
  fi
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

extract_manifest_package_path_field() {
  local manifest_path="$1"
  local field_name="$2"
  awk -v field_name="${field_name}" '
    /^\[package\]/ { in_package = 1; next }
    /^\[/ { in_package = 0 }
    in_package && $1 == field_name {
      gsub(/^[[:space:]]+|[[:space:]]+$/, "", $0)
      sub("^[^=]+=[[:space:]]*\"", "", $0)
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
require_command git
require_command python3
require_command rustup
require_command tar
require_command rg
require_command rustc
if ! command -v sha256sum >/dev/null 2>&1 && ! command -v shasum >/dev/null 2>&1; then
  echo "error: sha256sum or shasum is required" >&2
  exit 2
fi

echo "== validate publishable crate versions =="
for package in "${RELEASE_PACKAGES[@]}"; do
  manifest="$(manifest_path "${package}")"
  manifest_version="$(extract_manifest_version "${manifest}")"
  if [[ "${manifest_version}" != "${workspace_version}" ]]; then
    echo "error: version mismatch for ${package}: ${manifest_version} != ${workspace_version}" >&2
    exit 1
  fi
done

echo "== validate package manifest resources =="
for package in "${RELEASE_PACKAGES[@]}"; do
  manifest="$(manifest_path "${package}")"
  manifest_dir="$(dirname "${manifest}")"
  readme_path="$(extract_manifest_package_path_field "${manifest}" "readme")"
  if [[ -n "${readme_path}" ]]; then
    resolved_readme="$(cd "${manifest_dir}" && python3 -c 'import os,sys; print(os.path.normpath(sys.argv[1]))' "${readme_path}")"
    if [[ ! -f "${manifest_dir}/${resolved_readme}" ]]; then
      echo "error: ${package}: manifest readme path missing: ${readme_path}" >&2
      exit 1
    fi
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

echo "== cargo publish --dry-run --locked --no-verify for every release crate =="
rm -rf "${package_target_dir}" "${saved_tarball_dir}"
mkdir -p "${package_target_dir}" "${saved_tarball_dir}"
for package in "${RELEASE_PACKAGES[@]}"; do
  package_target_dir_run="${package_target_dir}/${package}"
  rm -rf "${package_target_dir_run}"
  mkdir -p "${package_target_dir_run}"
  echo "-- cargo publish -p ${package} --dry-run --locked --allow-dirty --no-verify"
  CARGO_TARGET_DIR="${package_target_dir_run}" \
    cargo publish -p "${package}" --dry-run --locked --allow-dirty --no-verify

  tarball="${package_target_dir_run}/package/${package}-${workspace_version}.crate"
  if [[ ! -f "${tarball}" ]]; then
    echo "-- cargo package -p ${package} --list --allow-dirty --no-verify (materialize tarball)"
    CARGO_TARGET_DIR="${package_target_dir_run}" \
      cargo package -p "${package}" --allow-dirty --no-verify >/dev/null
  fi
  [[ -f "${tarball}" ]] || {
    echo "error: missing tarball ${tarball}" >&2
    exit 1
  }

  cp "${tarball}" "${saved_tarball_dir}/"

  rm -rf "${package_target_dir_run}"
done

tarball_path() {
  local package="$1"
  echo "${saved_tarball_dir}/${package}-${workspace_version}.crate"
}

extract_packaged_file_to_tmp() {
  local package="$1"
  local packaged_path="$2"
  local dest_path="$3"
  local tarball
  tarball="$(tarball_path "${package}")"
  tar -xOf "${tarball}" "${package}-${workspace_version}/${packaged_path}" > "${dest_path}"
}

assert_tarball_contains() {
  local package="$1"
  local needle="$2"
  local tarball listing
  tarball="$(tarball_path "${package}")"
  [[ -f "${tarball}" ]] || {
    echo "error: missing tarball ${tarball}" >&2
    exit 1
  }
  listing="$(tar -tf "${tarball}")"
  grep -Fq "/${needle}" <<<"${listing}" || {
    echo "error: ${package} tarball missing ${needle}" >&2
    exit 1
  }
}

assert_packaged_file_matches_source() {
  local package="$1"
  local packaged_path="$2"
  local source_path="$3"
  local tmpfile expected actual
  [[ -f "${source_path}" ]] || {
    echo "error: source path missing for ${package}: ${source_path}" >&2
    exit 1
  }
  tmpfile="$(mktemp)"
  extract_packaged_file_to_tmp "${package}" "${packaged_path}" "${tmpfile}"
  expected="$(hash_file "${source_path}")"
  actual="$(hash_file "${tmpfile}")"
  rm -f "${tmpfile}"
  if [[ "${expected}" != "${actual}" ]]; then
    echo "error: ${package} packaged ${packaged_path} does not match source ${source_path}" >&2
    exit 1
  fi
}

smoke_packaged_crate() {
  local package="$1"
  shift
  local tarball tmpdir crate_root packaged_dir status
  tarball="$(tarball_path "${package}")"
  tmpdir="$(mktemp -d)"
  tar -xf "${tarball}" -C "${tmpdir}"
  crate_root="${tmpdir}/${package}-${workspace_version}"
  packaged_dir="${tmpdir}/packaged"
  prepare_packaged_registry "${packaged_dir}"
  ensure_standalone_workspace_manifest "${crate_root}/Cargo.toml"
  write_patch_section "${crate_root}/Cargo.toml" "${packaged_dir}"
  set +e
  (
    cd "${crate_root}"
    CARGO_TARGET_DIR="${tmpdir}/target" "$@"
  )
  status=$?
  set -e
  rm -rf "${tmpdir}"
  return "${status}"
}

prepare_packaged_registry() {
  local dest_dir="$1"
  mkdir -p "${dest_dir}"
  for package in "${RELEASE_PACKAGES[@]}"; do
    tar -xf "$(tarball_path "${package}")" -C "${dest_dir}"
  done
}

write_patch_section() {
  local dest_file="$1"
  local packaged_dir="$2"
  {
    echo "[patch.crates-io]"
    for package in "${RELEASE_PACKAGES[@]}"; do
      echo "${package} = { path = \"${packaged_dir}/${package}-${workspace_version}\" }"
    done
  } >> "${dest_file}"
}

ensure_standalone_workspace_manifest() {
  local manifest_path="$1"
  if ! rg -q '^\[workspace\]$' "${manifest_path}"; then
    printf '\n[workspace]\n' >> "${manifest_path}"
  fi
}

create_consumer_canary() {
  local canary_dir="$1"
  local packaged_dir="$2"
  local dependency_block="$3"
  local main_body="$4"

  mkdir -p "${canary_dir}/src"
  cat > "${canary_dir}/Cargo.toml" <<EOF
[package]
name = "$(basename "${canary_dir}")"
version = "0.1.0"
edition = "2021"
publish = false

[dependencies]
${dependency_block}
EOF
  ensure_standalone_workspace_manifest "${canary_dir}/Cargo.toml"
  write_patch_section "${canary_dir}/Cargo.toml" "${packaged_dir}"
  cat > "${canary_dir}/src/main.rs" <<EOF
${main_body}
EOF
}

run_consumer_canary() {
  local name="$1"
  local dependency_block="$2"
  local main_body="$3"
  local expected_last_line="$4"
  shift 4
  local tmpdir packaged_dir canary_dir output status actual_last_line
  tmpdir="$(mktemp -d)"
  packaged_dir="${tmpdir}/packaged"
  canary_dir="${tmpdir}/${name}"
  output="${tmpdir}/${name}.log"
  prepare_packaged_registry "${packaged_dir}"
  create_consumer_canary "${canary_dir}" "${packaged_dir}" "${dependency_block}" "${main_body}"
  set +e
  (
    cd "${canary_dir}"
    CARGO_TARGET_DIR="${tmpdir}/target" \
      CARGO_INCREMENTAL=0 \
      CARGO_PROFILE_DEV_DEBUG=0 \
      "$@"
  ) >"${output}" 2>&1
  status=$?
  set -e
  if [[ "${status}" -ne 0 ]]; then
    cat "${output}" >&2
    rm -rf "${tmpdir}"
    return "${status}"
  fi
  actual_last_line="$(awk 'NF { line = $0 } END { print line }' "${output}")"
  if [[ "${actual_last_line}" != "${expected_last_line}" ]]; then
    echo "error: ${name} expected last line '${expected_last_line}' but saw '${actual_last_line}'" >&2
    cat "${output}" >&2
    rm -rf "${tmpdir}"
    return 1
  fi
  rm -rf "${tmpdir}"
  return 0
}

ensure_rust_target_installed() {
  local target="$1"
  if ! rustup target list --installed | grep -qx "${target}"; then
    rustup target add "${target}"
  fi
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

echo "== verify packaged resource contents =="
assert_packaged_file_matches_source telltale "README.md" "${ROOT_DIR}/README.md"
assert_packaged_file_matches_source telltale-runtime "README.md" "${ROOT_DIR}/README.md"
assert_packaged_file_matches_source telltale-runtime "src/compiler/choreography.pest" "${ROOT_DIR}/rust/runtime/src/compiler/choreography.pest"
assert_packaged_file_matches_source telltale-bridge "README.md" "${ROOT_DIR}/README.md"

echo "== smoke check packaged telltale crate =="
smoke_packaged_crate telltale cargo check --lib --features full
ensure_rust_target_installed wasm32-unknown-unknown
smoke_packaged_crate telltale cargo check --lib --target wasm32-unknown-unknown --features wasm

echo "== smoke check packaged telltale-runtime crate =="
smoke_packaged_crate telltale-runtime cargo check --lib --all-features

echo "== smoke check packaged telltale-bridge crate =="
smoke_packaged_crate telltale-bridge cargo check --lib --all-features

echo "== run external consumer canary: telltale =="
run_consumer_canary \
  telltale-package-canary \
  "telltale = { version = \"=${workspace_version}\" }" \
  'use telltale::tell;

tell! {
    protocol ExternalCanary =
      roles A, B
      A -> B : Ping
}

fn main() {
    assert!(ExternalCanary::proof_status::SESSION_PROJECTABLE);
    assert!(ExternalCanary::proof_status::PROTOCOL_MACHINE_EXECUTABLE);
    println!("root canary ok: {}", ExternalCanary::proof_status::DEADLOCK_AUTOMATION_ELIGIBLE);
}' \
  "root canary ok: true" \
  cargo run --quiet

echo "== run external consumer canary: telltale-runtime =="
run_consumer_canary \
  telltale-runtime-package-canary \
  "$(printf 'telltale = { version = \"=%s\" }\ntelltale-runtime = { version = \"=%s\" }' "${workspace_version}" "${workspace_version}")" \
  'use telltale_runtime::{compile_choreography_with_extensions, tell};

tell! {
    protocol RuntimeCanary =
      roles A, B
      A -> B : Ping
}

fn main() {
    let tokens = compile_choreography_with_extensions(
        "protocol Generated =\n  roles A, B\n  A -> B : Ping\n",
    )
    .expect("packaged runtime parser/codegen should succeed");
    assert!(RuntimeCanary::proof_status::PROTOCOL_MACHINE_EXECUTABLE);
    let rendered = tokens.to_string();
    assert!(rendered.contains("Generated"));
    println!("runtime canary ok: {}", rendered.len());
}' \
  "runtime canary ok: 304" \
  cargo run --quiet

echo "== run external consumer canary: telltale-bridge =="
run_consumer_canary \
  telltale-bridge-package-canary \
  "$(printf 'serde_json = \"1\"\ntelltale-bridge = { version = \"=%s\" }\ntelltale-types = { version = \"=%s\" }' "${workspace_version}" "${workspace_version}")" \
  'use telltale_bridge::{global_to_json, json_to_global};
use telltale_types::{GlobalType, Label};

fn main() {
    let global = GlobalType::comm("Client", "Server", vec![(Label::new("ping"), GlobalType::End)]);
    let json = global_to_json(&global);
    let reparsed = json_to_global(&json).expect("bridge import/export roundtrip should succeed");
    assert_eq!(reparsed, global);
    println!("bridge canary ok: {}", serde_json::to_string(&json).unwrap());
}' \
  'bridge canary ok: {"branches":[{"continuation":{"kind":"end"},"label":{"name":"ping","sort":"unit"}}],"kind":"comm","receiver":"Server","sender":"Client"}' \
  cargo run --quiet

echo "== write package provenance manifest =="
export PACKAGE_ARTIFACT_DIR="${saved_tarball_dir}"
export PACKAGE_WORKSPACE_VERSION="${workspace_version}"
export PACKAGE_GIT_HEAD="$(git rev-parse HEAD)"
export PACKAGE_RUSTC_VERSION="$(rustc --version)"
export PACKAGE_CARGO_VERSION="$(cargo --version)"
export PACKAGE_WASM_LOCK_SHA256="$(hash_file "${WASM_EXAMPLE_LOCK_PATH}")"
python3 - <<'PY'
import json
import os
import pathlib
import subprocess

root = pathlib.Path.cwd()
artifact_dir = pathlib.Path(os.environ["PACKAGE_ARTIFACT_DIR"])
workspace_version = os.environ["PACKAGE_WORKSPACE_VERSION"]
git_head = os.environ["PACKAGE_GIT_HEAD"]
rustc_version = os.environ["PACKAGE_RUSTC_VERSION"]
cargo_version = os.environ["PACKAGE_CARGO_VERSION"]
wasm_lock_sha256 = os.environ["PACKAGE_WASM_LOCK_SHA256"]

packages = [
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

def sha256(path: pathlib.Path) -> str:
    if subprocess.run(["which", "sha256sum"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0:
        return subprocess.check_output(["sha256sum", str(path)], text=True).split()[0]
    return subprocess.check_output(["shasum", "-a", "256", str(path)], text=True).split()[0]

resource_files = {
    "telltale:README.md": root / "README.md",
    "telltale-runtime:README.md": root / "README.md",
    "telltale-runtime:src/compiler/choreography.pest": root / "rust/runtime/src/compiler/choreography.pest",
    "telltale-bridge:README.md": root / "README.md",
    "examples/wasm/README.md": root / "examples/wasm/README.md",
    "examples/wasm/harness.sh": root / "examples/wasm/harness.sh",
}

manifest = {
    "workspace_version": workspace_version,
    "git_head": git_head,
    "rustc_version": rustc_version,
    "cargo_version": cargo_version,
    "wasm_example_lock_sha256": wasm_lock_sha256,
    "tarballs": [],
    "resource_hashes": {
        key: sha256(path) for key, path in resource_files.items()
    },
}

for package in packages:
    tarball = artifact_dir / f"{package}-{workspace_version}.crate"
    manifest["tarballs"].append(
        {
            "package": package,
            "file": tarball.name,
            "sha256": sha256(tarball),
            "size_bytes": tarball.stat().st_size,
        }
    )

(artifact_dir / "provenance.json").write_text(json.dumps(manifest, indent=2) + "\n")
PY

echo "package-artifacts: ok"
