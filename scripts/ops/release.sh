#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

RELEASE_PACKAGES=(
  "telltale-macros"
  "telltale-types"
  "telltale-theory"
  "telltale"
  "telltale-choreography"
  "telltale-transport"
  "telltale-vm"
  "telltale-lean-bridge"
  "telltale-simulator"
)

DRY_RUN=0
SKIP_CI=0
CREATE_TAG=1
PUSH=0
ALLOW_DIRTY=0
REQUIRE_MAIN=1
VERSION=""
TAG_PREFIX="v"
TAG_NAME=""

usage() {
  cat <<'EOF'
Usage:
  ./scripts/ops/release.sh --version <version> [options]

Options:
  --version <version>   Release version (defaults to workspace version if omitted)
  --dry-run             Run all publishing steps with --dry-run
  --skip-ci             Skip just ci-dry-run preflight checks
  --no-tag              Skip git tag creation
  --push                Push current branch and tag after successful publish
  --allow-dirty         Allow a dirty git working tree
  --no-require-main      Allow releasing from non-main branches
  -h, --help            Show this help text
EOF
}

die() {
  echo "error: $*" >&2
  exit 1
}

require_command() {
  local cmd="$1"
  command -v "${cmd}" >/dev/null 2>&1 || die "${cmd} is required"
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

manifest_path() {
  local crate="$1"
  case "${crate}" in
    telltale-macros) echo "rust/macros/Cargo.toml" ;;
    telltale-types) echo "rust/types/Cargo.toml" ;;
    telltale-theory) echo "rust/theory/Cargo.toml" ;;
    telltale) echo "Cargo.toml" ;;
    telltale-choreography) echo "rust/choreography/Cargo.toml" ;;
    telltale-transport) echo "rust/transport/Cargo.toml" ;;
    telltale-vm) echo "rust/vm/Cargo.toml" ;;
    telltale-lean-bridge) echo "rust/lean-bridge/Cargo.toml" ;;
    telltale-simulator) echo "rust/simulator/Cargo.toml" ;;
    *) return 1 ;;
  esac
}

assert_version_format() {
  local version="$1"
  if [[ ! "${version}" =~ ^[0-9]+\.[0-9]+\.[0-9]+([.-][0-9A-Za-z.-]+)?$ ]]; then
    die "invalid release version '${version}'"
  fi
}

assert_clean_tree() {
  if [[ "${ALLOW_DIRTY}" -eq 1 ]]; then
    return
  fi
  if ! git diff --quiet || ! git diff --cached --quiet; then
    git status --short
    die "working tree is not clean. Use --allow-dirty if intentional"
  fi
}

assert_branch() {
  local branch
  branch="$(git rev-parse --abbrev-ref HEAD)"
  if [[ "${branch}" == "HEAD" ]]; then
    die "refusing to release from detached HEAD"
  fi
  if [[ "${REQUIRE_MAIN}" -eq 1 && "${branch}" != "main" ]]; then
    die "releases must be run from main unless --no-require-main is passed"
  fi
}

assert_versions_match() {
  local package="$1"
  local package_manifest_path
  local package_version
  package_manifest_path="$(manifest_path "${package}")" || die "unknown package: ${package}"
  package_version="$(extract_manifest_version "${package_manifest_path}")"
  if [[ -z "${package_version}" ]]; then
    die "unable to read version for ${package} from ${package_manifest_path}"
  fi
  if [[ "${package_version}" != "${VERSION}" ]]; then
    die "version mismatch for ${package}: ${package_version} != ${VERSION}"
  fi
}

run_ci_dry_run() {
  echo "== running preflight: just ci-dry-run =="
  just ci-dry-run
}

publish_package() {
  local package="$1"
  local cmd
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    cmd=(cargo publish -p "${package}" --dry-run --locked)
  else
    cmd=(cargo publish -p "${package}" --locked)
  fi
  if [[ "${ALLOW_DIRTY}" -eq 1 ]]; then
    cmd+=(--allow-dirty)
  fi
  echo "== ${cmd[*]} =="
  "${cmd[@]}"
}

create_release_tag() {
  if [[ "${CREATE_TAG}" -eq 0 ]]; then
    return
  fi
  TAG_NAME="${TAG_PREFIX}${VERSION}"
  if git rev-parse "${TAG_NAME}" >/dev/null 2>&1; then
    local existing_commit current_commit
    existing_commit="$(git rev-parse "${TAG_NAME}")"
    current_commit="$(git rev-parse HEAD)"
    if [[ "${existing_commit}" == "${current_commit}" ]]; then
      echo "== tag ${TAG_NAME} already exists and points to HEAD; reusing =="
      return
    fi
    die "tag ${TAG_NAME} already exists at ${existing_commit}, expected ${current_commit}"
  fi
  git tag -a "${TAG_NAME}" -m "Release ${TAG_NAME}"
  echo "== created git tag ${TAG_NAME} =="
}

push_git_refs() {
  if [[ "${PUSH}" -eq 0 ]]; then
    return
  fi
  local branch
  branch="$(git rev-parse --abbrev-ref HEAD)"
  echo "== pushing branch ${branch} =="
  git push origin "${branch}"
  if [[ -n "${TAG_NAME}" ]]; then
    echo "== pushing tag ${TAG_NAME} =="
    git push origin "${TAG_NAME}"
  fi
}

main() {
  require_command cargo
  require_command git

  while [[ "$#" -gt 0 ]]; do
    case "$1" in
      --version)
        if [[ "$#" -lt 2 ]]; then
          die "--version requires a value"
        fi
        VERSION="$2"
        shift 2
        ;;
      --version=*)
        VERSION="${1#*=}"
        shift
        ;;
      --dry-run)
        DRY_RUN=1
        shift
        ;;
      --skip-ci)
        SKIP_CI=1
        shift
        ;;
      --no-tag)
        CREATE_TAG=0
        shift
        ;;
      --push)
        PUSH=1
        shift
        ;;
      --allow-dirty)
        ALLOW_DIRTY=1
        shift
        ;;
      --no-require-main)
        REQUIRE_MAIN=0
        shift
        ;;
      -h|--help)
        usage
        exit 0
        ;;
      *)
        die "unknown argument: $1"
        ;;
    esac
  done

  if [[ -z "${VERSION}" ]]; then
    VERSION="$(extract_manifest_version "${ROOT_DIR}/Cargo.toml")"
  fi
  assert_version_format "${VERSION}"

  assert_branch
  assert_clean_tree

  for package in "${RELEASE_PACKAGES[@]}"; do
    echo "== validating version for ${package} =="
    assert_versions_match "${package}"
  done

  if [[ "${DRY_RUN}" -eq 0 && "${CARGO_REGISTRY_TOKEN:-}" == "" ]]; then
    die "CARGO_REGISTRY_TOKEN is not set; publishing will fail"
  fi

  if [[ "${SKIP_CI}" -eq 0 ]]; then
    require_command just
    run_ci_dry_run
  else
    echo "== skipping preflight checks =="
  fi

  for package in "${RELEASE_PACKAGES[@]}"; do
    publish_package "${package}"
  done

  create_release_tag
  push_git_refs

  echo "== release completed for ${VERSION} =="
}

main "$@"
