#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

tmp_root="${TMPDIR:-/tmp}"
if [[ ! -d "${tmp_root}" ]]; then
  export TMPDIR="/tmp"
fi

source "${ROOT_DIR}/scripts/lib/release-packages.sh"

workspace_version="$(awk '
  /^\[package\]/ { in_package = 1; next }
  /^\[/ { in_package = 0 }
  in_package && $1 == "version" {
    gsub(/ /, "", $0)
    sub(/^version="/, "", $0)
    sub(/"$/, "", $0)
    print $0
    exit
  }
' Cargo.toml)"

tmpdir="$(mktemp -d)"
trap 'rm -rf "${tmpdir}"' EXIT
fakebin="${tmpdir}/bin"
mkdir -p "${fakebin}"

published_file="${tmpdir}/published.txt"
publish_log="${tmpdir}/publish.log"
touch "${published_file}" "${publish_log}"

cat > "${fakebin}/cargo" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail

published_file="${TELLTALE_FAKE_PUBLISHED_FILE:?}"
publish_log="${TELLTALE_FAKE_PUBLISH_LOG:?}"
version="${TELLTALE_FAKE_VERSION:?}"
fail_pkg="${TELLTALE_FAKE_FAIL_PACKAGE:-}"
fail_marker="${TELLTALE_FAKE_FAIL_MARKER:?}"

cmd="${1:-}"
shift || true

case "${cmd}" in
  search)
    package="${1:-}"
    if grep -qx "${package}" "${published_file}"; then
      echo "${package} = \"${version}\" # fake-index"
    else
      echo "${package} = \"0.0.0\" # fake-index"
    fi
    ;;
  publish)
    package=""
    while [[ "$#" -gt 0 ]]; do
      case "$1" in
        -p)
          package="$2"
          shift 2
          ;;
        *)
          shift
          ;;
      esac
    done
    [[ -n "${package}" ]] || {
      echo "fake cargo publish missing -p <package>" >&2
      exit 2
    }
    echo "${package}" >> "${publish_log}"
    if [[ -n "${fail_pkg}" && "${package}" == "${fail_pkg}" && ! -f "${fail_marker}" ]]; then
      touch "${fail_marker}"
      echo "simulated publish failure for ${package}" >&2
      exit 1
    fi
    if ! grep -qx "${package}" "${published_file}"; then
      echo "${package}" >> "${published_file}"
    fi
    ;;
  *)
    echo "unexpected fake cargo command: ${cmd}" >&2
    exit 2
    ;;
esac
EOF

cat > "${fakebin}/git" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail

cmd="${1:-}"
shift || true

case "${cmd}" in
  diff)
    exit 0
    ;;
  status)
    exit 0
    ;;
  rev-parse)
    if [[ "${1:-}" == "--abbrev-ref" ]]; then
      echo "main"
    else
      echo "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
    fi
    ;;
  *)
    echo "unexpected fake git command: ${cmd}" >&2
    exit 2
    ;;
esac
EOF

cat > "${fakebin}/just" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
echo "unexpected just invocation during release recovery test" >&2
exit 2
EOF

chmod +x "${fakebin}/cargo" "${fakebin}/git" "${fakebin}/just"

release_cmd=(
  ./scripts/ops/release.sh
  --version "${workspace_version}"
  --skip-ci
  --no-tag
  --allow-dirty
  --no-require-main
)

fail_package="telltale-runtime"
fail_marker="${tmpdir}/fail-once.marker"

echo "== simulate partial release failure =="
if env \
  PATH="${fakebin}:${PATH}" \
  CARGO_REGISTRY_TOKEN="fake-token" \
  TELLTALE_FAKE_PUBLISHED_FILE="${published_file}" \
  TELLTALE_FAKE_PUBLISH_LOG="${publish_log}" \
  TELLTALE_FAKE_VERSION="${workspace_version}" \
  TELLTALE_FAKE_FAIL_PACKAGE="${fail_package}" \
  TELLTALE_FAKE_FAIL_MARKER="${fail_marker}" \
  "${release_cmd[@]}"; then
  echo "error: expected first release run to fail on ${fail_package}" >&2
  exit 1
fi

grep -qx "telltale" "${published_file}" || {
  echo "error: expected earlier packages to be published before simulated failure" >&2
  exit 1
}
if grep -qx "${fail_package}" "${published_file}"; then
  echo "error: failed package ${fail_package} should not be marked published after first run" >&2
  exit 1
fi

echo "== simulate release resume =="
env \
  PATH="${fakebin}:${PATH}" \
  CARGO_REGISTRY_TOKEN="fake-token" \
  TELLTALE_FAKE_PUBLISHED_FILE="${published_file}" \
  TELLTALE_FAKE_PUBLISH_LOG="${publish_log}" \
  TELLTALE_FAKE_VERSION="${workspace_version}" \
  TELLTALE_FAKE_FAIL_PACKAGE="" \
  TELLTALE_FAKE_FAIL_MARKER="${fail_marker}" \
  "${release_cmd[@]}"

for package in "${RELEASE_PACKAGES[@]}"; do
  grep -qx "${package}" "${published_file}" || {
    echo "error: resumed release never published ${package}" >&2
    exit 1
  }
done

for package in "${RELEASE_PACKAGES[@]}"; do
  count="$(grep -cx "${package}" "${publish_log}" || true)"
  if [[ "${package}" == "${fail_package}" ]]; then
    [[ "${count}" -eq 2 ]] || {
      echo "error: expected failed package ${package} to be attempted twice, saw ${count}" >&2
      exit 1
    }
  else
    [[ "${count}" -eq 1 ]] || {
      echo "error: expected package ${package} to be published once across resume, saw ${count}" >&2
      exit 1
    }
  fi
done

echo "release-recovery: ok"
