#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PORT="${PORT:-8000}"
DEFAULT_MESSAGE="Hello from the browser!"

info() {
    printf '[wasm harness] %s\n' "$*"
}

fail() {
    printf '[wasm harness] error: %s\n' "$*" >&2
    exit 1
}

require_tool() {
    local tool="$1"
    command -v "$tool" >/dev/null 2>&1 || fail "missing required tool: $tool"
}

usage() {
    cat <<'EOF'
Usage:
  ./harness.sh build
  ./harness.sh smoke [message]
  ./harness.sh serve [port]
  ./harness.sh run [port] [message]
  ./harness.sh help

Commands:
  build   Build the browser package into examples/wasm/pkg.
  smoke   Deterministically exercise run_ping_pong() through nodejs bindings.
  serve   Build the browser package and serve the example over HTTP.
  run     Build, run the node smoke check, then serve the browser demo.

Notes:
  - The script always runs from examples/wasm, regardless of the current shell cwd.
  - Use PORT=NNNN or pass an explicit port to serve/run.
EOF
}

build_web() {
    require_tool wasm-pack
    info "building web package"
    (
        cd "$SCRIPT_DIR"
        wasm-pack build --target web --dev
    )
}

smoke_node() {
    require_tool wasm-pack
    require_tool node

    local message="${1:-$DEFAULT_MESSAGE}"
    local tmp_root
    tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/telltale-wasm-smoke.XXXXXX")"

    cat >"$tmp_root/smoke.cjs" <<'EOF'
const assert = require('node:assert/strict');
const { init, run_ping_pong } = require('./pkg/wasm_examples.js');

init();

(async () => {
  const expected = process.argv[2];
  const result = await run_ping_pong(expected);

  assert.equal(result.sent_ping, expected, 'alice should send the input message');
  assert.equal(result.received_ping, expected, 'bob should receive the sent message');
  assert.equal(result.sent_pong, `Pong for: ${expected}`, 'bob should derive pong from the effect boundary');
  assert.equal(result.received_pong, `Pong for: ${expected}`, 'alice should receive the generated pong');

  console.log(JSON.stringify(result));
})().catch((error) => {
  console.error(error);
  process.exit(1);
});
EOF

    (
        trap 'rm -rf "$tmp_root"' EXIT

        info "building nodejs package for deterministic smoke run"
        (
            cd "$SCRIPT_DIR"
            wasm-pack build --target nodejs --dev --out-dir "$tmp_root/pkg" >/dev/null
        )

        info "running node smoke check"
        node "$tmp_root/smoke.cjs" "$message"
    )
}

start_server() {
    require_tool python3

    local port="${1:-$PORT}"

    info "serving demo from $SCRIPT_DIR"
    info "open http://127.0.0.1:${port}"
    (
        cd "$SCRIPT_DIR"
        exec python3 -m http.server "$port" --bind 127.0.0.1
    )
}

run_demo() {
    local port="${1:-$PORT}"
    local message="${2:-$DEFAULT_MESSAGE}"

    build_web
    smoke_node "$message"
    info "browser demo verified via node smoke run"
    start_server "$port"
}

command_name="${1:-run}"

case "$command_name" in
    build)
        build_web
        ;;
    smoke)
        smoke_node "${2:-$DEFAULT_MESSAGE}"
        ;;
    serve)
        build_web
        start_server "${2:-$PORT}"
        ;;
    run)
        run_demo "${2:-$PORT}" "${3:-$DEFAULT_MESSAGE}"
        ;;
    help|-h|--help)
        usage
        ;;
    *)
        usage
        fail "unknown command: $command_name"
        ;;
esac
