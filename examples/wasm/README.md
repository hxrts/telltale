# WASM Example

A minimal `tell!`-based ping-pong protocol compiled to WebAssembly.

## Overview

The example keeps protocol structure in the DSL and host impurity at the generated effect boundary:

- Alice sends `Ping(String)` to Bob.
- Bob uses the generated `BrowserRuntime` effect to derive a reply.
- Bob sends `Pong(String)` back to Alice.

The exported `run_ping_pong()` function executes the generated sessions and returns the observed round trip.

## Prerequisites

- `wasm-pack` 0.14.0
- `node`
- `python3`

Install `wasm-pack` if needed:

```bash
cargo install wasm-pack --version 0.14.0 --locked
```

## Quick Start

Build the browser package, run a deterministic smoke check through Node, then serve the demo:

```bash
cd examples/wasm
./harness.sh run
```

That command:

1. builds `pkg/` with `wasm-pack build --target web --dev`
2. builds a temporary `nodejs` package and executes `run_ping_pong()` end to end
3. serves the example at `http://127.0.0.1:8000`

## Harness Commands

Build only:

```bash
./harness.sh build
```

Run the deterministic smoke check only:

```bash
./harness.sh smoke
./harness.sh smoke "Hello from Alice!"
```

Serve the browser demo on a custom port:

```bash
./harness.sh serve 4173
./harness.sh run 4173 "Hello from Alice!"
```

The smoke check is the most reliable local validation path because it exercises the generated WASM bindings without depending on a browser driver.

## Browser Tests

The crate includes browser-only `wasm-bindgen-test` tests in [src/ping_pong.rs](src/ping_pong.rs). They do not run under the repository's `just wasm-test` Node lane.

Run them with a browser driver when available, for example:

```bash
cd examples/wasm
wasm-pack test --headless --chrome
```

## Repository Commands

From the repository root:

```bash
just wasm-build
just wasm-test
```

- `just wasm-build` builds the browser package for this example.
- `just wasm-test` runs the repository-managed Node WASM test lane; for this crate it validates compilation but skips the browser-only tests.

## Limitations

- The demo uses in-memory generated session wiring via `Roles::default()`.
- Real browser deployments should replace the in-memory path with a transport-backed session integration.
- WASM remains single-threaded, so concurrency is constrained by the host runtime.
