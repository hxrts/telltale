# WASM Ping-Pong Example

A minimal example demonstrating Telltale's `tell!`-based choreographic programming in WebAssembly.

## Overview

This example implements a simple two-party protocol where:
- Alice sends a "Ping" message to Bob
- Bob receives the Ping and responds with a "Pong" message

The protocol is declared with `tell!` and executed through the generated session types.

## Quick Start

Build and run the example:

```bash
cd examples/wasm-ping-pong
./build.sh
```

This script will:
1. Check for required tools (`wasm-pack` 0.14.0)
2. Build the WASM module
3. Generate an interactive HTML demo
4. Provide instructions for running

## Manual Building

To build for WASM manually:

```bash
# Install wasm-pack if not already installed
cargo install wasm-pack --version 0.14.0 --locked

# Build the WASM module
cd examples/wasm-ping-pong
wasm-pack build --target web
```

## Running Tests

Run WASM tests under Node:

```bash
cd ../..
just wasm-test
```

## Running

Create an `index.html` file to test in the browser:

```html
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>Telltale WASM Ping-Pong</title>
</head>
<body>
    <h1>Telltale WASM Example</h1>
    <button id="run">Run Ping-Pong Protocol</button>
    <pre id="output"></pre>
    
    <script type="module">
        import init, { run_ping_pong } from './pkg/wasm_ping_pong.js';
        
        async function runProtocol() {
            await init();
            
            const output = document.getElementById('output');
            output.textContent = 'Running protocol...\n';
            
            try {
                const result = await run_ping_pong("Hello from Alice!");
                output.textContent += `Alice sent: ${result.sent_ping}\n`;
                output.textContent += `Bob received: ${result.received_ping}\n`;
                output.textContent += `Bob sent: ${result.sent_pong}\n`;
                output.textContent += `Alice received: ${result.received_pong}\n`;
                
                output.textContent += '\nProtocol completed successfully!';
            } catch (e) {
                output.textContent += `\nError: ${e}`;
            }
        }
        
        document.getElementById('run').addEventListener('click', runProtocol);
    </script>
</body>
</html>
```

Then serve the directory with a local HTTP server:

```bash
python3 -m http.server
# Open http://localhost:8000 in your browser
```

## Limitations

- This example uses the generated in-memory session wiring from `Roles::default()`
- For real distributed WASM applications, you'd plug the same protocol into a browser transport
- WASM is single-threaded, so host execution remains constrained by the browser runtime
