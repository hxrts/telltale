# WASM Ping-Pong Example

A minimal example demonstrating Telltale's choreographic programming in WebAssembly.

## Overview

This example implements a simple two-party protocol where:
- Alice sends a "Ping" message to Bob
- Bob receives the Ping and responds with a "Pong" message

The protocol uses Telltale's choreographic effect system with the `InMemoryHandler` for communication.

## Quick Start

Build and run the example:

```bash
cd examples/wasm-ping-pong
./build.sh
```

This script will:
1. Check for required tools (wasm-pack)
2. Build the WASM module
3. Generate an interactive HTML demo
4. Provide instructions for running

## Manual Building

To build for WASM manually:

```bash
# Install wasm-pack if not already installed
cargo install wasm-pack

# Build the WASM module
cd examples/wasm-ping-pong
wasm-pack build --target web
```

## Running Tests

Run WASM tests in a headless browser:

```bash
# Firefox (recommended)
wasm-pack test --headless --firefox

# Chrome
wasm-pack test --headless --chrome
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
        import init, { run_alice, run_bob } from './pkg/wasm_ping_pong.js';
        
        async function runProtocol() {
            await init();
            
            const output = document.getElementById('output');
            output.textContent = 'Running protocol...\n';
            
            try {
                // For demo purposes, we'll run these processes sequentially
                const aliceResult = await run_alice("Hello from Alice!");
                output.textContent += `Alice received: ${aliceResult}\n`;
                
                const bobResult = await run_bob();
                output.textContent += `Bob received: ${bobResult}\n`;
                
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

- Uses `InMemoryHandler` which works for single-context demos
- For real distributed WASM applications, you'd need a network transport (WebSockets, WebRTC, etc.)
- WASM is single-threaded, so parallel execution is limited
