#!/usr/bin/env bash
# Build script for WASM ping-pong example
#
# This script builds the Telltale WASM example and prepares it for browser deployment.

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${GREEN}Building Telltale WASM Ping-Pong Example${NC}"
echo "=========================================="

# Check if wasm-pack is installed
if ! command -v wasm-pack &> /dev/null; then
    echo -e "${RED}Error: wasm-pack is not installed${NC}"
    echo "Install it with: cargo install wasm-pack"
    echo "Or visit: https://rustwasm.github.io/wasm-pack/installer/"
    exit 1
fi

# Check if we're in the right directory
if [ ! -f "Cargo.toml" ]; then
    echo -e "${RED}Error: Cargo.toml not found${NC}"
    echo "Please run this script from the examples/wasm-ping-pong directory"
    exit 1
fi

echo -e "\n${YELLOW}Step 1: Building WASM module...${NC}"
wasm-pack build --target web --dev

echo -e "\n${YELLOW}Step 2: Creating demo HTML...${NC}"
cat > index.html << 'EOF'
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>Telltale WASM Ping-Pong Demo</title>
    <style>
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            max-width: 800px;
            margin: 50px auto;
            padding: 20px;
            background: #f5f5f5;
        }
        .container {
            background: white;
            padding: 30px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        h1 {
            color: #333;
            margin-top: 0;
        }
        .description {
            color: #666;
            margin-bottom: 20px;
            line-height: 1.6;
        }
        button {
            background: #4CAF50;
            color: white;
            border: none;
            padding: 12px 24px;
            font-size: 16px;
            border-radius: 4px;
            cursor: pointer;
            transition: background 0.3s;
        }
        button:hover {
            background: #45a049;
        }
        button:disabled {
            background: #ccc;
            cursor: not-allowed;
        }
        input {
            padding: 10px;
            font-size: 14px;
            border: 1px solid #ddd;
            border-radius: 4px;
            width: 300px;
            margin-right: 10px;
        }
        pre {
            background: #f9f9f9;
            padding: 15px;
            border-radius: 4px;
            border-left: 4px solid #4CAF50;
            overflow-x: auto;
            white-space: pre-wrap;
            word-wrap: break-word;
        }
        .output {
            margin-top: 20px;
        }
        .error {
            color: #d32f2f;
            background: #ffebee;
            padding: 10px;
            border-radius: 4px;
            margin-top: 10px;
        }
        .success {
            color: #388e3c;
            background: #e8f5e9;
            padding: 10px;
            border-radius: 4px;
            margin-top: 10px;
        }
        .controls {
            margin: 20px 0;
        }
    </style>
</head>
<body>
    <div class="container">
        <h1>Telltale WASM Demo</h1>
        <div class="description">
            <p>This demo showcases Telltale's choreographic programming running in WebAssembly.</p>
            <p>The protocol implements a simple two-party interaction where Alice sends a message to Bob,
            and Bob responds. All communication happens through in-memory channels, demonstrating
            that Telltale's session types work correctly in the browser.</p>
        </div>

        <div class="controls">
            <input type="text" id="messageInput" placeholder="Enter message for Alice to send" value="Hello from the browser!">
            <button id="runButton">Run Protocol</button>
        </div>

        <div class="output">
            <h3>Output:</h3>
            <pre id="output">Click 'Run Protocol' to start...</pre>
        </div>
    </div>

    <script type="module">
        import init, { run_alice, run_bob } from './pkg/wasm_ping_pong.js';

        const output = document.getElementById('output');
        const runButton = document.getElementById('runButton');
        const messageInput = document.getElementById('messageInput');

        function log(message, type = 'info') {
            const timestamp = new Date().toLocaleTimeString();
            output.textContent += `[${timestamp}] ${message}\n`;
        }

        function clearOutput() {
            output.textContent = '';
        }

        async function runProtocol() {
            clearOutput();
            runButton.disabled = true;

            try {
                const message = messageInput.value || "Hello from the browser!";
                log('Starting protocol execution...', 'info');
                log(`Alice will send: "${message}"`);

                // Note: In a real application, Alice and Bob would run in separate contexts
                // For this demo, we're running them sequentially to show the concept

                log('Running Alice\'s protocol...');
                const aliceResult = await run_alice(message);
                log(`Alice received response: "${aliceResult}"`);

                log('Running Bob\'s protocol...');
                const bobResult = await run_bob();
                log(`Bob received: "${bobResult}"`);

                log('');
                log('Protocol completed successfully!');
                log('');
                log('This demonstrates:');
                log('  • Session types working in WASM');
                log('  • Effect handlers in the browser');
                log('  • Type-safe message passing');
                log('  • Choreographic programming');

            } catch (error) {
                log(`Error: ${error}`, 'error');
                console.error(error);
            } finally {
                runButton.disabled = false;
            }
        }

        async function initialize() {
            try {
                await init();
                log('WASM module loaded successfully');
                log('Ready to run protocol!\n');
                runButton.addEventListener('click', runProtocol);
            } catch (error) {
                output.textContent = `Failed to initialize WASM module: ${error}`;
                console.error(error);
            }
        }

        initialize();
    </script>
</body>
</html>
EOF

echo -e "\n${GREEN}Build complete!${NC}"
echo -e "\nTo test the example:"
echo -e "  1. Start a local server:"
echo -e "     ${YELLOW}python3 -m http.server 8000${NC}"
echo -e "  2. Open your browser to:"
echo -e "     ${YELLOW}http://localhost:8000${NC}"
echo -e "\n${GREEN}Have fun with WASM session types!${NC}"
