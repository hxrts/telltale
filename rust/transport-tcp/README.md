# rumpsteak-transport-tcp

TCP transport implementation for the Rumpsteak session types library.

## Overview

This crate provides a production-ready TCP transport that implements the `Transport` trait from `rumpsteak-aura-choreography`. It enables session-typed protocols to communicate over TCP between separate processes or machines.

## Features

- **Length-prefixed framing**: Reliable message boundaries over TCP streams
- **Automatic retry**: Configurable connection retry with exponential backoff
- **Role-based routing**: Each role has a unique address
- **Tracing integration**: Built-in observability with the `tracing` crate
- **Graceful shutdown**: Clean connection teardown

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
rumpsteak-transport-tcp = "0.7"
rumpsteak-aura-choreography = "0.7"
tokio = { version = "1", features = ["full"] }
```

## Usage

### Basic Example

```rust
use rumpsteak_transport_tcp::{TcpTransport, TcpTransportConfig};
use rumpsteak_aura_choreography::Transport;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Configure Alice's transport
    let config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
        .with_peer("Bob", "127.0.0.1:8081");

    // Create and start
    let transport = TcpTransport::new(config);
    transport.start().await?;

    // Connect to Bob
    transport.connect_to("Bob").await?;

    // Use the Transport trait
    transport.send("Bob", b"Hello, Bob!".to_vec()).await?;
    let response = transport.recv("Bob").await?;

    println!("Received: {:?}", String::from_utf8_lossy(&response));

    transport.close().await?;
    Ok(())
}
```

### Configuration from Environment

```rust
use rumpsteak_transport_tcp::TcpTransportConfig;

// Reads from environment variables:
// - ROLE: Role name
// - LISTEN_ADDR: Address to listen on
// - PEER_BOB: Address for Bob
// - PEER_CAROL: Address for Carol
let config = TcpTransportConfig::from_env()?;
```

### Custom Retry Configuration

```rust
use rumpsteak_transport_tcp::{TcpTransportConfig, config::RetryConfig};
use std::time::Duration;

let config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
    .with_peer("Bob", "127.0.0.1:8081")
    .with_retry(RetryConfig {
        max_attempts: 10,
        initial_delay: Duration::from_millis(50),
        max_delay: Duration::from_secs(30),
        backoff_multiplier: 1.5,
    });
```

## Multi-Process Deployment

For production deployments where each role runs in a separate process:

```bash
# Terminal 1: Run Alice
export ROLE=Alice
export LISTEN_ADDR=127.0.0.1:8080
export PEER_BOB=127.0.0.1:8081
cargo run --bin my_protocol

# Terminal 2: Run Bob
export ROLE=Bob
export LISTEN_ADDR=127.0.0.1:8081
export PEER_ALICE=127.0.0.1:8080
cargo run --bin my_protocol
```

## Message Framing

All messages are framed with a 4-byte big-endian length prefix:

```
+------------------+-------------------+
| Length (4 bytes) | Payload (N bytes) |
| Big-endian u32   |                   |
+------------------+-------------------+
```

## Connection Handshake

When a connection is established:
1. The connecting peer sends its role name (length-prefixed)
2. The accepting peer reads the role name
3. Both sides can now route messages by role

## License

MIT OR Apache-2.0
