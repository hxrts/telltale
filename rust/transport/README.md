# rumpsteak-transport

Production transport implementations for the Rumpsteak session types library.

## Overview

This crate provides production-ready transport implementations that implement the `Transport` trait from `rumpsteak-aura-choreography`. It enables session-typed protocols to communicate over TCP between separate processes or machines.

## Features

- **TCP transport**: Length-prefixed framing for reliable message boundaries
- **IPv4 and IPv6 support**: Full dual-stack networking capability
- **Environment resolver**: Endpoint discovery via environment variables
- **Transport factory**: Factory pattern for easy transport instantiation
- **Automatic retry**: Configurable connection retry with exponential backoff
- **Role-based routing**: Each role has a unique address
- **Tracing integration**: Built-in observability with the `tracing` crate
- **Graceful shutdown**: Clean connection teardown

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
rumpsteak-transport = "*"
rumpsteak-aura-choreography = "*"
tokio = { version = "1", features = ["full"] }
```

## Usage

### Direct Configuration

```rust
use rumpsteak_transport::{TcpTransport, TcpTransportConfig, Message, Transport};
use rumpsteak_aura_choreography::RoleName;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Configure Alice's transport
    let config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
        .with_peer("Bob", "127.0.0.1:8081");

    // Create and start
    let transport = TcpTransport::new(config);
    transport.start().await?;

    // Connect to Bob
    let bob = RoleName::from_static("Bob");
    transport.connect_to(bob.as_str()).await?;

    // Use the Transport trait with Message type
    let msg = Message::new(b"Hello, Bob!".to_vec())?;
    transport.send(&bob, msg).await?;
    let response = transport.recv(&bob).await?;

    println!("Received: {:?}", String::from_utf8_lossy(response.as_bytes()));

    transport.close().await?;
    Ok(())
}
```

### Using Factory with Environment Resolver

The `EnvResolver` discovers endpoints from environment variables:

```rust
use rumpsteak_transport::{EnvResolver, TcpTransportFactory, TcpTransportConfig};
use rumpsteak_aura_choreography::{TransportFactory, RoleName};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Set environment variables:
    //   RUMPSTEAK_ALICE_ENDPOINT=127.0.0.1:8080
    //   RUMPSTEAK_BOB_ENDPOINT=127.0.0.1:8081

    let resolver = EnvResolver::with_default_prefix();
    let config = TcpTransportConfig::default();
    let factory = TcpTransportFactory::new(resolver, config);

    // Create transport for Alice
    let transport = factory.create(&RoleName::from_static("Alice")).await?;

    Ok(())
}
```

### Custom Environment Prefix

```rust
use rumpsteak_transport::EnvResolver;

// Use custom prefix: MYAPP_ALICE_ENDPOINT, MYAPP_BOB_ENDPOINT, etc.
let resolver = EnvResolver::new("MYAPP")?;
```

### Legacy Configuration from Environment

```rust
use rumpsteak_transport::TcpTransportConfig;

// Reads from environment variables:
// - ROLE: Role name
// - LISTEN_ADDR: Address to listen on
// - PEER_BOB: Address for Bob
// - PEER_CAROL: Address for Carol
let config = TcpTransportConfig::from_env()?;
```

### Custom Retry Configuration

```rust
use rumpsteak_transport::{TcpTransportConfig, RetryConfig};
use std::time::Duration;

let retry = RetryConfig {
    max_attempts: 10,
    initial_delay: Duration::from_millis(200),
    max_delay: Duration::from_secs(30),
    backoff_multiplier: 2.0,
};

let config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
    .with_peer("Bob", "127.0.0.1:8081")
    .with_retry(retry);
```

## IPv6 Support

The transport supports both IPv4 and IPv6 addresses. Use bracket notation for IPv6:

### IPv6 Configuration

```rust
use rumpsteak_transport::TcpTransportConfig;

// IPv6 loopback
let config = TcpTransportConfig::new("Server", "[::1]:8080")
    .with_peer("Client", "[::1]:8081");

// IPv6 any address (dual-stack on most platforms)
let dual_stack = TcpTransportConfig::new("Server", "[::]:8080");

// Full IPv6 addresses
let production = TcpTransportConfig::new("Server", "[2001:db8::1]:8080")
    .with_peer("Client", "[2001:db8::2]:8081");
```

### Mixed IPv4/IPv6 Peers

```rust
use rumpsteak_transport::TcpTransportConfig;

// Gateway connecting IPv4 and IPv6 peers
let config = TcpTransportConfig::new("Gateway", "0.0.0.0:8080")
    .with_peer("LegacyService", "192.168.1.100:8081")
    .with_peer("ModernService", "[2001:db8::1]:8082");
```

### IPv6 Environment Variables

```bash
# IPv6 loopback
export RUMPSTEAK_ALICE_ENDPOINT=[::1]:8080

# Full IPv6 address
export RUMPSTEAK_BOB_ENDPOINT=[2001:db8::1]:8081

# Dual-stack binding
export RUMPSTEAK_SERVER_ENDPOINT=[::]:3000
```

## Multi-Process Deployment

For production deployments where each role runs in a separate process:

```bash
# Terminal 1: Run Alice
export RUMPSTEAK_ALICE_ENDPOINT=127.0.0.1:8080
export RUMPSTEAK_BOB_ENDPOINT=127.0.0.1:8081
cargo run --bin my_protocol -- --role Alice

# Terminal 2: Run Bob
export RUMPSTEAK_ALICE_ENDPOINT=127.0.0.1:8080
export RUMPSTEAK_BOB_ENDPOINT=127.0.0.1:8081
cargo run --bin my_protocol -- --role Bob
```

## Message Type

Messages use the `Message` type from `rumpsteak-aura-choreography` which validates size limits:

```rust
use rumpsteak_transport::Message;

// Create a message (validates size)
let msg = Message::new(b"Hello".to_vec())?;

// Access bytes
let bytes: &[u8] = msg.as_bytes();
let owned: Vec<u8> = msg.into_bytes();
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
