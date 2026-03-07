# telltale-transport

TCP transport implementations for the Telltale session types runtime.

## Overview

`telltale-transport` provides a TCP implementation of the `Transport` interface from `telltale-choreography`. It is intended for multi-process and multi-host deployments where roles communicate over network sockets. The crate includes endpoint resolution from environment variables and a factory API for runtime construction.

## Features

The transport uses length-prefixed message framing, role-addressed routing, and retry with exponential backoff. It supports IPv4 and IPv6 endpoints. It also provides `EnvResolver` and `TcpTransportFactory` for environment-driven configuration.

## Installation

Add these dependencies to `Cargo.toml`.

```toml
[dependencies]
telltale-transport = "3.0.0"
telltale-choreography = "3.0.0"
tokio = { version = "1", features = ["full"] }
```

This configuration gives access to the transport types, role identifiers, and Tokio runtime support used by the examples below.

## Usage

### Direct Configuration

```rust,no_run
use telltale_choreography::RoleName;
use telltale_transport::{TcpTransport, TcpTransportConfig, Transport};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
        .with_peer("Bob", "127.0.0.1:8081");

    let transport = TcpTransport::new(config);
    transport.start().await?;

    let bob = RoleName::from_static("Bob");
    transport.connect_to(bob.as_str()).await?;

    transport.send(&bob, b"Hello, Bob!".to_vec()).await?;
    let response = transport.recv(&bob).await?;

    println!("Received: {}", String::from_utf8_lossy(&response));

    transport.close().await?;
    Ok(())
}
```

This example constructs a transport directly, starts its listener, connects to a peer, and uses `send` and `recv` with raw byte payloads.

### Using Factory with Environment Resolver

The resolver reads endpoints from environment variables with the shape `{PREFIX}_{ROLE}_ENDPOINT`.

```bash
export TELLTALE_ALICE_ENDPOINT=127.0.0.1:8080
export TELLTALE_BOB_ENDPOINT=127.0.0.1:8081
```

These variables define role endpoints that the factory can resolve at runtime.

```rust,no_run
use telltale_choreography::RoleName;
use telltale_transport::{EnvResolver, TcpTransportConfig, TcpTransportFactory};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let resolver = EnvResolver::with_default_prefix();
    let base_config = TcpTransportConfig::default();
    let factory = TcpTransportFactory::new(resolver, base_config);

    let transport = factory.create(&RoleName::from_static("Alice")).await?;
    transport.close().await?;

    Ok(())
}
```

This flow is useful when role endpoints are injected by deployment tooling instead of hardcoded in application code.

### Custom Environment Prefix

```rust
use telltale_transport::EnvResolver;

let resolver = EnvResolver::new("MYAPP")?;
```

This produces variable names such as `MYAPP_ALICE_ENDPOINT` and `MYAPP_BOB_ENDPOINT`.

### Legacy Configuration from Environment

```rust
use telltale_transport::TcpTransportConfig;

// Reads from environment variables:
// - ROLE: Role name
// - LISTEN_ADDR: Address to listen on
// - PEER_BOB: Address for Bob
// - PEER_CAROL: Address for Carol
let config = TcpTransportConfig::from_env()?;
```

This entry point supports existing deployments that already use the `ROLE`, `LISTEN_ADDR`, and `PEER_*` naming scheme.

### Custom Retry Configuration

```rust
use telltale_transport::{TcpTransportConfig, RetryConfig};
use telltale_types::FixedQ32;
use std::time::Duration;

let retry = RetryConfig {
    max_attempts: 10,
    initial_delay: Duration::from_millis(200),
    max_delay: Duration::from_secs(30),
    backoff_multiplier: FixedQ32::from_ratio(2, 1)
        .expect("ratio 2/1 must be representable"),
};

let config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
    .with_peer("Bob", "127.0.0.1:8081")
    .with_retry(retry);
```

The retry policy controls connection attempts in `connect_to` and `connect_all`, including exponential backoff behavior.

## IPv6 Support

Use bracket notation for IPv6 addresses.

```rust
use telltale_transport::TcpTransportConfig;

let config = TcpTransportConfig::new("Server", "[::1]:8080")
    .with_peer("Client", "[::1]:8081");

let dual_stack = TcpTransportConfig::new("Server", "[::]:8080");

let production = TcpTransportConfig::new("Server", "[2001:db8::1]:8080")
    .with_peer("Client", "[2001:db8::2]:8081");
```

This syntax is required for parser correctness when an endpoint contains multiple colons.

```bash
export TELLTALE_ALICE_ENDPOINT=[::1]:8080
export TELLTALE_BOB_ENDPOINT=[2001:db8::1]:8081
export TELLTALE_SERVER_ENDPOINT=[::]:3000
```

These values can be consumed by `EnvResolver` in the same way as IPv4 endpoints.

## Message Framing

All payloads are sent with a 4-byte big-endian length prefix.

```text
+------------------+-------------------+
| Length (4 bytes) | Payload (N bytes) |
| Big-endian u32   |                   |
+------------------+-------------------+
```

This framing preserves message boundaries over TCP streams and allows deterministic decoding on receive.

## Connection Handshake

On connection setup, the initiating peer sends its role name using the same length-prefix format. The receiving side validates this name and binds the socket to the corresponding role channel for routing.
