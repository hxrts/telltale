# Composition Tutorial

This tutorial shows how to integrate rumpsteak-aura into your project and compose domain-specific choreographies using extensions.

## Prerequisites

- Rust 1.75 or later
- Basic understanding of [choreographic programming](01_getting_started.md)
- Familiarity with [effect handlers](06_rumpsteak_handler.md)

## Step 1: Add Dependencies

Add rumpsteak-aura to your `Cargo.toml`:

```toml
[dependencies]
rumpsteak-aura = "*"
rumpsteak-aura-choreography = "*"
rumpsteak-aura-choreography-macros = "*"

# For async runtime
tokio = { version = "1", features = ["full"] }
```

## Step 2: Define Your Domain Types

Create domain-specific types for your choreography:

```rust
// src/types.rs

use serde::{Deserialize, Serialize};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Role {
    Client,
    Server,
    Database,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AuthRequest {
    pub username: String,
    pub password: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AuthResponse {
    pub token: String,
    pub user_id: u64,
}
```

## Step 3: Create Domain Extensions

Define extensions for your domain needs:

```rust
// src/extensions.rs

use rumpsteak_aura_choreography::effects::*;
use std::any::{Any, TypeId};

#[derive(Clone, Debug)]
pub struct ValidateCapability {
    pub capability: String,
    pub role: Role,
}

impl ExtensionEffect for ValidateCapability {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "ValidateCapability"
    }

    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        // Role-specific extension - only this role participates
        vec![Box::new(self.role)]
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct LogEvent {
    pub message: String,
    pub level: LogLevel,
}

#[derive(Clone, Debug)]
pub enum LogLevel {
    Info,
    Warn,
    Error,
}

impl ExtensionEffect for LogEvent {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "LogEvent"
    }

    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        vec![]  // Global - all roles log
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect> {
        Box::new(self.clone())
    }
}
```

## Step 4: Create an Extensible Handler

Build a handler with extension support:

```rust
// src/handler.rs

use rumpsteak_aura_choreography::effects::*;
use crate::extensions::*;
use async_trait::async_trait;

pub struct DomainHandler {
    role: Role,
    registry: ExtensionRegistry<()>,
    capabilities: Vec<String>,
}

impl DomainHandler {
    pub fn new(role: Role, capabilities: Vec<String>) -> Self {
        let mut registry = ExtensionRegistry::new();

        // Register capability validation
        let caps = capabilities.clone();
        registry.register::<ValidateCapability, _>(move |_ep, ext| {
            let caps = caps.clone();
            Box::pin(async move {
                let validate = ext.as_any()
                    .downcast_ref::<ValidateCapability>()
                    .ok_or(ExtensionError::TypeMismatch {
                        expected: "ValidateCapability",
                        actual: ext.type_name(),
                    })?;

                if !caps.contains(&validate.capability) {
                    return Err(ExtensionError::ExecutionFailed {
                        type_name: "ValidateCapability",
                        error: format!(
                            "Missing capability: {}",
                            validate.capability
                        ),
                    });
                }

                println!("✓ Validated capability: {}", validate.capability);
                Ok(())
            })
        });

        // Register logging
        registry.register::<LogEvent, _>(|_ep, ext| {
            Box::pin(async move {
                let log = ext.as_any()
                    .downcast_ref::<LogEvent>()
                    .ok_or(ExtensionError::TypeMismatch {
                        expected: "LogEvent",
                        actual: ext.type_name(),
                    })?;

                println!("[{:?}] {}", log.level, log.message);
                Ok(())
            })
        });

        Self {
            role,
            registry,
            capabilities,
        }
    }
}

#[async_trait]
impl ExtensibleHandler for DomainHandler {
    type Endpoint = ();

    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint> {
        &self.registry
    }
}

#[async_trait]
impl ChoreoHandler for DomainHandler {
    type Role = Role;
    type Endpoint = ();

    async fn send<M: serde::Serialize + Send + Sync>(
        &mut self,
        _ep: &mut Self::Endpoint,
        to: Self::Role,
        msg: &M,
    ) -> Result<()> {
        println!("{:?} -> {:?}: sending message", self.role, to);
        Ok(())
    }

    async fn recv<M: serde::de::DeserializeOwned + Send>(
        &mut self,
        _ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> Result<M> {
        println!("{:?} <- {:?}: receiving message", self.role, from);
        Err(ChoreographyError::Transport(
            "recv not implemented in tutorial".into()
        ))
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        _who: Self::Role,
        label: Label,
    ) -> Result<()> {
        println!("{:?}: choosing {}", self.role, label.0);
        Ok(())
    }

    async fn offer(
        &mut self,
        _ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> Result<Label> {
        println!("{:?}: offering choice from {:?}", self.role, from);
        Ok(Label("default"))
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _at: Self::Role,
        _dur: std::time::Duration,
        body: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>> + Send,
    {
        body.await
    }
}
```

## Step 5: Build Your Choreography

Create a choreography using the effect algebra:

```rust
// src/choreography.rs

use rumpsteak_aura_choreography::effects::*;
use crate::types::*;
use crate::extensions::*;

pub fn auth_protocol() -> Program<Role, String> {
    Program::new()
        // Log protocol start
        .ext(LogEvent {
            message: "Starting authentication protocol".into(),
            level: LogLevel::Info,
        })
        
        // Validate client capability
        .ext(ValidateCapability {
            capability: "authenticate".into(),
            role: Role::Client,
        })
        
        // Client sends auth request to server
        .send(Role::Server, "auth_request".to_string())
        
        // Log authentication attempt
        .ext(LogEvent {
            message: "Authentication request sent".into(),
            level: LogLevel::Info,
        })
        
        // Server validates and queries database
        .ext(ValidateCapability {
            capability: "query_database".into(),
            role: Role::Server,
        })
        .send(Role::Database, "user_query".to_string())
        
        // Database responds
        .send(Role::Server, "user_data".to_string())
        
        // Server sends auth response to client
        .send(Role::Client, "auth_response".to_string())
        
        // Log success
        .ext(LogEvent {
            message: "Authentication complete".into(),
            level: LogLevel::Info,
        })
        
        .end()
}
```

## Step 6: Execute the Choreography

Put it all together:

```rust
// src/main.rs

mod types;
mod extensions;
mod handler;
mod choreography;

use rumpsteak_aura_choreography::effects::*;
use handler::DomainHandler;
use choreography::auth_protocol;
use types::Role;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create handler with capabilities
    let mut handler = DomainHandler::new(
        Role::Client,
        vec![
            "authenticate".into(),
            "query_database".into(),
        ],
    );

    // Build the choreography
    let program = auth_protocol();

    // Execute with extension support
    let mut endpoint = ();
    let result = interpret_extensible(&mut handler, &mut endpoint, program).await?;

    match result.final_state {
        InterpreterState::Completed => {
            println!("✓ Protocol completed successfully");
        }
        InterpreterState::Failed(err) => {
            println!("✗ Protocol failed: {}", err);
        }
        InterpreterState::Timeout => {
            println!("✗ Protocol timed out");
        }
    }

    Ok(())
}
```

## Advanced: Composition Patterns

### Pattern 1: Reusable Choreographic Primitives

Create library of composable patterns:

```rust
// src/patterns.rs

pub fn with_retry<R: RoleId, M: Clone>(
    program: Program<R, M>,
    max_attempts: u32,
) -> Program<R, M> {
    Program::new()
        .ext(RetryMetadata { max_attempts })
        .then(program)
}

pub fn with_timeout_ext<R: RoleId, M>(
    program: Program<R, M>,
    timeout_ms: u64,
) -> Program<R, M> {
    Program::new()
        .ext(TimeoutMetadata { timeout_ms })
        .then(program)
}

// Usage:
let resilient_protocol = with_retry(
    with_timeout_ext(auth_protocol(), 5000),
    3
);
```

### Pattern 2: Handler Composition

Compose multiple handlers:

```rust
pub struct ComposedHandler<H1, H2> {
    primary: H1,
    secondary: H2,
    registry: ExtensionRegistry<()>,
}

impl<H1, H2> ComposedHandler<H1, H2>
where
    H1: ExtensibleHandler,
    H2: ExtensibleHandler<Endpoint = H1::Endpoint>,
{
    pub fn new(primary: H1, secondary: H2) -> Self {
        let mut registry = ExtensionRegistry::new();
        // Merge registries from both handlers
        registry.merge(primary.extension_registry().clone());
        registry.merge(secondary.extension_registry().clone());
        
        Self { primary, secondary, registry }
    }
}
```

### Pattern 3: Cross-Crate Extensions

Share extensions across projects:

```rust
// In your library crate
pub mod extensions {
    pub use crate::ValidateCapability;
    pub use crate::LogEvent;
    pub use crate::RetryMetadata;
}

// In consuming crate
use my_library::extensions::*;

let program = Program::new()
    .ext(ValidateCapability { /* ... */ })
    .ext(LogEvent { /* ... */ });
```

## Testing

Test your choreographies and extensions:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_auth_protocol() {
        let mut handler = DomainHandler::new(
            Role::Client,
            vec!["authenticate".into()],
        );

        let program = auth_protocol();
        let mut endpoint = ();
        
        let result = interpret_extensible(
            &mut handler,
            &mut endpoint,
            program
        ).await.unwrap();

        assert_eq!(result.final_state, InterpreterState::Completed);
    }

    #[test]
    fn test_extension_registration() {
        let handler = DomainHandler::new(Role::Client, vec![]);
        
        assert!(handler.registry.is_registered::<ValidateCapability>());
        assert!(handler.registry.is_registered::<LogEvent>());
    }
}
```

## Next Steps

- Learn about [Extension Architecture](08_extension_architecture.md)
- Explore [Advanced Examples](../choreography/examples/)
- Read about [Testing Choreographies](07_testing.md)
- See [Rumpsteak Handler](06_rumpsteak_handler.md) for network protocols
