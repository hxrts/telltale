# Composition Tutorial

This tutorial integrates rumpsteak-aura into your project. It demonstrates composing domain-specific choreographies with extensions.

## Prerequisites

You need Rust 1.75 or later. Basic understanding of choreographic programming is required. See [Getting Started](01_getting_started.md) for fundamentals. Familiarity with effect handlers helps. See [Using Rumpsteak Handlers](07_rumpsteak_handler.md) for handler concepts.

## Step 1: Add Dependencies

Add rumpsteak-aura to your `Cargo.toml`.

```toml
[dependencies]
rumpsteak-aura = "0.7"
rumpsteak-aura-choreography = "0.7"
tokio = { version = "1", features = ["full"] }
```

The core library provides session types. The choreography layer provides effects and projection. Macros enable the choreography DSL. Tokio provides the async runtime.

## Step 2: Define Domain Types

Create domain-specific types for your choreography.

```rust
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

Roles represent participants. Messages are the data exchanged. Roles must implement `Copy`, `Clone`, `Debug`, `PartialEq`, `Eq`, and `Hash`. Messages must implement `Serialize` and `Deserialize`.

## Step 3: Create Domain Extensions

Define extensions for domain needs.

```rust
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
```

The `ValidateCapability` extension checks permissions. Only the specified role participates. The `participating_role_ids()` method returns a single boxed role.

Define a logging extension for all roles.

```rust
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
        vec![]
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

The `LogEvent` extension appears in all role projections. An empty vector makes it global.

## Step 4: Create an Extensible Handler

Build a handler with extension support.

```rust
use rumpsteak_aura_choreography::effects::*;
use async_trait::async_trait;

pub struct DomainHandler {
    role: Role,
    registry: ExtensionRegistry<()>,
    capabilities: Vec<String>,
}

impl DomainHandler {
    pub fn new(role: Role, capabilities: Vec<String>) -> Self {
        let mut registry = ExtensionRegistry::new();
        
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
                        error: format!("Missing capability: {}", validate.capability),
                    });
                }
                
                println!("Validated capability: {}", validate.capability);
                Ok(())
            })
        });
        
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
        
        Self { role, registry, capabilities }
    }
}
```

The handler stores capabilities. The registry maps extension types to handlers. Each registration provides an async handler function.

Implement the handler traits.

```rust
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
    ) -> ChoreoResult<()> {
        println!("{:?} -> {:?}: sending message", self.role, to);
        Ok(())
    }

    async fn recv<M: serde::de::DeserializeOwned + Send>(
        &mut self,
        _ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<M> {
        Err(ChoreographyError::Transport("recv not implemented".into()))
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        _who: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> ChoreoResult<()> {
        println!("{:?}: choosing {:?}", self.role, label);
        Ok(())
    }

    async fn offer(
        &mut self,
        _ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<<Self::Role as RoleId>::Label> {
        println!("{:?}: offering choice from {:?}", self.role, from);
        unimplemented!("offer not implemented for example")
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _at: Self::Role,
        _dur: std::time::Duration,
        body: F,
    ) -> ChoreoResult<T>
    where
        F: std::future::Future<Output = ChoreoResult<T>> + Send,
    {
        body.await
    }
}
```

The handler implements both `ExtensibleHandler` and `ChoreoHandler`. Extension handling happens through the registry. Choreographic operations implement protocol communication.

## Step 5: Build a Choreography

Create a choreography using the effect algebra.

```rust
use rumpsteak_aura_choreography::effects::*;

pub fn auth_protocol() -> Program<Role, String> {
    Program::new()
        .ext(LogEvent {
            message: "Starting authentication protocol".into(),
            level: LogLevel::Info,
        })
        .ext(ValidateCapability {
            capability: "authenticate".into(),
            role: Role::Client,
        })
        .send(Role::Server, "auth_request".to_string())
        .ext(LogEvent {
            message: "Authentication request sent".into(),
            level: LogLevel::Info,
        })
        .ext(ValidateCapability {
            capability: "query_database".into(),
            role: Role::Server,
        })
        .send(Role::Database, "user_query".to_string())
        .send(Role::Server, "user_data".to_string())
        .send(Role::Client, "auth_response".to_string())
        .ext(LogEvent {
            message: "Authentication complete".into(),
            level: LogLevel::Info,
        })
        .end()
}
```

The program combines extensions and communication. Logging appears before and after operations. Capability validation precedes privileged actions. Messages flow between roles.

## Step 6: Execute the Choreography

Combine the components and execute.

```rust
use rumpsteak_aura_choreography::effects::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut handler = DomainHandler::new(
        Role::Client,
        vec!["authenticate".into(), "query_database".into()],
    );
    
    let program = auth_protocol();
    let mut endpoint = ();
    
    let result = interpret_extensible(&mut handler, &mut endpoint, program).await?;
    
    match result.final_state {
        InterpreterState::Completed => {
            println!("Protocol completed successfully");
        }
        InterpreterState::Failed(err) => {
            println!("Protocol failed: {}", err);
        }
        InterpreterState::Timeout => {
            println!("Protocol timed out");
        }
    }
    
    Ok(())
}
```

The handler receives capabilities at construction. The program executes through the interpreter. The final state indicates success or failure.

## Advanced Patterns

Three advanced patterns enable sophisticated choreographies.

### Pattern 1: Reusable Primitives

Create composable protocol fragments.

```rust
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
```

Functions wrap protocols with cross-cutting concerns. Retry logic and timeouts apply to any program. Composition builds complex protocols from simple pieces.

Use the primitives in protocols.

```rust
let resilient_protocol = with_retry(
    with_timeout_ext(auth_protocol(), 5000),
    3
);
```

The protocol gains retry and timeout behavior. Primitives compose without modifying the base protocol.

### Pattern 2: Handler Composition

Compose multiple handlers into one.

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
        registry.merge(primary.extension_registry().clone());
        registry.merge(secondary.extension_registry().clone());
        
        Self { primary, secondary, registry }
    }
}
```

The composed handler merges extension registries. Both handlers contribute extensions. This enables modular handler design.

### Pattern 3: Cross-Crate Extensions

Share extensions across projects.

```rust
pub mod extensions {
    pub use crate::ValidateCapability;
    pub use crate::LogEvent;
    pub use crate::RetryMetadata;
}
```

Library crates export extension modules. Consuming crates import and use them.

```rust
use my_library::extensions::*;

let program = Program::new()
    .ext(ValidateCapability { /* ... */ })
    .ext(LogEvent { /* ... */ });
```

Extensions compose across crate boundaries. The type system maintains safety.

## Testing

Test choreographies and extensions independently.

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
        
        let result = interpret_extensible(&mut handler, &mut endpoint, program)
            .await
            .unwrap();
        
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

Integration tests verify protocol execution. Unit tests check extension registration. Both test types ensure correctness.

## Next Steps

Learn extension architecture in [DSL Extensions Part 1: Runtime Effect System](10_effect_extensions.md). Explore advanced examples in `rust/choreography/examples/`. Read about testing in the examples directory. See production handlers in [Using Rumpsteak Handlers](07_rumpsteak_handler.md).
