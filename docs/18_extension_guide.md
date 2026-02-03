# Extension Guide

This guide shows how to build and run runtime extensions with the effect system.

## Prerequisites

You need a recent Rust toolchain and the choreography crate. See [Getting Started](01_getting_started.md) for setup and [DSL Extensions Part 1: Runtime Effect System](16_effect_extensions.md) for the API reference.

## Step 1: Add Dependencies

Add the choreography crate and an async runtime.

```toml
[dependencies]
telltale-choreography = { path = "../rust/choreography" }
tokio = { version = "1", features = ["full"] }
```

Use a path dependency inside this workspace. For external projects, pin to the published crate version.

## Step 2: Define Roles and Messages

Define roles, labels, and messages for your protocol.

```rust
use serde::{Deserialize, Serialize};
use telltale_choreography::{LabelId, RoleId, RoleName};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Role {
    Client,
    Server,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Label {
    Ok,
}

impl LabelId for Label {
    fn as_str(&self) -> &'static str {
        match self {
            Label::Ok => "ok",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "ok" => Some(Label::Ok),
            _ => None,
        }
    }
}

impl RoleId for Role {
    type Label = Label;

    fn role_name(&self) -> RoleName {
        match self {
            Role::Client => RoleName::from_static("Client"),
            Role::Server => RoleName::from_static("Server"),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum Message {
    Ping,
    Pong,
}
```

Roles implement `RoleId`, labels implement `LabelId`, and messages are serializable.

## Step 3: Define an Extension

Create a domain specific extension that scopes to one role.

```rust
use std::any::{Any, TypeId};
use telltale_choreography::effects::ExtensionEffect;

#[derive(Clone, Debug)]
struct ValidateCapability {
    role: Role,
    capability: String,
}

impl ExtensionEffect<Role> for ValidateCapability {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "ValidateCapability"
    }

    fn participating_roles(&self) -> Vec<Role> {
        vec![self.role]
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect<Role>> {
        Box::new(self.clone())
    }
}
```

Use `participating_roles` to scope the extension. Return an empty vector to make it global.

## Step 4: Build an Extensible Handler

Register extension handlers and implement `ExtensibleHandler`.

```rust
use telltale_choreography::effects::{
    ChoreoHandler, ChoreoResult, ExtensionError, ExtensionRegistry, ExtensibleHandler,
};

struct DomainHandler {
    registry: ExtensionRegistry<(), Role>,
}

impl DomainHandler {
    fn new() -> Self {
        let mut registry = ExtensionRegistry::new();
        registry
            .register::<ValidateCapability, _>(|_ep, ext| {
                Box::pin(async move {
                    let validate = ext
                        .as_any()
                        .downcast_ref::<ValidateCapability>()
                        .ok_or(ExtensionError::TypeMismatch {
                            expected: "ValidateCapability",
                            actual: ext.type_name(),
                        })?;
                    tracing::info!(cap = %validate.capability, "validated capability");
                    Ok(())
                })
            })
            .expect("register extension");

        Self { registry }
    }
}

#[async_trait::async_trait]
impl ExtensibleHandler for DomainHandler {
    type Endpoint = ();

    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint, Role> {
        &self.registry
    }
}

#[async_trait::async_trait]
impl ChoreoHandler for DomainHandler {
    type Role = Role;
    type Endpoint = ();

    async fn send<M: serde::Serialize + Send + Sync>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _to: Self::Role,
        _msg: &M,
    ) -> ChoreoResult<()> {
        Ok(())
    }

    async fn recv<M: serde::de::DeserializeOwned + Send>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _from: Self::Role,
    ) -> ChoreoResult<M> {
        Err(telltale_choreography::ChoreographyError::Transport("recv not implemented".into()))
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        _who: Self::Role,
        _label: <Self::Role as RoleId>::Label,
    ) -> ChoreoResult<()> {
        Ok(())
    }

    async fn offer(
        &mut self,
        _ep: &mut Self::Endpoint,
        _from: Self::Role,
    ) -> ChoreoResult<<Self::Role as RoleId>::Label> {
        Err(telltale_choreography::ChoreographyError::Transport("offer not implemented".into()))
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

`ExtensionRegistry` stores handlers for each extension type. The `interpret_extensible` entry point uses this registry during execution.

## Step 5: Build and Run a Program

Insert extensions with `Program::ext` and interpret with `interpret_extensible`.

```rust
use telltale_choreography::{interpret_extensible, Program};

let program = Program::new()
    .ext(ValidateCapability {
        role: Role::Client,
        capability: "send".into(),
    })
    .send(Role::Server, Message::Ping)
    .end();

let mut handler = DomainHandler::new();
let mut endpoint = ();
let _ = interpret_extensible(&mut handler, &mut endpoint, program).await?;
```

Extensions appear in the projected program for participating roles. Use `interpret_extensible` whenever a program contains extensions.

## Testing

Unit tests can validate registry setup and projection behavior.

```rust
#[test]
fn test_registry() {
    let handler = DomainHandler::new();
    assert!(handler
        .extension_registry()
        .is_registered::<ValidateCapability>());
}
```

Use integration tests to check end to end protocol behavior with `interpret_extensible`.

See [Effect Handlers](07_effect_handlers.md) for handler patterns and [Choreographic DSL](04_choreographic_dsl.md) for core protocol syntax.
