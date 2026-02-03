# DSL Extensions Part 1: Runtime Effect System

This document explains the runtime extension system for choreography effects. Part 2 covers grammar and syntax extensions in [DSL Extensions Part 2: Syntax Extensions](17_syntax_extensions.md).

## Overview

Runtime extensions are type safe effects that can be inserted into `Program` sequences. Extensions are projected to roles during compilation and dispatched by `interpret_extensible` at runtime.

## ExtensionEffect

Extensions implement `ExtensionEffect` and specify which roles participate.

```rust
pub trait ExtensionEffect<R: RoleId>: Send + Sync + Debug {
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> &'static str;
    fn participating_roles(&self) -> Vec<R> { vec![] }
    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
    fn clone_box(&self) -> Box<dyn ExtensionEffect<R>>;
}
```

The default `participating_roles` implementation returns an empty vector, which makes the extension global. A non empty vector limits the extension to specific roles.

```rust
#[derive(Clone, Debug)]
pub struct ValidateCapability<R> {
    pub role: R,
    pub capability: String,
}

impl<R: RoleId> ExtensionEffect<R> for ValidateCapability<R> {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "ValidateCapability"
    }

    fn participating_roles(&self) -> Vec<R> {
        vec![self.role]
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect<R>> {
        Box::new(self.clone())
    }
}
```

This extension only appears in the projection for `role`. Use an empty vector to make it global.

## Extension Registry

Handlers register extension logic in an `ExtensionRegistry`.

```rust
let mut registry = ExtensionRegistry::new();
registry.register::<ValidateCapability<Role>, _>(|_ep, ext| {
    Box::pin(async move {
        let validate = ext
            .as_any()
            .downcast_ref::<ValidateCapability<Role>>()
            .ok_or_else(|| ExtensionError::TypeMismatch {
                expected: "ValidateCapability",
                actual: ext.type_name(),
            })?;
        tracing::info!(cap = %validate.capability, "checked capability");
        Ok(())
    })
})?;
```

`register` returns an error on duplicate handlers. Use `ExtensionRegistry::merge` to compose registries across modules.

## Interpreter Integration

Use `interpret_extensible` with handlers that implement `ExtensibleHandler`.

```rust
let mut handler = MyHandler::new();
let mut endpoint = ();
let result = interpret_extensible(&mut handler, &mut endpoint, program).await?;
```

The non extensible `interpret` function does not dispatch extensions, so the interpreter only logs a warning when it encounters an extension effect.

## Error Handling

Extension errors surface as `ExtensionError`.

```rust
pub enum ExtensionError {
    HandlerNotRegistered { type_name: &'static str },
    ExecutionFailed { type_name: &'static str, error: String },
    TypeMismatch { expected: &'static str, actual: &'static str },
    DuplicateHandler { type_name: &'static str },
    MergeConflict { type_name: &'static str },
}
```

Handlers should register all required extensions before interpretation. This keeps failures at startup instead of in the middle of protocol execution.

## Usage Example

Extensions are inserted into programs with `Program::ext`.

```rust
let program = Program::new()
    .ext(ValidateCapability {
        role: Role::Alice,
        capability: "send".into(),
    })
    .send(Role::Bob, Message::Ping)
    .end();
```

The extension appears before the send in the projected program for Alice. Other roles do not receive this extension because it is scoped to a single role.

See [Effect Handlers](07_effect_handlers.md) for handler details and [Extension Guide](18_extension_guide.md) for end to end workflows.
