# DSL Extensions

This document explains how to extend the choreography DSL with runtime effects and syntax extensions.

## Overview

The extension system has two parts. Runtime extensions add type-safe effects that can be inserted into `Program` sequences. Syntax extensions add new grammar rules and statement parsers to the DSL.

Extensions are projected to roles during compilation and dispatched by `interpret_extensible` at runtime.

## Runtime Effect Extensions

### ExtensionEffect Trait

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

The default `participating_roles` implementation returns an empty vector, which makes the extension global. A non-empty vector limits the extension to specific roles.

### Defining an Extension

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

### Extension Registry

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

The `register` method returns an error on duplicate handlers. Use `ExtensionRegistry::merge` to compose registries across modules.

### Error Handling

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

### Interpreter Integration

Use `interpret_extensible` with handlers that implement `ExtensibleHandler`.

```rust
let mut handler = MyHandler::new();
let mut endpoint = ();
let result = interpret_extensible(&mut handler, &mut endpoint, program).await?;
```

The non-extensible `interpret` function does not dispatch extensions. The interpreter only logs a warning when it encounters an extension effect.

### Using Extensions in Programs

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

## Syntax Extensions

### GrammarExtension Trait

Grammar extensions provide Pest rules and a list of statement rules they handle.

```rust
pub trait GrammarExtension: Send + Sync + Debug {
    fn grammar_rules(&self) -> &'static str;
    fn statement_rules(&self) -> Vec<&'static str>;
    fn priority(&self) -> u32 { 100 }
    fn extension_id(&self) -> &'static str;
}
```

The `priority` value resolves conflicts when multiple extensions define the same rule. Higher priority wins and conflicts are recorded by the registry.

### StatementParser and ProtocolExtension

Statement parsers translate matched rules into protocol extensions.

```rust
pub trait StatementParser: Send + Sync + Debug {
    fn can_parse(&self, rule_name: &str) -> bool;
    fn supported_rules(&self) -> Vec<String>;
    fn parse_statement(
        &self,
        rule_name: &str,
        content: &str,
        context: &ParseContext,
    ) -> Result<Box<dyn ProtocolExtension>, ParseError>;
}
```

`ProtocolExtension` instances participate in validation, projection, and code generation.

```rust
pub trait ProtocolExtension: Send + Sync + Debug {
    fn type_name(&self) -> &'static str;
    fn mentions_role(&self, role: &Role) -> bool;
    fn validate(&self, roles: &[Role]) -> Result<(), ExtensionValidationError>;
    fn project(&self, role: &Role, ctx: &ProjectionContext) -> Result<LocalType, ProjectionError>;
    fn generate_code(&self, ctx: &CodegenContext) -> proc_macro2::TokenStream;
}
```

Use these traits to attach new DSL constructs to projection and codegen.

### ExtensionRegistry for Syntax

The `ExtensionRegistry` stores grammar extensions and statement parsers.

```rust
let mut registry = ExtensionRegistry::new();
registry.register_grammar(MyGrammarExtension)?;
registry.register_parser(MyStatementParser, "my_parser".to_string());
```

The registry tracks rule conflicts and supports dependency checks. Use `get_detailed_conflicts` for human-readable conflict reports.

### GrammarComposer

`GrammarComposer` combines the base grammar with registered extension rules and caches the result.

```rust
let mut composer = GrammarComposer::new();
composer.register_extension(MyGrammarExtension);
let grammar = composer.compose()?;
```

The cache avoids recomposing the grammar when the extension set has not changed.

### ExtensionParser

`ExtensionParser` wires the grammar composer into the parsing pipeline.

```rust
let mut parser = ExtensionParser::new();
parser.register_extension(MyGrammarExtension, MyStatementParser);
let choreography = parser.parse_with_extensions(source)?;
```

The `parse_with_extensions` method currently runs the standard parser and does not dispatch extension statements. Extension grammar rules are composed, but statement parsing dispatch is not yet completed.

### Extension Discovery

The `extensions::discovery` module provides metadata and dependency management.

```rust
let mut discovery = ExtensionDiscovery::new();
discovery.add_search_path("./extensions");
let registry = discovery.create_registry(&["timeout".to_string()])?;
```

Discovery assembles an `ExtensionRegistry` in dependency order and performs basic validation.

## Complete Workflow Example

This section shows an end-to-end workflow for building and running a runtime extension.

### Step 1: Add Dependencies

Add the choreography crate and an async runtime.

```toml
[dependencies]
telltale-choreography = { path = "../rust/choreography" }
tokio = { version = "1", features = ["full"] }
```

Use a path dependency inside this workspace. For external projects, pin to the published crate version.

### Step 2: Define Roles and Messages

Define roles, labels, and messages for your protocol.

```rust
use serde::{Deserialize, Serialize};
use telltale_choreography::{LabelId, RoleId, RoleName};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Role { Client, Server }

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Label { Ok }

impl LabelId for Label {
    fn as_str(&self) -> &'static str {
        match self { Label::Ok => "ok" }
    }
    fn from_str(label: &str) -> Option<Self> {
        match label { "ok" => Some(Label::Ok), _ => None }
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
enum Message { Ping, Pong }
```

Roles implement `RoleId`, labels implement `LabelId`, and messages are serializable.

### Step 3: Build an Extensible Handler

Register extension handlers and implement `ExtensibleHandler`.

```rust
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
                    tracing::info!(cap = %validate.capability, "validated");
                    Ok(())
                })
            })
            .expect("register extension");
        Self { registry }
    }
}
```

`ExtensionRegistry` stores handlers for each extension type. The `interpret_extensible` entry point uses this registry during execution.

### Step 4: Build and Run a Program

Insert extensions with `Program::ext` and interpret with `interpret_extensible`.

```rust
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

Use integration tests to check end-to-end protocol behavior with `interpret_extensible`.

## Built-In Extensions

The `extensions::timeout` module contains a sample grammar extension, parser, and protocol extension. It is intended as a reference implementation and currently uses simplified parsing logic.

## Related Docs

- [Choreography Effect Handlers](08_effect_handlers.md)
- [Choreographic DSL](04_choreographic_dsl.md)
- [Using Telltale Handlers](09_telltale_handler.md)
