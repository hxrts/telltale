# Extension Architecture

The extension system enables domain-specific choreographic effects. Extensions maintain type safety and compose with algebraic effects.

## Overview

Extensions are typed algebraic effects. They participate in the full effect lifecycle. This includes construction, projection, interpretation, and composition.

Type-safe extension creation happens at construction time. Role-based filtering occurs during projection. Handler dispatch executes at interpretation time. Cross-crate reuse enables composition.

## Core Concepts

### ExtensionEffect Trait

All extensions implement the `ExtensionEffect` trait.

```rust
pub trait ExtensionEffect: Send + Sync + Debug {
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> &'static str;
    fn participating_role_ids(&self) -> Vec<Box<dyn Any>>;
    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
    fn clone_box(&self) -> Box<dyn ExtensionEffect>;
}
```

The trait provides `TypeId`-based discrimination for compile-time type safety. Type-erased role participation enables projection semantics while maintaining object safety. Type-safe downcasting uses the `Any` trait. Extension cloning supports effect algebra operations.

The trait uses `Vec<Box<dyn Any>>` for role information. This design balances object safety with third-party projection needs. Generic methods prevent trait objects. Extensions store as `Box<dyn ExtensionEffect>` in the effect algebra. Object-safe traits are required.

Type safety persists despite erasure. Rust's `Any` trait provides safe downcasting. Extensions box their specific role types. The effect algebra downcasts back to the choreography's role type. Mismatched types fail downcast and are skipped.

```rust
fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
    vec![Box::new(self.role)]
}
```

Runtime flexibility combines with compile-time safety. Extensions work with any role type. Role types check at definition and use sites. No runtime type confusion occurs.

### Extension Registry

The `ExtensionRegistry<E>` provides type-safe handler dispatch.

```rust
let mut registry = ExtensionRegistry::new();

registry.register::<MyExtension, _>(|endpoint, ext| {
    Box::pin(async move {
        let my_ext = ext.as_any()
            .downcast_ref::<MyExtension>()
            .ok_or(ExtensionError::TypeMismatch { ... })?;
        
        endpoint.do_something(my_ext)?;
        Ok(())
    })
});
```

The registry fails fast on unknown extensions. Type-safe registration prevents errors. Registries merge for composition. Empty registries have zero overhead.

### Effect Integration

Extensions integrate with the effect algebra.

```rust
let program = Program::new()
    .ext(ValidateCapability {
        capability: "send".into(),
        role: Alice
    })
    .send(Bob, Message("hello"))
    .ext(LogEvent {
        event: "message_sent".into()
    })
    .end();
```

Extensions appear before and after communication operations. The effect algebra maintains execution order.

## Projection Semantics

Extensions project based on `participating_role_ids()`. The method returns type-erased role values.

### Global Extensions

An empty vector makes an extension appear in all projections.

```rust
fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
    vec![]
}
```

Logging events use global extensions. All roles record the events.

### Role-Specific Extensions

A non-empty vector with boxed roles restricts projection.

```rust
fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
    vec![Box::new(self.role)]
}
```

Capability validation uses role-specific extensions. Only the specified role sees the extension.

### Multi-Role Extensions

Multiple roles participate by boxing each role.

```rust
fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
    vec![
        Box::new(Role::Alice),
        Box::new(Role::Bob),
    ]
}
```

Coordination extensions target specific role subsets. Only Alice and Bob handle this extension.

### Type Erasure and Downcasting

The effect algebra downcasts type-erased roles to concrete types.

```rust
for role_any in ext.participating_role_ids() {
    if let Some(role) = role_any.downcast_ref::<R>() {
        roles.insert(*role);
    }
}
```

This maintains object safety. Third-party extensions specify participating roles for projection.

## Implementing Projection

Extension developers control projection to different roles. Four design patterns cover common cases.

### Pattern 1: Global Extensions

Global extensions are visible to all roles.

```rust
#[derive(Clone, Debug)]
pub struct AuditLog {
    pub action: String,
    pub timestamp: u64,
}

impl ExtensionEffect for AuditLog {
    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        vec![]
    }
}
```

An empty vector makes the extension global. Logging, metrics, and global invariants use this pattern.

### Pattern 2: Single Role Extensions

Single role extensions apply to one specific role.

```rust
#[derive(Clone, Debug)]
pub struct ValidatePermission {
    pub permission: String,
    pub role: MyRole,
}

impl ExtensionEffect for ValidatePermission {
    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        vec![Box::new(self.role)]
    }
}
```

The extension stores the target role. Only that role participates. Validation, authorization, and local state updates use this pattern.

### Pattern 3: Multi-Role Extensions

Multiple specific roles handle multi-role extensions.

```rust
#[derive(Clone, Debug)]
pub struct ConsensusRound {
    pub round: u32,
    pub participants: Vec<NodeId>,
}

impl ExtensionEffect for ConsensusRound {
    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        self.participants
            .iter()
            .map(|p| Box::new(*p) as Box<dyn Any>)
            .collect()
    }
}
```

Each participant gets boxed. Consensus protocols, quorum operations, and multi-party computation use this pattern.

### Pattern 4: Conditional Projection

Participation can depend on extension state.

```rust
#[derive(Clone, Debug)]
pub struct OptionalNotification {
    pub message: String,
    pub notify_role: Option<Role>,
}

impl ExtensionEffect for OptionalNotification {
    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        if let Some(role) = self.notify_role {
            vec![Box::new(role)]
        } else {
            vec![]
        }
    }
}
```

The extension becomes global when no specific role is set. Conditional notifications, optional observers, and dynamic routing use this pattern.

## Implementation Constraints

Four constraints apply when implementing `participating_role_ids()`.

Boxed roles must match the choreography's role type `R: RoleId`. Role types must be `'static` for `Any` compatibility. Roles should be `Copy` or cheap to clone. The same extension value must always return the same roles.

## Complete Example

This example shows proper projection implementation.

```rust
use rumpsteak_aura_choreography::effects::*;
use std::any::{Any, TypeId};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ServiceRole {
    Gateway,
    AuthService,
    Database,
}

#[derive(Clone, Debug)]
pub struct RateLimitCheck {
    pub service: ServiceRole,
    pub limit: u32,
}

impl ExtensionEffect for RateLimitCheck {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
    
    fn type_name(&self) -> &'static str {
        "RateLimitCheck"
    }
    
    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        vec![Box::new(self.service)]
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

The service being rate-limited performs the check. Other services do not see this extension in their projection.

### Usage Example

The extension integrates into choreography programs.

```rust
fn api_request_protocol() -> Program<ServiceRole, Message> {
    Program::new()
        .ext(RateLimitCheck {
            service: ServiceRole::Gateway,
            limit: 1000,
        })
        .send(ServiceRole::AuthService, AuthRequest)
        .ext(RateLimitCheck {
            service: ServiceRole::AuthService,
            limit: 100,
        })
        .send(ServiceRole::Database, TokenQuery)
        .end()
}
```

Each service checks its own rate limit. The Gateway projection includes only the Gateway rate limit. The AuthService projection includes only the AuthService rate limit.

## Projection Behavior

Extensions project to participating roles only. Consider a three-role choreography with Alice, Bob, and Charlie.

```rust
Program::new()
    .ext(LogEvent { message: "start" })
    .ext(ValidateCapability { role: Alice, cap: "send" })
    .send(Bob, Message)
    .ext(AuditLog { action: "sent" })
    .end()
```

Alice's projection includes all extensions. Bob's projection includes `LogEvent` and `AuditLog` but not `ValidateCapability`. Charlie's projection includes `LogEvent` and `AuditLog` but not `ValidateCapability`.

The extension before `send` appears in Alice's projection only. Global extensions appear in all projections.

## Extension Ordering

Extensions maintain source order in projections. Consider this program.

```rust
Program::new()
    .ext(Ext1)
    .ext(Ext2)
    .send(Alice, Msg)
    .ext(Ext3)
    .end()
```

Alice's projection preserves the order. Ext1 executes first, then Ext2, then send, then Ext3. The handler processes extensions in definition order.

## Handler Patterns

Three patterns integrate extensions with handlers. Each pattern serves different needs.

### Pattern 1: Wrapper Handler

A wrapper handler adds extension support to existing handlers.

```rust
pub struct ExtensibleWrapper<H> {
    base: H,
    registry: ExtensionRegistry<H::Endpoint>,
}

impl<H> ExtensibleWrapper<H> {
    pub fn new(base: H, registry: ExtensionRegistry<H::Endpoint>) -> Self {
        Self { base, registry }
    }
}

impl<H: ChoreoHandler> ExtensibleHandler for ExtensibleWrapper<H> {
    type Endpoint = H::Endpoint;
    
    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint> {
        &self.registry
    }
}

impl<H: ChoreoHandler> ChoreoHandler for ExtensibleWrapper<H> {
    type Role = H::Role;
    type Endpoint = H::Endpoint;
    
    async fn send<M>(&mut self, ep: &mut Self::Endpoint, to: Self::Role, msg: &M) -> Result<()>
    where M: Serialize + Send + Sync {
        self.base.send(ep, to, msg).await
    }
}
```

The wrapper delegates choreographic operations to the base handler. Extensions use the separate registry. This enables adding extensions to any existing handler.

### Pattern 2: Registry Composition

Multiple registries merge for composition.

```rust
let mut registry = ExtensionRegistry::new();
registry.merge(auth_registry);
registry.merge(logging_registry);
registry.merge(metrics_registry);
```

Each domain provides its own registry. Merging combines all extension handlers. Duplicate registrations are detected at merge time.

### Pattern 3: Domain-Specific Handler

Domain handlers embed extension support directly.

```rust
pub struct DomainHandler {
    role: Role,
    registry: ExtensionRegistry<()>,
    capabilities: Vec<String>,
    budget: Arc<Mutex<u64>>,
}

impl DomainHandler {
    pub fn new(role: Role, caps: Vec<String>) -> Self {
        let mut registry = ExtensionRegistry::new();
        
        registry.register::<ValidateCapability, _>(move |_ep, ext| {
            Box::pin(async move {
                // Extension handling logic
                Ok(())
            })
        });
        
        Self { role, registry, capabilities: caps, budget: Arc::new(Mutex::new(1000)) }
    }
}
```

The handler owns its extensions. Domain-specific state integrates with extension handling. This pattern suits applications with fixed extension sets.

## Cross-Crate Composition

Extensions compose across crate boundaries. Crate A defines reusable primitives. Crate B uses those primitives.

### Defining Primitives

A library crate exports extension types.

```rust
#[derive(Clone, Debug)]
pub struct RoundRobinMetadata {
    pub participant_count: usize,
    pub current_index: usize,
}

impl ExtensionEffect for RoundRobinMetadata {
    // Implementation
}

pub fn round_robin<R: RoleId>(participants: Vec<R>) -> Program<R, ()> {
    Program::new()
        .ext(RoundRobinMetadata {
            participant_count: participants.len(),
            current_index: 0,
        })
        .end()
}
```

The crate provides both the extension type and helper functions. Users can combine these with their own extensions.

### Using Primitives

Application crates import and use extensions.

```rust
use my_library::extensions::{RoundRobinMetadata, round_robin};

let program = round_robin(vec![Alice, Bob, Charlie])
    .then(Program::new()
        .ext(CustomExtension { /* app-specific */ })
        .send(Alice, Message)
        .end()
    );
```

Extensions from different crates compose freely. The type system ensures safety.

## Error Handling

Extension errors follow fail-fast semantics. Unknown extensions cause immediate failure. Type mismatches produce clear error messages.

### Fail-Fast Semantics

Unregistered extensions terminate execution.

```rust
match interpret_extensible(&mut handler, &mut ep, program).await {
    Err(ChoreographyError::Extension(ExtensionError::UnknownExtension { type_name })) => {
        eprintln!("Extension {} not registered", type_name);
    }
    _ => {}
}
```

Registration happens before protocol execution. This catches configuration errors early.

### Type Mismatch Detection

Downcasts validate extension types.

```rust
let validated = ext.as_any()
    .downcast_ref::<ValidateCapability>()
    .ok_or(ExtensionError::TypeMismatch {
        expected: "ValidateCapability",
        actual: ext.type_name(),
    })?;
```

Type mismatches produce descriptive errors. The expected and actual type names appear in the error.

### Error Propagation

Extension errors propagate through the interpreter.

```rust
pub enum ExtensionError {
    UnknownExtension { type_name: &'static str },
    TypeMismatch { expected: &'static str, actual: &'static str },
    ExecutionFailed { type_name: &'static str, error: String },
}
```

Each error variant provides context. Handlers can distinguish between different failure modes.

## Performance

Extension overhead varies by usage pattern. Design decisions affect runtime cost.

### Zero Overhead Cases

Empty registries incur no cost. Programs without extensions run at baseline speed. The interpreter checks for extensions before dispatching.

### Minimal Overhead Cases

Extension dispatch uses `TypeId` comparison. This operation is fast. Dynamic dispatch for handlers adds minimal cost. Most overhead comes from extension logic itself.

### Optimization Tips

Register extensions once and reuse the registry. Avoid cloning extension data unnecessarily. Keep extension state small. Use `Copy` types for roles when possible.

## Best Practices

Follow these practices when designing extensions and handlers.

### Extension Design

Keep extensions focused on single concerns. Use global extensions sparingly. Prefer role-specific extensions for targeted behavior. Document which roles should handle your extension.

### Handler Design

Register all required extensions upfront. Provide clear error messages for failures. Use wrapper handlers to add extensions incrementally. Test extension handlers independently.

### Testing

Test extension projection behavior. Verify correct role participation. Check error handling for unregistered extensions. Test extension composition across crates.

## Examples

Complete examples demonstrate extension usage. See the `choreography/examples/` directory. The `extension_workflow.rs` example shows composition patterns. The `extension_capability.rs` example demonstrates validation. The `extension_logging.rs` example shows global extensions.

## Next Steps

Learn choreographic projection in [Choreographic Projection Patterns](04_projection.md). Understand effect handlers in [Effect Handlers](05_effect_handlers.md). Build complete applications with [Composition Tutorial](08_extension_guide.md).
