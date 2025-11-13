# Extension Architecture

The extension system enables domain-specific choreographic effects while maintaining type safety and algebraic effects composition.

## Overview

Extensions are typed algebraic effects that participate in the full effect lifecycle:
- **Construction**: Type-safe extension creation
- **Projection**: Role-based extension filtering
- **Interpretation**: Handler dispatch and execution
- **Composition**: Cross-crate extension reuse

## Core Concepts

### ExtensionEffect Trait

All extensions implement the `ExtensionEffect` trait:

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

**Key features**:
- `TypeId`-based discrimination (compile-time type safety)
- Type-erased role participation for projection semantics (object-safe)
- Type-safe downcasting via `Any` trait
- Cloneable for effect algebra operations

**Design Rationale: Type Erasure with Type Safety**:

The trait uses `Vec<Box<dyn Any>>` for role information instead of a generic method like `participating_roles<R: RoleId>(&self) -> Vec<R>`. This design choice balances two critical requirements:

1. **Object Safety**: Rust traits with generic methods cannot be used as trait objects (`Box<dyn ExtensionEffect>`). Since extensions are stored as `Box<dyn ExtensionEffect>` in the effect algebra, the trait must be object-safe.

2. **Third-Party Projection**: Extension authors need to specify which roles participate in their extensions for proper projection. Without this capability, extensions cannot be projected to specific roles.

**How Type Safety is Maintained**:

Despite type erasure, the system remains type-safe through Rust's `Any` trait downcasting:

```rust
// Extension author boxes their specific role type
fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
    vec![Box::new(self.role)]  // Role type known at extension definition
}

// Effect algebra safely downcasts back to the choreography's role type
for role_any in ext.participating_role_ids() {
    if let Some(role) = role_any.downcast_ref::<R>() {  // Type-safe downcast
        roles.insert(*role);
    }
    // Mismatched types are safely ignored (downcast fails)
}
```

**Type Safety Guarantees**:

- Extensions can only be created with concrete role types known at compile time
- Downcasting uses `TypeId` checks internally (no unsafe casting)
- Type mismatches result in the role being silently skipped (fail-safe behavior)
- Extension handlers use `TypeId` for type-safe dispatch to the correct handler
- No runtime type confusion is possible - incompatible types simply don't match

This approach provides **runtime flexibility** (extensions work with any role type) while maintaining **compile-time safety** (role types are checked where they're defined and used).

### Extension Registry

The `ExtensionRegistry<E>` provides type-safe handler dispatch:

```rust
let mut registry = ExtensionRegistry::new();

registry.register::<MyExtension, _>(|endpoint, ext| {
    Box::pin(async move {
        let my_ext = ext.as_any()
            .downcast_ref::<MyExtension>()
            .ok_or(ExtensionError::TypeMismatch { ... })?;

        // Handle extension logic
        endpoint.do_something(my_ext)?;
        Ok(())
    })
});
```

**Features**:
- Fail-fast on unknown extensions
- Type-safe handler registration
- Registry merging for composition
- Zero overhead when empty

### Effect Integration

Extensions integrate naturally with the effect algebra:

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

## Projection Semantics

Extensions project based on `participating_role_ids()`, which returns type-erased role values.

### Global Extensions

Empty vector → appears in all projections:

```rust
fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
    vec![]  // Global - all roles see this
}
```

Example: Logging events that all roles should record.

### Role-Specific Extensions

Non-empty vector with boxed roles → appears only in specified projections:

```rust
fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
    vec![Box::new(self.role)]  // Only this role sees it
}
```

Example: Capability validation for a specific role.

### Multi-Role Extensions

Multiple roles can participate in an extension:

```rust
fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
    vec![
        Box::new(Role::Alice),
        Box::new(Role::Bob),
    ]
}
```

Example: A coordination extension that only Alice and Bob need to handle.

### Type Erasure and Downcasting

The effect algebra internally downcasts type-erased roles back to the concrete role type:

```rust
// In algebra.rs collect_roles()
for role_any in ext.participating_role_ids() {
    if let Some(role) = role_any.downcast_ref::<R>() {
        roles.insert(*role);
    }
}
```

This approach maintains object safety while allowing third-party extensions to specify participating roles for projection.

## Implementing Projection in Your Extensions

As a third-party developer, you can fully control how your extensions project to different roles. Here's a comprehensive guide:

### Design Pattern 1: Global Extensions

If your extension should be visible to all roles in the choreography:

```rust
#[derive(Clone, Debug)]
pub struct AuditLog {
    pub action: String,
    pub timestamp: u64,
}

impl ExtensionEffect for AuditLog {
    // ... type_id, type_name, etc.

    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        vec![]  // Empty = global, all roles see this
    }

    // ... remaining trait methods
}
```

**Use cases**: Logging, metrics, global invariants, debugging

### Design Pattern 2: Single Role Extensions

If your extension applies to a specific role:

```rust
#[derive(Clone, Debug)]
pub struct ValidatePermission {
    pub permission: String,
    pub role: MyRole,  // Store the role
}

impl ExtensionEffect for ValidatePermission {
    // ... type_id, type_name, etc.

    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        vec![Box::new(self.role)]  // Only this role participates
    }

    // ... remaining trait methods
}
```

**Use cases**: Role-specific validation, authorization, local state updates

### Design Pattern 3: Multi-Role Extensions

If multiple specific roles need to handle your extension:

```rust
#[derive(Clone, Debug)]
pub struct ConsensusRound {
    pub round: u32,
    pub participants: Vec<NodeId>,
}

impl ExtensionEffect for ConsensusRound {
    // ... type_id, type_name, etc.

    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        // Box each participant
        self.participants
            .iter()
            .map(|p| Box::new(*p) as Box<dyn Any>)
            .collect()
    }

    // ... remaining trait methods
}
```

**Use cases**: Consensus protocols, quorum operations, multi-party computation

### Design Pattern 4: Conditional Projection

If participation depends on extension state:

```rust
#[derive(Clone, Debug)]
pub struct OptionalNotification {
    pub message: String,
    pub notify_role: Option<Role>,
}

impl ExtensionEffect for OptionalNotification {
    // ... type_id, type_name, etc.

    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        if let Some(role) = self.notify_role {
            vec![Box::new(role)]
        } else {
            vec![]  // Global if no specific role
        }
    }

    // ... remaining trait methods
}
```

**Use cases**: Conditional notifications, optional observers, dynamic routing

### Important Constraints

When implementing `participating_role_ids()`:

1. **Type Matching**: Boxed roles must match the choreography's role type `R: RoleId`
2. **Static Bounds**: Role types must be `'static` (required for `Any`)
3. **Copy/Clone**: Roles should be `Copy` or cheap to clone
4. **Consistency**: The same extension value should always return the same roles

### Complete Example

Here's a complete extension with proper projection:

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
        // Only the service being rate-limited needs to check
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

// Usage in a choreography:
fn api_request_protocol() -> Program<ServiceRole, Message> {
    Program::new()
        // Gateway rate limits incoming requests
        .ext(RateLimitCheck {
            service: ServiceRole::Gateway,
            limit: 1000,
        })
        .send(ServiceRole::Gateway, ServiceRole::AuthService, AuthRequest)
        // AuthService rate limits token generation
        .ext(RateLimitCheck {
            service: ServiceRole::AuthService,
            limit: 100,
        })
        .send(ServiceRole::AuthService, ServiceRole::Database, QueryUser)
        .end()
}
```

### Projection Behavior

Given the above choreography:

**Gateway's projection:**
```rust
// Gateway sees:
ext(RateLimitCheck { service: Gateway, limit: 1000 })  // ✓ Participates
send(AuthService, AuthRequest)
// (AuthService rate limit skipped - not Gateway's concern)
```

**AuthService's projection:**
```rust
// AuthService sees:
// (Gateway rate limit skipped - not AuthService's concern)
recv(Gateway, AuthRequest)
ext(RateLimitCheck { service: AuthService, limit: 100 })  // ✓ Participates
send(Database, QueryUser)
```

**Database's projection:**
```rust
// Database sees:
// (Both rate limits skipped - not Database's concern)
recv(AuthService, QueryUser)
```

This gives you full control over which roles execute which extension logic during projection.

### Ordering

Extensions maintain happens-before relationships:

```rust
// Global choreography
ext(ValidateCap(Alice))     // Alice sees this
send(Alice, Bob, msg)       // Both see this
ext(LogEvent("sent"))       // Both see this

// Alice's projection
ext(ValidateCap(Alice))     // ✓ Appears first
send(Bob, msg)              // ✓ Then send
ext(LogEvent("sent"))       // ✓ Then log

// Bob's projection
recv(Alice, msg)            // ✓ Receive
ext(LogEvent("sent"))       // ✓ Then log (ValidateCap skipped)
```

## Handler Patterns

### Pattern 1: Wrapper Handler

Wrap an existing handler with extension support:

```rust
pub struct ExtensibleWrapper<H: ChoreoHandler> {
    base: H,
    registry: ExtensionRegistry<H::Endpoint>,
}

impl<H: ChoreoHandler> ExtensibleWrapper<H> {
    pub fn new(base: H) -> Self {
        let mut registry = ExtensionRegistry::new();

        // Register your extensions
        registry.register::<MyExtension, _>(|ep, ext| {
            Box::pin(async move {
                // Handle extension
                Ok(())
            })
        });

        Self { base, registry }
    }
}

#[async_trait]
impl<H: ChoreoHandler> ExtensibleHandler for ExtensibleWrapper<H> {
    type Endpoint = H::Endpoint;

    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint> {
        &self.registry
    }
}

// Delegate ChoreoHandler methods to base
#[async_trait]
impl<H: ChoreoHandler> ChoreoHandler for ExtensibleWrapper<H> {
    type Role = H::Role;
    type Endpoint = H::Endpoint;

    async fn send<M: Serialize + Send + Sync>(
        &mut self, ep: &mut Self::Endpoint, to: Self::Role, msg: &M
    ) -> Result<()> {
        self.base.send(ep, to, msg).await
    }

    // ... delegate other methods
}
```

### Pattern 2: Registry Composition

Combine multiple registries:

```rust
let mut combined = ExtensionRegistry::new();
combined.merge(capability_registry);
combined.merge(logging_registry);
combined.merge(metrics_registry);
```

### Pattern 3: Domain-Specific Handler

Create handlers with built-in extension support:

```rust
pub struct DomainHandler {
    role: Role,
    registry: ExtensionRegistry<()>,
    // Domain-specific state
    capabilities: CapabilityStore,
    budget: FlowBudget,
}

impl DomainHandler {
    pub fn new(role: Role) -> Self {
        let mut registry = ExtensionRegistry::new();

        // Register domain extensions
        registry.register::<ValidateCapability, _>(/* ... */);
        registry.register::<ChargeFlowCost, _>(/* ... */);

        Self { role, registry, /* ... */ }
    }
}
```

## Cross-Crate Composition

Extensions enable reusable choreographic primitives:

### Crate A: Define Primitive

```rust
// round_robin/src/lib.rs

#[derive(Clone, Debug)]
pub struct RoundRobinMetadata {
    pub participant_count: usize,
    pub current_index: usize,
}

impl ExtensionEffect for RoundRobinMetadata {
    // Implementation...
}

pub fn round_robin<R, M>(roles: Vec<R>, task: M) -> Program<R, M>
where R: RoleId, M: Clone
{
    let mut program = Program::new();

    for (i, role) in roles.iter().enumerate() {
        program = program
            .ext(RoundRobinMetadata {
                participant_count: roles.len(),
                current_index: i,
            })
            .send(
                role.clone(),
                roles[(i + 1) % roles.len()].clone(),
                task.clone()
            );
    }

    program
}
```

### Crate B: Use Primitive

```rust
// my_app/src/main.rs

use round_robin::{round_robin, RoundRobinMetadata};

let protocol = Program::new()
    .ext(ValidateCapability {
        capability: "coordinate".into(),
        role: Coordinator
    })
    .then(round_robin(workers, Task::new()))
    .ext(LogEvent {
        event: "round_robin_complete".into()
    });
```

## Error Handling

### Fail-Fast Semantics

Unknown extensions cause immediate errors:

```rust
// If MyExtension is not registered:
handler.extension_registry()
    .handle(endpoint, ext)
    .await
    // Returns: ExtensionError::HandlerNotRegistered
```

### Type Mismatch Detection

Downcasting failures are caught:

```rust
let my_ext = ext.as_any()
    .downcast_ref::<MyExtension>()
    .ok_or(ExtensionError::TypeMismatch {
        expected: "MyExtension",
        actual: ext.type_name(),
    })?;
```

### Error Propagation

Extension errors propagate through the interpreter:

```rust
match interpret_extensible(&mut handler, &mut endpoint, program).await {
    Ok(result) => match result.final_state {
        InterpreterState::Completed => { /* success */ }
        InterpreterState::Failed(msg) => { /* extension failed */ }
        InterpreterState::Timeout => { /* timeout */ }
    }
    Err(e) => { /* handler error */ }
}
```

## Performance

### Zero Overhead

Programs without extensions have no overhead:
- No registry lookups
- No extension checks
- Same performance as base interpreter

### Minimal Overhead

Programs with extensions:
- Single `TypeId` comparison per extension
- One `HashMap` lookup per extension type
- Async function call overhead

### Optimization Tips

1. **Batch Extensions**: Group related extensions
2. **Use Global Extensions Sparingly**: They appear in all projections
3. **Minimize Extension Data**: Keep extension structs small
4. **Reuse Registries**: Build once, use many times

## Best Practices

### Extension Design

1. **Single Responsibility**: One extension, one concern
2. **Immutable Data**: Extensions should be value types
3. **Clear Semantics**: Document projection behavior
4. **Type Names**: Use descriptive type names for debugging

### Handler Design

1. **Validate Early**: Check extension data on receipt
2. **Clear Errors**: Provide actionable error messages
3. **Idempotent**: Extensions should be safely retryable
4. **Document Requirements**: What state/capabilities needed?

### Testing

1. **Unit Test Extensions**: Test extension implementation
2. **Test Registration**: Verify handlers are registered
3. **Test Projection**: Verify role participation logic
4. **Integration Tests**: Test full choreography execution

## Examples

See:
- [Logging Extension](../choreography/examples/extension_logging.rs)
- [Capability Validation](../choreography/examples/extension_capability.rs)
- [Integration Tests](../choreography/tests/extension_integration.rs)

## Next Steps

- [Composition Tutorial](09_composition_tutorial.md)
- [Effect Handlers](06_rumpsteak_handler.md)
- [Testing Choreographies](07_testing.md)
