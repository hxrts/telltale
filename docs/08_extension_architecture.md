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
    fn participating_roles<R: RoleId>(&self) -> Vec<R>;
    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
    fn clone_box(&self) -> Box<dyn ExtensionEffect>;
}
```

**Key features**:
- `TypeId`-based discrimination (compile-time type safety)
- Role participation for projection semantics
- Type-safe downcasting via `Any` trait
- Cloneable for effect algebra operations

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

Extensions project based on `participating_roles()`:

### Global Extensions

Empty roles vector → appears in all projections:

```rust
fn participating_roles<R: RoleId>(&self) -> Vec<R> {
    vec![]  // Global - all roles see this
}
```

Example: Logging events that all roles should record.

### Role-Specific Extensions

Non-empty roles → appears only in specified projections:

```rust
fn participating_roles<R: RoleId>(&self) -> Vec<R> {
    vec![self.role]  // Only this role sees it
}
```

Example: Capability validation for a specific role.

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
