# Effect Handlers and Session Types

Telltale uses algebraic effects as the intermediate representation between choreographic protocols and verified execution. The architecture has three layers: the choreography DSL specifies global protocols, the effect algebra represents projected per-role programs, and the VM executes bytecode verified against session types.

Formal connections at each layer boundary ensure that protocol-level guarantees carry through to execution.

## Three-Layer Architecture

The first layer is the choreography. A global protocol specifies interactions from all participants' perspectives. Projection produces a local session type for each role. See [Choreographic Projection Patterns](05_projection.md) for the projection algorithm.

The second layer is the effect algebra. The projected protocol for each role becomes a `Program` value, a sequence of choreographic effects that can be analyzed, composed, and verified before execution. The interpreter evaluates the program by dispatching each effect to a handler.

The third layer is the VM. The bytecode VM executes instructions that correspond to effect operations. A formal Lean specification mirrors the Rust implementation. The monitor checks each instruction against the role's local session type. See [VM Overview](11_vm_architecture.md) for the instruction set.

## Effect Algebra

The `Program<R, M>` type is a free algebra over choreographic effects. The `Effect<R, M>` enum defines the operation set.

```rust
pub enum Effect<R: RoleId, M> {
    Send { to: R, msg: M },
    Recv { from: R, msg_tag: MessageTag },
    Choose { at: R, label: <R as RoleId>::Label },
    Offer { from: R },
    Branch { choosing_role: R, branches: Vec<(<R as RoleId>::Label, Program<R, M>)> },
    Loop { iterations: Option<usize>, body: Box<Program<R, M>> },
    End,
}
```

The effect variants mirror local session type constructors. `Send` corresponds to the send type. `Recv` corresponds to the receive type. `Choose` and `Offer` correspond to select and branch types. `End` corresponds to the end type. This structural correspondence is the basis for the formal bridge between effects and session types.

Programs compose sequentially with the `then` method. The `End` effect terminates a program. The codegen in `effects_codegen.rs` translates projected protocols into `Program` builders, one per role.

## Two Handler Interfaces

The system defines two distinct handler traits for different purposes.

`ChoreoHandler` is async and typed. It operates on concrete Rust message types with serialization bounds. Handlers like `InMemoryHandler`, `TelltaleHandler`, and `RecordingHandler` implement this trait. Middleware like `Trace`, `Retry`, and `FaultInjection` compose as handler wrappers. See [Effect Handlers](08_effect_handlers.md) for usage.

```rust
pub trait ChoreoHandler: Send {
    type Role: RoleId;
    type Endpoint: Endpoint;
    async fn send<M: Serialize + Send + Sync>(&mut self, ep: &mut Self::Endpoint,
        to: Self::Role, msg: &M) -> ChoreoResult<()>;
    async fn recv<M: DeserializeOwned + Send>(&mut self, ep: &mut Self::Endpoint,
        from: Self::Role) -> ChoreoResult<M>;
    // ...
}
```

`EffectHandler` is synchronous and untyped. It operates on bytecode-level `Value` types. The VM uses this interface for simulation and runtime integration. It is simpler and more constrained, which makes it suitable for formal specification.

```rust
pub trait EffectHandler: Send + Sync {
    fn handle_send(&self, role: &str, partner: &str, label: &str,
        state: &[Value]) -> Result<Value, String>;
    fn handle_recv(&self, role: &str, partner: &str, label: &str,
        state: &mut Vec<Value>, payload: &Value) -> Result<(), String>;
    // ...
}
```

The separation creates a verification boundary. The VM's `EffectHandler` is simple enough to formalize in Lean. The `ChoreoHandler` provides the typed developer API. Protocol code written against `ChoreoHandler` is compiled to VM bytecode that executes through `EffectHandler`.

## Formal Bridge

The Lean formalization defines `EffectModel` as a typeclass that maps effect actions to session types.

```lean
class EffectModel (ε : Type u) where
  EffectAction : Type
  EffectCtx : Type
  exec : EffectAction → EffectCtx → EffectCtx
  handlerType : EffectAction → LocalType
```

The `handlerType` field is the formal bridge. Every effect action has an associated local type that represents its session-level protocol commitment. The `exec` field describes how the effect context evolves when the action executes.

The `WellTypedInstr` judgment in `Runtime/VM/Monitor.lean` checks that each VM instruction is consistent with the session type at the current program point.

```lean
inductive WellTypedInstr where
  | wt_send : ... → WellTypedInstr (.send chan val) (.protocol sid) (.send r T L') L'
  | wt_recv : ... → WellTypedInstr (.recv chan dst) (.protocol sid) (.recv r T L') L'
  | wt_invoke (action : EffectModel.EffectAction ε) (hsid : HandlerId) :
      WellTypedInstr (.invoke action) (.handler hsid) (EffectModel.handlerType action) .end_
```

Protocol effects (send, recv) advance the local type as specified. Guard effects (acquire, release) preserve the local type. Effect invocations consume their handler type. This judgment ensures that the VM never executes an instruction that violates the session type.

## Algebraic Composition

Effects compose algebraically through sum and product instances on `EffectModel`.

The sum instance enables protocol federation. A VM parameterized by `EffectModel (ε₁ + ε₂)` can execute effects from either domain. The `handlerType` dispatches to the appropriate component.

```lean
instance instEffectModelSum [EffectModel ε₁] [EffectModel ε₂] : EffectModel (Sum ε₁ ε₂) where
  EffectAction := Sum (EffectModel.EffectAction ε₁) (EffectModel.EffectAction ε₂)
  handlerType := fun a => match a with
    | Sum.inl a1 => EffectModel.handlerType a1
    | Sum.inr a2 => EffectModel.handlerType a2
```

The product instance enables joint effects where two domains act simultaneously. The `EffectSpec` class provides composable pre/postconditions that follow the same sum/product structure. Bridge classes connect the five domain model interfaces (identity, guard, persistence, effect, verification) and compose over sums automatically.

## Middleware as Handler Transformers

Middleware on the Rust side wraps `ChoreoHandler` implementations. Each middleware implements `ChoreoHandler` with the same associated types as the inner handler. Composition is by nesting.

```rust
let handler = InMemoryHandler::new(role);
let handler = Retry::with_config(handler, 3, Duration::from_millis(100));
let handler = Trace::with_prefix(handler, "Alice");
```

This structure forms a category. The identity handler (`NoOpHandler`) exists. Composition is associative. The `ExtensionRegistry` provides a second axis of composition for domain-specific effects registered at runtime. Extension effects carry `participating_roles()` to integrate with choreographic projection.

## Comparison to Prior Work

Lindley and Morris (2017) embed session types as effects in a language with native algebraic effect handlers. In their approach the session type is the effect type. The integration is tight but limited to binary session types with no choreographic layer.

Hillerstrom and Lindley (2016) use effect handlers for session typing in a concurrent setting. This work also targets binary sessions and does not address multiparty protocols or global choreographic specifications.

Choral (Giallorenzo, Montesi, Peressotti, 2024) provides choreographic programming in Java. It does not use algebraic effects as an intermediate representation and does not include formal verification.

Telltale's approach differs in three ways. It targets multiparty session types, not binary. It uses effects as an intermediate representation between choreographies and execution, not as the primary typing mechanism. It provides a formal Lean specification connecting all three layers. The `EffectModel.handlerType` bridge and the algebraic composition instances are the technical devices that make this connection precise.
