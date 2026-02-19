# Effect Handlers and Session Types

This document explains how effect execution is connected to session typing in the current Rust and Lean runtime.

## Three-Layer Contract

Telltale uses a three-layer contract.

| Layer | Artifact | Role |
|---|---|---|
| Global protocol layer | choreography and projection | defines role-local protocol obligations |
| Effect layer | handler interfaces | defines runtime action behavior |
| VM layer | bytecode and monitor checks | enforces instruction-level typing and admission rules |

Projection and runtime checks preserve protocol obligations across these layers.

## Rust Handler Surfaces

Rust has two handler interfaces with different scope.

| Interface | Location | Purpose |
|---|---|---|
| `ChoreoHandler` | `rust/choreography` | typed async API for generated choreography code |
| `EffectHandler` | `rust/vm/src/effect.rs` | synchronous VM-level API over bytecode values |

`EffectHandler` currently includes `handler_identity`, `handle_send`, `send_decision`, `handle_recv`, `handle_choose`, `step`, `handle_acquire`, `handle_release`, `topology_events`, and `output_condition_hint`.

The VM surface is deliberately smaller than the choreography API. This keeps runtime semantics explicit and testable.

## Lean Runtime Model Split

Lean models effect behavior with two typeclasses in `lean/Runtime/VM/Model/TypeClasses.lean`.

| Typeclass | Responsibility |
|---|---|
| `EffectRuntime` | executable effect action and context transition via `exec` |
| `EffectSpec` | typing-level handler obligations via `handlerType` |

This split separates executable semantics from typing obligations.

## Monitor-Typed Instruction Bridge

The unified instruction typing judgment is in `lean/Runtime/VM/Runtime/Monitor.lean`.

`WellTypedInstr` relates each instruction to a session kind and type transition. Communication instructions advance protocol local types. Guard and speculation instructions preserve typed state under their mode-specific rules. `invoke` typing is derived from `EffectSpec.handlerType`.

This is the formal bridge between effect actions and protocol safety.

## Composition

Lean composition instances for `EffectRuntime` and `EffectSpec` are defined in `lean/Runtime/VM/Composition/DomainComposition.lean`.

Sum composition supports protocol federation across effect domains. Product composition supports paired domain execution.

These instances keep the effect bridge compositional without changing the VM instruction model.

## Related Docs

- [Effect Handlers](08_effect_handlers.md)
- [VM Architecture](11_vm_architecture.md)
- [Lean Verification](18_lean_verification.md)
- [Lean-Rust Bridge](19_lean_rust_bridge.md)
