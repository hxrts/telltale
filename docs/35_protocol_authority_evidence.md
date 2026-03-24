# Protocol-Critical Authority and Evidence

This page defines what counts as protocol-critical authority in Telltale and
how evidence-bearing decisions are expected to behave.

## Scope

Telltale owns protocol-critical authority flow. It does not own arbitrary host
application state.

Use Telltale authority/evidence features when:

- the decision changes protocol control flow
- the decision must be replayable or auditable
- missing authority must fail closed instead of falling back silently
- the decision needs typed success/failure semantics

Keep logic in the host when:

- it is ordinary UI/application state with no protocol meaning
- it does not affect protocol-visible branching
- replay/audit semantics are not required

## Core Concepts

| Term | Meaning |
|---|---|
| authority | the right to drive a protocol-critical action |
| capability | the current runtime token that proves live authority |
| evidence | typed proof object consumed by a protocol-critical branch |
| receipt | typed proof that a transfer or handoff was staged/committed |
| typed failure | an explicit `Err`, cancellation, or timeout outcome rather than host-local absence |

## Language Shape

The current language surface uses a small set of explicit forms:

```tell
effect Runtime
  ready : Session -> Result CommitError ReadyWitness

protocol CommitFlow uses Runtime =
  let readiness = check Runtime.ready(session)
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
    | Err(TimedOut) =>
        Coordinator -> Worker : Cancel
```

Evidence binding uses ordinary `let`:

```tell
let receipt = transfer Session from Coordinator to Worker
```

Receipts and transfer-like bindings are linear and must be consumed exactly
once.

## Runtime Meaning

Language-level authority checks are expected to lower into the existing runtime
authority surfaces:

- `check Effect.op(...)` lowers to the typed protocol-machine effect boundary
- successful protocol-critical checks produce explicit evidence/witness objects
- invalid or missing evidence fails closed
- timeout and cancellation become explicit observable/runtime-audit outcomes
- transfer/delegation emits explicit receipts and audit records

This keeps the user-facing language aligned with:

- `EffectHandler` typed outcomes
- `OwnedSession` and runtime ownership capability checks
- `ReadinessWitness`, `CancellationWitness`, and `TimeoutWitness`
- `semantic_audit_log` and replay-visible event ordering

## No Fallback Masking

Protocol-critical authority must not degrade into ambient host heuristics.

Fail-closed rules:

- no implicit wildcard/default masking for `Result` and `Maybe`
- no ad hoc “missing data means false” authority checks
- no silent reuse of stale capabilities or receipts
- no hidden host-only branch decisions outside typed effect queries

## Relation to the Effect Bridge

This design does not create a second host/runtime bridge.

The authoritative path is:

1. declare a nominal `effect`
2. name it in `uses`
3. invoke it with `check Effect.op(...)`
4. lower it into the existing typed protocol-machine `invoke` boundary
5. preserve its outcome in effect/audit/replay surfaces

That matches the project’s existing typed effect-obligation architecture and
observational correctness story.

## Related Docs

- [Protocol-Critical Authority Scope](33_protocol_authority_scope.md)
- [Authority Language Surface](34_authority_language_surface.md)
- [Effect Handlers and Session Types](11_effect_session_bridge.md)
- [Protocol Machine Architecture](12_protocol_machine_architecture.md)
