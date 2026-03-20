# Authority Language Surface

This page records the current authority/failure-oriented DSL surface added on
top of the choreography parser.

It is the current reference page for language-level authority checks, typed
failure branching, and nominal effect interfaces.
It is intentionally narrower than a full generalized effect language.

## Current Surface

Top-level declarations:

- `type Name | Ctor | Ctor of Payload`
- `type alias Name = { ... }`
- `effect Runtime { ready : Session -> Result CommitError ReadyWitness }`
- `protocol Flow uses Runtime, Audit = ...`

Protocol-local forms:

- `let binding = check Runtime.op(args)`
- `let receipt = transfer Session from A to B`
- `let binding = ... in { ... }`
- `case expr of { | Ok witness -> { ... } | Err reason -> { ... } }`
- `timeout 5s at Coordinator { ... } on timeout { ... } on cancel { ... }`
- `choice at Coordinator { | Commit when check Runtime.ready(session) yields witness -> { ... } }`

## Review Sketches

These are the short canonical examples for the current reviewed language
additions.

### Nominal Effects and `uses`

```tell
effect Runtime
  ready : Session -> Result CommitError ReadyWitness

protocol Flow uses Runtime =
  ...
```

This is the smallest effect declaration plus dependency declaration that the language accepts.

### `Result` with `case/of`

```tell
case check Runtime.ready(session) of
  | Ok witness -> ...
  | Err reason -> ...
```

This is the canonical typed branching form for authority checks.

### `Maybe`

```tell
case maybeReceipt of
  | Just receipt -> ...
  | Nothing -> ...
```

This keeps absence explicit instead of falling back to implicit defaults.

### Custom Union and Alias

```tell
type CommitError = TimedOut | Cancelled
type alias ReadyWitness = { epoch : Int }
```

Custom unions and aliases name failure and evidence values directly in the DSL.

### Evidence Binding with `let`

```tell
let receipt = transfer Session from Coordinator to Worker
```

Ordinary `let` syntax is the only binding form used for receipts and other authority artifacts.

### Timeout and Cancellation

```tell
timeout 5s at Coordinator
  Worker -> Coordinator : Ready
on timeout
  Coordinator -> Worker : Cancel
on cancel
  Coordinator -> Worker : Cancelled
```

Timeout and cancellation are explicit protocol branches, not host-only control flow.

### Evidence Guard

```tell
choice at Coordinator
  | Commit when check Runtime.ready(session) yields witness -> ...
```

Evidence guards bind the witness directly at the branch point that authorizes the action.

### Linear Single-Use Binding

```tell
let receipt = transfer Session from Coordinator to Worker
commit transfer receipt
```

Transfers produce linear values that the compiler requires to be consumed exactly once.

### Local Helper Expression

```tell
let decision = check Runtime.ready(session)
in
case decision of
  | Ok witness -> ...
  | Err reason -> ...
```

`let ... in ...` keeps small authority decisions local instead of pushing them into host callbacks.

### No Implicit Default

```tell
case readiness of
  | Ok witness -> ...
  | Err reason -> ...
```

Protocol-critical matches must be exhaustive, and implicit catch-all masking is rejected.

### Typed External Query

```tell
let readiness = check Runtime.ready(session)
```

Typed external queries always enter the protocol through explicit `check` expressions.

## Result and Maybe

The DSL currently treats `Result` and `Maybe` as built-in naming conventions rather than a separate kind system.

- `Result` constructors: `Ok`, `Err`
- `Maybe` constructors: `Just`, `Nothing`

Current compiler rules:

- `case/of` over `Result` must include both `Ok` and `Err`
- `case/of` over `Maybe` must include both `Just` and `Nothing`
- implicit catch-all masking is not supported

## Let and Linearity

`let` is the normal binding form for authority values, receipts, and query results.

Current linear classification:

- `transfer ...` bindings are linear
- `check ...` bindings are not linear by default

Current linear rules:

- linear bindings must be consumed exactly once
- duplicate use is rejected
- implicit discard is rejected

Current cross-construct rule:

- the implementation counts use across subsequent statements and across explicit branch bodies
- this is intentionally fail-closed for `choice`, `case`, `timeout`, `loop`, `par`, `call`, and recursion until a richer flow-sensitive linear analysis is added

## Effect Declarations and Uses

`effect` declarations are nominal interfaces.

Current validation rules:

- effect interface names must be unique
- operation names must be unique within an effect
- `protocol ... uses ...` may reference only declared effects
- `check Effect.op(...)` and evidence guards may reference only:
  - effects named in `uses`
  - operations declared on those effects

This is the current clean-break contract.
There is no fallback to implicit host knowledge.

## Typed Host Effect Invocation

`check Effect.op(...)` is the language-level way to invoke typed host effects.

```tell
effect Runtime
  ready : Session -> Result CommitError ReadyWitness

protocol Flow uses Runtime =
  let readiness = check Runtime.ready(session)
```

Current contract:

- the protocol must declare the effect in `uses`
- the operation must exist on the named nominal interface
- lowering stays centered on the existing VM `invoke` boundary
- effect observations keep the nominal interface and operation identity for
  replay/audit surfaces

## Projection and Theory Boundary

Current projection behavior is intentionally explicit:

- `let` is treated as local-only and projects through to its continuation
- `case/of` is currently rejected by projection
- `timeout ... on timeout ... on cancel ...` is currently rejected by projection

This preserves MPST clarity while the explicit projection rules are still being designed.

Theory conversion has the same restriction:

- `let`, `case/of`, and `timeout` must be lowered further before conversion to theory-facing global types

## Lowering Boundary

The current lowering split is:

- parser/AST surface in `rust/choreography`
- VM/effect execution boundary in `rust/vm`
- typed handler boundary centered on VM `invoke`

Current intent:

- `effect` declarations become the source for generated Rust host interfaces
- `check Effect.op(...)` remains a DSL-level reference to a typed external query
- execution must still cross the same typed handler-obligation boundary rather than inventing a second host channel
- the Lean bridge statement for nominal effect declarations stays centered on the existing VM `invoke` obligation rather than a separate effect-language proof surface

## Observable Trace Model

Language-level effect usage is expected to remain observable through the same runtime/effect tracing surfaces used by VM replay and effect-bisimulation work.

Current design rule:

- language-level authority checks and evidence-sensitive decisions must map to explicit effect operations and explicit VM-visible events
- missing or ambiguous authoritative input must become typed failure, never silent fallback success
- canonical replay artifacts must preserve these decisions as structured semantic audit records rather than opaque host-only log text

## Future Extension Path

The initial design is nominal on purpose.

Not part of the current language surface:

- effect polymorphism
- parameterized effect rows
- generalized handler polymorphism

Reserved extension points:

- stable effect/interface names
- explicit operation signatures
- explicit `uses` lists
- AST nodes that separate effect references from generic expression calls

## Why Nominal First

The first effect-interface feature is deliberately nominal.

Reasons:

- the VM and Lean already have a typed effect-obligation boundary centered on
  `invoke`
- nominal interfaces are enough to make host dependencies explicit and typed
- observational audit/parity semantics are easier to stabilize with named
  interfaces and operations
- generalized effect polymorphism should wait until the nominal lowering,
  replay/audit model, and Rust/Lean correspondence are stable

This keeps the current system small while leaving a clean path toward later parameterized or polymorphic effects.
