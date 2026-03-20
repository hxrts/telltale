# Authority Language Surface

This page records the current authority/failure-oriented DSL surface added on top of the choreography parser.

It is a design-note and contract page for the current implementation.
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

## Observable Trace Model

Language-level effect usage is expected to remain observable through the same runtime/effect tracing surfaces used by VM replay and effect-bisimulation work.

Current design rule:

- language-level authority checks and evidence-sensitive decisions must map to explicit effect operations and explicit VM-visible events
- missing or ambiguous authoritative input must become typed failure, never silent fallback success

## Future Extension Path

The initial design is nominal on purpose.

Explicitly not implemented in this phase:

- effect polymorphism
- parameterized effect rows
- generalized handler polymorphism

Reserved extension points:

- stable effect/interface names
- explicit operation signatures
- explicit `uses` lists
- AST nodes that separate effect references from generic expression calls

This keeps the current system small while leaving a clean path toward later parameterized or polymorphic effects.
