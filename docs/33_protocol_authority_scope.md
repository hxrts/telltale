# Protocol-Critical Authority Scope

This note records the Phase 1 boundary decisions for protocol-critical
authority work in Telltale.

The goal is to move more protocol-critical correctness into the
VM/DSL/theory boundary without turning Telltale into a general-purpose
application runtime.

## Classification

### Move Into The Telltale Protocol-Machine/Effect Layer

These concerns belong in the protocol-machine/effect/runtime boundary because they are
protocol-critical, observable, and suitable for runtime enforcement.

| Concern | Why it belongs in Telltale |
|---|---|
| typed effect outcomes | replaces stringly failure at the protocol boundary |
| authority/evidence/receipt objects | removes ambient authority and raw-id control |
| explicit timeout/cancellation/failure semantics | prevents silent hangs and silent failure |
| typed external checks | turns authoritative queries into explicit protocol inputs |
| structured authority/failure traces | supports replay, audit, and effect-bisimulation-facing observability |
| nominal effect interfaces | makes protocol host dependencies explicit and typed |

### Move Into The Telltale DSL

These concerns belong in the language surface because they are the
ergonomic way to express the protocol-critical protocol-machine features above.

| Concern | Why it belongs in the DSL |
|---|---|
| `case/of` pattern matching | needed for typed branching over `Result`, `Maybe`, and evidence |
| unions and `type alias` | needed for typed failures, witnesses, and receipts |
| `let`-bound evidence values | keeps authority flow explicit and readable |
| compiler-enforced single-use linear bindings | makes receipt/capability consumption statically visible |
| timeout/cancel/failure syntax | makes failure control flow first-class |
| `check` syntax | exposes authoritative host queries as typed protocol operations |
| `effect` / `uses` declarations | describes typed host interfaces at the language level |

### Keep Host-Only

These concerns should remain outside Telltale because they are
application-specific, presentation-specific, or not good candidates for
the theorem-backed protocol core.

| Concern | Why it stays host-only |
|---|---|
| UI/view/reduction architecture | not protocol semantics |
| frontend state ownership taxonomies | product/runtime specific |
| storage, retries, transport polling, and background scheduling internals | implementation details behind the effect boundary |
| generic actor/resource lifecycle unrelated to protocol correctness | broader runtime concern than MPST/effect correctness |
| rendering-oriented observed state | not authoritative protocol truth |

## Taxonomy

These terms are the working vocabulary for the design.

| Term | Meaning |
|---|---|
| authority | the right to drive or mutate protocol-critical state |
| capability | a typed token representing currently valid authority |
| evidence | data that justifies a protocol-critical decision |
| receipt | a concrete evidence object produced by a protocol/runtime action such as transfer |
| failure outcome | a typed non-success result that changes protocol control flow |
| cancellation outcome | a typed result representing explicit cancellation rather than absence or timeout |
| timeout outcome | a typed result representing elapsed wait under protocol rules |

Working distinction:

- authority answers who may act
- capability is the concrete token used to exercise that authority
- evidence answers why a branch or action is permitted
- receipts are evidence produced by prior protocol/runtime actions

## Weak Current Surfaces

The current repo already has a strong protocol-machine/effect boundary.
Several parts of that boundary still rely on raw strings or convention-driven host behavior.

### VM/Effect Callback Surface

The VM `EffectHandler` trait in `rust/vm/src/effect/handler_trait.rs`
has now moved to typed outcomes.
Callbacks return `EffectResult<_>` with typed failure variants.
Failures use `EffectFailure` and `EffectFailureKind` rather than raw `String` classification.

This was the highest-priority boundary change because it makes timeout,
cancellation, stale authority, invalid evidence, determinism, topology,
and contract failures explicit at the protocol boundary.

### Guard/Evidence Surface

The guard boundary in `rust/vm/src/guard.rs` also uses `Result<_, String>`
for:

- `open_`
- `close`
- `encode_evidence`
- `decode_evidence`

This is a protocol-adjacent evidence surface and should converge toward
typed evidence/failure as the rest of the authority design firms up.

### Internal Runtime Surfaces Worth Tracking

Some lower-level VM/session functions also use raw strings today.
They are not all equally important.
They should be inventoried so future typed-boundary work does not stop at the trait edge.

Examples include:

- session send/recv/close operations in `rust/vm/src/session/state.rs`
- `SessionStore::close` in `rust/vm/src/session/store.rs`
- runtime shape validation in `rust/vm/src/loader.rs`

Phase 1 conclusion:

- the effect host boundary was the highest-priority weak surface and has
  now been tightened to typed outcomes
- the remaining highest-priority weak surface is the guard/evidence
  boundary
- the next priority is authority/evidence-carrying runtime APIs
- generic parser/compiler `String` errors are lower priority for this
  workstream unless they become part of the protocol authority surface

## Protocol-Critical Decisions Still Expressed As Ad Hoc Callbacks

These current host decisions are still mostly callback-shaped rather
than first-class language/runtime constructs:

| Current surface | Protocol-critical concern |
|---|---|
| `send_decision` | send/drop/delay/corrupt behavior and policy |
| `handle_recv` | receive-side state transition and effect interpretation |
| `step` | invoke-scoped integration work |
| `handle_acquire` / `handle_release` | guard/evidence validation |
| `topology_events` | failure and topology ingress |
| `output_condition_hint` | commit gating metadata |

These should not all become DSL constructs.
But the protocol-critical subset of their semantics should no longer be
available only as informal host behavior.

## Fit Test

A concern is eligible to move into Telltale when all of the following
hold:

1. It changes protocol-critical behavior rather than only presentation or
   app-internal behavior.
2. It can be represented as typed outcomes, evidence, receipts, or
   obligations rather than opaque host internals.
3. It is observable at the replay/audit/effect-trace boundary.
4. The protocol machine can enforce or at least validate it at a meaningful boundary.
5. Lean/Rust correspondence can model it without inventing a separate
   host-language semantics.

A concern should stay host-only when any of the following hold:

1. It is mainly UI/view/reduction logic.
2. It depends on implementation-specific nondeterministic runtime
   internals rather than typed protocol observations.
3. It cannot be expressed as typed evidence/outcomes without dragging in
   a general-purpose application semantics.
4. It is not part of the safety-visible or replay-visible protocol
   interface.

## Phase 1 Result

The immediate design direction is:

- strengthen the existing typed protocol-machine effect bridge rather than creating a
  second host boundary
- prioritize typed outcomes and typed evidence over generalized language
  abstraction
- add nominal effect interfaces first
- treat polymorphism as a later extension once the concrete effect model
  is stable
