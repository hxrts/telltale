import SessionCoTypes.AsyncSubtyping.Core
import SessionCoTypes.AsyncSubtyping.Decidable


/-! # Async Subtyping for Session Types

This module provides async subtyping and a sound bounded checker for it
(async subtyping is undecidable in general, even for regular types).

Async subtyping `S ≤ₐ T` allows a sender to proceed asynchronously,
buffering messages that the receiver has not yet consumed. This is the
appropriate subtyping relation for asynchronous message-passing systems.

## Modules

- `Core` : Definitions of async triples, step rules, coinductive relation
- `Decidable` : Sound bounded checker (accepted / stuck / outOfFuel)

## Main Results

- `AsyncSubtypeRel` : Coinductive async subtyping relation
- `checkAsync` : Bounded sound checker (parameterised by a sound type equality)
- `check_async_sound` : `checkAsync eqb fuel S T = .accepted → S ≤ₐ T`

## Usage

```lean
-- Check if S is an async subtype of T
example : Prop := S ≤ₐ T

-- With explicit buffer
example : Prop := S ≤ₐ[buf] T

-- Sound bounded check (`true` implies `S ≤ₐ T`; `false` is inconclusive)
example : Bool := isAsyncSubtypeBounded (fun _ _ => false) fuel S T
```
-/
