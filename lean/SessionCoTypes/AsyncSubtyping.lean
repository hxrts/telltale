import SessionCoTypes.AsyncSubtyping.Core
import SessionCoTypes.AsyncSubtyping.Decidable


/-! # Async Subtyping for Session Types

This module provides decidable async subtyping for regular session types.

Async subtyping `S ≤ₐ T` allows a sender to proceed asynchronously,
buffering messages that the receiver has not yet consumed. This is the
appropriate subtyping relation for asynchronous message-passing systems.

## Modules

- `Core` : Definitions of async triples, step rules, coinductive relation
- `Decidable` : Constructive decision procedure with soundness/completeness

## Main Results

- `AsyncSubtypeRel` : Coinductive async subtyping relation
- `reachable_triples_finite` : Finiteness for regular types
- `checkAsync` : Decision algorithm
- `checkAsync_sound` : Soundness theorem
- `checkAsync_complete` : Completeness theorem
- `async_subtype_decidable_constructive` : Decidable instance

## Usage

```lean
-- Check if S is an async subtype of T
example : Prop := S ≤ₐ T

-- With explicit buffer
example : Prop := S ≤ₐ[buf] T

-- Decision procedure
example : Bool := isAsyncSubtype S T unfoldBound fuel
```
-/
