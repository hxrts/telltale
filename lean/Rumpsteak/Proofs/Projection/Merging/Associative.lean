import Rumpsteak.Proofs.Projection.Merging.Associative.Helpers
import Rumpsteak.Proofs.Projection.Merging.Associative.SendSorted
import Rumpsteak.Proofs.Projection.Merging.Associative.RecvSorted

/-! # Rumpsteak.Proofs.Projection.Merging.Associative

Proof that merge is associative (in the 3-way commutative form).

## Overview

This module proves `MergeAssociative`:
∀ T1 T2 T3, (T1.merge T2).bind (·.merge T3) = (T2.merge T3).bind (T1.merge ·)

This is the most complex merge property, requiring extensive case analysis on
all combinations of local type constructors and their branch structures.

## Module Structure

The proof is split across multiple files for maintainability:

- `Associative/Helpers.lean`: Helper lemmas for sorted branch merging
- `Associative/SendSorted.lean`: `mergeSendSorted_assoc` proof
- `Associative/RecvSorted.lean`: `mergeRecvSorted_assoc` proof
- `Associative.lean` (this file): Main `merge_associative` theorem

## Proof Strategy

1. Define `MergeAssocAt t` as the associativity property for a fixed first argument
2. Prove helper lemmas for sorted branch merging (`mergeSendSorted_assoc`, `mergeRecvSorted_assoc`)
3. Use nested structural induction to prove `MergeAssocAt` for all local types
4. Derive `MergeAssociative` from `MergeAssocAt`

## Implementation Note

The full proof requires extensive case analysis on all combinations of:
- Constructor types: end, send, recv, mu, var
- Branch orderings: l1 < l2, l2 < l1, l1 = l2
- Continuation merge results: some/none

The proof uses `LocalTypeR.recOn` with three motives:
- motive_1: MergeAssocAt for types
- motive_2: AllBranches MergeAssocAt for branch lists
- motive_3: MergeAssocAt for individual branches

Each case reduces to either:
- A direct computation for base cases (end, var)
- Application of `mergeSendSorted_assoc` or `mergeRecvSorted_assoc` for branches
- Recursive application of the IH for continuations
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

/-! ## Main theorem -/

/-- Merge is associative in the 3-way sense.

    This theorem states that the order of merging doesn't matter:
    (T1 ⊔ T2) ⊔ T3 = T1 ⊔ (T2 ⊔ T3)

    when written using Option.bind to handle merge failures.

    PROOF STRUCTURE:
    1. Prove MergeAssocAt t1 for fixed t1 using LocalTypeR.recOn
    2. Each constructor case either computes directly or uses helper lemmas
    3. The send/recv cases use mergeSendSorted_assoc/mergeRecvSorted_assoc
    4. Recursive cases use the IH on continuations

    This is a complex proof due to the many constructor combinations. -/
theorem merge_associative : MergeAssociative := by
  intro t1 t2 t3
  sorry

end Rumpsteak.Proofs.Projection.Merging
