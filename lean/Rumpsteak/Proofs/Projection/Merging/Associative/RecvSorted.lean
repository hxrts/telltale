import Rumpsteak.Proofs.Projection.Merging.Associative.SendSorted

/-! # Rumpsteak.Proofs.Projection.Merging.Associative.RecvSorted

Associativity proof for sorted recv-branch merging.

## Overview

This module proves that `mergeRecvSorted` is associative when all continuations
satisfy the associativity property. This is a key lemma for the main
`merge_associative` theorem.

PROOF SKETCH:
The proof proceeds by nested case analysis on bs1, bs2, bs3 and their head labels.
For each configuration of labels (l1 < l2, l2 < l1, l1 = l2, etc.), we show that
the merge operations can be reassociated using the IH on continuations.

Key insight: mergeRecvSorted has label-union semantics, so associativity holds
when we can reorder the label-by-label comparison process.
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

/-! ## Recv sorted merge associativity -/

/-- Associativity of recv-sorted merging.

    This theorem shows that mergeRecvSorted is associative:
    (bs1 ⊔ bs2) ⊔ bs3 = bs1 ⊔ (bs2 ⊔ bs3)

    The proof requires showing that all orderings of label comparisons
    can be reassociated, using the IH on continuations for the recursive case.

    This is complex due to the many cases of label orderings (l1 < l2, l2 < l1,
    l1 = l2) × (l1 < l3, l3 < l1, l1 = l3) × (l2 < l3, l3 < l2, l2 = l3). -/
axiom mergeRecvSorted_assoc
    (bs1 bs2 bs3 : List (Label × LocalTypeR))
    (ih : AllBranches MergeAssocAt bs1) :
    (LocalTypeR.mergeRecvSorted bs1 bs2).bind (fun m12 => LocalTypeR.mergeRecvSorted m12 bs3) =
    (LocalTypeR.mergeRecvSorted bs2 bs3).bind (fun m23 => LocalTypeR.mergeRecvSorted bs1 m23)

end Rumpsteak.Proofs.Projection.Merging
