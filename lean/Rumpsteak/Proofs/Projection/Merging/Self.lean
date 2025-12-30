import Rumpsteak.Proofs.Projection.Merging.Basic
import Rumpsteak.Proofs.Projection.Merging.SortLemmas

/-! # Rumpsteak.Proofs.Projection.Merging.Self

Proof that merge is self-idempotent: merging a type with itself always succeeds
and returns the canonical form.

## Overview

This module proves `MergeSelf`: ∀ T, T.merge T = some (canonical T).

The proof uses nested structural induction on local types. For send and recv
types, the canonicalization function produces the same ordering as the merge
algorithm's internal sorting.
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

attribute [local instance] boolRelToRel

/-! ## Main theorem -/

theorem merge_self : MergeSelf := by
  intro t
  -- Use the nested recursor (Lean 4.24 `induction` does not support nested inductives).
  refine LocalTypeR.recOn
    (motive_1 := fun t => LocalTypeR.merge t t = some (canonical t))
    (motive_2 := fun bs => AllBranches (fun t => LocalTypeR.merge t t = some (canonical t)) bs)
    (motive_3 := fun b => LocalTypeR.merge b.2 b.2 = some (canonical b.2))
    t
    (by simp [canonical, LocalTypeR.merge])
    (fun partner branches ihBranches => by
      -- Canonicalization matches the internal sorting performed by `mergeSendBranches`.
      let bs := LocalTypeR.sortBranches branches
      have hperm : bs.Perm branches := by
        simpa [bs, LocalTypeR.sortBranches] using (List.mergeSort_perm branches LocalTypeR.branchLe)
      have ihSorted :
          AllBranches (fun t => LocalTypeR.merge t t = some (canonical t)) bs :=
        AllBranches.of_perm _ hperm ihBranches
      have hSendSorted :
          LocalTypeR.mergeSendSorted bs bs =
            some (bs.map fun (l, t) => (l, canonical t)) :=
        mergeSendSorted_self bs ihSorted
      simp [canonical, canonicalBranches_eq_map, LocalTypeR.merge, bs, hSendSorted])
    (fun partner branches ihBranches => by
      let bs := LocalTypeR.sortBranches branches
      have hperm : bs.Perm branches := by
        simpa [bs, LocalTypeR.sortBranches] using (List.mergeSort_perm branches LocalTypeR.branchLe)
      have ihSorted :
          AllBranches (fun t => LocalTypeR.merge t t = some (canonical t)) bs :=
        AllBranches.of_perm _ hperm ihBranches
      have hRecvSorted :
          LocalTypeR.mergeRecvSorted bs bs =
            some (bs.map fun (l, t) => (l, canonical t)) :=
        mergeRecvSorted_self bs ihSorted
      have hPair : bs.Pairwise LocalTypeR.branchLe := by
        simpa [bs] using pairwise_sortBranches branches
      have hPairMap :
          (bs.map fun b => (b.1, canonical b.2)).Pairwise LocalTypeR.branchLe :=
        pairwise_map_snd bs canonical hPair
      have hSort : LocalTypeR.sortBranches (bs.map fun b => (b.1, canonical b.2)) =
          (bs.map fun b => (b.1, canonical b.2)) :=
        sortBranches_eq_of_pairwise _ hPairMap
      simp [canonical, canonicalBranches_eq_map, LocalTypeR.merge, bs, hRecvSorted, hSort])
    (fun v body ihBody => by
      simp [canonical, LocalTypeR.merge, ihBody])
    (fun v => by simp [canonical, LocalTypeR.merge])
    (AllBranches.nil _)
    (fun head tail ihHead ihTail =>
      AllBranches.cons _ head tail ihHead ihTail)
    (fun _fst _snd ihSnd => ihSnd)

end Rumpsteak.Proofs.Projection.Merging
