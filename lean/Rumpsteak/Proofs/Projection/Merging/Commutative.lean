import Rumpsteak.Proofs.Projection.Merging.Basic
import Rumpsteak.Proofs.Projection.Merging.SortLemmas

/-! # Rumpsteak.Proofs.Projection.Merging.Commutative

Proof that merge is commutative.

## Overview

This module proves `MergeCommutative`: ∀ T1 T2, T1.merge T2 = T2.merge T1.

The proof uses nested structural induction on local types. For send and recv
types, commutativity reduces to the commutativity of the sorted branch merge
operations.
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

attribute [local instance] boolRelToRel

/-! ## Main theorem -/

theorem merge_commutative : MergeCommutative := by
  intro t1 t2
  -- Structural case split on both types.
  have ht1 :
      (∀ t1 : LocalTypeR, ∀ t2 : LocalTypeR, LocalTypeR.merge t1 t2 = LocalTypeR.merge t2 t1) := by
    intro t1
    refine LocalTypeR.recOn
      (motive_1 := fun t1 => ∀ t2, LocalTypeR.merge t1 t2 = LocalTypeR.merge t2 t1)
      (motive_2 := fun bs =>
        AllBranches (fun t => ∀ u, LocalTypeR.merge t u = LocalTypeR.merge u t) bs)
      (motive_3 := fun b => ∀ u, LocalTypeR.merge b.2 u = LocalTypeR.merge u b.2)
      t1
      (by
        intro t2
        cases t2 <;> simp [LocalTypeR.merge])
      (fun partner branches ihBranches => by
        intro t2
        cases t2 with
        | send partner2 branches2 =>
          by_cases hPartner : partner = partner2
          · subst hPartner
            -- Reduce to commutativity of send-branch merging.
            let bs1 := LocalTypeR.sortBranches branches
            let bs2 := LocalTypeR.sortBranches branches2
            have hperm : bs1.Perm branches := by
              simpa [bs1, LocalTypeR.sortBranches] using (List.mergeSort_perm branches LocalTypeR.branchLe)
            have ihSorted :
                AllBranches (fun t => ∀ u, LocalTypeR.merge t u = LocalTypeR.merge u t) bs1 :=
              AllBranches.of_perm _ hperm ihBranches
            have hSend :
                LocalTypeR.mergeSendSorted bs1 bs2 = LocalTypeR.mergeSendSorted bs2 bs1 := by
              exact mergeSendSorted_comm bs1 bs2 ihSorted
            simp [LocalTypeR.merge, bs1, bs2, hSend]
          · have hPartner' : partner2 ≠ partner := fun h => hPartner (Eq.symm h)
            simp [LocalTypeR.merge, hPartner, hPartner']
        | _ =>
          simp [LocalTypeR.merge])
      (fun partner branches ihBranches => by
        intro t2
        cases t2 with
        | recv partner2 branches2 =>
          by_cases hPartner : partner = partner2
          · subst hPartner
            -- Reduce to commutativity of recv-branch merging.
            let bs1 := LocalTypeR.sortBranches branches
            let bs2 := LocalTypeR.sortBranches branches2
            have hperm : bs1.Perm branches := by
              simpa [bs1, LocalTypeR.sortBranches] using (List.mergeSort_perm branches LocalTypeR.branchLe)
            have ihSorted :
                AllBranches (fun t => ∀ u, LocalTypeR.merge t u = LocalTypeR.merge u t) bs1 :=
              AllBranches.of_perm _ hperm ihBranches
            have hRecv :
                LocalTypeR.mergeRecvSorted bs1 bs2 = LocalTypeR.mergeRecvSorted bs2 bs1 :=
              by
                exact mergeRecvSorted_comm bs1 bs2 ihSorted
            simp [LocalTypeR.merge, bs1, bs2, hRecv]
          · have hPartner' : partner2 ≠ partner := fun h => hPartner (Eq.symm h)
            simp [LocalTypeR.merge, hPartner, hPartner']
        | _ =>
          simp [LocalTypeR.merge])
      (fun v body ihBody => by
        intro t2
        cases t2 with
        | mu v2 body2 =>
          by_cases h : v = v2
          · subst h
            have hBody : LocalTypeR.merge body body2 = LocalTypeR.merge body2 body := ihBody body2
            simp [LocalTypeR.merge, hBody]
          · have h' : v2 ≠ v := fun hv => h hv.symm
            simp [LocalTypeR.merge, h, h']
        | _ =>
          simp [LocalTypeR.merge])
      (fun v => by
        intro t2
        cases t2 with
        | var a =>
          by_cases h : v = a
          · subst h
            simp [LocalTypeR.merge]
          · have h' : a ≠ v := fun h2 => h h2.symm
            simp [LocalTypeR.merge, h, h']
        | _ =>
          simp [LocalTypeR.merge])
      (AllBranches.nil _)
      (fun head tail ihHead ihTail =>
        AllBranches.cons _ head tail ihHead ihTail)
      (fun _fst _snd ihSnd => ihSnd)
  exact ht1 t1 t2

end Rumpsteak.Proofs.Projection.Merging
