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
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

attribute [local instance] boolRelToRel

/-! ## Main theorem -/

theorem merge_associative : MergeAssociative := by
  intro t1 t2 t3
  have ht1 : MergeAssocAt t1 := by
    refine LocalTypeR.recOn
      (motive_1 := fun t => MergeAssocAt t)
      (motive_2 := fun bs => AllBranches MergeAssocAt bs)
      (motive_3 := fun b => MergeAssocAt b.2)
      t1
      -- Case: end
      (by
        intro u v
        show (LocalTypeR.merge .end u).bind (fun m => LocalTypeR.merge m v) =
             (LocalTypeR.merge u v).bind (fun m => LocalTypeR.merge .end m)
        match u with
        | .end => cases v <;> simp [LocalTypeR.merge]
        | .send p1 bs1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match v with
          | .end => simp [LocalTypeR.merge]
          | .send p2 bs2 =>
            simp only [LocalTypeR.merge]
            by_cases hp : p1 = p2
            · simp only [hp, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) <;>
                simp [Option.bind, LocalTypeR.merge]
            · simp [hp, bne_iff_ne, Option.bind]
          | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
          | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .recv p1 bs1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match v with
          | .end => simp [LocalTypeR.merge]
          | .send _ _ => simp [LocalTypeR.merge, Option.bind]
          | .recv p2 bs2 =>
            simp only [LocalTypeR.merge]
            by_cases hp : p1 = p2
            · simp only [hp, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) <;>
                simp [Option.bind, LocalTypeR.merge]
            · simp [hp, bne_iff_ne, Option.bind]
          | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .mu x1 body1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match v with
          | .end => simp [LocalTypeR.merge]
          | .send _ _ => simp [LocalTypeR.merge, Option.bind]
          | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
          | .mu x2 body2 =>
            simp only [LocalTypeR.merge]
            by_cases hx : x1 = x2
            · simp only [hx, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.merge body1 body2 <;>
                simp [Option.bind, LocalTypeR.merge]
            · simp [hx, bne_iff_ne, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .var x1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match v with
          | .end => simp [LocalTypeR.merge]
          | .send _ _ => simp [LocalTypeR.merge, Option.bind]
          | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
          | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
          | .var x2 =>
            simp only [LocalTypeR.merge]
            by_cases hx : x1 = x2
            · simp [hx, Option.bind, LocalTypeR.merge]
            · simp [hx, Option.bind])
      -- Case: send
      (fun partner branches1 ihBranches => by
        intro u v
        cases u with
        | send partner2 branches2 =>
          cases v with
          | send partner3 branches3 =>
            by_cases hP12 : partner = partner2
            · subst hP12
              by_cases hP13 : partner = partner3
              · subst hP13
                let bs1 := LocalTypeR.sortBranches branches1
                let bs2 := LocalTypeR.sortBranches branches2
                let bs3 := LocalTypeR.sortBranches branches3

                have hperm1 : bs1.Perm branches1 := by
                  simpa [bs1, LocalTypeR.sortBranches] using
                    (List.mergeSort_perm branches1 LocalTypeR.branchLe)
                have ihSorted : AllBranches MergeAssocAt bs1 :=
                  AllBranches.of_perm _ hperm1 ihBranches

                have hSorted1 : bs1.Pairwise LocalTypeR.branchLe := by
                  simpa [bs1] using pairwise_sortBranches branches1
                have hSorted2 : bs2.Pairwise LocalTypeR.branchLe := by
                  simpa [bs2] using pairwise_sortBranches branches2
                have hSorted3 : bs3.Pairwise LocalTypeR.branchLe := by
                  simpa [bs3] using pairwise_sortBranches branches3

                have hSort12 :
                    ∀ {m12}, LocalTypeR.mergeSendSorted bs1 bs2 = some m12 →
                      LocalTypeR.sortBranches m12 = m12 := by
                  intro m12 hm12
                  have hPair : m12.Pairwise LocalTypeR.branchLe :=
                    mergeSendSorted_pairwise (bs1 := bs1) (bs2 := bs2) (rest := m12) hSorted1 hm12
                  exact sortBranches_eq_of_pairwise m12 hPair

                have hSort23 :
                    ∀ {m23}, LocalTypeR.mergeSendSorted bs2 bs3 = some m23 →
                      LocalTypeR.sortBranches m23 = m23 := by
                  intro m23 hm23
                  have hPair : m23.Pairwise LocalTypeR.branchLe :=
                    mergeSendSorted_pairwise (bs1 := bs2) (bs2 := bs3) (rest := m23) hSorted2 hm23
                  exact sortBranches_eq_of_pairwise m23 hPair

                have hAssoc :=
                  mergeSendSorted_assoc bs1 bs2 bs3 ihSorted

                have hL :
                    (LocalTypeR.merge (.send partner branches1) (.send partner branches2)).bind
                        (fun m => LocalTypeR.merge m (.send partner branches3)) =
                      (LocalTypeR.mergeSendSorted bs1 bs2).bind (fun m12 =>
                        (LocalTypeR.mergeSendSorted m12 bs3).bind (fun m123 =>
                          some (.send partner m123))) := by
                  simp only [LocalTypeR.merge, bs1, bs2, bs3, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                  simp only [Option.bind_eq_bind, Option.bind_some]
                  conv_lhs =>
                    rw [Option.bind_assoc]
                  cases hMerge12 : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches branches1)
                                                              (LocalTypeR.sortBranches branches2) with
                  | none => simp [Option.bind]
                  | some m12 =>
                    simp only [Option.bind]
                    have hSortM12 : LocalTypeR.sortBranches m12 = m12 := hSort12 hMerge12
                    simp only [LocalTypeR.merge, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                    simp only [Option.bind_eq_bind, Option.bind_some]
                    rw [hSortM12]

                have hR :
                    (LocalTypeR.merge (.send partner branches2) (.send partner branches3)).bind
                        (fun m => LocalTypeR.merge (.send partner branches1) m) =
                      (LocalTypeR.mergeSendSorted bs2 bs3).bind (fun m23 =>
                        (LocalTypeR.mergeSendSorted bs1 m23).bind (fun m123 =>
                          some (.send partner m123))) := by
                  simp only [LocalTypeR.merge, bs1, bs2, bs3, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                  simp only [Option.bind_eq_bind, Option.bind_some]
                  conv_lhs =>
                    rw [Option.bind_assoc]
                  cases hMerge23 : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches branches2)
                                                              (LocalTypeR.sortBranches branches3) with
                  | none => simp [Option.bind]
                  | some m23 =>
                    simp only [Option.bind]
                    have hSortM23 : LocalTypeR.sortBranches m23 = m23 := hSort23 hMerge23
                    simp only [LocalTypeR.merge, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                    simp only [Option.bind_eq_bind, Option.bind_some]
                    rw [hSortM23]

                simp only [MergeAssocAt]
                intro u v
                rw [hL, hR]
                exact hAssoc
              · simp only [MergeAssocAt]
                intro u v
                simp only [LocalTypeR.merge, bne_iff_ne, Ne.symm hP13, ↓reduceIte, Option.none_bind]
                simp only [bne_iff_ne, Ne.symm hP13, ↓reduceIte, Option.none_bind]
            · simp only [MergeAssocAt]
              intro u v
              simp only [LocalTypeR.merge, bne_iff_ne, Ne.symm hP12, ↓reduceIte, Option.none_bind]
              cases v with
              | send partner3 branches3 =>
                simp only [LocalTypeR.merge, Option.bind]
                by_cases hP23 : partner2 = partner3
                · subst hP23
                  cases h : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches branches2)
                                                        (LocalTypeR.sortBranches branches3) with
                  | none => simp [Option.bind]
                  | some merged =>
                    simp only [↓reduceIte, Option.some_bind]
                    simp only [LocalTypeR.merge, bne_iff_ne, hP12, ↓reduceIte]
                · simp only [bne_iff_ne, Ne.symm hP23, ↓reduceIte, Option.none_bind]
              | _ => simp [LocalTypeR.merge, Option.bind]
          | _ =>
            simp only [MergeAssocAt]
            intro u v
            simp only [LocalTypeR.merge, Option.none_bind]
            cases v <;> simp [LocalTypeR.merge, Option.bind]
        | _ =>
          simp only [MergeAssocAt]
          intro u v
          simp only [LocalTypeR.merge, Option.none_bind]
          cases v <;> simp [LocalTypeR.merge, Option.bind])
      -- Case: recv
      (fun partner branches1 ihBranches => by
        intro u v
        cases u with
        | recv partner2 branches2 =>
          cases v with
          | recv partner3 branches3 =>
            by_cases hP12 : partner = partner2
            · subst hP12
              by_cases hP13 : partner = partner3
              · subst hP13
                let bs1 := LocalTypeR.sortBranches branches1
                let bs2 := LocalTypeR.sortBranches branches2
                let bs3 := LocalTypeR.sortBranches branches3

                have hperm1 : bs1.Perm branches1 := by
                  simpa [bs1, LocalTypeR.sortBranches] using
                    (List.mergeSort_perm branches1 LocalTypeR.branchLe)
                have ihSorted : AllBranches MergeAssocAt bs1 :=
                  AllBranches.of_perm _ hperm1 ihBranches

                have hSorted1 : bs1.Pairwise LocalTypeR.branchLe := by
                  simpa [bs1] using pairwise_sortBranches branches1
                have hSorted2 : bs2.Pairwise LocalTypeR.branchLe := by
                  simpa [bs2] using pairwise_sortBranches branches2

                have hSort12 :
                    ∀ {m12}, LocalTypeR.mergeRecvSorted bs1 bs2 = some m12 →
                      LocalTypeR.sortBranches m12 = m12 := by
                  intro m12 hm12
                  have hPair : m12.Pairwise LocalTypeR.branchLe :=
                    mergeRecvSorted_pairwise (bs1 := bs1) (bs2 := bs2) (rest := m12) hSorted1 hSorted2 hm12
                  exact sortBranches_eq_of_pairwise m12 hPair

                have hSort23 :
                    ∀ {m23}, LocalTypeR.mergeRecvSorted bs2 bs3 = some m23 →
                      LocalTypeR.sortBranches m23 = m23 := by
                  intro m23 hm23
                  have hSorted3 : bs3.Pairwise LocalTypeR.branchLe := by
                    simpa [bs3] using pairwise_sortBranches branches3
                  have hPair : m23.Pairwise LocalTypeR.branchLe :=
                    mergeRecvSorted_pairwise (bs1 := bs2) (bs2 := bs3) (rest := m23) hSorted2 hSorted3 hm23
                  exact sortBranches_eq_of_pairwise m23 hPair

                have hAssoc :=
                  mergeRecvSorted_assoc bs1 bs2 bs3 ihSorted

                have hL :
                    (LocalTypeR.merge (.recv partner branches1) (.recv partner branches2)).bind
                        (fun m => LocalTypeR.merge m (.recv partner branches3)) =
                      (LocalTypeR.mergeRecvSorted bs1 bs2).bind (fun m12 =>
                        (LocalTypeR.mergeRecvSorted m12 bs3).bind (fun m123 =>
                          some (.recv partner m123))) := by
                  simp only [LocalTypeR.merge, bs1, bs2, bs3, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                  simp only [Option.bind_eq_bind, Option.bind_some]
                  conv_lhs =>
                    rw [Option.bind_assoc]
                  cases hMerge12 : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches branches1)
                                                              (LocalTypeR.sortBranches branches2) with
                  | none => simp [Option.bind]
                  | some m12 =>
                    simp only [Option.bind]
                    have hSortM12 : LocalTypeR.sortBranches m12 = m12 := hSort12 hMerge12
                    simp only [LocalTypeR.merge, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                    simp only [Option.bind_eq_bind, Option.bind_some]
                    rw [hSortM12]

                have hR :
                    (LocalTypeR.merge (.recv partner branches2) (.recv partner branches3)).bind
                        (fun m => LocalTypeR.merge (.recv partner branches1) m) =
                      (LocalTypeR.mergeRecvSorted bs2 bs3).bind (fun m23 =>
                        (LocalTypeR.mergeRecvSorted bs1 m23).bind (fun m123 =>
                          some (.recv partner m123))) := by
                  simp only [LocalTypeR.merge, bs1, bs2, bs3, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                  simp only [Option.bind_eq_bind, Option.bind_some]
                  conv_lhs =>
                    rw [Option.bind_assoc]
                  cases hMerge23 : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches branches2)
                                                              (LocalTypeR.sortBranches branches3) with
                  | none => simp [Option.bind]
                  | some m23 =>
                    simp only [Option.bind]
                    have hSortM23 : LocalTypeR.sortBranches m23 = m23 := hSort23 hMerge23
                    simp only [LocalTypeR.merge, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                    simp only [Option.bind_eq_bind, Option.bind_some]
                    rw [hSortM23]

                simp only [MergeAssocAt]
                intro u v
                rw [hL, hR]
                exact hAssoc
              · simp only [MergeAssocAt]
                intro u v
                simp only [LocalTypeR.merge, bne_iff_ne, Ne.symm hP13, ↓reduceIte, Option.none_bind]
                simp only [bne_iff_ne, Ne.symm hP13, ↓reduceIte, Option.none_bind]
            · simp only [MergeAssocAt]
              intro u v
              simp only [LocalTypeR.merge, bne_iff_ne, Ne.symm hP12, ↓reduceIte, Option.none_bind]
              cases v with
              | recv partner3 branches3 =>
                simp only [LocalTypeR.merge, Option.bind]
                by_cases hP23 : partner2 = partner3
                · subst hP23
                  cases h : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches branches2)
                                                        (LocalTypeR.sortBranches branches3) with
                  | none => simp [Option.bind]
                  | some merged =>
                    simp only [↓reduceIte, Option.some_bind, LocalTypeR.merge, bne_iff_ne, hP12, ↓reduceIte]
                · simp only [bne_iff_ne, Ne.symm hP23, ↓reduceIte, Option.none_bind]
              | _ => simp [LocalTypeR.merge, Option.bind]
          | _ =>
            simp only [MergeAssocAt]
            intro u v
            simp only [LocalTypeR.merge, Option.none_bind]
            cases v <;> simp [LocalTypeR.merge, Option.bind]
        | _ =>
          simp only [MergeAssocAt]
          intro u v
          simp only [LocalTypeR.merge, Option.none_bind]
          cases v <;> simp [LocalTypeR.merge, Option.bind])
      -- Case: mu
      (fun v body ihBody => by
        intro u w
        show (LocalTypeR.merge (.mu v body) u).bind (fun m => LocalTypeR.merge m w) =
             (LocalTypeR.merge u w).bind (fun m => LocalTypeR.merge (.mu v body) m)
        match u with
        | .end => simp [LocalTypeR.merge, Option.bind]
        | .send _ _ =>
          simp only [LocalTypeR.merge, Option.none_bind]
          cases w <;> simp [LocalTypeR.merge, Option.bind]
        | .recv _ _ =>
          simp only [LocalTypeR.merge, Option.none_bind]
          cases w <;> simp [LocalTypeR.merge, Option.bind]
        | .var _ =>
          simp only [LocalTypeR.merge, Option.none_bind]
          cases w <;> simp [LocalTypeR.merge, Option.bind]
        | .mu v' body' =>
          match w with
          | .end =>
            simp only [LocalTypeR.merge, Option.bind]
            by_cases hv : v = v'
            · simp [hv, Option.bind]
            · simp [hv, bne_iff_ne, Option.bind]
          | .send _ _ =>
            simp only [LocalTypeR.merge, Option.bind]
            by_cases hv : v = v'
            · simp [hv, Option.bind]
            · simp [hv, bne_iff_ne, Option.bind]
          | .recv _ _ =>
            simp only [LocalTypeR.merge, Option.bind]
            by_cases hv : v = v'
            · simp [hv, Option.bind]
            · simp [hv, bne_iff_ne, Option.bind]
          | .var _ =>
            simp only [LocalTypeR.merge, Option.bind]
            by_cases hv : v = v'
            · simp [hv, Option.bind]
            · simp [hv, bne_iff_ne, Option.bind]
          | .mu v'' body'' =>
            simp only [LocalTypeR.merge, Option.bind]
            by_cases hv : v = v'
            · subst hv
              by_cases hv'' : v = v''
              · subst hv''
                simp only [beq_self_eq_true, ↓reduceIte, bne_self_eq_false, Option.bind_eq_bind]
                have hBodyAssoc := ihBody body' body''
                cases hM12 : LocalTypeR.merge body body' with
                | none =>
                  simp only [Option.none_bind]
                  cases hM23 : LocalTypeR.merge body' body'' with
                  | none => simp [Option.bind]
                  | some m23 =>
                    simp only [Option.some_bind]
                    have : (LocalTypeR.merge body body').bind (fun m => LocalTypeR.merge m body'') =
                           (LocalTypeR.merge body' body'').bind (fun m => LocalTypeR.merge body m) := hBodyAssoc
                    simp only [hM12, hM23, Option.none_bind, Option.some_bind] at this
                    simp [this]
                | some m12 =>
                  simp only [Option.some_bind]
                  cases hM23 : LocalTypeR.merge body' body'' with
                  | none =>
                    simp only [Option.none_bind]
                    have : (LocalTypeR.merge body body').bind (fun m => LocalTypeR.merge m body'') =
                           (LocalTypeR.merge body' body'').bind (fun m => LocalTypeR.merge body m) := hBodyAssoc
                    simp only [hM12, hM23, Option.some_bind, Option.none_bind] at this
                    simp [this]
                  | some m23 =>
                    simp only [Option.some_bind]
                    have : (LocalTypeR.merge body body').bind (fun m => LocalTypeR.merge m body'') =
                           (LocalTypeR.merge body' body'').bind (fun m => LocalTypeR.merge body m) := hBodyAssoc
                    simp only [hM12, hM23, Option.some_bind] at this
                    cases hM123 : LocalTypeR.merge m12 body'' with
                    | none =>
                      simp only [Option.none_bind]
                      rw [← this]
                      simp [hM123]
                    | some m123 =>
                      simp only [Option.some_bind]
                      have hEq : LocalTypeR.merge m12 body'' = LocalTypeR.merge body m23 := this
                      simp only [hM123] at hEq
                      simp [hEq]
              · simp only [beq_self_eq_true, ↓reduceIte, bne_self_eq_false, bne_iff_ne, hv'', ↓reduceIte]
                simp only [Option.bind_eq_bind, Option.none_bind]
                cases hM12 : LocalTypeR.merge body body' with
                | none => simp [Option.bind]
                | some m12 => simp [Option.bind]
            · simp only [bne_iff_ne, hv, ↓reduceIte, Option.none_bind]
              by_cases hv' : v' = v''
              · subst hv'
                simp only [beq_self_eq_true, ↓reduceIte, Option.bind_eq_bind]
                cases hM23 : LocalTypeR.merge body' body'' with
                | none => simp [Option.bind]
                | some m23 =>
                  simp only [Option.some_bind]
                  simp only [LocalTypeR.merge, bne_iff_ne, hv, ↓reduceIte]
              · simp [bne_iff_ne, hv', Option.bind])
      -- Case: var
      (fun v => by
        intro u w
        show (LocalTypeR.merge (.var v) u).bind (fun m => LocalTypeR.merge m w) =
             (LocalTypeR.merge u w).bind (fun m => LocalTypeR.merge (.var v) m)
        match u with
        | .end =>
          simp only [LocalTypeR.merge, Option.none_bind]
          cases w <;> simp [LocalTypeR.merge, Option.bind]
        | .send p1 bs1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match w with
          | .end => simp [LocalTypeR.merge]
          | .send p2 bs2 =>
            simp only [LocalTypeR.merge]
            by_cases hp : p1 = p2
            · simp only [hp, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) <;>
                simp [Option.bind, LocalTypeR.merge]
            · simp [hp, bne_iff_ne, Option.bind]
          | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
          | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .recv p1 bs1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match w with
          | .end => simp [LocalTypeR.merge]
          | .send _ _ => simp [LocalTypeR.merge, Option.bind]
          | .recv p2 bs2 =>
            simp only [LocalTypeR.merge]
            by_cases hp : p1 = p2
            · simp only [hp, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) <;>
                simp [Option.bind, LocalTypeR.merge]
            · simp [hp, bne_iff_ne, Option.bind]
          | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .mu x1 body1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match w with
          | .end => simp [LocalTypeR.merge]
          | .send _ _ => simp [LocalTypeR.merge, Option.bind]
          | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
          | .mu x2 body2 =>
            simp only [LocalTypeR.merge]
            by_cases hx : x1 = x2
            · simp only [hx, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.merge body1 body2 <;> simp [Option.bind, LocalTypeR.merge]
            · simp [hx, bne_iff_ne, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .var a =>
          simp only [LocalTypeR.merge]
          by_cases hva : v = a
          · subst hva
            match w with
            | .end => simp [LocalTypeR.merge]
            | .send _ _ => simp [LocalTypeR.merge, Option.bind]
            | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
            | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
            | .var b =>
              by_cases hvb : v = b
              · simp [hvb, LocalTypeR.merge, Option.bind]
              · simp [hvb, LocalTypeR.merge, Option.bind]
          · simp only [hva, ↓reduceIte, Option.none_bind]
            match w with
            | .end => simp [LocalTypeR.merge]
            | .send _ _ => simp [LocalTypeR.merge, Option.bind]
            | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
            | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
            | .var b =>
              by_cases hab : a = b
              · subst hab
                simp [LocalTypeR.merge, Option.bind, hva]
              · simp [hab, LocalTypeR.merge, Option.bind])
      -- motive_2 and motive_3: branch list induction
      (AllBranches.nil _)
      (fun head tail ihHead ihTail =>
        AllBranches.cons _ head tail ihHead ihTail)
      (fun _fst _snd ihSnd => ihSnd)
  simpa [MergeAssociative, MergeAssocAt] using ht1 t2 t3

end Rumpsteak.Proofs.Projection.Merging
