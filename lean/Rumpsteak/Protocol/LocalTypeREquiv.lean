import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ProjectionR
import Mathlib.Data.List.Forall2

/-! # Rumpsteak.Protocol.LocalTypeREquiv

Equi-recursive equivalence for local types.

This mirrors the shape of the coinductive EQ2 relation in the Coq artifact
(`subject_reduction/theories/CoTypes/coLocal.v`), but is encoded as an inductive
equivalence closure with explicit μ-unfold and branch-alignment rules (branch
lists are assumed to be in a canonical order, e.g. sorted by label name).
This is the minimal relation needed for projection commutation lemmas.
-/

namespace Rumpsteak.Protocol.LocalTypeR

open Rumpsteak.Protocol.GlobalType (Label)
abbrev sortBranches := Rumpsteak.Protocol.ProjectionR.LocalTypeR.sortBranches

mutual
  inductive LocalTypeR.equiv : LocalTypeR → LocalTypeR → Prop
    | refl (t : LocalTypeR) : LocalTypeR.equiv t t
    | symm {t1 t2 : LocalTypeR} : LocalTypeR.equiv t1 t2 → LocalTypeR.equiv t2 t1
    | trans {t1 t2 t3 : LocalTypeR} :
        LocalTypeR.equiv t1 t2 → LocalTypeR.equiv t2 t3 → LocalTypeR.equiv t1 t3
    | mu_unfold (t : String) (body : LocalTypeR) :
        LocalTypeR.equiv (.mu t body) (body.substitute t (.mu t body))
    | send (partner : String) (bs1 bs2 : List (Label × LocalTypeR)) :
        BranchesEquiv (sortBranches bs1) (sortBranches bs2) →
        LocalTypeR.equiv (.send partner bs1) (.send partner bs2)
    | recv (partner : String) (bs1 bs2 : List (Label × LocalTypeR)) :
        BranchesEquiv (sortBranches bs1) (sortBranches bs2) →
        LocalTypeR.equiv (.recv partner bs1) (.recv partner bs2)

  inductive BranchesEquiv : List (Label × LocalTypeR) → List (Label × LocalTypeR) → Prop
    | nil : BranchesEquiv [] []
    | cons (l1 l2 : Label) (t1 t2 : LocalTypeR)
        (bs1 bs2 : List (Label × LocalTypeR)) :
        l1.name = l2.name →
        LocalTypeR.equiv t1 t2 →
        BranchesEquiv bs1 bs2 →
        BranchesEquiv ((l1, t1) :: bs1) ((l2, t2) :: bs2)
end

/-! ## Coq-aligned naming

`EQ2` in the Coq artifact corresponds to the equi-recursive equivalence here. -/
abbrev EQ2 := LocalTypeR.equiv

theorem eq2_iff_equiv {t1 t2 : LocalTypeR} : EQ2 t1 t2 ↔ LocalTypeR.equiv t1 t2 := Iff.rfl

/-- Canonicalized branch equivalence (sort by label name before comparing). -/
def BranchesEquivNorm (bs1 bs2 : List (Label × LocalTypeR)) : Prop :=
  BranchesEquiv (sortBranches bs1) (sortBranches bs2)

theorem LocalTypeR.equiv_refl (t : LocalTypeR) : LocalTypeR.equiv t t :=
  LocalTypeR.equiv.refl t

theorem LocalTypeR.equiv_symm {t1 t2 : LocalTypeR} (h : LocalTypeR.equiv t1 t2) :
    LocalTypeR.equiv t2 t1 :=
  @LocalTypeR.equiv.symm t1 t2 h

theorem LocalTypeR.equiv_trans {t1 t2 t3 : LocalTypeR} :
    LocalTypeR.equiv t1 t2 → LocalTypeR.equiv t2 t3 → LocalTypeR.equiv t1 t3 :=
  @LocalTypeR.equiv.trans t1 t2 t3

theorem LocalTypeR.equiv_mu_unfold (t : String) (body : LocalTypeR) :
    LocalTypeR.equiv (.mu t body) (body.substitute t (.mu t body)) :=
  LocalTypeR.equiv.mu_unfold t body

theorem LocalTypeR.equiv_send
    (partner : String) (bs1 bs2 : List (Label × LocalTypeR)) :
    BranchesEquivNorm bs1 bs2 →
    LocalTypeR.equiv (.send partner bs1) (.send partner bs2) :=
  LocalTypeR.equiv.send partner bs1 bs2


theorem LocalTypeR.equiv_recv
    (partner : String) (bs1 bs2 : List (Label × LocalTypeR)) :
    BranchesEquivNorm bs1 bs2 →
    LocalTypeR.equiv (.recv partner bs1) (.recv partner bs2) :=
  LocalTypeR.equiv.recv partner bs1 bs2


theorem BranchesEquiv_refl (bs : List (Label × LocalTypeR)) : BranchesEquiv bs bs := by
  induction bs with
  | nil => exact BranchesEquiv.nil
  | cons bt rest ih =>
    cases bt with
    | mk l t =>
      exact BranchesEquiv.cons l l t t rest rest rfl (LocalTypeR.equiv_refl t) ih

theorem BranchesEquiv_symm {bs1 bs2 : List (Label × LocalTypeR)}
    (h : BranchesEquiv bs1 bs2) : BranchesEquiv bs2 bs1 := by
  cases h with
  | nil => exact BranchesEquiv.nil
  | cons l1 l2 t1 t2 bs1 bs2 hname heq hrest =>
    exact BranchesEquiv.cons l2 l1 t2 t1 bs2 bs1 hname.symm
      (LocalTypeR.equiv_symm heq) (BranchesEquiv_symm hrest)

theorem BranchesEquiv_trans {bs1 bs2 bs3 : List (Label × LocalTypeR)}
    (h12 : BranchesEquiv bs1 bs2) (h23 : BranchesEquiv bs2 bs3) :
    BranchesEquiv bs1 bs3 := by
  cases h12 with
  | nil =>
    cases h23 with
    | nil => exact BranchesEquiv.nil
  | cons l1 l2 t1 t2 bs1 bs2 hname12 heq12 hrest12 =>
    cases h23 with
    | cons l2' l3 t2' t3 bs2' bs3 hname23 heq23 hrest23 =>
      exact BranchesEquiv.cons l1 l3 t1 t3 bs1 bs3
        (Eq.trans hname12 hname23) (LocalTypeR.equiv_trans heq12 heq23)
        (BranchesEquiv_trans hrest12 hrest23)

theorem BranchesEquivNorm_refl (bs : List (Label × LocalTypeR)) :
    BranchesEquivNorm bs bs :=
  BranchesEquiv_refl (sortBranches bs)

theorem BranchesEquivNorm_symm {bs1 bs2 : List (Label × LocalTypeR)}
    (h : BranchesEquivNorm bs1 bs2) : BranchesEquivNorm bs2 bs1 :=
  BranchesEquiv_symm h

theorem BranchesEquivNorm_trans {bs1 bs2 bs3 : List (Label × LocalTypeR)}
    (h12 : BranchesEquivNorm bs1 bs2) (h23 : BranchesEquivNorm bs2 bs3) :
    BranchesEquivNorm bs1 bs3 :=
  BranchesEquiv_trans h12 h23

theorem BranchesEquiv_of_forall2 {bs1 bs2 : List (Label × LocalTypeR)}
    (h : List.Forall₂ (fun b1 b2 =>
      b1.1.name = b2.1.name ∧ LocalTypeR.equiv b1.2 b2.2) bs1 bs2) :
    BranchesEquiv bs1 bs2 := by
  cases bs1 with
  | nil =>
    cases bs2 with
    | nil =>
      cases h
      exact BranchesEquiv.nil
    | cons _ _ =>
      cases h
  | cons a bs1' =>
    cases bs2 with
    | nil =>
      cases h
    | cons b bs2' =>
      cases h with
      | cons hhead htail =>
        rcases hhead with ⟨hname, heq⟩
        cases a with
        | mk l1 t1 =>
          cases b with
          | mk l2 t2 =>
        exact BranchesEquiv.cons l1 l2 t1 t2 bs1' bs2' hname heq
          (BranchesEquiv_of_forall2 htail)

theorem LocalTypeR.equiv_send_of_forall2
    (partner : String) (bs1 bs2 : List (Label × LocalTypeR)) :
    List.Forall₂ (fun b1 b2 =>
      b1.1.name = b2.1.name ∧ LocalTypeR.equiv b1.2 b2.2)
      (sortBranches bs1) (sortBranches bs2) →
    LocalTypeR.equiv (.send partner bs1) (.send partner bs2) := by
  intro h
  exact LocalTypeR.equiv_send partner bs1 bs2 (BranchesEquiv_of_forall2 h)

theorem LocalTypeR.equiv_recv_of_forall2
    (partner : String) (bs1 bs2 : List (Label × LocalTypeR)) :
    List.Forall₂ (fun b1 b2 =>
      b1.1.name = b2.1.name ∧ LocalTypeR.equiv b1.2 b2.2)
      (sortBranches bs1) (sortBranches bs2) →
    LocalTypeR.equiv (.recv partner bs1) (.recv partner bs2) := by
  intro h
  exact LocalTypeR.equiv_recv partner bs1 bs2 (BranchesEquiv_of_forall2 h)

end Rumpsteak.Protocol.LocalTypeR
