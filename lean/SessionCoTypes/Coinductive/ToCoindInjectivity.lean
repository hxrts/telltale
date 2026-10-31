
import Mathlib
import SessionCoTypes.Coinductive.LocalTypeC
import SessionCoTypes.Coinductive.Bridge
import SessionCoTypes.Coinductive.Observable
import SessionTypes.LocalTypeR

/- ## Structured Block 1 -/
set_option linter.dupNamespace false

/-! # toCoind Injectivity

Proof that the toCoind embedding is injective up to payload erasure.

**Decision: `toCoind` keeps erasing payloads.** `LocalTypeC` has no payload
field, so `toCoind t = toCoind u ↔ erasePayloads t = erasePayloads u`
(`to_coind_eq_iff_erase_payloads`); injectivity holds only modulo
`erasePayloads`. Since inductive `SessionCoTypes.EQ2` now compares branch
payloads (`BranchesRel` requires `a.2.1 = b.2.1`), inductive `EQ2` is
strictly finer than `EQ2C` through `toCoind`: only the direction
`EQ2 a b → EQ2C (toCoind a) (toCoind b)` can hold in general, and the
converse additionally needs payload agreement between `a` and `b`
(e.g. `erasePayloads a = a` and `erasePayloads b = b`, as for projections of
delegation-free global types). No completeness theorem of the form
`EQ2C (toCoind a) (toCoind b) → EQ2 a b` is stated in this development. -/

/-
The Problem. The toCoind embedding forgets branch payload annotations, so it is
injective only up to payload erasure. This is essential for round-trip correctness.

Solution Structure. Defines `erasePayloads`, proves `toCoind (erasePayloads t) = toCoind t`
and `toCoind t = toCoind u ↔ erasePayloads t = erasePayloads u` by case analysis over
constructors (mutually recursive with the branch-list versions), and indexing lemmas
for toCoindBranches (length, get).
-/

namespace SessionCoTypes.Coinductive

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

/-! ## Payload Erasure

`toCoind` forgets the optional payload `ValType` carried by each branch, so it is
injective only up to payload erasure. -/

mutual
  /-- Reset every branch payload annotation to `none`, recursively. -/
  def erasePayloads : LocalTypeR → LocalTypeR
    | .end => .end
    | .var x => .var x
    | .mu x body => .mu x (erasePayloads body)
    | .send p bs => .send p (erasePayloadsBranches bs)
    | .recv p bs => .recv p (erasePayloadsBranches bs)

  /-- Branch-list companion of `erasePayloads`. -/
  def erasePayloadsBranches : List BranchR → List BranchR
    | [] => []
    | (lb, _vt, t) :: rest => (lb, none, erasePayloads t) :: erasePayloadsBranches rest
end

mutual
  /-- Erasing payloads does not change the coinductive image. -/
  theorem to_coind_erase_payloads : ∀ t : LocalTypeR, toCoind (erasePayloads t) = toCoind t
    | .end => rfl
    | .var _ => rfl
    | .mu x body => by
        simp only [erasePayloads, to_coind_mu, to_coind_erase_payloads body]
    | .send p bs => by
        simp only [erasePayloads, to_coind_send, to_coind_branches_erase_payloads bs]
    | .recv p bs => by
        simp only [erasePayloads, to_coind_recv, to_coind_branches_erase_payloads bs]

  /-- Branch-list version of `to_coind_erase_payloads`. -/
  theorem to_coind_branches_erase_payloads :
      ∀ bs : List BranchR, toCoindBranches (erasePayloadsBranches bs) = toCoindBranches bs
    | [] => rfl
    | (lb, _vt, t) :: rest => by
        simp only [erasePayloadsBranches, toCoindBranches, to_coind_erase_payloads t,
          to_coind_branches_erase_payloads rest]
end

-- toCoind Injectivity up to Payload Erasure

mutual
  theorem to_coind_injective_erase :
      ∀ {t u : LocalTypeR}, toCoind t = toCoind u → erasePayloads t = erasePayloads u
    | .end, .end, _ => rfl
    | .end, .var _, h => by cases (congrArg head h)
    | .end, .mu _ _, h => by cases (congrArg head h)
    | .end, .send _ _, h => by cases (congrArg head h)
    | .end, .recv _ _, h => by cases (congrArg head h)
    | .var _, .end, h => by cases (congrArg head h)
    | .var x, .var y, h => by
        have hhead := congrArg head h
        have hx : x = y := by simpa [head_mk_var] using hhead
        subst hx; rfl
    | .var _, .mu _ _, h => by cases (congrArg head h)
    | .var _, .send _ _, h => by cases (congrArg head h)
    | .var _, .recv _ _, h => by cases (congrArg head h)
    | .mu _ _, .end, h => by cases (congrArg head h)
    | .mu _ _, .var _, h => by cases (congrArg head h)
    | .mu x body, .mu y body', h => by
        have hdest := congrArg PFunctor.M.dest h
        simp [toCoind, mkMu] at hdest
        have hxhy := (Sigma.mk.inj_iff.mp hdest)
        have hx : x = y := by cases hxhy.1; rfl
        subst hx
        have hfun : (fun _ : Unit => toCoind body) = (fun _ : Unit => toCoind body') := by
          exact eq_of_heq hxhy.2
        have hchild : toCoind body = toCoind body' := by
          simpa using congrArg (fun f => f ()) hfun
        exact congrArg (LocalTypeR.mu x) (to_coind_injective_erase hchild)
    | .mu _ _, .send _ _, h => by cases (congrArg head h)
    | .mu _ _, .recv _ _, h => by cases (congrArg head h)
    -- toCoind Injectivity up to Payload Erasure: Send/Recv Constructor Cases
    | .send _ _, .end, h => by cases (congrArg head h)
    | .send _ _, .var _, h => by cases (congrArg head h)
    | .send _ _, .mu _ _, h => by cases (congrArg head h)
    | .send p bs, .send q cs, h => by
        have hhead := congrArg head h
        have hhead' : p = q ∧ (toCoindBranches bs).map Prod.fst =
            (toCoindBranches cs).map Prod.fst := by
          simpa [toCoind, head_mk_send] using hhead
        have hpq : p = q := hhead'.1
        subst hpq
        have hbranches : toCoindBranches bs = toCoindBranches cs := by
          have h' := congrArg branchesOf h
          simpa [toCoind, branches_of_mk_send] using h'
        have hbs := to_coind_branches_injective_erase hbranches
        simp only [erasePayloads, hbs]
    | .send _ _, .recv _ _, h => by cases (congrArg head h)
/- ## Structured Block 2 -/
    | .recv _ _, .end, h => by cases (congrArg head h)
    | .recv _ _, .var _, h => by cases (congrArg head h)
    | .recv _ _, .mu _ _, h => by cases (congrArg head h)
    | .recv _ _, .send _ _, h => by cases (congrArg head h)
    | .recv p bs, .recv q cs, h => by
        have hhead := congrArg head h
        have hhead' : p = q ∧ (toCoindBranches bs).map Prod.fst =
            (toCoindBranches cs).map Prod.fst := by
          simpa [toCoind, head_mk_recv] using hhead
        have hpq : p = q := hhead'.1
        subst hpq
        have hbranches : toCoindBranches bs = toCoindBranches cs := by
          have h' := congrArg branchesOf h
          simpa [toCoind, branches_of_mk_recv] using h'
        have hbs := to_coind_branches_injective_erase hbranches
        simp only [erasePayloads, hbs]

  -- toCoindBranches Injectivity

  theorem to_coind_branches_injective_erase :
      ∀ {bs cs : List BranchR}, toCoindBranches bs = toCoindBranches cs →
        erasePayloadsBranches bs = erasePayloadsBranches cs
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [toCoindBranches] at h
    | _ :: _, [], h => by simp [toCoindBranches] at h
    | (lb, vt, t) :: bs, (lc, wt, u) :: cs, h => by
        have hcons :
            (lb, toCoind t) = (lc, toCoind u) ∧
              toCoindBranches bs = toCoindBranches cs := by
          simpa [toCoindBranches] using h
        rcases hcons with ⟨hhead, htail⟩
        have hlabel : lb = lc := congrArg Prod.fst hhead
        have ht := to_coind_injective_erase (congrArg Prod.snd hhead)
        have hrest := to_coind_branches_injective_erase htail
        simp only [erasePayloadsBranches, hlabel, ht, hrest]
end

/-- `toCoind` is injective up to payload erasure. -/
theorem to_coind_eq_iff_erase_payloads {t u : LocalTypeR} :
    toCoind t = toCoind u ↔ erasePayloads t = erasePayloads u := by
  refine ⟨to_coind_injective_erase, fun h => ?_⟩
  rw [← to_coind_erase_payloads t, ← to_coind_erase_payloads u, h]

-- toCoindBranches Indexing

lemma to_coind_branches_length (bs : List BranchR) :
    (toCoindBranches bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons _ _ ih => simp [toCoindBranches, ih]

lemma to_coind_branches_get {bs : List BranchR} (i : Fin bs.length) :
    (toCoindBranches bs).get (castFin (to_coind_branches_length bs).symm i) =
      ((bs.get i).1, toCoind (bs.get i).2.2) := by
  induction bs with
  | nil => exact (Fin.elim0 i)
  | cons b bs ih =>
      cases i using Fin.cases with
      | zero =>
          cases b with
          | mk label rest => cases rest with | mk vt cont => simp [toCoindBranches, castFin, to_coind_branches_length]
      | succ i =>
          have h := ih i
          simp only [castFin, List.get_eq_getElem, Fin.val_succ] at h ⊢
          cases b with
          | mk label rest => cases rest with | mk vt cont => simpa [toCoindBranches] using h

/- ## Structured Block 3 -/
lemma to_coind_branches_get_snd {bs : List BranchR} (i : Fin bs.length) :
    ((toCoindBranches bs).get (castFin (to_coind_branches_length bs).symm i)).2 =
      toCoind (bs.get i).2.2 := by
  simpa using congrArg Prod.snd (to_coind_branches_get (bs := bs) i)

lemma labels_get_eq {bs : List BranchR} (i : Fin (bs.map Prod.fst).length) :
    (bs.map Prod.fst).get i = (bs.get (castFin (by simp) i)).1 := by
  induction bs with
  | nil => exact (Fin.elim0 i)
  | cons b bs ih =>
      cases i using Fin.cases with
      | zero => cases b with | mk label rest => cases rest with | mk vt cont => simp [castFin]
      | succ i => simp [castFin]

end SessionCoTypes.Coinductive
