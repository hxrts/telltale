import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.Observable
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-!
The Problem. The toCoind embedding from inductive to coinductive types should be
injective: distinct inductive types should map to distinct coinductive types.
This is essential for round-trip correctness.

The difficulty is that the proof requires mutual induction over both LocalTypeR
and branch lists, with careful handling of each constructor case.

Solution Structure.
1. toCoind_injective: main injectivity theorem by case analysis
2. toCoindBranches_injective: branch list injectivity (mutually recursive)
3. Indexing lemmas for toCoindBranches (length, get)
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-! ## toCoind Injectivity -/

mutual
  theorem toCoind_injective : ∀ {t u : LocalTypeR}, toCoind t = toCoind u → t = u
    | .end, .end, _ => rfl
    | .end, .var _, h => by cases (congrArg head h)
    | .end, .mu _ _, h => by cases (congrArg head h)
    | .end, .send _ _, h => by cases (congrArg head h)
    | .end, .recv _ _, h => by cases (congrArg head h)
    | .var _, .end, h => by cases (congrArg head h)
    | .var x, .var y, h => by
        have hhead := congrArg head h
        have hx : x = y := by simpa [head_mkVar] using hhead
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
        exact congrArg (LocalTypeR.mu x) (toCoind_injective hchild)
    | .mu _ _, .send _ _, h => by cases (congrArg head h)
    | .mu _ _, .recv _ _, h => by cases (congrArg head h)
    | .send _ _, .end, h => by cases (congrArg head h)
    | .send _ _, .var _, h => by cases (congrArg head h)
    | .send _ _, .mu _ _, h => by cases (congrArg head h)
    | .send p bs, .send q cs, h => by
        have hhead := congrArg head h
        have hhead' : p = q ∧ (toCoindBranches bs).map Prod.fst =
            (toCoindBranches cs).map Prod.fst := by
          simpa [toCoind, head_mkSend] using hhead
        have hpq : p = q := hhead'.1
        subst hpq
        have hbranches : toCoindBranches bs = toCoindBranches cs := by
          have h' := congrArg branchesOf h
          simpa [toCoind, branchesOf_mkSend] using h'
        have hbs : bs = cs := toCoindBranches_injective hbranches
        subst hbs; rfl
    | .send _ _, .recv _ _, h => by cases (congrArg head h)
    | .recv _ _, .end, h => by cases (congrArg head h)
    | .recv _ _, .var _, h => by cases (congrArg head h)
    | .recv _ _, .mu _ _, h => by cases (congrArg head h)
    | .recv _ _, .send _ _, h => by cases (congrArg head h)
    | .recv p bs, .recv q cs, h => by
        have hhead := congrArg head h
        have hhead' : p = q ∧ (toCoindBranches bs).map Prod.fst =
            (toCoindBranches cs).map Prod.fst := by
          simpa [toCoind, head_mkRecv] using hhead
        have hpq : p = q := hhead'.1
        subst hpq
        have hbranches : toCoindBranches bs = toCoindBranches cs := by
          have h' := congrArg branchesOf h
          simpa [toCoind, branchesOf_mkRecv] using h'
        have hbs : bs = cs := toCoindBranches_injective hbranches
        subst hbs; rfl

  theorem toCoindBranches_injective :
      ∀ {bs cs : List (Label × LocalTypeR)}, toCoindBranches bs = toCoindBranches cs → bs = cs
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [toCoindBranches] at h
    | _ :: _, [], h => by simp [toCoindBranches] at h
    | (lb, t) :: bs, (lc, u) :: cs, h => by
        have hcons :
            (lb, toCoind t) = (lc, toCoind u) ∧
              toCoindBranches bs = toCoindBranches cs := by
          simpa [toCoindBranches] using h
        rcases hcons with ⟨hhead, htail⟩
        have hlabel : lb = lc := congrArg Prod.fst hhead
        have ht : t = u := toCoind_injective (congrArg Prod.snd hhead)
        subst hlabel; subst ht
        have hrest : bs = cs := toCoindBranches_injective htail
        subst hrest; rfl
end

/-! ## toCoindBranches Indexing -/

lemma toCoindBranches_length (bs : List (Label × LocalTypeR)) :
    (toCoindBranches bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons _ _ ih => simp [toCoindBranches, ih]

lemma toCoindBranches_get {bs : List (Label × LocalTypeR)} (i : Fin bs.length) :
    (toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i) =
      ((bs.get i).1, toCoind (bs.get i).2) := by
  induction bs with
  | nil => exact (Fin.elim0 i)
  | cons b bs ih =>
      cases i using Fin.cases with
      | zero =>
          cases b with
          | mk label cont => simp [toCoindBranches, castFin, toCoindBranches_length]
      | succ i => simpa [castFin, toCoindBranches_length] using ih i

lemma toCoindBranches_get_snd {bs : List (Label × LocalTypeR)} (i : Fin bs.length) :
    ((toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i)).2 =
      toCoind (bs.get i).2 := by
  simpa using congrArg Prod.snd (toCoindBranches_get (bs := bs) i)

lemma labels_get_eq {bs : List (Label × LocalTypeR)} (i : Fin (bs.map Prod.fst).length) :
    (bs.map Prod.fst).get i = (bs.get (castFin (by simp) i)).1 := by
  induction bs with
  | nil => exact (Fin.elim0 i)
  | cons b bs ih =>
      cases i using Fin.cases with
      | zero => cases b with | mk label cont => simp [castFin]
      | succ i => simp [castFin]

end RumpsteakV2.Coinductive
