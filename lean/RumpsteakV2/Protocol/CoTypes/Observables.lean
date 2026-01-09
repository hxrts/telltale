import RumpsteakV2.Protocol.LocalTypeR

/-! # Observable Behavior Predicates

This file defines membership predicates that capture observable behavior of local types
after mu-unfolding. These are analogous to ITree's `Terminates` and `CanDo` predicates.

## Module Structure

This file is extracted from Bisim.lean to avoid circular dependencies:
- Bisim.lean imports Project.lean
- Tactics need observable predicates but not Project.lean
- Solution: Extract observables here, both Bisim and tactics import this

## Contents

1. Membership predicates: UnfoldsToEnd, UnfoldsToVar, CanSend, CanRecv
2. Observable classification sum type
3. Basic properties: reflexivity, exclusivity, incompatibility lemmas

-/

namespace RumpsteakV2.Protocol.CoTypes.Observables

open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.GlobalType

/-! ## Membership Predicates

These predicates capture observable behavior after mu-unfolding, analogous to
ITree's `Terminates` and `CanDo` from QpfTypes PR #49. -/

/-- `UnfoldsToEnd a` holds when `a` unfolds (through any number of mu-substitutions)
    to the `end` constructor.

    Analogous to ITree's `Terminates` predicate. -/
inductive UnfoldsToEnd : LocalTypeR → Prop where
  | base : UnfoldsToEnd .end
  | mu {t : String} {body : LocalTypeR} :
      UnfoldsToEnd (body.substitute t (.mu t body)) →
      UnfoldsToEnd (.mu t body)

/-- `UnfoldsToVar a v` holds when `a` unfolds to the variable `v`. -/
inductive UnfoldsToVar : LocalTypeR → String → Prop where
  | base : UnfoldsToVar (.var v) v
  | mu {t : String} {body : LocalTypeR} {v : String} :
      UnfoldsToVar (body.substitute t (.mu t body)) v →
      UnfoldsToVar (.mu t body) v

/-- `CanSend a partner branches` holds when `a` unfolds to a send with the given
    partner and branches.

    Analogous to ITree's `CanDo` predicate for `vis` events. -/
inductive CanSend : LocalTypeR → String → List (Label × LocalTypeR) → Prop where
  | base : CanSend (.send partner branches) partner branches
  | mu {t : String} {body : LocalTypeR} {partner : String}
      {branches : List (Label × LocalTypeR)} :
      CanSend (body.substitute t (.mu t body)) partner branches →
      CanSend (.mu t body) partner branches

/-- `CanRecv a partner branches` holds when `a` unfolds to a recv with the given
    partner and branches. -/
inductive CanRecv : LocalTypeR → String → List (Label × LocalTypeR) → Prop where
  | base : CanRecv (.recv partner branches) partner branches
  | mu {t : String} {body : LocalTypeR} {partner : String}
      {branches : List (Label × LocalTypeR)} :
      CanRecv (body.substitute t (.mu t body)) partner branches →
      CanRecv (.mu t body) partner branches

/-! ## Observable Behavior Classification

Every closed, well-formed local type has exactly one observable behavior after
unfolding: it either unfolds to end, to a free variable, or can send/recv. -/

/-- Observable behavior classification for a local type. -/
inductive Observable : LocalTypeR → Prop where
  | is_end {a} : UnfoldsToEnd a → Observable a
  | is_var {a v} : UnfoldsToVar a v → Observable a
  | is_send {a p bs} : CanSend a p bs → Observable a
  | is_recv {a p bs} : CanRecv a p bs → Observable a

/-! ## Basic Properties of Membership Predicates -/

/-- UnfoldsToEnd is reflexive for end types. -/
theorem UnfoldsToEnd.end_refl : UnfoldsToEnd .end := UnfoldsToEnd.base

/-- UnfoldsToVar is reflexive for var types. -/
theorem UnfoldsToVar.var_refl (v : String) : UnfoldsToVar (.var v) v := UnfoldsToVar.base

/-- CanSend is reflexive for send types. -/
theorem CanSend.send_refl (partner : String) (branches : List (Label × LocalTypeR)) :
    CanSend (.send partner branches) partner branches := CanSend.base

/-- CanRecv is reflexive for recv types. -/
theorem CanRecv.recv_refl (partner : String) (branches : List (Label × LocalTypeR)) :
    CanRecv (.recv partner branches) partner branches := CanRecv.base

/-- Non-mu types that are not end cannot unfold to end. -/
theorem UnfoldsToEnd.not_var {v : String} : ¬UnfoldsToEnd (.var v) := nofun
theorem UnfoldsToEnd.not_send {p : String} {bs : List (Label × LocalTypeR)} :
    ¬UnfoldsToEnd (.send p bs) := nofun
theorem UnfoldsToEnd.not_recv {p : String} {bs : List (Label × LocalTypeR)} :
    ¬UnfoldsToEnd (.recv p bs) := nofun

/-! ## Incompatibility Lemmas

These lemmas prove that different observable behaviors are mutually exclusive.
They use coordinated induction on both predicates. -/

/-- Unfolding to end excludes unfolding to a variable. -/
theorem UnfoldsToEnd.not_var_of_end {a : LocalTypeR} (h : UnfoldsToEnd a) :
    ∀ v, ¬UnfoldsToVar a v := by
  induction h with
  | base => intro v hvar; cases hvar
  | @mu t body _ ih => intro v hvar; cases hvar with | @mu _ _ _ h => exact ih v h

/-- Unfolding to a variable excludes unfolding to end. -/
theorem UnfoldsToVar.not_end_of_var {a : LocalTypeR} {v : String} (h : UnfoldsToVar a v) :
    ¬UnfoldsToEnd a := by
  induction h with
  | base => intro hend; cases hend
  | @mu t body v' _ ih => intro hend; cases hend with | @mu _ _ h => exact ih h

/-- A type that can send cannot unfold to end. -/
theorem CanSend.not_end {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend a p bs) : ¬UnfoldsToEnd a := by
  induction h with
  | base => intro hend; cases hend
  | @mu t body p' bs' _ ih => intro hend; cases hend with | @mu _ _ h => exact ih h

/-- A type that can recv cannot unfold to end. -/
theorem CanRecv.not_end {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv a p bs) : ¬UnfoldsToEnd a := by
  induction h with
  | base => intro hend; cases hend
  | @mu t body p' bs' _ ih => intro hend; cases hend with | @mu _ _ h => exact ih h

/-- A type that can send cannot unfold to a var. -/
theorem CanSend.not_var {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend a p bs) : ∀ v, ¬UnfoldsToVar a v := by
  induction h with
  | base => intro v hvar; cases hvar
  | @mu t body p' bs' _ ih => intro v hvar; cases hvar with | @mu _ _ _ h => exact ih v h

/-- A type that can recv cannot unfold to a var. -/
theorem CanRecv.not_var {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv a p bs) : ∀ v, ¬UnfoldsToVar a v := by
  induction h with
  | base => intro v hvar; cases hvar
  | @mu t body p' bs' _ ih => intro v hvar; cases hvar with | @mu _ _ _ h => exact ih v h

/-- A type that can send cannot recv. -/
theorem CanSend.not_recv {a : LocalTypeR} {p q : String}
    {bs cs : List (Label × LocalTypeR)}
    (hs : CanSend a p bs) : ¬CanRecv a q cs := by
  induction hs with
  | base => intro hr; cases hr
  | @mu t body p' bs' _ ih => intro hr; cases hr with | @mu _ _ _ _ h => exact ih h

/-! ## Determinism of Membership Predicates -/

/-- If a type unfolds to two variables, they must be the same. -/
theorem UnfoldsToVar.deterministic {a : LocalTypeR} {v w : String}
    (hv : UnfoldsToVar a v) (hw : UnfoldsToVar a w) : v = w := by
  induction hv with
  | base => cases hw; rfl
  | @mu t body v' _ ih => cases hw with | @mu _ _ _ h => exact ih h

/-- If a type can send, the partner and branches are unique. -/
theorem CanSend.deterministic {a : LocalTypeR} {p q : String}
    {bs cs : List (Label × LocalTypeR)}
    (hp : CanSend a p bs) (hq : CanSend a q cs) : p = q ∧ bs = cs := by
  induction hp with
  | base => cases hq; exact ⟨rfl, rfl⟩
  | @mu t body p' bs' _ ih => cases hq with | @mu _ _ _ _ h => exact ih h

/-- If a type can recv, the partner and branches are unique. -/
theorem CanRecv.deterministic {a : LocalTypeR} {p q : String}
    {bs cs : List (Label × LocalTypeR)}
    (hp : CanRecv a p bs) (hq : CanRecv a q cs) : p = q ∧ bs = cs := by
  induction hp with
  | base => cases hq; exact ⟨rfl, rfl⟩
  | @mu t body p' bs' _ ih => cases hq with | @mu _ _ _ _ h => exact ih h

end RumpsteakV2.Protocol.CoTypes.Observables
