import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.CoTypes.EQ2

set_option linter.dupNamespace false

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

namespace RumpsteakV2.Protocol.CoTypes.Observable

open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.CoTypes.EQ2

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

/-! ## Duality Lemmas -/

/-- Unfolding to end is preserved by dual. -/
theorem UnfoldsToEnd.dual {t : LocalTypeR} (h : UnfoldsToEnd t) : UnfoldsToEnd t.dual := by
  -- Structural recursion; mu case uses dual_substitute.
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (UnfoldsToEnd.base)
  | @mu v body _ ih =>
      have ih' : UnfoldsToEnd (body.dual.substitute v (LocalTypeR.mu v body).dual) := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (UnfoldsToEnd.mu (t := v) (body := body.dual) ih')

/-- Unfolding to var is preserved by dual. -/
theorem UnfoldsToVar.dual {t : LocalTypeR} {v : String} (h : UnfoldsToVar t v) :
    UnfoldsToVar t.dual v := by
  -- Structural recursion; mu case uses dual_substitute.
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (UnfoldsToVar.base)
  | @mu t body v' _ ih =>
      have ih' : UnfoldsToVar (body.dual.substitute t (LocalTypeR.mu t body).dual) v' := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (UnfoldsToVar.mu (t := t) (body := body.dual) (v := v') ih')

/-- Dual of CanSend is CanRecv. -/
theorem CanSend.dual {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend t p bs) : CanRecv t.dual p (LocalTypeR.dualBranches bs) := by
  -- Structural recursion; mu case uses dual_substitute.
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (CanRecv.base)
  | @mu t body p' bs' _ ih =>
      have ih' : CanRecv (body.dual.substitute t (LocalTypeR.mu t body).dual) p'
        (LocalTypeR.dualBranches bs') := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (CanRecv.mu (t := t) (body := body.dual) (partner := p')
        (branches := LocalTypeR.dualBranches bs') ih')

/-- Dual of CanRecv is CanSend. -/
theorem CanRecv.dual {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv t p bs) : CanSend t.dual p (LocalTypeR.dualBranches bs) := by
  -- Structural recursion; mu case uses dual_substitute.
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (CanSend.base)
  | @mu t body p' bs' _ ih =>
      have ih' : CanSend (body.dual.substitute t (LocalTypeR.mu t body).dual) p'
        (LocalTypeR.dualBranches bs') := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (CanSend.mu (t := t) (body := body.dual) (partner := p')
        (branches := LocalTypeR.dualBranches bs') ih')

/-- Duality swaps CanSend and CanRecv. -/
theorem CanSend.dual_iff_CanRecv {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)} :
    CanSend t p bs ↔ CanRecv t.dual p (LocalTypeR.dualBranches bs) := by
  -- Both directions are by dualizing twice.
  constructor
  · exact CanSend.dual
  · intro h
    have h' : CanSend t.dual.dual p (LocalTypeR.dualBranches (LocalTypeR.dualBranches bs)) :=
      CanRecv.dual (t := t.dual) h
    simpa [LocalTypeR.dual_dual, dualBranches_dualBranches] using h'

/-- Duality swaps CanRecv and CanSend. -/
theorem CanRecv.dual_iff_CanSend {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)} :
    CanRecv t p bs ↔ CanSend t.dual p (LocalTypeR.dualBranches bs) := by
  -- Both directions are by dualizing twice.
  constructor
  · exact CanRecv.dual
  · intro h
    have h' : CanRecv t.dual.dual p (LocalTypeR.dualBranches (LocalTypeR.dualBranches bs)) :=
      CanSend.dual (t := t.dual) h
    simpa [LocalTypeR.dual_dual, dualBranches_dualBranches] using h'

/-! ## One-Step Inversion Lemmas

These lemmas expose the single-step structure of the membership predicates.
They are useful for unfolding-style proofs without manual `cases` every time. -/

theorem UnfoldsToEnd.cases {a : LocalTypeR} (h : UnfoldsToEnd a) :
    a = .end ∨ ∃ t body, a = .mu t body ∧ UnfoldsToEnd (body.substitute t (.mu t body)) := by
  cases h with
  | base => exact Or.inl rfl
  | mu h' => exact Or.inr ⟨_, _, rfl, h'⟩

theorem UnfoldsToEnd.mu_inv {t : String} {body : LocalTypeR}
    (h : UnfoldsToEnd (.mu t body)) : UnfoldsToEnd (body.substitute t (.mu t body)) := by
  cases h with
  | mu h' => exact h'

theorem UnfoldsToVar.cases {a : LocalTypeR} {v : String} (h : UnfoldsToVar a v) :
    a = .var v ∨ ∃ t body, a = .mu t body ∧ UnfoldsToVar (body.substitute t (.mu t body)) v := by
  cases h with
  | base => exact Or.inl rfl
  | mu h' => exact Or.inr ⟨_, _, rfl, h'⟩

theorem UnfoldsToVar.mu_inv {t : String} {body : LocalTypeR} {v : String}
    (h : UnfoldsToVar (.mu t body) v) : UnfoldsToVar (body.substitute t (.mu t body)) v := by
  cases h with
  | mu h' => exact h'

theorem CanSend.cases {a : LocalTypeR} {partner : String} {branches : List (Label × LocalTypeR)}
    (h : CanSend a partner branches) :
    a = .send partner branches ∨
      ∃ t body, a = .mu t body ∧ CanSend (body.substitute t (.mu t body)) partner branches := by
  cases h with
  | base => exact Or.inl rfl
  | mu h' => exact Or.inr ⟨_, _, rfl, h'⟩

theorem CanSend.mu_inv {t : String} {body : LocalTypeR} {partner : String}
    {branches : List (Label × LocalTypeR)}
    (h : CanSend (.mu t body) partner branches) :
    CanSend (body.substitute t (.mu t body)) partner branches := by
  cases h with
  | mu h' => exact h'

theorem CanRecv.cases {a : LocalTypeR} {partner : String} {branches : List (Label × LocalTypeR)}
    (h : CanRecv a partner branches) :
    a = .recv partner branches ∨
      ∃ t body, a = .mu t body ∧ CanRecv (body.substitute t (.mu t body)) partner branches := by
  -- Reduce recv to send on the dual type.
  have hsend : CanSend a.dual partner (LocalTypeR.dualBranches branches) := CanRecv.dual h
  rcases CanSend.cases hsend with hbase | ⟨t, body, hmu, hstep⟩
  · left
    -- Dualizing send gives recv on the original type.
    have hbase' := congrArg LocalTypeR.dual hbase
    simpa [LocalTypeR.dual, dualBranches_dualBranches, LocalTypeR.dual_dual] using hbase'
  · right
    refine ⟨t, body.dual, ?_, ?_⟩
    · -- Dualizing the mu constructor keeps the binder.
      have hmu' := congrArg LocalTypeR.dual hmu
      simpa [LocalTypeR.dual, LocalTypeR.dual_dual] using hmu'
    · -- Dualize the step and simplify.
      have hrecv := CanSend.dual hstep
      simpa [LocalTypeR.dual_substitute, LocalTypeR.dual, dualBranches_dualBranches] using hrecv

theorem CanRecv.mu_inv {t : String} {body : LocalTypeR} {partner : String}
    {branches : List (Label × LocalTypeR)}
    (h : CanRecv (.mu t body) partner branches) :
    CanRecv (body.substitute t (.mu t body)) partner branches := by
  -- Peel the mu case via CanRecv.cases.
  rcases CanRecv.cases (a := .mu t body) h with hbase | ⟨t', body', hmu, hstep⟩
  · cases hbase
  · cases hmu
    simpa using hstep

/-! ## Observable Behavior Classification

Every closed, well-formed local type has exactly one observable behavior after
unfolding: it either unfolds to end, to a free variable, or can send/recv. -/

/-- Observable behavior classification for a local type. -/
inductive Observable : LocalTypeR → Prop where
  | is_end {a} : UnfoldsToEnd a → Observable a
  | is_var {a v} : UnfoldsToVar a v → Observable a
  | is_send {a p bs} : CanSend a p bs → Observable a
  | is_recv {a p bs} : CanRecv a p bs → Observable a

/-! ## Observable Relations -/

/-- Relation between observables induced by a relation on local types. -/
abbrev Rel := LocalTypeR → LocalTypeR → Prop

inductive ObservableRel (R : Rel) : {a b : LocalTypeR} → Observable a → Observable b → Prop where
  | is_end {a b : LocalTypeR} {ha : UnfoldsToEnd a} {hb : UnfoldsToEnd b} :
      ObservableRel R (Observable.is_end ha) (Observable.is_end hb)
  | is_var {a b : LocalTypeR} {v : String} {ha : UnfoldsToVar a v} {hb : UnfoldsToVar b v} :
      ObservableRel R (Observable.is_var ha) (Observable.is_var hb)
  | is_send {a b : LocalTypeR} {p : String} {bs cs : List (Label × LocalTypeR)}
      {ha : CanSend a p bs} {hb : CanSend b p cs} :
      BranchesRel R bs cs →
      ObservableRel R (Observable.is_send ha) (Observable.is_send hb)
  | is_recv {a b : LocalTypeR} {p : String} {bs cs : List (Label × LocalTypeR)}
      {ha : CanRecv a p bs} {hb : CanRecv b p cs} :
      BranchesRel R bs cs →
      ObservableRel R (Observable.is_recv ha) (Observable.is_recv hb)

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
    CanRecv (.recv partner branches) partner branches := by
  -- Obtain recv reflexivity by dualizing send reflexivity.
  have hsend : CanSend (.send partner (LocalTypeR.dualBranches branches)) partner
      (LocalTypeR.dualBranches branches) := CanSend.send_refl _ _
  have hrecv := CanSend.dual hsend
  simpa [LocalTypeR.dual, dualBranches_dualBranches] using hrecv

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
  -- Reduce recv to send on the dual type.
  intro hend
  have hsend : CanSend a.dual p (LocalTypeR.dualBranches bs) := CanRecv.dual h
  have hend_dual : UnfoldsToEnd a.dual := UnfoldsToEnd.dual hend
  exact (CanSend.not_end hsend) hend_dual

/-- A type that can send cannot unfold to a var. -/
theorem CanSend.not_var {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend a p bs) : ∀ v, ¬UnfoldsToVar a v := by
  induction h with
  | base => intro v hvar; cases hvar
  | @mu t body p' bs' _ ih => intro v hvar; cases hvar with | @mu _ _ _ h => exact ih v h

/-- A type that can recv cannot unfold to a var. -/
theorem CanRecv.not_var {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv a p bs) : ∀ v, ¬UnfoldsToVar a v := by
  -- Reduce recv to send on the dual type.
  intro v hvar
  have hsend : CanSend a.dual p (LocalTypeR.dualBranches bs) := CanRecv.dual h
  have hvar_dual : UnfoldsToVar a.dual v := UnfoldsToVar.dual hvar
  exact (CanSend.not_var hsend) v hvar_dual

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
  -- Reduce recv determinism to send determinism on the dual type.
  have hp' : CanSend a.dual p (LocalTypeR.dualBranches bs) := CanRecv.dual hp
  have hq' : CanSend a.dual q (LocalTypeR.dualBranches cs) := CanRecv.dual hq
  obtain ⟨hpq, hbs⟩ := CanSend.deterministic hp' hq'
  have hbs' : bs = cs := by
    -- dualBranches is involutive on both sides.
    have hdual := congrArg LocalTypeR.dualBranches hbs
    simpa [dualBranches_dualBranches] using hdual
  exact ⟨hpq, hbs'⟩

end RumpsteakV2.Protocol.CoTypes.Observable
