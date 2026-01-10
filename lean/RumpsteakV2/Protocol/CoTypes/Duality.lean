import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.CoTypes.Observables
import RumpsteakV2.Protocol.CoTypes.EQ2

/-! # LocalTypeR Duality

Duality lemmas for LocalTypeR and observable predicates.
This module reuses the existing `LocalTypeR.dual` definition and adds
preservation properties needed to reduce send/recv duplication.
-/

namespace RumpsteakV2.Protocol.LocalTypeR

/-- Duality is an involution (theorem alias). -/
theorem dual_involutive (t : LocalTypeR) : t.dual.dual = t :=
  LocalTypeR.dual_dual t

/-- Duality on branches is an involution (theorem alias). -/

/-- dualBranches as a map (helper for branch proofs). -/
theorem dualBranches_eq_map (bs : List (Label × LocalTypeR)) :
    dualBranches bs = bs.map (fun b => (b.1, b.2.dual)) := by
  induction bs with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk l t =>
          simp [dualBranches, ih]

/-- Duality on branches is an involution (theorem alias). -/
theorem dualBranches_involutive (bs : List (Label × LocalTypeR)) :
    dualBranches (dualBranches bs) = bs :=
  dualBranches_dualBranches bs

mutual
  /-- Duality preserves free variables. -/
  theorem freeVars_dual : (t : LocalTypeR) → t.dual.freeVars = t.freeVars := by
    intro t
    cases t with
    | end => rfl
    | var v => rfl
    | send p bs =>
        simp [LocalTypeR.dual, LocalTypeR.freeVars, freeVarsOfBranches_dual]
    | recv p bs =>
        simp [LocalTypeR.dual, LocalTypeR.freeVars, freeVarsOfBranches_dual]
    | mu v body =>
        simp [LocalTypeR.dual, LocalTypeR.freeVars, freeVars_dual]

  /-- Duality preserves freeVarsOfBranches. -/
  theorem freeVarsOfBranches_dual : (bs : List (Label × LocalTypeR)) →
      freeVarsOfBranches (dualBranches bs) = freeVarsOfBranches bs := by
    intro bs
    cases bs with
    | nil => rfl
    | cons head tail =>
        cases head with
        | mk l t =>
            simp [dualBranches, freeVarsOfBranches, freeVars_dual, freeVarsOfBranches_dual]
end

/-- Duality preserves closedness. -/
theorem dual_isClosed (t : LocalTypeR) : t.isClosed = t.dual.isClosed := by
  simp [LocalTypeR.isClosed, freeVars_dual]

/-- Duality preserves guardedness. -/
theorem dual_isGuarded (t : LocalTypeR) (v : String) :
    t.dual.isGuarded v = t.isGuarded v := by
  induction t with
  | end => rfl
  | var w => simp [LocalTypeR.dual, LocalTypeR.isGuarded]
  | send p bs => simp [LocalTypeR.dual, LocalTypeR.isGuarded]
  | recv p bs => simp [LocalTypeR.dual, LocalTypeR.isGuarded]
  | mu v' body ih =>
      by_cases hv : v == v'
      · simp [LocalTypeR.dual, LocalTypeR.isGuarded, hv]
      · simp [LocalTypeR.dual, LocalTypeR.isGuarded, hv, ih]

mutual
  /-- Duality preserves contractiveness. -/
  theorem dual_isContractive : (t : LocalTypeR) → t.dual.isContractive = t.isContractive := by
    intro t
    cases t with
    | end => rfl
    | var v => rfl
    | send p bs =>
        simp [LocalTypeR.dual, LocalTypeR.isContractive, dual_isContractiveBranches]
    | recv p bs =>
        simp [LocalTypeR.dual, LocalTypeR.isContractive, dual_isContractiveBranches]
    | mu v body =>
        simp [LocalTypeR.dual, LocalTypeR.isContractive, dual_isGuarded, dual_isContractive]

  /-- Duality preserves contractiveness of branches. -/
  theorem dual_isContractiveBranches : (bs : List (Label × LocalTypeR)) →
      isContractiveBranches (dualBranches bs) = isContractiveBranches bs := by
    intro bs
    cases bs with
    | nil => rfl
    | cons head tail =>
        cases head with
        | mk l t =>
            simp [dualBranches, isContractiveBranches, dual_isContractive, dual_isContractiveBranches]
end

end RumpsteakV2.Protocol.LocalTypeR

namespace RumpsteakV2.Protocol.CoTypes.Observables

open RumpsteakV2.Protocol.LocalTypeR

/-- Unfolding to end is preserved by dual. -/
theorem UnfoldsToEnd.dual {t : LocalTypeR} (h : UnfoldsToEnd t) : UnfoldsToEnd t.dual := by
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (UnfoldsToEnd.base)
  | @mu v body _ ih =>
      have ih' : UnfoldsToEnd (body.dual.substitute v (.mu v body).dual) := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (UnfoldsToEnd.mu (t := v) (body := body.dual) ih')

/-- Unfolding to var is preserved by dual. -/
theorem UnfoldsToVar.dual {t : LocalTypeR} {v : String} (h : UnfoldsToVar t v) :
    UnfoldsToVar t.dual v := by
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (UnfoldsToVar.base (v := v))
  | @mu t body v' _ ih =>
      have ih' : UnfoldsToVar (body.dual.substitute t (.mu t body).dual) v' := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (UnfoldsToVar.mu (t := t) (body := body.dual) (v := v') ih')

/-- Dual of CanSend is CanRecv. -/
theorem CanSend.dual {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend t p bs) : CanRecv t.dual p (LocalTypeR.dualBranches bs) := by
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (CanRecv.base (partner := p) (branches := LocalTypeR.dualBranches bs))
  | @mu t body p' bs' _ ih =>
      have ih' : CanRecv (body.dual.substitute t (.mu t body).dual) p' (LocalTypeR.dualBranches bs') := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (CanRecv.mu (t := t) (body := body.dual) (partner := p')
        (branches := LocalTypeR.dualBranches bs') ih')

/-- Dual of CanRecv is CanSend. -/
theorem CanRecv.dual {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv t p bs) : CanSend t.dual p (LocalTypeR.dualBranches bs) := by
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (CanSend.base (partner := p) (branches := LocalTypeR.dualBranches bs))
  | @mu t body p' bs' _ ih =>
      have ih' : CanSend (body.dual.substitute t (.mu t body).dual) p' (LocalTypeR.dualBranches bs') := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (CanSend.mu (t := t) (body := body.dual) (partner := p')
        (branches := LocalTypeR.dualBranches bs') ih')

/-- Duality swaps CanSend and CanRecv. -/
theorem CanSend.dual_iff_CanRecv {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)} :
    CanSend t p bs ↔ CanRecv t.dual p (LocalTypeR.dualBranches bs) := by
  constructor
  · exact CanSend.dual
  · intro h
    have h' : CanSend t.dual.dual p (LocalTypeR.dualBranches (LocalTypeR.dualBranches bs)) :=
      CanRecv.dual (t := t.dual) h
    simpa [LocalTypeR.dual_involutive, LocalTypeR.dualBranches_involutive] using h'

/-- Duality swaps CanRecv and CanSend. -/
theorem CanRecv.dual_iff_CanSend {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)} :
    CanRecv t p bs ↔ CanSend t.dual p (LocalTypeR.dualBranches bs) := by
  constructor
  · exact CanRecv.dual
  · intro h
    have h' : CanRecv t.dual.dual p (LocalTypeR.dualBranches (LocalTypeR.dualBranches bs)) :=
      CanSend.dual (t := t.dual) h
    simpa [LocalTypeR.dual_involutive, LocalTypeR.dualBranches_involutive] using h'

end RumpsteakV2.Protocol.CoTypes.Observables
