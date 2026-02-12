import SessionTypes.LocalTypeR.Core.Base

/-! # SessionTypes.LocalTypeR.Core.Contractiveness

Contractiveness and partner-occurrence helpers for LocalTypeR.
-/

/-
The Problem. Later typing/simulation proofs rely on lightweight
contractiveness/occurrence facts that should be isolated from core syntax.

Solution Structure. Collects the contractiveness and hasRecvFrom helper lemmas
on top of the base LocalTypeR definitions.
-/

set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace SessionTypes.LocalTypeR

/-! ## Lightweight Contractiveness and Partner Occurrence -/

/-- Local contractiveness check for mu bodies (vars are non-contractive). -/
def LocalTypeR.lcontractive : LocalTypeR → Bool
  | .end => true
  | .var _ => false
  | .send _ _ => true
  | .recv _ _ => true
  | .mu _ body =>
      match body with
      | .var _ => false
      | .mu _ _ => false
      | .send _ _ => true
      | .recv _ _ => true
      | .end => true

/-- `hasSendTo e partner` holds when `e` can send to `partner` somewhere in its structure. -/
inductive LocalTypeR.hasSendTo : LocalTypeR → String → Prop where
  | send {partner : String} {branches : List BranchR} :
      hasSendTo (.send partner branches) partner
  | send_branch {receiver partner : String} {branches : List BranchR}
      {lb : BranchR} :
      lb ∈ branches → hasSendTo lb.2.2 partner → hasSendTo (.send receiver branches) partner
  | recv_branch {sender partner : String} {branches : List BranchR}
      {lb : BranchR} :
      lb ∈ branches → hasSendTo lb.2.2 partner → hasSendTo (.recv sender branches) partner
  | mu {t : String} {body : LocalTypeR} {partner : String} :
      hasSendTo body partner → hasSendTo (.mu t body) partner
  | noncontractive {t : String} {body : LocalTypeR} {partner : String} :
      LocalTypeR.lcontractive body = false → hasSendTo (.mu t body) partner

/-- `hasRecvFrom e partner` holds when `e` can receive from `partner` somewhere in its structure. -/
inductive LocalTypeR.hasRecvFrom : LocalTypeR → String → Prop where
  | recv {partner : String} {branches : List BranchR} :
      hasRecvFrom (.recv partner branches) partner
  | send_branch {receiver partner : String} {branches : List BranchR}
      {lb : BranchR} :
      lb ∈ branches → hasRecvFrom lb.2.2 partner → hasRecvFrom (.send receiver branches) partner
  | recv_branch {sender partner : String} {branches : List BranchR}
      {lb : BranchR} :
      lb ∈ branches → hasRecvFrom lb.2.2 partner → hasRecvFrom (.recv sender branches) partner
  | mu {t : String} {body : LocalTypeR} {partner : String} :
      hasRecvFrom body partner → hasRecvFrom (.mu t body) partner
  | noncontractive {t : String} {body : LocalTypeR} {partner : String} :
      LocalTypeR.lcontractive body = false → hasRecvFrom (.mu t body) partner

/-! ## Mu Lifting Helpers -/

/-- Lift send partner occurrence through mu. -/
theorem LocalTypeR.hasSendTo_mu {t : String} {body : LocalTypeR} {partner : String}
    (h : body.hasSendTo partner) : (LocalTypeR.mu t body).hasSendTo partner :=
  LocalTypeR.hasSendTo.mu h

/-- Lift recv partner occurrence through mu. -/
theorem LocalTypeR.hasRecvFrom_mu {t : String} {body : LocalTypeR} {partner : String}
    (h : body.hasRecvFrom partner) : (LocalTypeR.mu t body).hasRecvFrom partner :=
  LocalTypeR.hasRecvFrom.mu h

/-! ## Direct Constructor Helpers -/

/-- Direct send partner occurrence. -/
theorem LocalTypeR.hasSendTo_send {partner : String} {branches : List BranchR} :
    (LocalTypeR.send partner branches).hasSendTo partner :=
  LocalTypeR.hasSendTo.send

/-- Direct recv partner occurrence. -/
theorem LocalTypeR.hasRecvFrom_recv {partner : String} {branches : List BranchR} :
    (LocalTypeR.recv partner branches).hasRecvFrom partner :=
  LocalTypeR.hasRecvFrom.recv

/-! ## Branch Propagation Helpers -/

/-- Propagate send partner occurrence through send branches. -/
theorem LocalTypeR.hasSendTo_send_branch {receiver partner : String} {branches : List BranchR}
    {lb : BranchR} (hmem : lb ∈ branches) (h : lb.2.2.hasSendTo partner) :
    (LocalTypeR.send receiver branches).hasSendTo partner :=
  LocalTypeR.hasSendTo.send_branch hmem h

/-- Propagate send partner occurrence through recv branches. -/
theorem LocalTypeR.hasSendTo_recv_branch {sender partner : String} {branches : List BranchR}
    {lb : BranchR} (hmem : lb ∈ branches) (h : lb.2.2.hasSendTo partner) :
    (LocalTypeR.recv sender branches).hasSendTo partner :=
  LocalTypeR.hasSendTo.recv_branch hmem h

/-- Propagate recv partner occurrence through send branches. -/
theorem LocalTypeR.hasRecvFrom_send_branch {receiver partner : String} {branches : List BranchR}
    {lb : BranchR} (hmem : lb ∈ branches) (h : lb.2.2.hasRecvFrom partner) :
    (LocalTypeR.send receiver branches).hasRecvFrom partner :=
  LocalTypeR.hasRecvFrom.send_branch hmem h

/-- Propagate recv partner occurrence through recv branches. -/
theorem LocalTypeR.hasRecvFrom_recv_branch {sender partner : String} {branches : List BranchR}
    {lb : BranchR} (hmem : lb ∈ branches) (h : lb.2.2.hasRecvFrom partner) :
    (LocalTypeR.recv sender branches).hasRecvFrom partner :=
  LocalTypeR.hasRecvFrom.recv_branch hmem h

/-! ## Noncontractive Fallback Helpers -/

/-- Any noncontractive mu counts as sending to every partner. -/
theorem LocalTypeR.hasSendTo_noncontractive {t : String} {body : LocalTypeR} {partner : String}
    (h : LocalTypeR.lcontractive body = false) : (LocalTypeR.mu t body).hasSendTo partner :=
  LocalTypeR.hasSendTo.noncontractive h

/-- Any noncontractive mu counts as receiving from every partner. -/
theorem LocalTypeR.hasRecvFrom_noncontractive {t : String} {body : LocalTypeR} {partner : String}
    (h : LocalTypeR.lcontractive body = false) : (LocalTypeR.mu t body).hasRecvFrom partner :=
  LocalTypeR.hasRecvFrom.noncontractive h
end SessionTypes.LocalTypeR
