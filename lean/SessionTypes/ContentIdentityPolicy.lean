import SessionTypes.GlobalType
import SessionTypes.LocalTypeR
import Mathlib.Data.List.Dedup

set_option autoImplicit false

/-! # SessionTypes.ContentIdentityPolicy

Closed-only canonical identity policy with explicit open-term template identity.

This mirrors the Rust `Contentable` contract:
- canonical content identity is defined only for closed terms
- template identity is defined for open and closed terms and carries an explicit
  free-variable interface.
-/

namespace SessionTypes.ContentIdentity

open SessionTypes
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

/-- Canonicalized free-variable interface used by template identity envelopes. -/
def canonicalFreeVarInterface (vars : List String) : List String :=
  (vars.eraseDups.toArray.qsort (· < ·)).toList

/-- Open-term template envelope for global types. -/
structure GlobalTemplateEnvelope where
  freeVars : List String
  body : GlobalType
  deriving Repr, Inhabited

/-- Open-term template envelope for local types. -/
structure LocalTemplateEnvelope where
  freeVars : List String
  body : LocalTypeR
  deriving Repr, Inhabited

/-- Canonical bytes are only defined for closed/all-bound global types. -/
def globalToCanonicalIdentityBytes? (g : GlobalType) : Option ByteArray :=
  if g.allVarsBound then
    some (String.toUTF8 (reprStr g))
  else
    none

/-- Template envelope is always defined and records free-variable interface. -/
def globalTemplateEnvelope (g : GlobalType) : SessionTypes.ContentIdentity.GlobalTemplateEnvelope :=
  { freeVars := canonicalFreeVarInterface g.freeVars, body := g }

/-- Template bytes are defined for open and closed terms. -/
def globalToTemplateIdentityBytes (g : GlobalType) : ByteArray :=
  String.toUTF8 (reprStr (globalTemplateEnvelope g))

theorem global_canonical_identity_some_iff_all_vars_bound (g : GlobalType) :
    (∃ bytes, globalToCanonicalIdentityBytes? g = some bytes) ↔ g.allVarsBound = true := by
  by_cases h : g.allVarsBound = true
  · constructor
    · intro _; exact h
    · intro _; refine ⟨String.toUTF8 (reprStr g), ?_⟩
      simp [globalToCanonicalIdentityBytes?, h]
  · constructor
    · intro hs
      rcases hs with ⟨bytes, hs⟩
      simp [globalToCanonicalIdentityBytes?, h] at hs
    · intro htrue
      exact (h htrue).elim

theorem global_canonical_identity_none_of_not_all_vars_bound (g : GlobalType)
    (h : g.allVarsBound = false) :
    globalToCanonicalIdentityBytes? g = none := by
  simp [globalToCanonicalIdentityBytes?, h]

theorem global_template_identity_always_defined (g : GlobalType) :
    ∃ bytes, globalToTemplateIdentityBytes g = bytes := by
  exact ⟨String.toUTF8 (reprStr (globalTemplateEnvelope g)), rfl⟩

theorem global_template_envelope_records_interface (g : GlobalType) :
    (globalTemplateEnvelope g).freeVars = canonicalFreeVarInterface g.freeVars := by
  rfl

/-- Canonical bytes are only defined for closed local types. -/
def localToCanonicalIdentityBytes? (t : LocalTypeR) : Option ByteArray :=
  if t.isClosed then
    some (String.toUTF8 (reprStr t))
  else
    none

/-- Template envelope is always defined and records free-variable interface. -/
def localTemplateEnvelope (t : LocalTypeR) : SessionTypes.ContentIdentity.LocalTemplateEnvelope :=
  { freeVars := canonicalFreeVarInterface t.freeVars, body := t }

/-- Template bytes are defined for open and closed local terms. -/
def localToTemplateIdentityBytes (t : LocalTypeR) : ByteArray :=
  String.toUTF8 (reprStr (localTemplateEnvelope t))

theorem local_canonical_identity_some_iff_closed (t : LocalTypeR) :
    (∃ bytes, localToCanonicalIdentityBytes? t = some bytes) ↔ t.isClosed = true := by
  by_cases h : t.isClosed = true
  · constructor
    · intro _; exact h
    · intro _; refine ⟨String.toUTF8 (reprStr t), ?_⟩
      simp [localToCanonicalIdentityBytes?, h]
  · constructor
    · intro hs
      rcases hs with ⟨bytes, hs⟩
      simp [localToCanonicalIdentityBytes?, h] at hs
    · intro htrue
      exact (h htrue).elim

theorem local_canonical_identity_none_of_not_closed (t : LocalTypeR)
    (h : t.isClosed = false) :
    localToCanonicalIdentityBytes? t = none := by
  simp [localToCanonicalIdentityBytes?, h]

theorem local_template_identity_always_defined (t : LocalTypeR) :
    ∃ bytes, localToTemplateIdentityBytes t = bytes := by
  exact ⟨String.toUTF8 (reprStr (localTemplateEnvelope t)), rfl⟩

theorem local_template_envelope_records_interface (t : LocalTypeR) :
    (localTemplateEnvelope t).freeVars = canonicalFreeVarInterface t.freeVars := by
  rfl

end SessionTypes.ContentIdentity
