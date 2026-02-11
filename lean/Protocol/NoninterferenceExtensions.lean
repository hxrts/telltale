import Protocol.NoninterferenceCore

/-! # Protocol.NoninterferenceExtensions

Derived contextual-closure and exactness wrappers layered on top of the
core noninterference development.
-/

/-
The Problem. Core noninterference proves blind-step invariance, but downstream
papers need packaged corollaries for contextual closure, coherence alignment,
and exactness-style theorem interfaces.

Solution Structure. Reuse core lemmas to build extension theorems in four
clusters: contextual closure, coherence connection, typed-step composition, and
blindness/observational-invariance exactness wrappers.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section
/-! ## Contextual Closure -/

/-- Blind steps preserve CEquiv across the contextual Step relation. -/
theorem blind_step_preserves_CEquiv {C C' : Config}
    {s : SessionId} {r : Role}
    (hStep : Step C C')
    (hBlindSend : ∀ ep target T L, lookupG C.G ep = some (.send target T L) →
                  ep.sid = s → BlindToSend r ep.role target)
    (hBlindSelect : ∀ ep target branches, lookupG C.G ep = some (.select target branches) →
                    ep.sid = s → BlindToSend r ep.role target)
    (hBlindRecv : ∀ ep source T L, lookupG C.G ep = some (.recv source T L) →
                  ep.sid = s → BlindToRecv r source ep.role)
    (hBlindBranch : ∀ ep source branches, lookupG C.G ep = some (.branch source branches) →
                    ep.sid = s → BlindToRecv r source ep.role)
    (hFreshBufs : ∀ sender receiver,
      lookupBuf C.bufs ⟨C.nextSid, sender, receiver⟩ = []) :
    C ≈[s, r] C' := by
  induction hStep with
  | base hBase =>
      exact blind_step_preserves_CEquiv_single hBase hBlindSend hBlindSelect
        hBlindRecv hBlindBranch hFreshBufs
  | seq_left hProc hSub ih =>
      rename_i Cmid P Q
      have h := ih hBlindSend hBlindSelect hBlindRecv hBlindBranch hFreshBufs
      exact CEquiv_ignore_proc (C':=Cmid) (P:=P) (Q:=.seq Cmid.proc Q) h
  | par_left hProc hSub ih =>
      rename_i Cmid P Q nS nG nS' nG'
      have h := ih hBlindSend hBlindSelect hBlindRecv hBlindBranch hFreshBufs
      exact CEquiv_ignore_proc (C':=Cmid) (P:=P) (Q:=.par nS' nG' Cmid.proc Q) h
  | par_right hProc hSub ih =>
      rename_i Cmid P Q nS nG nS' nG'
      have h := ih hBlindSend hBlindSelect hBlindRecv hBlindBranch hFreshBufs
      exact CEquiv_ignore_proc (C':=Cmid) (P:=Q) (Q:=.par nS' nG' P Cmid.proc) h

/-! ## Coherence Connection -/

/-- CEquiv for all roles implies equal lookups.
    This connects noninterference to the Coherence invariant.

    Note: For list-backed GEnv/DEnv, equal lookups don't imply list equality,
    but they do imply observational equivalence which suffices for Coherence. -/
theorem CEquiv_all_implies_lookup_eq {C₁ C₂ : Config}
    (hEquiv : ∀ s r, C₁ ≈[s, r] C₂) :
    (∀ ep, lookupG C₁.G ep = lookupG C₂.G ep) ∧
    (∀ e, lookupD C₁.D e = lookupD C₂.D e) := by
  constructor
  · -- G lookup equality: for any endpoint ep.
    intro ep
    have h := hEquiv ep.sid ep.role
    exact h.1
  · -- D lookup equality: for any edge e.
    intro e
    have h := hEquiv e.sid e.receiver
    exact h.2.2 e.sender

/-! ## TypedStep Composition -/

/-- Compose noninterference with subject reduction (TypedStep → Step). -/
theorem blind_typed_step_preserves_CEquiv {n : SessionId}
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {s : SessionId} {r : Role}
    (hTS : TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P')
    (hBlindSend : ∀ ep target T L, lookupG G ep = some (.send target T L) →
      ep.sid = s → BlindToSend r ep.role target)
    (hBlindSelect : ∀ ep target branches, lookupG G ep = some (.select target branches) →
      ep.sid = s → BlindToSend r ep.role target)
    (hBlindRecv : ∀ ep source T L, lookupG G ep = some (.recv source T L) →
      ep.sid = s → BlindToRecv r source ep.role)
    (hBlindBranch : ∀ ep source branches, lookupG G ep = some (.branch source branches) →
      ep.sid = s → BlindToRecv r source ep.role)
    (hFreshBufs : ∀ sender receiver,
      lookupBuf bufs ⟨n, sender, receiver⟩ = []) :
    { proc := P, store := store, bufs := bufs, G := G, D := D, nextSid := n } ≈[s, r]
    { proc := P', store := store', bufs := bufs', G := G', D := D', nextSid := n } := by
  let C : Config := { proc := P, store := store, bufs := bufs, G := G, D := D, nextSid := n }
  let C' : Config := { proc := P', store := store', bufs := bufs', G := G', D := D', nextSid := n }
  have hStep : Step C C' := subject_reduction (n:=n) hTS
  simpa [C, C'] using
    (blind_step_preserves_CEquiv (C:=C) (C':=C') hStep
      hBlindSend hBlindSelect hBlindRecv hBlindBranch hFreshBufs)

/-! ## Exactness Wrappers (Blindness ↔ Observational Invariance) -/

/-- Forward observational-invariance form used in exactness packaging.
    This is the existing theorem shape, factored as a named proposition. -/
def BlindObservationalInvarianceSingle (s : SessionId) (r : Role) : Prop :=
  ∀ {C C' : Config},
    Step C C' →
    (∀ ep target T L, lookupG C.G ep = some (.send target T L) →
      ep.sid = s → BlindToSend r ep.role target) →
    (∀ ep target branches, lookupG C.G ep = some (.select target branches) →
      ep.sid = s → BlindToSend r ep.role target) →
    (∀ ep source T L, lookupG C.G ep = some (.recv source T L) →
      ep.sid = s → BlindToRecv r source ep.role) →
    (∀ ep source branches, lookupG C.G ep = some (.branch source branches) →
      ep.sid = s → BlindToRecv r source ep.role) →
    (∀ sender receiver, lookupBuf C.bufs ⟨C.nextSid, sender, receiver⟩ = []) →
    C ≈[s, r] C'

/-- Forward direction is exactly `blind_step_preserves_CEquiv`. -/
theorem blind_observational_invariance_single
    {s : SessionId} {r : Role} :
    BlindObservationalInvarianceSingle s r := by
  intro C C' hStep hBlindSend hBlindSelect hBlindRecv hBlindBranch hFreshBufs
  exact blind_step_preserves_CEquiv hStep hBlindSend hBlindSelect hBlindRecv hBlindBranch hFreshBufs

/-- Strict counterexample witness interface for a non-blind step.
    This packages the witness expected by reverse-direction exactness arguments. -/
structure NonBlindStepCounterexample (C C' : Config) (s : SessionId) (r : Role) : Type where
  step : Step C C'
  sender : Role
  receiver : Role
  notBlind : ¬ BlindTo r sender receiver
  breaksObservation : ¬ (C ≈[s, r] C')

/-- Reverse-direction witness oracle: every observational failure is explained
    by a non-blind step witness. -/
def NonBlindCounterexampleOracle (s : SessionId) (r : Role) : Prop :=
  ∀ {C C' : Config}, Step C C' → ¬ (C ≈[s, r] C') →
    Nonempty (NonBlindStepCounterexample C C' s r)

/-- Exactness package for single-step blindness reasoning:
    forward invariance + strict non-blind counterexample oracle. -/
def BlindnessExactnessSingle (s : SessionId) (r : Role) : Prop :=
  BlindObservationalInvarianceSingle s r ∧ NonBlindCounterexampleOracle s r

/-- Build single-step exactness from the existing forward theorem plus a supplied
    strict counterexample oracle for the reverse direction. -/
theorem blindness_exactness_single_of_counterexample_oracle
    {s : SessionId} {r : Role}
    (hOracle : NonBlindCounterexampleOracle s r) :
    BlindnessExactnessSingle s r := by
  exact ⟨blind_observational_invariance_single, hOracle⟩

end

/-!
## Summary

This module establishes noninterference for MPST:

1. **CEquiv**: Configuration equivalence for a role (same local type,
   incoming buffers, incoming traces)
2. **BlindTo**: When a role is neither sender nor receiver
3. **Step locality**: Steps only affect participant state
4. **blind_step_preserves_CEquiv**: The core noninterference theorem

The proofs rely on the per-edge structure of MPST: since each edge is
independent, steps on one edge cannot affect observations on unrelated edges.

**Status**: Main noninterference proofs complete. The newSession case uses a
fresh-buffer assumption for the next session ID.
-/
