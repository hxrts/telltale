import Runtime.Proofs.ProgressCore
import Runtime.Proofs.ProgressTheorems

set_option autoImplicit false

/-! # Protocol-Machine Liveness API

Bundle-oriented liveness API mirroring the consensus validation style:
- required assumptions (well-formedness, termination model, fairness witness)
- optional progress hypothesis
- hypothesis validation summaries
- theorem wrappers from bundled evidence -/

/-
The Problem. Users need a clean API for accessing protocol-machine liveness guarantees without
navigating internal proof structure. The consensus validation pattern (required
assumptions, optional hypotheses, validation summaries) provides a proven template.

Solution Structure. Defines `HypothesisWitness` for carrying proofs as evidence,
`ProgressFrontier` and `ProgressEnabled` predicates for instruction enablement,
and `ProgressHypothesis` for optional initial-state assumptions. Provides theorem
wrappers that discharge obligations from bundled evidence.
-/

section

universe u

variable {ν : Type u} [VerificationModel ν]

/-! ## Core Liveness API -/

/-- Type-level wrapper for carrying a proof as optional evidence. -/
structure HypothesisWitness (P : Prop) : Type where
  proof : P

/-- Local alias of the frontier condition used by `protocol_machine_progress`. -/
def ProgressFrontier (store : SessionStore ν) : Prop :=
  (∃ ep target T L', SessionStore.lookupType store ep = some (.send target T L')) ∨
  (∃ ep source T L' rest,
    SessionStore.lookupType store ep = some (.recv source T L') ∧
    SessionStore.lookupTrace store { sid := ep.sid, sender := source, receiver := ep.role } = T :: rest) ∨
  (∃ ep target ℓ bs L',
    SessionStore.lookupType store ep = some (.select target bs) ∧
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L')) ∨
  (∃ ep source bs ℓ L' rest,
    SessionStore.lookupType store ep = some (.branch source bs) ∧
    SessionStore.lookupBuffer store { sid := ep.sid, sender := source, receiver := ep.role } = .string ℓ :: rest ∧
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L'))

/-- Local alias of the enabled-instruction witness produced by `protocol_machine_progress`. -/
def ProgressEnabled (store : SessionStore ν) : Prop :=
  (∃ ep target T, SendEnabled store ep target T) ∨
  (∃ ep source T, RecvEnabled store ep source T) ∨
  (∃ ep target ℓ, SelectEnabled store ep target ℓ) ∨
  (∃ ep source, BranchEnabled store ep source)

/-- Optional progress hypothesis at the initial state.
If provided, it discharges the frontier premise of `protocol_machine_progress`. -/
abbrev ProgressHypothesis (store : SessionStore ν) : Prop :=
  ¬ AllSessionsComplete store → ProgressFrontier store

/-! ## Liveness Bundles -/

/-- Concrete fairness witness for a specific termination model. -/
structure FairnessWitness (model : ProtocolMachineTerminationModel (ν := ν)) where
  k : Nat
  sched : Nat → Nat
  k_ge_numRoles : k ≥ model.numRoles
  fair : FairScheduler model.numRoles k sched

/-- Bundle of liveness assumptions, with optional progress hypothesis. -/
structure ProtocolMachineLivenessBundle (store₀ : SessionStore ν) where
  wellFormed : WellFormedVMState store₀
  model : ProtocolMachineTerminationModel (ν := ν)
  fairness : FairnessWitness (ν := ν) model
  progressHypothesis? : Option (HypothesisWitness (ProgressHypothesis store₀)) := none

/-- Built-in hypothesis labels for protocol-machine liveness bundle validation. -/
inductive ProtocolMachineLivenessHypothesis where
  | wellFormedInitial
  | terminationModel
  | fairScheduler
  | progressHypothesis
  deriving Repr, DecidableEq, Inhabited

/-- Result of validating one protocol-machine liveness hypothesis. -/
structure ProtocolMachineLivenessValidationResult where
  hypothesis : ProtocolMachineLivenessHypothesis
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Validation summary over a hypothesis list. -/
structure ProtocolMachineLivenessSummary where
  results : List ProtocolMachineLivenessValidationResult
  allPassed : Bool
  deriving Repr, Inhabited

/-- Built-in liveness core bundle (required assumptions only). -/
def protocolMachineLivenessCoreHypotheses : List ProtocolMachineLivenessHypothesis :=
  [ .wellFormedInitial
  , .terminationModel
  , .fairScheduler
  ]

/-- Built-in bundle that also requires an explicit progress hypothesis. -/
def protocolMachineLivenessWithProgressHypotheses : List ProtocolMachineLivenessHypothesis :=
  protocolMachineLivenessCoreHypotheses ++ [.progressHypothesis]

/-! ## Hypothesis Validation -/

/-- Validate one liveness hypothesis against a concrete bundle. -/
def validateProtocolMachineLivenessHypothesis {store₀ : SessionStore ν}
    (bundle : ProtocolMachineLivenessBundle store₀)
    (h : ProtocolMachineLivenessHypothesis) : ProtocolMachineLivenessValidationResult :=
  match h with
  | .wellFormedInitial =>
      { hypothesis := h
      , passed := true
      , detail := "Initial protocol-machine state well-formedness is provided in the bundle."
      }
  | .terminationModel =>
      { hypothesis := h
      , passed := true
      , detail := "A protocol-machine termination model is provided in the bundle."
      }
  | .fairScheduler =>
      { hypothesis := h
      , passed := true
      , detail := "A k-fair scheduling witness is provided in the bundle."
      }
  | .progressHypothesis =>
      { hypothesis := h
      , passed := bundle.progressHypothesis?.isSome
      , detail := "Optional progress hypothesis (non-terminal implies frontier-enabled) is provided."
      }

/-- Validate an arbitrary liveness hypothesis bundle. -/
def validateProtocolMachineLivenessWithHypotheses {store₀ : SessionStore ν}
    (bundle : ProtocolMachineLivenessBundle store₀)
    (hs : List ProtocolMachineLivenessHypothesis) : ProtocolMachineLivenessSummary :=
  let rs := hs.map (validateProtocolMachineLivenessHypothesis bundle)
  { results := rs
  , allPassed := rs.all (fun r => r.passed)
  }

/-- Convenience validator for required liveness assumptions only. -/
def validateProtocolMachineLivenessCore {store₀ : SessionStore ν}
    (bundle : ProtocolMachineLivenessBundle store₀) : ProtocolMachineLivenessSummary :=
  validateProtocolMachineLivenessWithHypotheses bundle protocolMachineLivenessCoreHypotheses

/-- Convenience validator requiring optional progress hypothesis as well. -/
def validateProtocolMachineLivenessWithProgress {store₀ : SessionStore ν}
    (bundle : ProtocolMachineLivenessBundle store₀) : ProtocolMachineLivenessSummary :=
  validateProtocolMachineLivenessWithHypotheses bundle protocolMachineLivenessWithProgressHypotheses

/-! ## Theorem Wrappers -/

/-- Termination theorem instantiated from a liveness bundle. -/
theorem protocol_machine_termination_from_bundle {store₀ : SessionStore ν}
    (bundle : ProtocolMachineLivenessBundle store₀) :
    ∃ (n : Nat) (store_final : SessionStore ν),
      store_final = executeSchedule bundle.model.step store₀ bundle.fairness.sched n ∧
      AllSessionsComplete store_final ∧
      n ≤ bundle.fairness.k * protocolMachineMeasure store₀ := by
  simpa using
    (protocol_machine_termination_under_fairness (store₀ := store₀) bundle.model
      (sched := bundle.fairness.sched) (k := bundle.fairness.k)
      bundle.wellFormed bundle.fairness.k_ge_numRoles bundle.fairness.fair)

/-- If a progress hypothesis is provided, it can be used directly to derive
initial-state enabledness. -/
theorem protocol_machine_progress_from_optional_hypothesis {store₀ : SessionStore ν}
    (bundle : ProtocolMachineLivenessBundle store₀)
    (hNonTerminal : ¬ AllSessionsComplete store₀)
    (hHasProgress : bundle.progressHypothesis?.isSome = true) :
    ProgressEnabled store₀ := by
  cases hOpt : bundle.progressHypothesis? with
  | none =>
      simp [hOpt] at hHasProgress
  | some hProgress =>
      simpa [ProgressEnabled] using
        (protocol_machine_progress bundle.wellFormed hNonTerminal (hProgress.proof hNonTerminal))

end
