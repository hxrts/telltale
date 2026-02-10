import Runtime.Proofs.Progress

set_option autoImplicit false

/-! # VM Liveness API

Bundle-oriented liveness API mirroring the consensus validation style:
- required assumptions (well-formedness, termination model, fairness witness)
- optional progress hypothesis
- hypothesis validation summaries
- theorem wrappers from bundled evidence -/

/-
The Problem. Users need a clean API for accessing VM liveness guarantees without
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

/-- Local alias of the frontier condition used by `vm_progress`. -/
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

/-- Local alias of the enabled-instruction witness produced by `vm_progress`. -/
def ProgressEnabled (store : SessionStore ν) : Prop :=
  (∃ ep target T, SendEnabled store ep target T) ∨
  (∃ ep source T, RecvEnabled store ep source T) ∨
  (∃ ep target ℓ, SelectEnabled store ep target ℓ) ∨
  (∃ ep source, BranchEnabled store ep source)

/-- Optional progress hypothesis at the initial state.
If provided, it discharges the frontier premise of `vm_progress`. -/
abbrev ProgressHypothesis (store : SessionStore ν) : Prop :=
  ¬ AllSessionsComplete store → ProgressFrontier store

/-- Concrete fairness witness for a specific termination model. -/
structure FairnessWitness (model : VMTerminationModel (ν := ν)) where
  k : Nat
  sched : Nat → Nat
  k_ge_numRoles : k ≥ model.numRoles
  fair : FairScheduler model.numRoles k sched

/-- Bundle of liveness assumptions, with optional progress hypothesis. -/
structure VMLivenessBundle (store₀ : SessionStore ν) where
  wellFormed : WellFormedVMState store₀
  model : VMTerminationModel (ν := ν)
  fairness : FairnessWitness (ν := ν) model
  progressHypothesis? : Option (HypothesisWitness (ProgressHypothesis store₀)) := none

/-- Built-in hypothesis labels for VM liveness bundle validation. -/
inductive VMLivenessHypothesis where
  | wellFormedInitial
  | terminationModel
  | fairScheduler
  | progressHypothesis
  deriving Repr, DecidableEq, Inhabited

/-- Result of validating one VM liveness hypothesis. -/
structure VMLivenessValidationResult where
  hypothesis : VMLivenessHypothesis
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Validation summary over a hypothesis list. -/
structure VMLivenessSummary where
  results : List VMLivenessValidationResult
  allPassed : Bool
  deriving Repr, Inhabited

/-- Built-in liveness core bundle (required assumptions only). -/
def vmLivenessCoreHypotheses : List VMLivenessHypothesis :=
  [ .wellFormedInitial
  , .terminationModel
  , .fairScheduler
  ]

/-- Built-in bundle that also requires an explicit progress hypothesis. -/
def vmLivenessWithProgressHypotheses : List VMLivenessHypothesis :=
  vmLivenessCoreHypotheses ++ [.progressHypothesis]

/-- Validate one liveness hypothesis against a concrete bundle. -/
def validateVMLivenessHypothesis {store₀ : SessionStore ν}
    (bundle : VMLivenessBundle store₀)
    (h : VMLivenessHypothesis) : VMLivenessValidationResult :=
  match h with
  | .wellFormedInitial =>
      { hypothesis := h
      , passed := true
      , detail := "Initial VM state well-formedness is provided in the bundle."
      }
  | .terminationModel =>
      { hypothesis := h
      , passed := true
      , detail := "A VM termination model is provided in the bundle."
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
def validateVMLivenessWithHypotheses {store₀ : SessionStore ν}
    (bundle : VMLivenessBundle store₀)
    (hs : List VMLivenessHypothesis) : VMLivenessSummary :=
  let rs := hs.map (validateVMLivenessHypothesis bundle)
  { results := rs
  , allPassed := rs.all (fun r => r.passed)
  }

/-- Convenience validator for required liveness assumptions only. -/
def validateVMLivenessCore {store₀ : SessionStore ν}
    (bundle : VMLivenessBundle store₀) : VMLivenessSummary :=
  validateVMLivenessWithHypotheses bundle vmLivenessCoreHypotheses

/-- Convenience validator requiring optional progress hypothesis as well. -/
def validateVMLivenessWithProgress {store₀ : SessionStore ν}
    (bundle : VMLivenessBundle store₀) : VMLivenessSummary :=
  validateVMLivenessWithHypotheses bundle vmLivenessWithProgressHypotheses

/-- Termination theorem instantiated from a liveness bundle. -/
theorem vm_termination_from_bundle {store₀ : SessionStore ν}
    (bundle : VMLivenessBundle store₀) :
    ∃ (n : Nat) (store_final : SessionStore ν),
      store_final = executeSchedule bundle.model.step store₀ bundle.fairness.sched n ∧
      AllSessionsComplete store_final ∧
      n ≤ bundle.fairness.k * vmMeasure store₀ := by
  simpa using
    (vm_termination_under_fairness (store₀ := store₀) bundle.model
      (sched := bundle.fairness.sched) (k := bundle.fairness.k)
      bundle.wellFormed bundle.fairness.k_ge_numRoles bundle.fairness.fair)

/-- If a progress hypothesis is provided, it can be used directly to derive
initial-state enabledness. -/
theorem vm_progress_from_optional_hypothesis {store₀ : SessionStore ν}
    (bundle : VMLivenessBundle store₀)
    (hNonTerminal : ¬ AllSessionsComplete store₀)
    (hHasProgress : bundle.progressHypothesis?.isSome = true) :
    ProgressEnabled store₀ := by
  cases hOpt : bundle.progressHypothesis? with
  | none =>
      simp [hOpt] at hHasProgress
  | some hProgress =>
      simpa [ProgressEnabled] using
        (vm_progress bundle.wellFormed hNonTerminal (hProgress.proof hNonTerminal))

end
