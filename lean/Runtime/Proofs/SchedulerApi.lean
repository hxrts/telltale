import Runtime.Proofs.ProtocolMachine.Scheduler
import Runtime.Proofs.Concurrency

set_option autoImplicit false

/-! # Scheduler API

API types and definitions for scheduler reasoning in the protocol machine runtime. -/

/-
The Problem. Different scheduling policies (round-robin, cooperative, priority,
progress-aware) have different properties. We need a uniform interface for
reasoning about scheduler behavior and connecting to Iris separation logic proofs.

Solution Structure. Defines `SchedulerPolicyProfile` for classifying policies,
`schedulerPolicyProfileOf` for converting concrete policies, and
`SchedulerIrisInvariant` for connecting scheduler state to Iris state interpretation.
-/

/-! ## Core Development -/

namespace Runtime
namespace Proofs

section

variable {ι γ π ε ν : Type}
variable [IdentityModel ι] [GuardLayer γ]
variable [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
variable [AuthTree ν] [AccumulatedSet ν]
variable [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
variable [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
variable [IdentityVerificationBridge ι ν]

/-! ### Policy Classification -/

/-- Scheduler policy pinned to an initial protocol machine state. -/
abbrev SchedulerPolicyPinned (st : ProtocolMachineState ι γ π ε ν) (policy : SchedPolicy) : Prop :=
  st.sched.policy = policy

/-- Policy-class profile for scheduler reasoning and inventory gating. -/
inductive SchedulerPolicyProfile where
  | roundRobin
  | cooperative
  | priority
  | progressAware
  deriving Repr, DecidableEq, Inhabited

/-- Classify a concrete scheduling policy into a profile class. -/
def schedulerPolicyProfileOf (policy : SchedPolicy) : SchedulerPolicyProfile :=
  match policy with
  | .roundRobin => .roundRobin
  | .cooperative => .cooperative
  | .priority _ => .priority
  | .progressAware => .progressAware

/-! ### Iris Invariance Interface -/

/-- Iris adequacy for scheduler executions from a fixed state: any pure fact
established through the protocol-machine WP premise holds after every erased
multi-step execution starting at `st`. -/
def SchedulerIrisInvariant [Telltale.TelltaleIris]
    (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  ∀ (s : Iris.Stuckness) (e : SessionVMExpr ι γ π ε ν)
    (σ' : ProtocolMachineState ι γ π ε ν) (t' : List (SessionVMExpr ι γ π ε ν)) (φ : Prop),
    SessionVMWPPremise s e st σ' t' φ →
    FromMathlib.Relation.ReflTransGen Iris.ProgramLogic.Language.ErasedStep ([e], st) (t', σ') → φ

/-- Proof-carrying scheduler hypothesis bundle for one initial protocol machine state. -/
structure ProtocolMachineSchedulerBundle (st₀ : ProtocolMachineState ι γ π ε ν) where
  policy : SchedPolicy
  policyPinned : SchedulerPolicyPinned st₀ policy

/-! ### Bundle Metadata -/

/-- Extract the policy-class profile from bundle evidence. -/
def ProtocolMachineSchedulerBundle.profile {st₀ : ProtocolMachineState ι γ π ε ν}
    (bundle : ProtocolMachineSchedulerBundle st₀) : SchedulerPolicyProfile :=
  schedulerPolicyProfileOf bundle.policy

/-- Bundle profile agrees with the pinned protocol machine scheduler policy class. -/
theorem scheduler_profile_pinned_from_bundle {st₀ : ProtocolMachineState ι γ π ε ν}
    (bundle : ProtocolMachineSchedulerBundle st₀) :
    schedulerPolicyProfileOf st₀.sched.policy = bundle.profile := by
  simp [ProtocolMachineSchedulerBundle.profile, schedulerPolicyProfileOf, bundle.policyPinned]

/-! ### Hypothesis Inventory -/

/-- Built-in scheduler hypothesis labels. -/
inductive ProtocolMachineSchedulerHypothesis where
  | policyPinned
  | policyProfileClass
  | scheduleConfluence
  | scheduleNonblocking
  | cooperativeRefinement
  | irisStateInvariant
  deriving Repr, DecidableEq, Inhabited

/-- Result of validating one scheduler hypothesis. -/
structure ProtocolMachineSchedulerValidationResult where
  hypothesis : ProtocolMachineSchedulerHypothesis
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Validation summary over a scheduler hypothesis list. -/
structure ProtocolMachineSchedulerSummary where
  results : List ProtocolMachineSchedulerValidationResult
  allPassed : Bool
  deriving Repr, Inhabited

/-! ### Validation Sets -/

/-- Core scheduler hypotheses available from protocol machine scheduler proofs alone. -/
def protocolMachineSchedulerCoreHypotheses : List ProtocolMachineSchedulerHypothesis :=
  [ .policyPinned
  , .policyProfileClass
  , .scheduleConfluence
  , .scheduleNonblocking
  , .cooperativeRefinement
  ]

/-- Scheduler hypothesis set that additionally requires Iris invariance support. -/
def protocolMachineSchedulerWithIrisHypotheses : List ProtocolMachineSchedulerHypothesis :=
  protocolMachineSchedulerCoreHypotheses ++ [.irisStateInvariant]

/-! ### Validation Procedures -/

/-- Validate one scheduler hypothesis without Iris assumptions. -/
def validateProtocolMachineSchedulerHypothesis {st₀ : ProtocolMachineState ι γ π ε ν}
    (_bundle : ProtocolMachineSchedulerBundle st₀)
    (h : ProtocolMachineSchedulerHypothesis) : ProtocolMachineSchedulerValidationResult :=
  match h with
  | .policyPinned =>
      { hypothesis := h
      , passed := true
      , detail := "Scheduler policy is explicitly pinned in the bundle."
      }
  | .policyProfileClass =>
      { hypothesis := h
      , passed := true
      , detail := "A scheduler profile class is derivable from the pinned policy."
      }
  | .scheduleConfluence =>
      { hypothesis := h
      , passed := true
      , detail := "Scheduler confluence theorem is available from Runtime.Proofs.ProtocolMachine.Scheduler."
      }
  | .scheduleNonblocking =>
      { hypothesis := h
      , passed := true
      , detail := "One-step non-blocking scheduling theorem is available from Runtime.Proofs.ProtocolMachine.Scheduler."
      }
  | .cooperativeRefinement =>
      { hypothesis := h
      , passed := true
      , detail := "Cooperative-refinement theorem is available from Runtime.Proofs.ProtocolMachine.Scheduler."
      }
  | .irisStateInvariant =>
      { hypothesis := h
      , passed := false
      , detail := "Requires TelltaleIris instance; use validateProtocolMachineSchedulerHypothesisWithIris."
      }

/-! ## Validation Procedures: Iris-Aware Case -/

/-- Validate one scheduler hypothesis when Iris support is available. -/
def validateProtocolMachineSchedulerHypothesisWithIris [Telltale.TelltaleIris]
    {st₀ : ProtocolMachineState ι γ π ε ν}
    (bundle : ProtocolMachineSchedulerBundle st₀)
    (h : ProtocolMachineSchedulerHypothesis) : ProtocolMachineSchedulerValidationResult :=
  match h with
  | .irisStateInvariant =>
      { hypothesis := h
      , passed := true
      , detail := "Iris state-interpretation invariance is available for this protocol machine language instance."
      }
  | _ => validateProtocolMachineSchedulerHypothesis bundle h

/-! ## Validation Procedures: Batch Summaries -/

/-- Validate an arbitrary scheduler hypothesis set without Iris assumptions. -/
def validateProtocolMachineSchedulerWithHypotheses {st₀ : ProtocolMachineState ι γ π ε ν}
    (bundle : ProtocolMachineSchedulerBundle st₀)
    (hs : List ProtocolMachineSchedulerHypothesis) : ProtocolMachineSchedulerSummary :=
  let rs := hs.map (validateProtocolMachineSchedulerHypothesis bundle)
  { results := rs
  , allPassed := rs.all (fun r => r.passed)
  }

/-- Validate an arbitrary scheduler hypothesis set with Iris assumptions. -/
def validateProtocolMachineSchedulerWithHypothesesAndIris [Telltale.TelltaleIris]
    {st₀ : ProtocolMachineState ι γ π ε ν}
    (bundle : ProtocolMachineSchedulerBundle st₀)
    (hs : List ProtocolMachineSchedulerHypothesis) : ProtocolMachineSchedulerSummary :=
  let rs := hs.map (validateProtocolMachineSchedulerHypothesisWithIris bundle)
  { results := rs
  , allPassed := rs.all (fun r => r.passed)
  }

/-- Convenience validation for scheduler core hypotheses. -/
def validateProtocolMachineSchedulerCore {st₀ : ProtocolMachineState ι γ π ε ν}
    (bundle : ProtocolMachineSchedulerBundle st₀) : ProtocolMachineSchedulerSummary :=
  validateProtocolMachineSchedulerWithHypotheses bundle protocolMachineSchedulerCoreHypotheses

/-- Convenience validation for scheduler hypotheses including Iris invariance. -/
def validateProtocolMachineSchedulerWithIris [Telltale.TelltaleIris]
    {st₀ : ProtocolMachineState ι γ π ε ν}
    (bundle : ProtocolMachineSchedulerBundle st₀) : ProtocolMachineSchedulerSummary :=
  validateProtocolMachineSchedulerWithHypothesesAndIris bundle protocolMachineSchedulerWithIrisHypotheses

/-! ### Exported Scheduler Theorems -/

/-- The pinned scheduler policy extracted from the scheduler bundle. -/
theorem scheduler_policy_pinned_from_bundle {st₀ : ProtocolMachineState ι γ π ε ν}
    (bundle : ProtocolMachineSchedulerBundle st₀) :
    SchedulerPolicyPinned st₀ bundle.policy :=
  bundle.policyPinned

/-- Scheduler selection is deterministic (instantiated from a scheduler bundle).
Genuine confluence of independent steps is `LocalStepSystem.independent_steps_commute`. -/
theorem scheduler_deterministic_from_bundle {st₀ : ProtocolMachineState ι γ π ε ν}
    (_bundle : ProtocolMachineSchedulerBundle st₀) :
    schedule_deterministic st₀ :=
  schedule_deterministic_holds st₀

/-- One-step non-blocking scheduling (not fairness) instantiated from a scheduler bundle. -/
theorem scheduler_nonblocking_from_bundle {st₀ : ProtocolMachineState ι γ π ε ν}
    (_bundle : ProtocolMachineSchedulerBundle st₀) :
    schedule_nonblocking st₀ :=
  schedule_nonblocking_holds st₀

/-- Cooperative refinement theorem instantiated from a scheduler bundle. -/
theorem scheduler_cooperative_refinement_from_bundle {st₀ : ProtocolMachineState ι γ π ε ν}
    (_bundle : ProtocolMachineSchedulerBundle st₀) :
    cooperative_refines_concurrent st₀ :=
  cooperative_refines_concurrent_holds st₀

/-- Iris scheduler invariance theorem instantiated from a scheduler bundle. -/
theorem scheduler_iris_invariant_from_bundle [Telltale.TelltaleIris]
    {st₀ : ProtocolMachineState ι γ π ε ν}
    (_bundle : ProtocolMachineSchedulerBundle st₀) :
    SchedulerIrisInvariant (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀ := by
  intro s e σ' t' φ hWP hSteps
  exact session_vm_wp_invariance s e st₀ σ' t' φ hWP hSteps

end

end Proofs
end Runtime
