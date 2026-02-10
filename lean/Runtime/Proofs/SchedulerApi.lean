import Runtime.Proofs.VM.Scheduler
import Runtime.Proofs.Concurrency

set_option autoImplicit false

/-! # Scheduler API

API types and definitions for scheduler reasoning in the VM runtime. -/

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

/-- Scheduler policy pinned to an initial VM state. -/
abbrev SchedulerPolicyPinned (st : VMState ι γ π ε ν) (policy : SchedPolicy) : Prop :=
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

/-- Iris state-interpretation invariance for scheduler executions from a fixed state. -/
def SchedulerIrisInvariant [Telltale.TelltaleIris]
    (st : VMState ι γ π ε ν) : Prop :=
  ∀ (e : Expr) (Φ : SessionVMVal → iProp),
    iProp.entails iProp.emp
      (iProp.wand
        (Iris.state_interp
          (instLanguageSessionVM (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν)) st)
        (Iris.wp
          (instLanguageSessionVM (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν)) Mask.top e Φ)) →
    ∀ e' σ',
      Iris.MultiStep' (Λ:=instLanguageSessionVM (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν))
        e st e' σ' →
      iProp.entails iProp.emp
        (bupd
          (Iris.state_interp
            (instLanguageSessionVM (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν)) σ'))

/-- Proof-carrying scheduler hypothesis bundle for one initial VM state. -/
structure VMSchedulerBundle (st₀ : VMState ι γ π ε ν) where
  policy : SchedPolicy
  policyPinned : SchedulerPolicyPinned st₀ policy

/-- Extract the policy-class profile from bundle evidence. -/
def VMSchedulerBundle.profile {st₀ : VMState ι γ π ε ν}
    (bundle : VMSchedulerBundle st₀) : SchedulerPolicyProfile :=
  schedulerPolicyProfileOf bundle.policy

/-- Bundle profile agrees with the pinned VM scheduler policy class. -/
theorem scheduler_profilePinned_from_bundle {st₀ : VMState ι γ π ε ν}
    (bundle : VMSchedulerBundle st₀) :
    schedulerPolicyProfileOf st₀.sched.policy = bundle.profile := by
  simp [VMSchedulerBundle.profile, schedulerPolicyProfileOf, bundle.policyPinned]

/-- Built-in scheduler hypothesis labels. -/
inductive VMSchedulerHypothesis where
  | policyPinned
  | policyProfileClass
  | scheduleConfluence
  | starvationFree
  | cooperativeRefinement
  | irisStateInvariant
  deriving Repr, DecidableEq, Inhabited

/-- Result of validating one scheduler hypothesis. -/
structure VMSchedulerValidationResult where
  hypothesis : VMSchedulerHypothesis
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Validation summary over a scheduler hypothesis list. -/
structure VMSchedulerSummary where
  results : List VMSchedulerValidationResult
  allPassed : Bool
  deriving Repr, Inhabited

/-- Core scheduler hypotheses available from VM scheduler proofs alone. -/
def vmSchedulerCoreHypotheses : List VMSchedulerHypothesis :=
  [ .policyPinned
  , .policyProfileClass
  , .scheduleConfluence
  , .starvationFree
  , .cooperativeRefinement
  ]

/-- Scheduler hypothesis set that additionally requires Iris invariance support. -/
def vmSchedulerWithIrisHypotheses : List VMSchedulerHypothesis :=
  vmSchedulerCoreHypotheses ++ [.irisStateInvariant]

/-- Validate one scheduler hypothesis without Iris assumptions. -/
def validateVMSchedulerHypothesis {st₀ : VMState ι γ π ε ν}
    (_bundle : VMSchedulerBundle st₀)
    (h : VMSchedulerHypothesis) : VMSchedulerValidationResult :=
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
      , detail := "Scheduler confluence theorem is available from Runtime.Proofs.VM.Scheduler."
      }
  | .starvationFree =>
      { hypothesis := h
      , passed := true
      , detail := "Starvation-freedom theorem is available from Runtime.Proofs.VM.Scheduler."
      }
  | .cooperativeRefinement =>
      { hypothesis := h
      , passed := true
      , detail := "Cooperative-refinement theorem is available from Runtime.Proofs.VM.Scheduler."
      }
  | .irisStateInvariant =>
      { hypothesis := h
      , passed := false
      , detail := "Requires TelltaleIris instance; use validateVMSchedulerHypothesisWithIris."
      }

/-- Validate one scheduler hypothesis when Iris support is available. -/
def validateVMSchedulerHypothesisWithIris [Telltale.TelltaleIris]
    {st₀ : VMState ι γ π ε ν}
    (bundle : VMSchedulerBundle st₀)
    (h : VMSchedulerHypothesis) : VMSchedulerValidationResult :=
  match h with
  | .irisStateInvariant =>
      { hypothesis := h
      , passed := true
      , detail := "Iris state-interpretation invariance is available for this VM language instance."
      }
  | _ => validateVMSchedulerHypothesis bundle h

/-- Validate an arbitrary scheduler hypothesis set without Iris assumptions. -/
def validateVMSchedulerWithHypotheses {st₀ : VMState ι γ π ε ν}
    (bundle : VMSchedulerBundle st₀)
    (hs : List VMSchedulerHypothesis) : VMSchedulerSummary :=
  let rs := hs.map (validateVMSchedulerHypothesis bundle)
  { results := rs
  , allPassed := rs.all (fun r => r.passed)
  }

/-- Validate an arbitrary scheduler hypothesis set with Iris assumptions. -/
def validateVMSchedulerWithHypothesesAndIris [Telltale.TelltaleIris]
    {st₀ : VMState ι γ π ε ν}
    (bundle : VMSchedulerBundle st₀)
    (hs : List VMSchedulerHypothesis) : VMSchedulerSummary :=
  let rs := hs.map (validateVMSchedulerHypothesisWithIris bundle)
  { results := rs
  , allPassed := rs.all (fun r => r.passed)
  }

/-- Convenience validation for scheduler core hypotheses. -/
def validateVMSchedulerCore {st₀ : VMState ι γ π ε ν}
    (bundle : VMSchedulerBundle st₀) : VMSchedulerSummary :=
  validateVMSchedulerWithHypotheses bundle vmSchedulerCoreHypotheses

/-- Convenience validation for scheduler hypotheses including Iris invariance. -/
def validateVMSchedulerWithIris [Telltale.TelltaleIris]
    {st₀ : VMState ι γ π ε ν}
    (bundle : VMSchedulerBundle st₀) : VMSchedulerSummary :=
  validateVMSchedulerWithHypothesesAndIris bundle vmSchedulerWithIrisHypotheses

/-- The pinned scheduler policy extracted from the scheduler bundle. -/
theorem scheduler_policyPinned_from_bundle {st₀ : VMState ι γ π ε ν}
    (bundle : VMSchedulerBundle st₀) :
    SchedulerPolicyPinned st₀ bundle.policy :=
  bundle.policyPinned

/-- Scheduler confluence theorem instantiated from a scheduler bundle. -/
theorem scheduler_confluence_from_bundle {st₀ : VMState ι γ π ε ν}
    (_bundle : VMSchedulerBundle st₀) :
    schedule_confluence st₀ :=
  schedule_confluence_holds st₀

/-- Starvation-freedom theorem instantiated from a scheduler bundle. -/
theorem scheduler_starvationFree_from_bundle {st₀ : VMState ι γ π ε ν}
    (_bundle : VMSchedulerBundle st₀) :
    starvation_free st₀ :=
  starvation_free_holds st₀

/-- Cooperative refinement theorem instantiated from a scheduler bundle. -/
theorem scheduler_cooperativeRefinement_from_bundle {st₀ : VMState ι γ π ε ν}
    (_bundle : VMSchedulerBundle st₀) :
    cooperative_refines_concurrent st₀ :=
  cooperative_refines_concurrent_holds st₀

/-- Iris scheduler invariance theorem instantiated from a scheduler bundle. -/
theorem scheduler_irisInvariant_from_bundle [Telltale.TelltaleIris]
    {st₀ : VMState ι γ π ε ν}
    (_bundle : VMSchedulerBundle st₀) :
    SchedulerIrisInvariant (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀ := by
  intro e Φ hWP e' σ' hStep
  exact state_interp_invariant (e := e) (σ := st₀) (Φ := Φ) hWP e' σ' hStep

end

end Proofs
end Runtime
