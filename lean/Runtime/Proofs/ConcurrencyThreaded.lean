import Runtime.VM.Runtime.ThreadedRunner

/-! # Threaded Concurrency Refinement

The canonical runner remains the reference semantics. This module states and
proves threaded-to-canonical refinement facts at concurrency `1`, plus a
premise-bundled conditional refinement theorem for higher concurrency.
-/

set_option autoImplicit false

universe u

section

variable {ι γ π ε ν : Type u}
variable [IdentityModel ι] [GuardLayer γ]
variable [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
variable [AuthTree ν] [AccumulatedSet ν]
variable [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
variable [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
variable [IdentityVerificationBridge ι ν]

/-! ## Concurrency-1 Equivalence -/

/-- Threaded round and canonical round coincide at concurrency `1`. -/
theorem sched_round_threaded_one_eq_sched_round_one
    (st : VMState ι γ π ε ν) :
    schedRoundThreaded 1 st = schedRound 1 st := by
  unfold schedRoundThreaded schedRound
  cases hStep : schedStep st with
  | none => simp
  | some st' => simp

/-- Fuel-bounded threaded and canonical runners coincide at concurrency `1`. -/
theorem run_scheduled_threaded_one_eq_run_scheduled
    (fuel : Nat) (st : VMState ι γ π ε ν) :
    runScheduledThreaded fuel 1 st = runScheduled fuel 1 st := by
  induction fuel generalizing st with
  | zero =>
      simp [runScheduledThreaded, runScheduled]
  | succ fuel ih =>
      simp [runScheduledThreaded, runScheduled,
        sched_round_threaded_one_eq_sched_round_one, ih]

/-- Certified threaded round refinement:
if the certificate validates and the certified wave executor refines the
canonical one-step round, then the threaded round refines canonical. -/
theorem sched_round_threaded_refines_canonical_of_certified_round
    (n : Nat) (st : VMState ι γ π ε ν)
    (hN0 : n ≠ 0) (hN1 : n ≠ 1)
    (hCert : checkWaveCertificate st (plannedWaveCertificate n st) = true)
    (hRefine :
      executePlannedWaves st (plannedWaveCertificate n st).waves = schedRound 1 st) :
    schedRoundThreaded n st = schedRound 1 st := by
  unfold schedRoundThreaded executeCertifiedRound executeThreadedRoundPlan
  simp [hN0, hN1, planThreadedRound, checkThreadedRoundPlan, hCert, hRefine]

/-! ## Conditional Refinement Premises -/

/-- Premise bundle for conditional threaded-to-canonical round refinement. -/
structure ThreadedRoundRefinementPremises (n : Nat) where
  round_refines_canonical :
    ∀ st : VMState ι γ π ε ν,
      schedRoundThreaded n st = schedRound 1 st

/-- If each threaded round refines the canonical one-step round, then the
fuel-bounded threaded runner refines the canonical runner. -/
theorem run_scheduled_threaded_refines_canonical_of_round
    (fuel n : Nat) (st : VMState ι γ π ε ν)
    (premises : ThreadedRoundRefinementPremises (ι := ι) (γ := γ)
      (π := π) (ε := ε) (ν := ν) n) :
    runScheduledThreaded fuel n st = runScheduled fuel 1 st := by
  induction fuel generalizing st with
  | zero =>
      simp [runScheduledThreaded, runScheduled]
  | succ fuel ih =>
      have hround := premises.round_refines_canonical
      simp [runScheduledThreaded, runScheduled, hround, ih]

/-! ## Per-Session Trace Corollaries -/

/-- Session-filtered normalized traces are equal for threaded and canonical
runners at concurrency `1`. -/
theorem per_session_trace_threaded_one_eq_canonical
    (fuel : Nat) (st : VMState ι γ π ε ν) (sid : SessionId) :
    filterBySid sid (Runtime.VM.normalizeTrace (runScheduledThreaded fuel 1 st).obsTrace) =
    filterBySid sid (Runtime.VM.normalizeTrace (runScheduled fuel 1 st).obsTrace) := by
  simp [run_scheduled_threaded_one_eq_run_scheduled]

/-- Session-filtered normalized trace equality under conditional round
refinement assumptions. -/
theorem per_session_trace_threaded_refines_canonical_of_round
    (fuel n : Nat) (st : VMState ι γ π ε ν) (sid : SessionId)
    (premises : ThreadedRoundRefinementPremises (ι := ι) (γ := γ)
      (π := π) (ε := ε) (ν := ν) n) :
    filterBySid sid (Runtime.VM.normalizeTrace (runScheduledThreaded fuel n st).obsTrace) =
    filterBySid sid (Runtime.VM.normalizeTrace (runScheduled fuel 1 st).obsTrace) := by
  simp [run_scheduled_threaded_refines_canonical_of_round (fuel := fuel) (n := n)
    (st := st) premises]

end
