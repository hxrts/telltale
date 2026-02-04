import Runtime.VM.RunScheduled
import Runtime.VM.Scheduler
import Runtime.ProgramLogic.LanguageInstance
import Runtime.Compat.WP

/-
The Problem. Show that per-session normalized traces are invariant under
concurrency bounds and scheduler policy, while keeping Iris reasoning out of
the VM boundary.

Solution Structure. We factor out Iris invariance, then prove scheduler
normalization lemmas, and finally derive per-session trace invariants.
-/

/-! ## Concurrency Invariance Proofs -/

set_option autoImplicit false
noncomputable section

universe u

/-! ## Iris invariance helper -/

theorem state_interp_invariant {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (e : Expr) (σ : VMState ι γ π ε ν) (Φ : Iris.Language.val (SessionVM ι γ π ε ν) → iProp)
    (hWP : iProp.entails iProp.emp
      (iProp.wand (Iris.state_interp (SessionVM ι γ π ε ν) σ)
        (Iris.wp (SessionVM ι γ π ε ν) Mask.top e Φ))) :
    ∀ e' σ',
      Iris.MultiStep' (Λ:=SessionVM ι γ π ε ν) e σ e' σ' →
      iProp.entails iProp.emp (bupd (Iris.state_interp (SessionVM ι γ π ε ν) σ')) :=
  -- Delegate to the generic Iris invariance lemma.
  Iris.wp_invariance (Λ:=SessionVM ι γ π ε ν) (e:=e) (σ:=σ) (Φ:=Φ) hWP

/-! ## Scheduler invariance helpers -/

private lemma schedRound_eq_one {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (n : Nat) (st : VMState ι γ π ε ν) (hn : n ≥ 1) :
    schedRound n st = schedRound 1 st := by
  cases n with
  | zero =>
      cases hn
  | succ n' =>
      -- Only the nonzero case is used by `schedRound`.
      simp [schedRound]

private lemma runScheduled_eq_one {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (fuel n : Nat) (st : VMState ι γ π ε ν) (hn : n ≥ 1) :
    runScheduled fuel n st = runScheduled fuel 1 st := by
  induction fuel generalizing st with
  | zero =>
      -- Base case: no fuel means no steps.
      simp [runScheduled]
  | succ fuel ih =>
      -- Inductive step: normalize the round count to one.
      simp [runScheduled, schedRound_eq_one (n:=n) (st:=_) hn, ih]

private lemma runScheduled_policy_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (fuel n : Nat) (st : VMState ι γ π ε ν) :
    runScheduled fuel n st =
    runScheduled fuel n { st with sched := { st.sched with policy := .roundRobin } } := by
  induction fuel generalizing st with
  | zero =>
      -- Base case: no fuel means no steps.
      simp [runScheduled]
  | succ fuel ih =>
      -- Inductive step: policy is ignored by the scheduler.
      simp [runScheduled, ih]

/-! ## Per-session trace invariance -/

theorem per_session_trace_N_invariant {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (_hwf : WFVMState st) (sid : SessionId) (fuel n1 n2 : Nat)
    (hn1 : n1 ≥ 1) (hn2 : n2 ≥ 1) :
    filterBySid sid (Runtime.VM.normalizeTrace (runScheduled fuel n1 st).obsTrace) =
    filterBySid sid (Runtime.VM.normalizeTrace (runScheduled fuel n2 st).obsTrace) := by
  -- Reduce both schedules to the single-round form.
  have h1 := runScheduled_eq_one (fuel:=fuel) (n:=n1) (st:=st) hn1
  have h2 := runScheduled_eq_one (fuel:=fuel) (n:=n2) (st:=st) hn2
  simp [h1, h2]

theorem per_session_trace_policy_invariant {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (_hwf : WFVMState st) (sid : SessionId) (fuel concurrency : Nat) :
    filterBySid sid (Runtime.VM.normalizeTrace (runScheduled fuel concurrency st).obsTrace) =
    filterBySid sid (Runtime.VM.normalizeTrace (runScheduled fuel concurrency
      { st with sched := { st.sched with policy := .roundRobin } }).obsTrace) := by
  -- The scheduler ignores policy in the current spec.
  have h := runScheduled_policy_eq (fuel:=fuel) (n:=concurrency) (st:=st)
  simp [h]
