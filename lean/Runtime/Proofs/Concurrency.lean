import Runtime.ProtocolMachine.Runtime.Runner
import Runtime.ProtocolMachine.Runtime.Scheduler
import Runtime.ProgramLogic.LanguageInstance
import IrisExtractionInstance

/-! # Concurrency Invariance Proofs

Per-session normalized trace invariance and round-robin normalization. -/

/-
The Problem. Show that per-session normalized traces are invariant under
concurrency bounds, and provide the round-robin normalization property, while
keeping Iris reasoning out of the protocol machine boundary.

Solution Structure. We factor out Iris invariance, prove scheduler/concurrency
normalization lemmas, and derive per-session trace invariants.
-/

/-! ## Concurrency Invariance Proofs -/

set_option autoImplicit false
section

universe u

variable [Telltale.TelltaleIris]

/-! ## Iris adequacy for the protocol machine -/

section IrisAdequacy

open Iris Iris.BI Iris.ProgramLogic Language.Notation

local bi (IProp Telltale.TelltaleIris.GF)

variable {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]

/-- The premise of Iris's `wp_invariance`, instantiated at the protocol-machine
language: under any invariant-resource instance one can allocate a state
interpretation for `σ₁`, a weakest precondition for `e`, and a proof that the
state interpretation of `σ₂` yields `φ`. -/
def SessionVMWPPremise (s : Stuckness) (e : SessionVMExpr ι γ π ε ν)
    (σ₁ σ₂ : ProtocolMachineState ι γ π ε ν) (t₂ : List (SessionVMExpr ι γ π ε ν))
    (φ : Prop) : Prop :=
  ∀ [InvGS_gen .hasLC Telltale.TelltaleIris.GF] (κs : List Unit),
    ⊢ iprop(|={⊤}=>
      ∃ (stateI : ProtocolMachineState ι γ π ε ν → List Unit → Nat →
            IProp Telltale.TelltaleIris.GF)
        (forkPost : SessionVMVal → IProp Telltale.TelltaleIris.GF),
      letI _ : IrisGS_gen .hasLC (SessionVMExpr ι γ π ε ν) Telltale.TelltaleIris.GF :=
        .mk (toStateInterp := ⟨fun σ _ => stateI σ⟩)
          (fun _ => 0) forkPost (fun _ _ _ _ => fupd_intro)
      iprop(stateI σ₁ κs 0 ∗ WP e @ s ; ⊤ {{ _v, iprop(True) }} ∗
            (stateI σ₂ [] (.pred (List.length t₂)) -∗ ∃ (E : CoPset), |={⊤,E}=> ⌜φ⌝)))

/-- Protocol-machine adequacy: if the Iris premise holds, then `φ` holds after
any erased multi-step execution of the protocol machine from `([e], σ₁)` to
`(t₂, σ₂)`. This is upstream Iris's `wp_invariance` at the session-VM language. -/
theorem session_vm_wp_invariance (s : Stuckness) (e : SessionVMExpr ι γ π ε ν)
    (σ₁ σ₂ : ProtocolMachineState ι γ π ε ν) (t₂ : List (SessionVMExpr ι γ π ε ν))
    (φ : Prop) (hwp : SessionVMWPPremise s e σ₁ σ₂ t₂ φ)
    (hsteps : ([e], σ₁) -·->ₜₚ* (t₂, σ₂)) : φ :=
  wp_invariance (GF := Telltale.TelltaleIris.GF) s e σ₁ σ₂ t₂ φ hwp hsteps

end IrisAdequacy

/-! ## Scheduler invariance helpers -/

omit [Telltale.TelltaleIris] in
private lemma sched_round_eq_one {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (n : Nat) (st : ProtocolMachineState ι γ π ε ν) (hn : n ≥ 1) :
    schedRound n st = schedRound 1 st := by
  cases n with
  | zero =>
      cases hn
  | succ n' =>
      -- Only the nonzero case is used by `schedRound`.
      simp [schedRound]

omit [Telltale.TelltaleIris] in
private lemma run_scheduled_eq_one {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (fuel n : Nat) (st : ProtocolMachineState ι γ π ε ν) (hn : n ≥ 1) :
    runScheduled fuel n st = runScheduled fuel 1 st := by
  induction fuel generalizing st with
  | zero =>
      -- Base case: no fuel means no steps.
      simp [runScheduled]
  | succ fuel ih =>
      -- Inductive step: normalize the round count to one.
      simp [runScheduled, sched_round_eq_one (n:=n) (st:=_) hn, ih]

omit [Telltale.TelltaleIris] in
private lemma run_scheduled_policy_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (fuel n : Nat) (st : ProtocolMachineState ι γ π ε ν)
    (hpol : st.sched.policy = .roundRobin) :
    runScheduled fuel n st =
    runScheduled fuel n { st with sched := { st.sched with policy := .roundRobin } } := by
  -- Under round-robin policy, the normalization update is definitionally idempotent.
  cases st with
  | mk config code programs coroutines buffers persistent nextCoroId nextSessionId arena sessions
      resourceStates guardResources sched monitor obsTrace clock crashedSites partitionedEdges mask
      ghostSessions progressSupply =>
    cases sched with
    | mk policy readyQueue blockedSet timeslice stepCount =>
      simp at hpol
      cases hpol
      rfl

/-! ## Per-session trace invariance -/

omit [Telltale.TelltaleIris] in
theorem per_session_trace_n_invariant {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν)
    (_hwf : WFVMState st) (sid : SessionId) (fuel n1 n2 : Nat)
    (hn1 : n1 ≥ 1) (hn2 : n2 ≥ 1) :
    filterBySid sid (Runtime.ProtocolMachine.normalizeTrace (runScheduled fuel n1 st).obsTrace) =
    filterBySid sid (Runtime.ProtocolMachine.normalizeTrace (runScheduled fuel n2 st).obsTrace) := by
  -- Reduce both schedules to the single-round form.
  have h1 := run_scheduled_eq_one (fuel:=fuel) (n:=n1) (st:=st) hn1
  have h2 := run_scheduled_eq_one (fuel:=fuel) (n:=n2) (st:=st) hn2
  simp [h1, h2]

omit [Telltale.TelltaleIris] in
theorem per_session_trace_policy_invariant {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν)
    (_hwf : WFVMState st) (sid : SessionId) (fuel concurrency : Nat)
    (hpol : st.sched.policy = .roundRobin) :
    filterBySid sid (Runtime.ProtocolMachine.normalizeTrace (runScheduled fuel concurrency st).obsTrace) =
    filterBySid sid (Runtime.ProtocolMachine.normalizeTrace (runScheduled fuel concurrency
      { st with sched := { st.sched with policy := .roundRobin } }).obsTrace) := by
  -- Round-robin normalization is idempotent.
  have h := run_scheduled_policy_eq (fuel:=fuel) (n:=concurrency) (st:=st) hpol
  simp [h]
