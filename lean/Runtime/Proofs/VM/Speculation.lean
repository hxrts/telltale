import Runtime.VM.Semantics.ExecSpeculation

/-! # Runtime.Proofs.VM.Speculation

Operational lemmas for VM speculation instructions (`fork`, `join`, `abort`).
-/

set_option autoImplicit false

universe u

section

theorem stepFork_depth_monotone_success
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (sidReg : Reg)
    (spec : SpeculationState) (gsid : Nat)
    (hEnabled : st.config.speculationEnabled = true)
    (hSpec : coro.specState = some spec)
    (hDepth : spec.depth ≠ 0)
    (hReg : readReg coro.regs sidReg = some (.nat gsid)) :
    let out := stepFork st coro sidReg
    ∃ d',
      out.coro.specState = some { ghostSid := gsid, depth := d' } ∧
      d' < spec.depth := by
  refine ⟨spec.depth - 1, ?_⟩
  constructor
  · simp [stepFork, hEnabled, hSpec, hDepth, hReg, pack, advancePc]
  · cases hDepthNat : spec.depth with
    | zero =>
        cases hDepth hDepthNat
    | succ _ =>
        simp

theorem stepJoin_cleanup_when_reconciled
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (spec : SpeculationState)
    (hSpec : coro.specState = some spec)
    (hMatch : matchesRealState st spec.ghostSid = true) :
    let out := stepJoin st coro
    out.coro.specState = none ∧
    out.st.ghostSessions.sessions = st.ghostSessions.sessions.erase spec.ghostSid ∧
    out.st.ghostSessions.checkpoints = st.ghostSessions.checkpoints.erase spec.ghostSid := by
  simp [stepJoin, hSpec, hMatch, pack, advancePc]

theorem stepAbort_restores_scoped_checkpoint
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (spec : SpeculationState) (checkpoint : VMSpeculationCheckpoint)
    (hSpec : coro.specState = some spec)
    (hCheckpoint : st.ghostSessions.checkpoints.get? spec.ghostSid = some checkpoint) :
    let out := stepAbort st coro
    out.coro.specState = none ∧
    out.st.obsTrace = st.obsTrace.take checkpoint.traceLen ∧
    out.st.nextEffectNonce = checkpoint.nextEffectNonce ∧
    out.st.ghostSessions.sessions = st.ghostSessions.sessions.erase spec.ghostSid ∧
    out.st.ghostSessions.checkpoints = st.ghostSessions.checkpoints.erase spec.ghostSid := by
  have hCheckpoint' : st.ghostSessions.checkpoints[spec.ghostSid]? = some checkpoint := by
    simpa using hCheckpoint
  simp [stepAbort, hSpec, pack, advancePc, hCheckpoint']

end
