import Runtime.VM.Runtime.Failure.Transitions

set_option autoImplicit false

universe u

/-! ## Recovery predicates -/

def FailureSessionCoherent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_sid : SessionId) : Prop :=
  -- Session is coherent if it exists and is not closed.
  ∃ stSess, (_sid, stSess) ∈ _st.sessions ∧ stSess.phase ≠ .closed

def FStarDrain {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st _st' : VMState ι γ π ε ν) : Prop :=
  -- Configuration and programs are preserved across drain.
  _st'.config = _st.config ∧
  _st'.programs = _st.programs ∧
  -- No normal scheduling step is possible (quiescent).
  schedStep _st' = none ∧
  -- All closed sessions have empty buffers and traces.
  (∀ sid (stSess : SessionState ν), (sid, stSess) ∈ _st'.sessions →
    stSess.phase = .closed → stSess.buffers = [] ∧ stSess.traces = (∅ : DEnv))

def Recoverable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId)
    (_crashed : List (IdentityModel.SiteId ι)) : Prop :=
  -- Recovery requires a drained state with coherent session.
  ∃ st', FStarDrain st st' ∧ FailureSessionCoherent st' sid

def SiteParticipates {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_site : IdentityModel.SiteId ι)
    (_sid : SessionId) : Prop :=
  -- Site participates if the session is live and the site isn't crashed.
  FailureSessionCoherent _st _sid ∧ _site ∉ _st.crashedSites

def Participates {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_p : IdentityModel.ParticipantId ι)
    (_sid : SessionId) : Prop :=
  -- Participant participates if any of its sites participates.
  ∃ s ∈ IdentityModel.sites _p, SiteParticipates _st s _sid

def CanResume {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_p : IdentityModel.ParticipantId ι)
    (_sid : SessionId) : Prop :=
  -- A surviving participant can resume if it still participates.
  ParticipantSurvives _st.crashedSites _p ∧ Participates _st _p _sid

def crash_nonparticipant_preserves {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_site : IdentityModel.SiteId ι)
    (_sid : SessionId) : Prop :=
  -- If the site is not involved, coherence is preserved after crash.
  ¬ SiteParticipates _st _site _sid →
    FailureSessionCoherent _st _sid →
    FailureSessionCoherent (crashSite _st _site) _sid

def participant_failover {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_p : IdentityModel.ParticipantId ι)
    (_site : IdentityModel.SiteId ι) : Prop :=
  -- Participant can fail over if it survives and has an alternate site.
  ParticipantSurvives _st.crashedSites _p ∧ _site ∈ IdentityModel.sites _p

def crash_close_safe {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_sid : SessionId)
    (_survivor : IdentityModel.ParticipantId ι)
    (_crashed : List (IdentityModel.SiteId ι)) : Prop :=
  -- Closing after crash preserves coherence for surviving participant.
  ParticipantSurvives _crashed _survivor →
    FailureSessionCoherent _st _sid →
    FailureSessionCoherent (closeSession _st _sid) _sid
