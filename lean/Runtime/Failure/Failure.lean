import Runtime.VM.State
import Runtime.Scheduler.Scheduler
import Runtime.Compat.Inv

/-
The Problem. The VM needs a failure model that is parametric over the
identity model and integrates crashes, partitions, and recovery without
committing to a concrete recovery algorithm.

Solution Structure. Define failure modes, a failure-aware step relation,
and recovery predicates as lightweight stubs aligned with runtime.md §9.
-/

/-!
# Task 24: Failure Model and Recovery

Failure-aware step relation and recovery predicates
from runtime.md §9.

## Definitions

- `Failure` — site crash, partition, heal, corrupt, timeout
- `ParticipantLost`, `ParticipantSurvives`
- `FStep` — failure-aware step relation
- `Recoverable`, `crash_nonparticipant_preserves`
- `participant_failover`, `crash_close_safe`

Dependencies: Task 23, Scheduler.
-/

set_option autoImplicit false

universe u

/-! ## Failure modes -/

inductive Failure (ι : Type u) [IdentityModel ι] where
  -- Failure events that perturb transport or sites.
  | siteCrash (site : IdentityModel.SiteId ι)
  | partition (edges : List Edge)
  | heal (edges : List Edge)
  | corrupt (edge : Edge) (seqNo : Nat)
  | timeout (edge : Edge) (deadline : Nat)

def ParticipantLost {ι : Type u} [IdentityModel ι]
    (crashed : List (IdentityModel.SiteId ι))
    (p : IdentityModel.ParticipantId ι) : Prop :=
  -- A participant is lost if all of its sites crashed.
  ∀ s ∈ IdentityModel.sites p, s ∈ crashed

def ParticipantSurvives {ι : Type u} [IdentityModel ι]
    (crashed : List (IdentityModel.SiteId ι))
    (p : IdentityModel.ParticipantId ι) : Prop :=
  -- A participant survives if at least one site remains.
  ∃ s ∈ IdentityModel.sites p, s ∉ crashed

/-! ## Failure-aware step relation -/

def crashSite {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (_site : IdentityModel.SiteId ι) : VMState ι γ π ε ν :=
  -- Placeholder: mark site as crashed and update transport/session state.
  st

def disconnectEdges {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (_edges : List Edge) : VMState ι γ π ε ν :=
  -- Placeholder: disconnect edges in the transport layer.
  st

def reconnectEdges {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (_edges : List Edge) : VMState ι γ π ε ν :=
  -- Placeholder: reconnect edges in the transport layer.
  st

def closeSession {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (_sid : SessionId) : VMState ι γ π ε ν :=
  -- Placeholder: close a session after a crash is detected.
  st

inductive FStep {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] :
    VMState ι γ π ε ν → VMState ι γ π ε ν → Prop where
  -- Failure-aware step relation for the VM.
  | normal (st st' : VMState ι γ π ε ν)
      (h : schedStep st = some st') : FStep st st'
  | siteCrash (st : VMState ι γ π ε ν) (site : IdentityModel.SiteId ι) :
      FStep st (crashSite st site)
  | partition (st : VMState ι γ π ε ν) (edges : List Edge) :
      FStep st (disconnectEdges st edges)
  | heal (st : VMState ι γ π ε ν) (edges : List Edge) :
      FStep st (reconnectEdges st edges)
  | closeOnCrash (st : VMState ι γ π ε ν) (sid : SessionId) :
      -- Surviving participants can close sessions after a crash.
      FStep st (closeSession st sid)

/-! ## Recovery predicates -/

def SessionCoherent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_sid : SessionId) : Prop :=
  -- Placeholder: session coherence predicate.
  True

def FStarDrain {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st _st' : VMState ι γ π ε ν) : Prop :=
  -- Placeholder: closure under failure-aware steps.
  True

def Recoverable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId)
    (_crashed : List (IdentityModel.SiteId ι)) : Prop :=
  -- Recovery requires a drained state with coherent session.
  ∃ st', FStarDrain st st' ∧ SessionCoherent st' sid

def SiteParticipates {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_site : IdentityModel.SiteId ι)
    (_sid : SessionId) : Prop :=
  -- Placeholder: site participates in a session.
  True

def Participates {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_p : IdentityModel.ParticipantId ι)
    (_sid : SessionId) : Prop :=
  -- Placeholder: participant participates in a session.
  True

def CanResume {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_p : IdentityModel.ParticipantId ι)
    (_sid : SessionId) : Prop :=
  -- Placeholder: participant can resume a crashed session.
  True

def crash_nonparticipant_preserves {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_site : IdentityModel.SiteId ι)
    (_sid : SessionId) : Prop :=
  -- Placeholder: non-participant crash preserves coherence.
  True

def participant_failover {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_p : IdentityModel.ParticipantId ι)
    (_site : IdentityModel.SiteId ι) : Prop :=
  -- Placeholder: surviving participant can fail over.
  True

def crash_close_safe {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_sid : SessionId)
    (_survivor : IdentityModel.ParticipantId ι)
    (_crashed : List (IdentityModel.SiteId ι)) : Prop :=
  -- Placeholder: crash-close safety for surviving participant.
  True
