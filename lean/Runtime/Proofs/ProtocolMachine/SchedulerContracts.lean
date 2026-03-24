import Runtime.ProtocolMachine.Runtime.SchedulerStep

set_option autoImplicit false

/-! # Runtime.Proofs.ProtocolMachine.SchedulerContracts

Proof-facing scheduler contract predicates. These are separated from the
protocol-machine runtime implementation so the runtime tree stays executable and
model-focused.
-/

universe u

def single_lane_schedule_compat {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν)
    (laneOf' : LaneOfMap)
    (laneQueues' : LaneQueueMap)
    (laneBlocked' : LaneBlockedMap γ)
    (handoffs' : List CrossLaneHandoff) : Prop :=
  schedule { st with
    sched := { st.sched with
      laneOf := laneOf'
      laneQueues := laneQueues'
      laneBlocked := laneBlocked'
      crossLaneHandoffs := handoffs' } } = schedule st

def schedule_confluence {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  ∀ st1 st2, schedule st = some st1 → schedule st = some st2 → st1 = st2

def policy_selection_deterministic {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (policy : SchedPolicy) (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  st.sched.policy = policy → schedule_confluence st

def roundRobin_selection_deterministic {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  policy_selection_deterministic .roundRobin st

def cooperative_selection_deterministic {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  policy_selection_deterministic .cooperative st

def priority_selection_deterministic {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (f : CoroutineId → Nat) (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  policy_selection_deterministic (.priority f) st

def progressAware_selection_deterministic {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  policy_selection_deterministic .progressAware st

def cooperative_refines_concurrent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  let st' := { st with sched := syncLaneViews st.sched }
  st.sched.policy = .cooperative →
    pickRunnableInQueue .roundRobin st' st'.sched.readyQueue =
      pickRunnableInQueue st'.sched.policy st' st'.sched.readyQueue

def starvation_free {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  ∀ cid, cid ∈ st.sched.readyQueue →
    match st.coroutines[cid]? with
    | none => True
    | some c => (c.status = .ready ∨ c.status = .speculating) →
        ∃ cid' st', schedule st = some (cid', st')
