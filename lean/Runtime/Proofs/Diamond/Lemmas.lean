import Runtime.VM.Exec
import Batteries.Data.List.Perm

/-!
# Cross-Session Diamond: Frame Lemmas

Infrastructure for proving that executing two coroutines on disjoint sessions
in either order yields equivalent VM states. The key insight: each instruction
modifies only its own coroutine entry (via `updateCoro`) and possibly
session-local state. With distinct coroutine IDs and disjoint sessions,
these modifications commute.

## Main definitions

- `VMStateEqModTrace`: State equivalence ignoring `obsTrace` ordering
- `updateCoro_comm`: Setting distinct coroutine array indices commutes
- Frame lemmas for `faultPack`, `blockPack`, `continuePack`, `appendEvent`
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

/-! ## State Equivalence Modulo Trace Ordering -/

/-- Two VM states are equivalent modulo trace ordering if they agree on all
    computational fields and their observable traces are permutations.
    This is the correct notion of commutativity for concurrent steps:
    the trace is a multiset of ticked events, not an ordered sequence. -/
def VMStateEqModTrace {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st1 st2 : VMState ι γ π ε ν) : Prop :=
  { st1 with obsTrace := [] } = { st2 with obsTrace := [] } ∧
  st1.obsTrace.Perm st2.obsTrace

theorem VMStateEqModTrace.refl {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : VMStateEqModTrace st st :=
  ⟨Eq.refl _, List.Perm.refl _⟩

theorem VMStateEqModTrace.of_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    {st1 st2 : VMState ι γ π ε ν} (h : st1 = st2) : VMStateEqModTrace st1 st2 := by
  subst h; exact VMStateEqModTrace.refl _

/-! ## Array.set Commutativity -/

/-- Setting two distinct indices in an array commutes. -/
theorem Array_set_set_comm {α : Type u} (a : Array α)
    (i j : Nat) (vi vj : α)
    (hi : i < a.size) (hj : j < a.size) (hne : i ≠ j) :
    (a.set i vi hi).set j vj (by simp [Array.size_set]; exact hj) =
    (a.set j vj hj).set i vi (by simp [Array.size_set]; exact hi) := by
  apply Array.ext_getElem?
  intro k
  simp [Array.getElem?_set]
  split <;> split <;> simp_all

/-! ## updateCoro Commutativity -/

/-- Updating two distinct coroutine entries commutes. This is the core frame
    lemma: when c1 ≠ c2, writing back c1's modified coroutine and c2's modified
    coroutine produces the same array regardless of order. -/
theorem updateCoro_comm {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c1 c2 : CoroutineId)
    (co1 co2 : CoroutineState γ ε)
    (hne : c1 ≠ c2) (h1 : c1 < st.coroutines.size) (h2 : c2 < st.coroutines.size) :
    updateCoro (updateCoro st c1 co1) c2 co2 =
    updateCoro (updateCoro st c2 co2) c1 co1 := by
  unfold updateCoro
  simp only [Array.size_set, h1, h2, ↓reduceDIte]
  congr 1
  exact Array_set_set_comm _ _ _ _ _ h1 h2 hne

/-! ## appendEvent Lemmas -/

/-- appendEvent with none is the identity. -/
@[simp] theorem appendEvent_none {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : appendEvent st none = st := by
  simp [appendEvent]

/-- appendEvent with internal event is the identity. -/
@[simp] theorem appendEvent_internal {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) :
    appendEvent st (some StepEvent.internal) = st := by
  simp [appendEvent]

/-- appendEvent only modifies obsTrace — all other fields are preserved. -/
theorem appendEvent_preserves_core {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    { (appendEvent st ev) with obsTrace := [] } = { st with obsTrace := [] } := by
  cases ev with
  | none => simp [appendEvent]
  | some e =>
    cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

/-- updateCoro preserves obsTrace. -/
theorem updateCoro_obsTrace {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).obsTrace = st.obsTrace := by
  unfold updateCoro
  split <;> rfl

/-- updateCoro at c1 doesn't affect the coroutine entry at c2 ≠ c1. -/
theorem updateCoro_get_ne {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c1 c2 : CoroutineId)
    (co : CoroutineState γ ε)
    (hne : c1 ≠ c2) (h1 : c1 < st.coroutines.size) :
    (updateCoro st c1 co).coroutines[c2]? = st.coroutines[c2]? := by
  unfold updateCoro
  simp only [h1, ↓reduceDIte, Array.getElem?_set]
  split
  · simp_all
  · rfl

/-- updateCoro preserves programs. -/
theorem updateCoro_programs {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).programs = st.programs := by
  unfold updateCoro; split <;> rfl

/-- updateCoro preserves config. -/
theorem updateCoro_config {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).config = st.config := by
  unfold updateCoro; split <;> rfl

/-- updateCoro preserves monitor. -/
theorem updateCoro_monitor {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).monitor = st.monitor := by
  unfold updateCoro; split <;> rfl

/-- updateCoro preserves clock. -/
theorem updateCoro_clock {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).clock = st.clock := by
  unfold updateCoro; split <;> rfl

/-! ## StepPack Frame Lemmas -/

/-- faultPack preserves the VM state (only modifies the coroutine). -/
@[simp] theorem faultPack_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (err : Fault γ) (msg : String) :
    (faultPack st coro err msg).st = st := by
  simp [faultPack, pack]

/-- blockPack preserves the VM state. -/
@[simp] theorem blockPack_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (reason : BlockReason γ) :
    (blockPack st coro reason).st = st := by
  simp [blockPack, pack]

/-- continuePack preserves the VM state. -/
@[simp] theorem continuePack_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ev : Option (StepEvent ε)) :
    (continuePack st coro ev).st = st := by
  simp [continuePack, pack]

/-- haltPack preserves the VM state. -/
@[simp] theorem haltPack_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) :
    (haltPack st coro).st = st := by
  simp [haltPack, pack]

/-- faultPack event is internal (not appended to obsTrace). -/
@[simp] theorem faultPack_event_internal {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (err : Fault γ) (msg : String) :
    (faultPack st coro err msg).res.event = some StepEvent.internal := by
  simp [faultPack, pack, mkRes]

/-- blockPack event is none. -/
@[simp] theorem blockPack_event_none {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (reason : BlockReason γ) :
    (blockPack st coro reason).res.event = none := by
  simp [blockPack, pack, mkRes]

/-! ## Additional updateCoro Preservation Lemmas -/

@[simp] theorem updateCoro_sessions {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).sessions = st.sessions := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_buffers {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).buffers = st.buffers := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_guardResources {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).guardResources = st.guardResources := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_persistent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).persistent = st.persistent := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_nextCoroId {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).nextCoroId = st.nextCoroId := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_nextSessionId {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).nextSessionId = st.nextSessionId := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_resourceStates {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).resourceStates = st.resourceStates := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_coroutines_size {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).coroutines.size = st.coroutines.size := by
  unfold updateCoro; split <;> simp [Array.size_set]

/-! ## appendEvent Field Preservation -/

@[simp] theorem appendEvent_preserves_coroutines {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).coroutines = st.coroutines := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

@[simp] theorem appendEvent_preserves_programs {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).programs = st.programs := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

@[simp] theorem appendEvent_preserves_config {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).config = st.config := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

@[simp] theorem appendEvent_preserves_monitor {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).monitor = st.monitor := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

@[simp] theorem appendEvent_preserves_sessions {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).sessions = st.sessions := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

@[simp] theorem appendEvent_preserves_buffers {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).buffers = st.buffers := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

@[simp] theorem appendEvent_preserves_guardResources {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).guardResources = st.guardResources := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

@[simp] theorem appendEvent_preserves_persistent {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).persistent = st.persistent := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

@[simp] theorem appendEvent_preserves_nextCoroId {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).nextCoroId = st.nextCoroId := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

@[simp] theorem appendEvent_preserves_nextSessionId {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).nextSessionId = st.nextSessionId := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

@[simp] theorem appendEvent_preserves_clock {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).clock = st.clock := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

/-! ## Group A Step Function Frame Lemmas

For Group A instructions, the step function returns `pack.st = st`: these
instructions only modify the coroutine (via `continuePack`, `faultPack`,
`blockPack`, `haltPack`, or `pack _ st _`), never the VM state itself. -/

@[simp] theorem stepLoadImm_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (dst : Reg) (v : Value) :
    (stepLoadImm st coro dst v).st = st := by
  unfold stepLoadImm; split <;> simp [continuePack, faultPack, pack]

@[simp] theorem stepMov_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (dst src : Reg) :
    (stepMov st coro dst src).st = st := by
  unfold stepMov; split <;> (try simp [faultPack, pack]); split <;> simp [continuePack, pack]

@[simp] theorem stepJmp_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (target : PC) :
    (stepJmp st coro target).st = st := by
  unfold stepJmp; simp [pack]

@[simp] theorem stepYield_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) :
    (stepYield st coro).st = st := by
  unfold stepYield; simp [pack]

@[simp] theorem stepFork_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (sidReg : Reg) :
    (stepFork st coro sidReg).st = st := by
  unfold stepFork; split <;> simp [pack, faultPack]

@[simp] theorem stepJoin_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) :
    (stepJoin st coro).st = st := by
  unfold stepJoin; simp [pack]

@[simp] theorem stepAbort_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) :
    (stepAbort st coro).st = st := by
  unfold stepAbort; simp [pack]

@[simp] theorem stepTag_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (fact dst : Reg) :
    (stepTag st coro fact dst).st = st := by
  unfold stepTag
  split
  · -- some (.prod (.chan ep) (.string s)): nested match on setReg
    split <;> simp [continuePack, faultPack, pack]
  · simp [faultPack, pack]
  · simp [faultPack, pack]

@[simp] theorem stepCheck_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (knowledge target dst : Reg) :
    (stepCheck st coro knowledge target dst).st = st := by
  unfold stepCheck
  split
  · -- some (.prod (.chan ep) (.string s)): nested matches on readReg (tgtRole) and setReg
    -- split on readReg target (tgtRole), then zeta-reduce have bindings, then split on setReg
    split <;> (simp only []; split <;> simp [faultPack, continuePack, pack])
  · simp [faultPack, pack]
  · simp [faultPack, pack]

@[simp] theorem stepAcquire_st_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (layer : γ) (dst : Reg) :
    (stepAcquire st coro layer dst).st = st := by
  unfold stepAcquire
  split
  · simp [faultPack, pack]
  · split
    · simp [faultPack, pack]
    · split
      · simp [blockPack, pack]
      · -- GuardLayer.open_ = some ev; have/let bindings hide the match from split
        simp only []   -- zeta-reduce have bindings so split can see match setReg
        split
        · simp [faultPack, pack]
        · simp [continuePack, pack]

/-! ## commitPack Preservation Lemmas -/

/-- `commitPack` preserves `programs` from the step pack's state. -/
theorem commitPack_preserves_programs {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (coroId : CoroutineId) (p : StepPack ι γ π ε ν) :
    (commitPack coroId p).1.programs = p.st.programs := by
  unfold commitPack; simp [appendEvent_preserves_programs, updateCoro_programs]

/-- `commitPack` preserves `config` from the step pack's state. -/
theorem commitPack_preserves_config {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (coroId : CoroutineId) (p : StepPack ι γ π ε ν) :
    (commitPack coroId p).1.config = p.st.config := by
  unfold commitPack; simp [appendEvent_preserves_config, updateCoro_config]

/-- `commitPack` preserves `monitor` from the step pack's state. -/
theorem commitPack_preserves_monitor {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (coroId : CoroutineId) (p : StepPack ι γ π ε ν) :
    (commitPack coroId p).1.monitor = p.st.monitor := by
  unfold commitPack; simp [appendEvent_preserves_monitor, updateCoro_monitor]

/-! ## stepInstr Field Preservation

No instruction modifies `programs`, `config`, or `monitor`. Group A instructions
return `pack.st = st` (proved above). Group B/C instructions return
`{ st with buffers/sessions/persistent/... := ... }` which also preserves these
fields, but proving it requires unfolding through private helpers in each
`Exec*.lean` file. Those cases are sorry'd pending per-module preservation lemmas. -/

/-- `stepInstr` preserves `programs` for all instructions. -/
theorem stepInstr_preserves_programs {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (i : Instr γ ε) :
    (stepInstr st coro i).st.programs = st.programs := by
  unfold stepInstr
  cases i with
  | loadImm dst v => simp
  | mov dst src => simp
  | jmp target => simp
  | yield => simp
  | halt => simp
  | fork sidReg => simp
  | join => simp
  | abort => simp
  | tag fact dst => simp
  | check knowledge target dst => simp
  | acquire layer dst => simp
  -- Group B/C: preserves programs but requires unfolding private helpers
  | send _ _ => sorry
  | recv _ _ => sorry
  | offer _ _ => sorry
  | choose _ _ => sorry
  | release _ _ => sorry
  | invoke _ => sorry
  | «open» _ _ _ _ => sorry
  | close _ => sorry
  | spawn _ _ => sorry
  | transfer _ _ _ => sorry

/-- `stepInstr` preserves `config` for all instructions. -/
theorem stepInstr_preserves_config {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (i : Instr γ ε) :
    (stepInstr st coro i).st.config = st.config := by
  unfold stepInstr
  cases i with
  | loadImm dst v => simp
  | mov dst src => simp
  | jmp target => simp
  | yield => simp
  | halt => simp
  | fork sidReg => simp
  | join => simp
  | abort => simp
  | tag fact dst => simp
  | check knowledge target dst => simp
  | acquire layer dst => simp
  | send _ _ => sorry
  | recv _ _ => sorry
  | offer _ _ => sorry
  | choose _ _ => sorry
  | release _ _ => sorry
  | invoke _ => sorry
  | «open» _ _ _ _ => sorry
  | close _ => sorry
  | spawn _ _ => sorry
  | transfer _ _ _ => sorry

/-- `stepInstr` preserves `monitor` for all instructions. -/
theorem stepInstr_preserves_monitor {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (i : Instr γ ε) :
    (stepInstr st coro i).st.monitor = st.monitor := by
  unfold stepInstr
  cases i with
  | loadImm dst v => simp
  | mov dst src => simp
  | jmp target => simp
  | yield => simp
  | halt => simp
  | fork sidReg => simp
  | join => simp
  | abort => simp
  | tag fact dst => simp
  | check knowledge target dst => simp
  | acquire layer dst => simp
  | send _ _ => sorry
  | recv _ _ => sorry
  | offer _ _ => sorry
  | choose _ _ => sorry
  | release _ _ => sorry
  | invoke _ => sorry
  | «open» _ _ _ _ => sorry
  | close _ => sorry
  | spawn _ _ => sorry
  | transfer _ _ _ => sorry

/-! ## Diamond-Specific Infrastructure

Composition lemmas for the `updateCoro + appendEvent` pattern used by the
diamond proof. The key result is `updateCoro_appendEvent_pair_fields_eq`:
two independent `updateCoro + appendEvent` operations on distinct coroutines
produce states that agree on all non-trace computational fields. -/

/-- appendEvent preserves `resourceStates`. -/
@[simp] theorem appendEvent_preserves_resourceStates {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : Option (StepEvent ε)) :
    (appendEvent st ev).resourceStates = st.resourceStates := by
  cases ev with
  | none => simp [appendEvent]
  | some e => cases e with
    | internal => simp [appendEvent]
    | obs o => simp [appendEvent]

/-- updateCoro preserves `resourceStates`. -/
@[simp] theorem updateCoro_resourceStates' {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).resourceStates = st.resourceStates := by
  unfold updateCoro; split <;> rfl

/-- When `execInstr` returns the state unchanged, the result is `VMStateEqModTrace.refl`.
    This covers: coroutine not found, done, faulted. -/
theorem execInstr_unchanged_modTrace {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId)
    (h : (execInstr st c).1 = st) :
    VMStateEqModTrace (execInstr st c).1 st := by
  rw [h]; exact VMStateEqModTrace.refl _

/-- `updateCoro + appendEvent` preserves core state (all fields except obsTrace
    are structurally determined by `updateCoro`). -/
theorem updateCoro_appendEvent_core {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId)
    (co : CoroutineState γ ε) (ev : Option (StepEvent ε)) :
    { appendEvent (updateCoro st c co) ev with obsTrace := [] } =
    { updateCoro st c co with obsTrace := [] } :=
  appendEvent_preserves_core _ _

/-- `updateCoro_comm` applied through `appendEvent`: composing
    `(updateCoro + appendEvent)` at c1 then `(updateCoro + appendEvent)` at c2
    yields the same core state (modulo trace) as the reverse order.
    This is the key structural lemma for the Group A diamond case. -/
theorem updateCoro_appendEvent_pair_core_eq {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (c1 c2 : CoroutineId) (co1 co2 : CoroutineState γ ε)
    (ev1 ev2 : Option (StepEvent ε))
    (hne : c1 ≠ c2) (h1 : c1 < st.coroutines.size) (h2 : c2 < st.coroutines.size) :
    { appendEvent (updateCoro (appendEvent (updateCoro st c1 co1) ev1) c2 co2) ev2
        with obsTrace := [] } =
    { appendEvent (updateCoro (appendEvent (updateCoro st c2 co2) ev2) c1 co1) ev1
        with obsTrace := [] } := by
  -- The proof reduces to updateCoro_comm through these steps:
  -- 1. appendEvent_preserves_core strips outer appendEvent (obsTrace zeroed)
  -- 2. appendEvent only modifies obsTrace, so updateCoro sees same coroutines array
  --    regardless of whether appendEvent was applied first
  -- 3. updateCoro_comm gives Array_set_set_comm for distinct indices
  -- The main obstacle is Lean's structure equality with 20+ fields requiring
  -- explicit congruence through updateCoro's if-then-else on array bounds.
  sorry
