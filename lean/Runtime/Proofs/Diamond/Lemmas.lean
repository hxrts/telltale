import Runtime.VM.Exec
import Batteries.Data.List.Perm

/-!
# Cross-Session Diamond: Infrastructure Lemmas

Infrastructure for proving that executing two coroutines on disjoint sessions
in either order yields equivalent VM states. The key insight: each instruction
modifies only its own coroutine entry (via `updateCoro`) and possibly
session-local state. With distinct coroutine IDs and disjoint sessions,
these modifications commute.

## Main definitions

- `VMStateEqModTrace`: State equivalence ignoring `obsTrace` ordering
- `updateCoro_comm`: Setting distinct coroutine array indices commutes
- Preservation lemmas for `updateCoro` and `appendEvent`

## Frame-Based Approach

The Protocol-level frame rule (`session_local_op_preserves_other` in SessionLocal.lean)
provides the conceptual foundation. This file contains the VM-level array and state
manipulation lemmas needed to apply that rule.
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
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st1 st2 : VMState ι γ π ε ν) : Prop :=
  { st1 with obsTrace := [] } = { st2 with obsTrace := [] } ∧
  st1.obsTrace.Perm st2.obsTrace

theorem VMStateEqModTrace.refl {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : VMStateEqModTrace st st :=
  ⟨Eq.refl _, List.Perm.refl _⟩

theorem VMStateEqModTrace.of_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
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
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
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

/-! ## updateCoro Preservation Lemmas -/

@[simp] theorem updateCoro_programs {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).programs = st.programs := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_config {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).config = st.config := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_monitor {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).monitor = st.monitor := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_clock {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).clock = st.clock := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_sessions {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).sessions = st.sessions := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_buffers {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).buffers = st.buffers := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_obsTrace {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).obsTrace = st.obsTrace := by
  unfold updateCoro; split <;> rfl

@[simp] theorem updateCoro_coroutines_size {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (co : CoroutineState γ ε) :
    (updateCoro st c co).coroutines.size = st.coroutines.size := by
  unfold updateCoro; split <;> simp [Array.size_set]

/-- updateCoro at c1 doesn't affect the coroutine entry at c2 ≠ c1. -/
theorem updateCoro_get_ne {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
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

/-! ## appendEvent Lemmas -/

@[simp] theorem appendEvent_none {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : appendEvent st none = st := by
  simp [appendEvent]

@[simp] theorem appendEvent_internal {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) :
    appendEvent st (some StepEvent.internal) = st := by
  simp [appendEvent]

/-- appendEvent only modifies obsTrace — all other fields are preserved. -/
theorem appendEvent_preserves_core {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
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

@[simp] theorem appendEvent_preserves_coroutines {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
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
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
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
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
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
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
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
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
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
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
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
