import Distributed.Families.CRDT.Core.CoreModel

set_option autoImplicit false

/-! # Distributed.Families.CRDT.Core.BoundaryCounterexamples

Counterexamples showing why the reusable OpCore boundary keeps its causal
guard, determinism, and replay-discipline assumptions explicit.
-/

namespace Distributed
namespace CRDT

/-! ## Missing Causal Guard -/

/-- Canonical unit operation payload used in counterexamples. -/
def unitOpCore : OpCore Unit Unit :=
  { opTag := (), args := () }

/-- Interpreter where guard rejects an incrementing operation. -/
def interpDeniedIncrement : OpCoreInterpreter Nat Unit Unit Unit where
  causalGuard := fun _ _ _ => false
  delta := fun _ _ s => s + 1

/-- Reference run for the causal-guard counterexample (guarded semantics). -/
def refRunDenied : Run Nat :=
  fun _ => 0

/-- Guardless implementation run that executes the denied operation at tick 0. -/
def implRunNoGuardDenied : Run Nat :=
  fun n => if n = 0 then evalCoreNoGuard interpDeniedIncrement unitOpCore () 0 else 0

/-- Removing `causalGuard` admits an observable envelope violation. -/
theorem envelope_counterexample_without_causal_guard :
    ¬ Envelope natUnitModel refRunDenied implRunNoGuardDenied := by
  intro hEnv
  have h0 : EqSafe natUnitModel (refRunDenied 0) (implRunNoGuardDenied 0) := hEnv 0
  have hEq : (0 : Nat) = 1 := by
    simp [EqSafe, natUnitModel, refRunDenied, implRunNoGuardDenied, evalCoreNoGuard,
      interpDeniedIncrement, unitOpCore] at h0
  exact Nat.zero_ne_one hEq

/-! ## Nondeterministic Step -/

/-- Nondeterministic one-step semantics used to witness loss of determinism. -/
def evalCoreNondet (s out : Nat) : Prop :=
  out = s ∨ out = s + 1

/-- Reference run for nondeterminism counterexample. -/
def refRunDetZero : Run Nat :=
  fun _ => 0

/-- One admissible nondeterministic implementation run choosing the divergent branch. -/
def implRunNondetOne : Run Nat :=
  fun n => if n = 0 then 1 else 0

/-- Removing determinism admits distinct outcomes from the same input step. -/
theorem nondeterministic_step_exists_distinct :
    ∃ out₁ out₂, evalCoreNondet 0 out₁ ∧ evalCoreNondet 0 out₂ ∧ out₁ ≠ out₂ := by
  refine ⟨0, 1, ?_, ?_, by decide⟩
  · simp [evalCoreNondet]
  · simp [evalCoreNondet]

/-- Nondeterministic divergent branch violates the envelope against deterministic reference. -/
theorem envelope_counterexample_without_determinism :
    evalCoreNondet 0 (implRunNondetOne 0) ∧
      ¬ Envelope natUnitModel refRunDetZero implRunNondetOne := by
  refine ⟨?_, ?_⟩
  · simp [evalCoreNondet, implRunNondetOne]
  · intro hEnv
    have h0 : EqSafe natUnitModel (refRunDetZero 0) (implRunNondetOne 0) := hEnv 0
    have hEq : (0 : Nat) = 1 := by
      simp [EqSafe, natUnitModel, refRunDetZero, implRunNondetOne] at h0
    exact Nat.zero_ne_one hEq

/-! ## Replay Discipline -/

/-- Interpreter with duplicate-sensitive delta (increment). -/
def interpReplayUnsafe : OpCoreInterpreter Nat Unit Unit Unit where
  causalGuard := fun _ _ _ => true
  delta := fun _ _ s => s + 1

/-- Reference run where an operation is delivered once. -/
def refRunSingleDelivery : Run Nat :=
  fun n => if n = 0 then evalCore interpReplayUnsafe unitOpCore () 0 else 0

/-- Implementation run where the same operation is replayed/duplicated at tick 0. -/
def implRunDuplicateDelivery : Run Nat :=
  fun n =>
    if n = 0 then
      evalCore interpReplayUnsafe unitOpCore ()
        (evalCore interpReplayUnsafe unitOpCore () 0)
    else
      0

/-- Without replay/duplication discipline, replay stability can fail. -/
theorem replay_stable_fails_without_replay_discipline :
    ¬ ReplayStableCoreEval interpReplayUnsafe := by
  intro hReplay
  have hAt0 := hReplay unitOpCore () 0
  have hEq : (2 : Nat) = 1 := by
    simp [evalCore, interpReplayUnsafe, unitOpCore] at hAt0
  exact (by decide : (2 : Nat) ≠ 1) hEq

/-- Duplicate delivery under non-idempotent deltas violates the envelope. -/
theorem envelope_counterexample_without_replay_discipline :
    ¬ Envelope natUnitModel refRunSingleDelivery implRunDuplicateDelivery := by
  intro hEnv
  have h0 : EqSafe natUnitModel (refRunSingleDelivery 0) (implRunDuplicateDelivery 0) := hEnv 0
  have hEq : (1 : Nat) = 2 := by
    simp [EqSafe, natUnitModel, refRunSingleDelivery, implRunDuplicateDelivery,
      evalCore, interpReplayUnsafe, unitOpCore] at h0
  exact (by decide : (1 : Nat) ≠ 2) hEq

/-- Combined OpCore boundary/minimality witness suite for removed components. -/
theorem op_core_boundary_minimality_counterexamples :
    (¬ Envelope natUnitModel refRunDenied implRunNoGuardDenied) ∧
      (evalCoreNondet 0 (implRunNondetOne 0) ∧
        ¬ Envelope natUnitModel refRunDetZero implRunNondetOne) ∧
      (¬ ReplayStableCoreEval interpReplayUnsafe ∧
        ¬ Envelope natUnitModel refRunSingleDelivery implRunDuplicateDelivery) := by
  refine ⟨envelope_counterexample_without_causal_guard, ?_, ?_⟩
  · exact envelope_counterexample_without_determinism
  · exact ⟨replay_stable_fails_without_replay_discipline,
      envelope_counterexample_without_replay_discipline⟩

end CRDT
end Distributed
