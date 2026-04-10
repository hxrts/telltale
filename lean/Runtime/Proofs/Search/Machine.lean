import Runtime.Proofs.Search.Executable

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Machine

Machine-level search theorems layered on top of the executable reduced machine
semantics.

The original `Machine` layer used an abstract step constructor. The strengthened
proof surface now treats executable reduced stepping as primary and derives the
machine-facing theorems from that concrete semantics.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Machine-level canonical step packaged as one executable reduced step plus
the current-state invariant bundle. -/
structure CanonicalMachineStep
    (goal : Nat) (current next : SearchMachineState) : Prop where
  currentInvariants : MachineInvariants goal current
  next_eq_executable : next = executableCanonicalStep goal current

/-- A machine trace follows executable reduced canonical stepping. -/
abbrev CanonicalMachineTrace (goal : Nat) (trace : SearchMachineTrace) : Prop :=
  ∀ i, CanonicalMachineStep goal (trace i) (trace (i + 1))

/-- The executable reduced one-step semantics exposes the same next-step
service fact for current min-priority entries as the frontier-only fairness
layer. -/
theorem canonical_machine_step_services_current_min_priority_entries
    {goal : Nat}
    {current next : SearchMachineState}
    (hStep : CanonicalMachineStep goal current next)
    {entry : FrontierEntry}
    (hMin : IsMinPriority current.frontier entry) :
    entry ∉ next.frontier := by
  rw [hStep.next_eq_executable, executableCanonicalStep, executableNextFrontier]
  exact canonical_serial_one_step_fair_for_min_priority_entries hMin

/-- The executable reduced step preserves the explicit invariant bundle. -/
theorem canonical_machine_step_preserves_invariants
    {goal : Nat}
    {current next : SearchMachineState}
    (hStep : CanonicalMachineStep goal current next) :
    MachineInvariants goal next := by
  rw [hStep.next_eq_executable]
  exact executable_canonical_step_preserves_invariants hStep.currentInvariants

/-- Machine traces inherit the frontier-facing one-step eventual service theorem
for currently min-priority entries through frontier projection. -/
theorem canonical_machine_trace_currently_min_priority_eventually_serviced
    {goal start : Nat}
    {trace : SearchMachineTrace}
    {entry : FrontierEntry}
    (hTrace : CanonicalMachineTrace goal trace)
    (hMin : IsMinPriority (trace start).frontier entry) :
    EventuallyServicedWithin (frontierTraceOfMachineTrace trace) start 1 entry := by
  refine ⟨0, Nat.zero_lt_one, ?_⟩
  simpa [frontierTraceOfMachineTrace] using
    canonical_machine_step_services_current_min_priority_entries (hTrace start) hMin

/-- The executable trace relation refines directly into the packaged
machine-step relation. -/
theorem executable_trace_refines_canonical_machine_trace
    {goal : Nat}
    {trace : SearchMachineTrace}
    (hTrace : ExecutableCanonicalMachineTrace goal trace)
    (hInv : ∀ i, MachineInvariants goal (trace i)) :
    CanonicalMachineTrace goal trace := by
  intro i
  exact
    { currentInvariants := hInv i
    , next_eq_executable := hTrace i
    }

/-- The executable reduced step artifact matches the canonical reduced artifact
surface. This is the runtime-facing refinement boundary from executable machine
stepping back into the existing search artifact vocabulary. -/
theorem canonical_machine_step_artifact_refines_runtime_boundary
    (goal : Nat) (state : SearchMachineState) :
    executableStepArtifact goal state = canonicalStepArtifact state.frontier :=
  executable_step_artifact_refines_canonical_step_artifact goal state

/-- The reduced runtime-state artifact vocabulary is explicitly extracted from
the executable machine state. -/
theorem canonical_machine_state_artifact_is_runtime_projection
    (state : SearchMachineState) :
    stateArtifactOfMachineState state =
      stateArtifactOfStateSlice (stateSliceOfMachineState state) :=
  runtime_state_artifact_of_machine_state_is_projection state

end Search
end Proofs
end Runtime
