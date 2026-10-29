import Protocol.Deployment
import Protocol.Determinism
import Protocol.Simulation.Properties

/-! # Examples

Small worked examples over the Protocol operational semantics: a sequential
program `assign; skip` executed to termination, with its step decided by
`stepBaseDecide` and its successor shown unique.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-- Example configuration: `x := unit` with an empty runtime state. -/
def exampleAssignConfig : Config :=
  { proc := .assign "x" .unit, store := [], bufs := [], G := [], D := (∅ : DEnv), nextSid := 0 }

/-- Expected successor of `exampleAssignConfig`: terminated, with `x` bound. -/
def exampleAssignDone : Config :=
  { exampleAssignConfig with proc := .skip, store := [("x", .unit)] }

/-- The example assignment takes a base step to `exampleAssignDone`. -/
theorem example_assign_step : StepBase exampleAssignConfig exampleAssignDone :=
  StepBase.assign rfl

/-- The decision procedure finds that step. -/
theorem example_assign_decide :
    stepBaseDecide exampleAssignConfig = some exampleAssignDone :=
  step_decide_complete_base example_assign_step

/-- Any base successor of the example configuration is `exampleAssignDone`. -/
theorem example_assign_unique {C' : Config} (h : StepBase exampleAssignConfig C') :
    C' = exampleAssignDone :=
  step_base_deterministic_strong h example_assign_step

/-- The example runs to a terminated configuration in the multi-step closure. -/
theorem example_assign_terminates :
    Steps exampleAssignConfig exampleAssignDone ∧ exampleAssignDone.proc = .skip :=
  ⟨Relation.ReflTransGen.single (Step.base example_assign_step), rfl⟩

end
