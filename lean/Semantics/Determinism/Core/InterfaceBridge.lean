import Semantics.Determinism.Core.GlobalDeterminism
import Semantics.SubjectReduction

/-!
# Determinism/SubjectReduction Interface Bridge

Bridge lemmas connecting the environment-indexed determinism configuration to
the process-indexed subject-reduction configuration.
-/

set_option autoImplicit false

namespace Semantics.Determinism

open Semantics.Environment

/-- Embed a subject-reduction configuration into the determinism interface by
fixing an environment snapshot. -/
def ofSubjectConfiguration
    (c : Semantics.SubjectReduction.Configuration) (env : EnvConfig := default) :
    Configuration :=
  { globalType := c.globalType, env := env }

/-- The bridge embedding preserves the global type component exactly. -/
theorem ofSubjectConfiguration_globalType
    (c : Semantics.SubjectReduction.Configuration) (env : EnvConfig := default) :
    (ofSubjectConfiguration c env).globalType = c.globalType := rfl

/-- A subject-reduction step induces a determinism step once branch-label
uniqueness is supplied on the source global type. -/
theorem ofSubjectStep_to_configStep
    {c c' : Semantics.SubjectReduction.Configuration}
    {act : GlobalActionR}
    {env : EnvConfig}
    (hStep : Semantics.SubjectReduction.ConfigStep c c' act)
    (hUnique : c.globalType.uniqueBranchLabels = true) :
    ConfigStep (ofSubjectConfiguration c env) (ofSubjectConfiguration c' env) act := by
  exact ⟨hUnique, hStep.global_step, rfl⟩

end Semantics.Determinism
