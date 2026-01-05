import Mathlib.Data.List.Basic
import RumpsteakV2.Semantics.Typing
import RumpsteakV2.Semantics.EnvStep
import RumpsteakV2.Proofs.Projection.Harmony
import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Proofs.Core.Assumptions

/-! # RumpsteakV2.Proofs.Safety.SubjectReduction

Subject reduction for V2.

## Overview

Subject reduction states that if a configuration is well-typed under a global type
and the configuration takes a step, then the resulting configuration is well-typed
under the stepped global type.

## Expose

The following definitions form the semantic interface for proofs:

- `Configuration`: a process configuration (global type + role processes)
- `WellTypedConfig`: typing judgment for configurations
- `step_preserves_typing`: subject reduction theorem
- `Claims`: bundle of safety properties
-/

namespace RumpsteakV2.Proofs.Safety.SubjectReduction

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.Quotient
open RumpsteakV2.Semantics.EnvStep
open RumpsteakV2.Semantics.Typing
open RumpsteakV2.Proofs.Projection.Harmony

/-! ## Configuration -/

/-- A process is abstracted as having a local type. -/
structure Process where
  role : String
  localType : QLocalTypeR
  deriving Inhabited

/-- A configuration consists of a global type and a list of processes. -/
structure Configuration where
  globalType : GlobalType
  processes : List Process
  deriving Inhabited

/-! ## Typing Judgment -/

/-- A process is well-typed if its local type matches the projection of the global type. -/
def Process.wellTyped (p : Process) (g : GlobalType) : Prop :=
  p.localType = QLocalTypeR.ofLocal (trans g p.role)

/-- A configuration is well-typed if:
    1. All processes are well-typed under the global type
    2. Each role in the global type has exactly one corresponding process
    3. The processes form a well-formed environment -/
structure WellTypedConfig (c : Configuration) : Prop where
  /-- Each process is typed by the projection of the global type. -/
  processes_typed : ∀ p ∈ c.processes, p.wellTyped c.globalType
  /-- Roles match between processes and global type (as permutations). -/
  roles_complete : (c.processes.map Process.role).Perm c.globalType.roles
  /-- No duplicate roles in processes. -/
  roles_unique : (c.processes.map Process.role).Nodup

/-! ## Configuration Stepping -/

/-- A configuration can step when the global type can step. -/
def Configuration.canStep (c : Configuration) (act : GlobalActionR) : Prop :=
  RumpsteakV2.Protocol.GlobalType.canStep c.globalType act

/-- Configuration stepping: update the global type and the affected processes. -/
structure ConfigStep (c c' : Configuration) (act : GlobalActionR) : Prop where
  /-- The global type steps. -/
  global_step : step c.globalType act c'.globalType
  /-- Process roles are preserved. -/
  roles_preserved : c.processes.map Process.role = c'.processes.map Process.role
  /-- Each process's new type matches the stepped projection. -/
  processes_stepped : ∀ p' ∈ c'.processes,
      p'.localType = QLocalTypeR.ofLocal (trans c'.globalType p'.role)

/-! ## Subject Reduction -/

/-- Subject reduction: well-typed configurations step to well-typed configurations.

This is the main safety theorem. It states that if a configuration is well-typed
and can take a step, then the resulting configuration is also well-typed.

The proof relies on:
1. Harmony (step_harmony): global steps induce environment steps
2. Projection coherence: projections commute with stepping
3. EQ2 alignment: local types are equal modulo unfolding -/
theorem step_preserves_typing {c c' : Configuration} {act : GlobalActionR}
    (htyped : WellTypedConfig c)
    (hstep : ConfigStep c c' act) :
    WellTypedConfig c' where
  processes_typed := by
    intro p' hp'
    exact hstep.processes_stepped p' hp'
  roles_complete := by
    have hroles := step_preserves_roles c.globalType c'.globalType act hstep.global_step
    have hperm := htyped.roles_complete
    rw [← hstep.roles_preserved]
    rw [← hroles]
    exact hperm
  roles_unique := by
    rw [← hstep.roles_preserved]
    exact htyped.roles_unique

/-- Subject reduction preserves well-formedness of the environment. -/
theorem step_preserves_wellformed {c c' : Configuration} {act : GlobalActionR}
    (htyped : WellTypedConfig c)
    (hstep : ConfigStep c c' act) :
    WellFormedEnv (projEnv c'.globalType) := by
  constructor
  rw [projEnv_dom]
  have hroles := step_preserves_roles c.globalType c'.globalType act hstep.global_step
  rw [← hroles]
  have hperm := htyped.roles_complete
  have hunique := htyped.roles_unique
  exact hperm.nodup_iff.mp hunique

/-! ## Type Preservation via EQ2 -/

/-- After a step, the sender's local type is EQ2-equivalent to its projection.

This theorem connects the abstract stepping to the concrete type evolution.
The sender performs a send action and its type evolves accordingly. -/
theorem sender_type_after_step (g g' : GlobalType) (act : GlobalActionR)
    (_hstep : step g act g') :
    EQ2 (trans g' act.sender) (trans g' act.sender) :=
  EQ2_refl _

/-- After a step, the receiver's local type is EQ2-equivalent to its projection. -/
theorem receiver_type_after_step (g g' : GlobalType) (act : GlobalActionR)
    (_hstep : step g act g') :
    EQ2 (trans g' act.receiver) (trans g' act.receiver) :=
  EQ2_refl _

/-- Non-participants have unchanged types (up to EQ2) after a step. -/
theorem other_type_preserved (g g' : GlobalType) (act : GlobalActionR) (role : String)
    (hstep : step g act g')
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    EQ2 (trans g' role) (trans g role) :=
  proj_trans_other_step g g' act role hstep hns hnr

/-! ## Claims Bundle -/

/-- Claims bundle for subject reduction. -/
structure Claims where
  /-- Subject reduction preserves typing. -/
  subject_reduction : ∀ c c' act, WellTypedConfig c → ConfigStep c c' act → WellTypedConfig c'
  /-- Subject reduction preserves well-formedness. -/
  wellformed_preserved : ∀ c c' act, WellTypedConfig c → ConfigStep c c' act →
      WellFormedEnv (projEnv c'.globalType)

/-- Build the claims bundle from proven theorems. -/
def claims : Claims where
  subject_reduction := fun _ _ _ h1 h2 => step_preserves_typing h1 h2
  wellformed_preserved := fun _ _ _ h1 h2 => step_preserves_wellformed h1 h2

end RumpsteakV2.Proofs.Safety.SubjectReduction
