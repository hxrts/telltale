import Telltale.Protocol.CoTypes.Quotient
import Telltale.Protocol.GlobalType
import Telltale.Protocol.LocalTypeR
import Telltale.Protocol.Projection.Trans

set_option linter.dupNamespace false

/-!
The Problem. Given a global type and its stepping semantics, we need a way
to represent the local view of each participant. The challenge is that global
types step as a whole, but each role only sees its local session type.

We must connect global steps to local environment updates in a way that:
1. Preserves the relationship between global and local types via projection
2. Handles the fact that role sets can shrink during execution
3. Supports reasoning about multi-role configurations

Solution Structure. We define:
1. ProjectedEnv: maps roles to their local types (via trans projection)
2. projEnv/projEnvOnto: construct environments from global types
3. EnvStep/EnvStepOnto: lift global steps to environment transitions
4. Preservation theorems showing domain consistency
-/

/-! # Telltale.Semantics.EnvStep

Environment-step relation for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `ProjectedEnv`
- `ProjectedEnv.lookup`
- `ProjectedEnv.set`
- `projEnv`
- `EnvStep`
- `step_to_envstep`
- `envstep_preserves_dom`
-/

namespace Telltale.Semantics.EnvStep

open Telltale.Protocol.GlobalType
open Telltale.Protocol.LocalTypeR
open Telltale.Protocol.Projection.Trans
open Telltale.Protocol.CoTypes.Quotient

/-! ## Basic Definitions -/

/-- Projected environment mapping roles to local types (quotiented). -/
abbrev ProjectedEnv := List (String × QLocalTypeR)

namespace ProjectedEnv

/-- Lookup a role in a projected environment. -/
def lookup (env : ProjectedEnv) (role : String) : Option QLocalTypeR :=
  (env.find? (fun pair => pair.1 == role)).map Prod.snd

/-- Set a role in a projected environment (insert if missing). -/
def set (env : ProjectedEnv) (role : String) (lt : QLocalTypeR) : ProjectedEnv :=
  match env with
  | [] => [(role, lt)]
  | (r, t) :: rest =>
      if r == role then
        (role, lt) :: rest
      else
        (r, t) :: set rest role lt

end ProjectedEnv

/-! ## Projection and Environment Steps -/

/-- Project a global type into a role-indexed environment. -/
def projEnv (g : GlobalType) : ProjectedEnv :=
  g.roles.map fun role => (role, QLocalTypeR.ofLocal (trans g role))

/-- Environment step induced by a global step through projection.

This lifts global type transitions to environment-level transitions by
projecting both the source and target global types. -/
inductive EnvStep : ProjectedEnv → GlobalActionR → ProjectedEnv → Prop where
  | of_global (g g' : GlobalType) (act : GlobalActionR) :
      step g act g' →
      EnvStep (projEnv g) act (projEnv g')

/-! ## Derived Theorems -/

/-- Global step implies environment step (via projection). -/
theorem step_to_envstep (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') :
    EnvStep (projEnv g) act (projEnv g') :=
  EnvStep.of_global g g' act hstep

/-- projEnv produces an environment with the same domain as g.roles. -/
theorem projEnv_dom (g : GlobalType) :
    (projEnv g).map Prod.fst = g.roles := by
  simp only [projEnv, List.map_map, Function.comp_def, List.map_id']

/-- Global step can only shrink the role set (roles are contained).

This is the correct formulation from the ECOOP 2025 paper (Tirore et al.):
stepping can remove roles that only appear in the reduced interaction,
but cannot add new roles.

Proof by mutual induction on step and BranchesStep:
- `comm_head`: Branch continuation's roles ⊆ rolesOfBranches ⊆ g.roles
- `comm_async`: BranchesStep preserves branch structure, IH applies
- `mu`: substitute_mu_roles_subset shows substitution doesn't add roles -/
theorem step_roles_subset (g g' : GlobalType) (act : GlobalActionR)
    (h : step g act g') : ∀ p, p ∈ g'.roles → p ∈ g.roles :=
  @step.rec
    (motive_1 := fun g _act g' _ => ∀ p, p ∈ g'.roles → p ∈ g.roles)
    (motive_2 := fun bs _act bs' _ => ∀ p, p ∈ rolesOfBranches bs' → p ∈ rolesOfBranches bs)
    -- comm_head case
    (fun sender receiver branches label cont hmem p hp => by
      simp only [GlobalType.roles]
      have hp' : p ∈ rolesOfBranches branches := by
        induction branches with
        | nil => simp at hmem
        | cons hd tl ih =>
            simp only [rolesOfBranches, List.mem_append]
            cases hmem with
            | head => left; simp_all
            | tail _ htail => right; exact ih htail
      exact mem_eraseDups_of_mem (List.mem_append.mpr (Or.inr hp')))
    -- comm_async case
    (fun sender receiver branches branches' act label cont _hns _hcond _hmem _hcan _hbstep ih_bstep p hp => by
      simp only [GlobalType.roles] at hp ⊢
      have hp' := mem_of_mem_eraseDups hp
      simp only [List.mem_append] at hp'
      cases hp' with
      | inl hsr => exact mem_eraseDups_of_mem (List.mem_append.mpr (Or.inl hsr))
      | inr hr => exact mem_eraseDups_of_mem (List.mem_append.mpr (Or.inr (ih_bstep p hr))))
    -- mu case
    (fun t body act g' _hstep ih_step p hp => by
      simp only [GlobalType.roles]
      have hsub := ih_step p hp
      exact substitute_mu_roles_subset body t p hsub)
    -- BranchesStep nil case
    (fun _act _p hp => by simp [rolesOfBranches] at hp)
    -- BranchesStep cons case
    (fun label g g' rest rest' act _hstep _hbstep ih_step ih_bstep p hp => by
      simp only [rolesOfBranches, List.mem_append] at hp ⊢
      cases hp with
      | inl hl => left; exact ih_step p hl
      | inr hr => right; exact ih_bstep p hr)
    (t := h)

/-! ## Projection onto Fixed Role Set

Following the Coq mechanization (ECOOP 2025), we project onto a fixed role set S
rather than g.roles. This handles the case where roles shrink during stepping. -/

/-- Project a global type onto a fixed role set. -/
def projEnvOnto (g : GlobalType) (S : List String) : ProjectedEnv :=
  S.map fun role => (role, QLocalTypeR.ofLocal (trans g role))

/-- projEnvOnto produces an environment with domain S. -/
theorem projEnvOnto_dom (g : GlobalType) (S : List String) :
    (projEnvOnto g S).map Prod.fst = S := by
  simp only [projEnvOnto, List.map_map, Function.comp_def, List.map_id']

/-- Environment step onto a fixed role set.

This variant requires that the initial global type's roles are contained in S,
ensuring that projection is well-defined even as roles shrink during execution. -/
inductive EnvStepOnto (S : List String) :
    ProjectedEnv → GlobalActionR → ProjectedEnv → Prop where
  | of_global (g g' : GlobalType) (act : GlobalActionR) :
      step g act g' →
      (∀ p, p ∈ g.roles → p ∈ S) →
      EnvStepOnto S (projEnvOnto g S) act (projEnvOnto g' S)

/-- Environment step onto fixed role set preserves domain.

The domain remains S throughout execution, even as the active roles
in the global type may shrink. -/
theorem envstepOnto_preserves_dom {S : List String} {env env' : ProjectedEnv}
    {act : GlobalActionR} (hstep : EnvStepOnto S env act env') :
    env.map Prod.fst = env'.map Prod.fst := by
  cases hstep with
  | of_global g g' _ _ _ =>
      simp only [projEnvOnto_dom]

/-! ## Legacy API (deprecated)

These definitions are kept for backward compatibility but should be migrated
to use the fixed role set approach. -/

end Telltale.Semantics.EnvStep
