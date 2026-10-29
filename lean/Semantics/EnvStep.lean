import SessionCoTypes.EQ2
import SessionTypes.GlobalType
import SessionTypes.LocalTypeR
import Choreography.Projection.Project

set_option linter.dupNamespace false


/-
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
3. EnvStep: an independent environment-level communication step on
   representative environments (related to global steps in Choreography.Harmony)
4. Preservation theorems showing domain consistency
-/

/-! # Semantics.EnvStep

Environment-step relation for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `ProjectedEnv`
- `ProjectedEnv.lookup`
- `ProjectedEnv.set`
- `projEnv`
- `LocalEnv`, `projLocalEnvOnto`
- `EnvStep`
-/

namespace Semantics.EnvStep

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open SessionCoTypes.EQ2

/-! ## Basic Definitions -/

/-- Projected environment mapping roles to representative local types. -/
abbrev ProjectedEnv := List (String × LocalTypeR)

namespace ProjectedEnv

/-- Lookup a role in a projected environment. -/
def lookup (env : ProjectedEnv) (role : String) : Option LocalTypeR :=
  (env.find? (fun pair => pair.1 == role)).map Prod.snd

/-- Set a role in a projected environment (insert if missing). -/
def set (env : ProjectedEnv) (role : String) (lt : LocalTypeR) : ProjectedEnv :=
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
  g.roles.map fun role => (role, trans g role)

/-! ## Derived Theorems -/

/-- projEnv produces an environment with the same domain as g.roles. -/
theorem proj_env_dom (g : GlobalType) :
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
      exact mem_erase_dups_of_mem (List.mem_append.mpr (Or.inr hp')))
    -- comm_async case
    (fun sender receiver branches branches' act label cont _hns _hcond _hmem _hcan _hbstep ih_bstep p hp => by
      simp only [GlobalType.roles] at hp ⊢
      have hp' := mem_of_mem_erase_dups hp
      simp only [List.mem_append] at hp'
      cases hp' with
      | inl hsr => exact mem_erase_dups_of_mem (List.mem_append.mpr (Or.inl hsr))
      | inr hr => exact mem_erase_dups_of_mem (List.mem_append.mpr (Or.inr (ih_bstep p hr))))
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
  S.map fun role => (role, trans g role)

/-- projEnvOnto produces an environment with domain S. -/
theorem proj_env_onto_dom (g : GlobalType) (S : List String) :
    (projEnvOnto g S).map Prod.fst = S := by
  simp only [projEnvOnto, List.map_map, Function.comp_def, List.map_id']

/-! ## Representative-Level Environments and Environment Steps

`EnvStep` is stated over environments of *representative* local types
(`LocalTypeR`), not over `QLocalTypeR`, which is a subsingleton
(`SessionCoTypes.Quotient.QLocalTypeR.of_local_eq`). -/

/-- Environment mapping roles to representative local types. -/
abbrev LocalEnv := List (String × LocalTypeR)

/-- Lookup a role in a representative-level environment. -/
def LocalEnv.lookup (env : LocalEnv) (role : String) : Option LocalTypeR :=
  (env.find? (fun pair => pair.1 == role)).map Prod.snd

/-- Project a global type onto a fixed role set, keeping representatives. -/
def projLocalEnvOnto (g : GlobalType) (S : List String) : LocalEnv :=
  S.map fun role => (role, trans g role)

/-- Lookup in a projected environment: the projection if the role is in `S`. -/
theorem lookup_proj_local_env_onto (g : GlobalType) (S : List String) (p : String) :
    (projLocalEnvOnto g S).lookup p = if p ∈ S then some (trans g p) else none := by
  induction S with
  | nil => simp [projLocalEnvOnto, LocalEnv.lookup]
  | cons r rest ih =>
      by_cases h : r = p
      · subst h; simp [projLocalEnvOnto, LocalEnv.lookup]
      · have hb : ((r, trans g r).1 == p) = false := by simpa using h
        simp only [projLocalEnvOnto, LocalEnv.lookup, List.map_cons, List.find?_cons, hb] at ih ⊢
        rw [ih]; simp [Ne.symm h]

/-- `projLocalEnvOnto` has domain `S`. -/
theorem proj_local_env_onto_dom (g : GlobalType) (S : List String) :
    (projLocalEnvOnto g S).map Prod.fst = S := by
  simp only [projLocalEnvOnto, List.map_map, Function.comp_def, List.map_id']

/-- Environment-level communication step, defined independently of global steps.

For `act = p → q : ℓ`: the domain is unchanged; `p`'s type is a send to `q`
offering `ℓ` and becomes (up to `EQ2`) the `ℓ` continuation; `q`'s type is a
receive from `p` offering `ℓ` and becomes (up to `EQ2`) its `ℓ` continuation;
every other role keeps its type up to `EQ2`. -/
structure EnvStep (env : LocalEnv) (act : GlobalActionR) (env' : LocalEnv) : Prop where
  /-- The role domain is preserved. -/
  dom : env'.map Prod.fst = env.map Prod.fst
  /-- The sender performs the send of `act.label`. -/
  sender : ∃ bs cont, env.lookup act.sender = some (.send act.receiver bs) ∧
    (act.label, none, cont) ∈ bs ∧ ∃ t', env'.lookup act.sender = some t' ∧ EQ2 t' cont
  /-- The receiver performs the matching receive. -/
  receiver : ∃ bs cont, env.lookup act.receiver = some (.recv act.sender bs) ∧
    (act.label, none, cont) ∈ bs ∧ ∃ t', env'.lookup act.receiver = some t' ∧ EQ2 t' cont
  /-- All other roles are unchanged up to `EQ2`. -/
  frame : ∀ p, p ≠ act.sender → p ≠ act.receiver → ∀ t, env.lookup p = some t →
    ∃ t', env'.lookup p = some t' ∧ EQ2 t' t

end Semantics.EnvStep
