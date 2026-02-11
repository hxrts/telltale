import Choreography.Harmony.SubstitutionCore

/-! # Choreography.Harmony.SubstitutionUnfold

Single mu-unfold substitution/projection commutation lemmas.
-/

/-
The Problem. Connect projection-substitution commutation to one-step mu-unfold behavior.

Solution Structure. Split guarded/unguarded projected-body cases and reuse core commutation.
-/

namespace Choreography.Harmony
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionCoTypes.EQ2
/-! ## subst_end_unguarded_eq2_end -/
open Choreography.Harmony.SubstEndUnguarded (subst_end_unguarded_eq2_end)

/-- Projection commutes with mu-substitution up to EQ2.

With the Coq-style `trans` definition:
- `trans (.mu t body) role = if (trans body role).isGuarded t then .mu t (trans body role) else .end`

The key cases:
1. If `(trans body role).isGuarded t = true`: projection produces `.mu t (trans body role)`
   and we use trans_subst_comm to show correspondence
2. If `(trans body role).isGuarded t = false`: projection produces `.end`, and
   substitution also produces `.end` (matching behavior)

Coq reference: This follows from full_eunf_subst in coLocal.v. -/
private theorem trans_substitute_unfold_guarded
    (t : String) (body : GlobalType) (role : String) (hclosed : (GlobalType.mu t body).isClosed = true)
    (hguard : (projTrans body role).isGuarded t = true) :
    EQ2 (projTrans (body.substitute t (GlobalType.mu t body)) role)
        ((projTrans (GlobalType.mu t body) role).unfold) := by
  -- Guarded case: both sides are the unfolded mu, use trans_subst_comm.
  have h_proj_mu : projTrans (.mu t body) role = LocalTypeR.mu t (projTrans body role) := by
    simp [projTrans, Choreography.Projection.Project.trans, hguard]
  rw [h_proj_mu, LocalTypeR.unfold_mu, ← h_proj_mu]
  exact trans_subst_comm body t (.mu t body) role hclosed

private theorem trans_substitute_unfold_unguarded
    (t : String) (body : GlobalType) (role : String) (hclosed : (GlobalType.mu t body).isClosed = true)
    (hguard : (projTrans body role).isGuarded t = false) :
    EQ2 (projTrans (body.substitute t (GlobalType.mu t body)) role)
        ((projTrans (GlobalType.mu t body) role).unfold) := by
  -- Unguarded case: projection collapses to end, use subst_end_unguarded_eq2_end.
  have h_proj_end : projTrans (.mu t body) role = LocalTypeR.end := by
    simp [projTrans, Choreography.Projection.Project.trans, hguard]
  rw [h_proj_end]
  simp [LocalTypeR.unfold]
  have hproj_subst :
      projTrans (body.substitute t (.mu t body)) role =
        (projTrans body role).substitute t (projTrans (.mu t body) role) :=
    Choreography.Projection.ProjSubst.proj_subst_mu_self t body role hclosed
  have hproj_subst' :
      projTrans (body.substitute t (.mu t body)) role =
        (projTrans body role).substitute t LocalTypeR.end := by
    simpa [h_proj_end] using hproj_subst
  have hsub_end : EQ2 ((projTrans body role).substitute t LocalTypeR.end) LocalTypeR.end :=
    subst_end_unguarded_eq2_end (projTrans body role) t hguard
  simpa [← hproj_subst'] using hsub_end

/-- Projection commutes with a single mu-unfold (up to EQ2) for closed globals. -/
theorem trans_substitute_unfold (t : String) (body : GlobalType) (role : String)
    (hclosed : (GlobalType.mu t body).isClosed = true) :
    EQ2 (projTrans (body.substitute t (GlobalType.mu t body)) role)
        ((projTrans (GlobalType.mu t body) role).unfold) := by
  -- Case split on whether the projected body is guarded.
  by_cases hguard : (projTrans body role).isGuarded t = true
  · exact trans_substitute_unfold_guarded t body role hclosed hguard
  · have hguard' : (projTrans body role).isGuarded t = false := by
      cases h : (projTrans body role).isGuarded t with
      | true => exact (False.elim (hguard h))
      | false => rfl
    exact trans_substitute_unfold_unguarded t body role hclosed hguard'


end Choreography.Harmony
