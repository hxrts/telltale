import Choreography.Harmony.StepHarmony

/-! # Choreography.Harmony.SubstitutionCoreRelnnThe projection-substitution relation `ProjSubstRel` and the left mu crossed-unfold lemma used by `Choreography.Harmony.SubstitutionCore`. -/


/-
The Problem. Show projection commutes with global substitution up to EQ2.

Solution Structure. Define a coinductive witness relation, prove it is a post-fixpoint, and
close via paco coinduction.
-/

namespace Choreography.Harmony
/-! ## Substitution Commutation -/

open SessionCoTypes.EQ2Paco
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionCoTypes.EQ2
open Choreography.Projection.Project (trans_comm_sender trans_comm_receiver trans_comm_other)

/-- Witness relation for trans_subst_comm: pairs arising from projection-substitution. -/
def ProjSubstRel (t : String) (G : GlobalType) (role : String) : Rel := fun a b =>
  ∃ g : GlobalType,
    a = projTrans (g.substitute t G) role ∧
    b = (projTrans g role).substitute t (projTrans G role)

/-! ## Mu-Unfold Lemmas

The following lemmas capture the semantic properties needed for the mu cases.
These are proven in MuUnfoldLemmas.lean using proj_subst and EQ2 infrastructure. -/

/-- Mu-mu crossed unfold: left unfold relates to right mu.

When body_L and body_R are projections of related global types (via ProjSubstRel),
their mu-wrappers and s-unfolds are EQ2-related.

**Parameters:**
- body_L = trans (inner.substitute t G) role
- body_R = (trans inner role).substitute t (trans G role)
- hL : body_L is guarded for s (the trans of substituted inner)
- hR_pre : (trans inner role) is guarded for s (pre-substitution)

**Proof:** Uses `proj_subst` to rewrite both occurrences of `trans (inner.substitute t G) role`
to `(trans inner role).substitute t (trans G role)`, then applies `eq2_mu_self_unfold`.

**Proven in:** MuUnfoldLemmas.lean -/
theorem eq2_mu_crossed_unfold_left
    {s t : String} {inner G : GlobalType} {role : String}
    (hGclosed : G.isClosed = true)
    (hL : (Choreography.Projection.Project.trans (inner.substitute t G) role).isGuarded s = true)
    (hR_pre : (Choreography.Projection.Project.trans inner role).isGuarded s = true) :
    EQ2 ((Choreography.Projection.Project.trans (inner.substitute t G) role).substitute s
           (.mu s (Choreography.Projection.Project.trans (inner.substitute t G) role)))
        (.mu s ((Choreography.Projection.Project.trans inner role).substitute t
                 (Choreography.Projection.Project.trans G role))) :=
  MuUnfoldLemmas.eq2_mu_crossed_unfold_left' hGclosed hL hR_pre

end Choreography.Harmony
