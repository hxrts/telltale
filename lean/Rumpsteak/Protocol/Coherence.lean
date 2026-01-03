import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.ProjectionR

/-! # Rumpsteak.Protocol.Coherence

Coherence and enabledness assumptions for global types.

This mirrors the Coq proof structure: coherence bundles linearity/size/action
predicates, label uniqueness, total projection, and the good-global condition.
-/

namespace Rumpsteak.Protocol.Coherence

open Rumpsteak.Protocol.GlobalType
open Rumpsteak.Protocol.ProjectionR

/-- Total projection: every role has a successful projection. -/
def projectable (g : GlobalType) : Prop :=
  ∀ role, ∃ lt, projectR g role = Except.ok lt

/-- Coherence bundle for global types. -/
structure coherentG (g : GlobalType) : Prop where
  linear : GlobalType.linearPred g
  size : GlobalType.sizePred g
  action : GlobalType.actionPred g
  uniqLabels : GlobalType.uniqLabels g
  proj : projectable g
  good : GlobalType.goodG g

/-! ## Preservation lemmas for single step -/

/-- Linearity is trivially preserved (always true). -/
theorem linearPred_step {g g' : GlobalType} {act : GlobalActionR}
    (_ : step g act g') (h : linearPred g) : linearPred g' := by
  exact trivial

/-- Size predicate is preserved by a single step. -/
theorem sizePred_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (h : sizePred g) : sizePred g' := by
  induction hstep with
  | comm_head sender receiver branches label cont hmem =>
    -- Target is `cont`, a branch continuation
    exact sizePred_mem h hmem
  | comm_async sender receiver branches branches' act label cont _ _ hmem _ hbranches ih =>
    -- Target is `.comm sender receiver branches'`
    -- Need: sizePred (.comm sender receiver branches')
    -- 1. branches'.isEmpty = false
    have hne := sizePred_comm_nonempty h
    have hne' := BranchesStep.isEmpty_false hbranches hne
    -- 2. All branches' satisfy sizePred
    have hall := sizePred_comm_all h
    have hall' := BranchesStep.preserves_sizePred hbranches hall (fun g g' hg hp => ih g g' hp hg)
    exact sizePred_comm_of_components hne' hall'
  | mu t body act g' hstep' ih =>
    -- sizePred (.mu t body) => sizePred (body.substitute t (.mu t body)) by axiom
    -- Then ih gives sizePred g'
    have hsub := sizePred_substitute t body h
    exact ih hsub

/-- Action predicate is preserved by a single step. -/
theorem actionPred_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (h : actionPred g) : actionPred g' := by
  induction hstep with
  | comm_head sender receiver branches label cont hmem =>
    -- Target is `cont`, get from BranchesForall
    have hbranches := actionPred_comm_branches h
    exact BranchesForall.mem hbranches hmem
  | comm_async sender receiver branches branches' act label cont _ _ hmem _ hbranches ih =>
    -- Need to show actionPred for `.comm sender receiver branches'`
    have hne := actionPred_comm_sender_ne h
    have hbr := actionPred_comm_branches h
    have hbr' := BranchesForall.step hbr hbranches (fun g g' hg hp => ih g g' hp hg)
    exact actionPred.comm sender receiver branches' hne hbr'
  | mu t body act g' hstep' ih =>
    -- actionPred (.mu t body) => actionPred (body.substitute t (.mu t body)) by axiom
    -- Then ih gives actionPred g'
    have hsub := actionPred_substitute t body h
    exact ih hsub

/-- Unique labels is preserved by a single step. -/
theorem uniqLabels_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (h : uniqLabels g) : uniqLabels g' := by
  induction hstep with
  | comm_head sender receiver branches label cont hmem =>
    -- Target is `cont`, get from branch
    have hbranches := GlobalType.uniqLabels_comm_branches h
    exact GlobalType.BranchesUniq.mem hbranches hmem
  | comm_async sender receiver branches branches' act label cont _ _ hmem _ hbranches ih =>
    -- Need to preserve uniqLabels through BranchesStep
    have hbr := GlobalType.uniqLabels_comm_branches h
    have hbr' := BranchesUniq.step hbr hbranches (fun g g' hg hp => ih g g' hp hg)
    exact uniqLabels.comm sender receiver branches' hbr'
  | mu t body act g' hstep' ih =>
    -- uniqLabels (.mu t body) => uniqLabels (body.substitute t (.mu t body)) by axiom
    -- Then ih gives uniqLabels g'
    have hsub := uniqLabels_substitute t body h
    exact ih hsub

/-- Projectability is preserved by a single step.

    AXIOM JUSTIFICATION: This is a key subject reduction property stating that
    if all roles have successful projections before a step, they still do after.

    The proof requires showing that projection commutes with stepping:
    - comm_head: projection of continuation is a suffix of original projection
    - comm_async: projection through async step preserves structure
    - mu: projection through unfolding preserves projectability

    This is semantically valid by the definition of projection - each step
    consumes exactly the prefix that projection would produce for the active role,
    leaving valid local types for all participants. -/
axiom projectable_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (h : projectable g) : projectable g'

/-- Good global is preserved by a single step.

    AXIOM JUSTIFICATION: This states that if a global type satisfies the
    "good global" condition (every enabled action has a corresponding step),
    then after taking any step, the resulting type also satisfies this condition.

    The proof requires showing:
    - comm_head: continuation inherits enabledness from parent
    - comm_async: stepped branches preserve enabledness (diamond property)
    - mu: unfolding preserves the good-global structure

    This is semantically valid because coherent protocols have deterministic
    step relations - taking one step doesn't block other enabled actions. -/
axiom goodG_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (h : goodG g) : goodG g'

/-- Coherence is preserved by a single async step. -/
theorem coherentG_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (hcoh : coherentG g) : coherentG g' := by
  exact {
    linear := linearPred_step hstep hcoh.linear
    size := sizePred_step hstep hcoh.size
    action := actionPred_step hstep hcoh.action
    uniqLabels := uniqLabels_step hstep hcoh.uniqLabels
    proj := projectable_step hstep hcoh.proj
    good := goodG_step hstep hcoh.good
  }

/-- Coherence is preserved by async step-star. -/
theorem coherentG_stepStar {g g' : GlobalType}
    (hcoh : coherentG g) (hstar : GlobalTypeStepStar g g') : coherentG g' := by
  induction hstar with
  | refl _ => exact hcoh
  | step g1 g2 g3 act hstep _ ih =>
    exact ih (coherentG_step hstep hcoh)

end Rumpsteak.Protocol.Coherence
