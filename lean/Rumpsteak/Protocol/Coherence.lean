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
    -- Need to show branches' has non-empty branches and all continuations satisfy sizePred
    -- This requires showing BranchesStep preserves sizePred
    sorry
  | mu t body act g' hstep' ih =>
    -- Need sizePred for body.substitute => sizePred for g'
    sorry

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
    -- Need to construct BranchesForall for branches'
    sorry
  | mu t body act g' hstep' ih =>
    -- Need actionPred for body => actionPred for body.substitute => ih gives actionPred g'
    sorry

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
    sorry
  | mu t body act g' hstep' ih =>
    sorry

/-- Projectability is preserved by a single step. -/
theorem projectable_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (h : projectable g) : projectable g' := by
  -- This is the most complex: need to show all roles remain projectable
  sorry

/-- Good global is preserved by a single step. -/
theorem goodG_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (h : goodG g) : goodG g' := by
  -- Need to show enabledness => step exists after taking a step
  sorry

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
