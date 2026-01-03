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

/-- Coherence is preserved by async steps (to be proved). -/
axiom coherentG_stepStar {g g' : GlobalType} :
  coherentG g → GlobalTypeStepStar g g' → coherentG g'

end Rumpsteak.Protocol.Coherence
