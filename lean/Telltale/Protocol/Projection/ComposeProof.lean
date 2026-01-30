import Telltale.Protocol.CoTypes.EQ2
import Telltale.Protocol.Projection.Project
import Telltale.Protocol.Projection.Project.ImplExtraction

/-
The Problem. When composing projection relations through mu types, we need to
show that EQ2 equivalence composes with CProjectTransRel. The challenge is
that mu introduces coinductive structure, but we don't want full coinduction.

We must prove: if a EQ2 (.mu v body) and (.mu v body) CProjectTransRel c,
then a EQ2F CProjectTransRelComp c (single-step without coinduction).

Solution Structure. Use monotonicity and subset reasoning rather than paco
coinduction, since we're proving a single-step property EQ2F, not EQ2.
-/

/-! # Direct Proof for CProjectTransRel Composition

This module provides a direct proof for composing EQ2 and CProjectTransRel through mu.

The key insight: we don't need paco's coinduction machinery here because we're proving
a single-step property (EQ2F). We can directly use:
1. Monotonicity of EQ2F
2. The existing CProjectTransRel_postfix theorem
3. The fact that CProjectTransRel ⊆ CProjectTransRelComp

## Main Result

- `EQ2_CProjectTransRel_compose_through_mu`: Direct composition proof
-/

namespace Telltale.Protocol.Projection.ProjectPaco

open Telltale.Protocol.CoTypes.EQ2
open Telltale.Protocol.LocalTypeR
open Telltale.Protocol.Projection.Project

/-! ## Main Composition Theorem -/

/-- Composing EQ2 and CProjectTransRel through a mu intermediate satisfies EQ2F.

    **Proof strategy**:
    1. Use CProjectTransRel_postfix to get: EQ2F (EQ2_closure CProjectTransRel) (.mu v body) c
    2. Use monotonicity to lift: EQ2_closure CProjectTransRel ⊆ EQ2_closure CProjectTransRelComp
       (since CProjectTransRel is the base case of CProjectTransRelComp)
    3. Apply EQ2F.mono to get the result

    This is simpler than using paco_coind because we're proving a single-step property,
    not a coinductive relation. -/
theorem EQ2_CProjectTransRel_compose_through_mu
    {a c : LocalTypeR} {v : String} {body : LocalTypeR}
    (heq : EQ2 a (.mu v body))
    (hrel : CProjectTransRel (.mu v body) c)
    (hWFa : LocalTypeR.WellFormed a) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelComp) a c := by
  exact Telltale.Protocol.Projection.Project.EQ2_CProjectTransRel_compose_through_mu
    heq hrel hWFa hWFc


end Telltale.Protocol.Projection.ProjectPaco
