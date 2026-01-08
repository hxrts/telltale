import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.Projection.Project

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

namespace RumpsteakV2.Protocol.Projection.ProjectPaco

open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Project

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
    (hrel : CProjectTransRel (.mu v body) c) :
    EQ2F (EQ2_closure CProjectTransRelComp) a c := by

  -- Get EQ2F structure from CProjectTransRel_postfix
  have hrel_f : EQ2F (EQ2_closure CProjectTransRel) (.mu v body) c :=
    CProjectTransRel_postfix (.mu v body) c hrel

  -- Monotonicity: EQ2_closure CProjectTransRel ⊆ EQ2_closure CProjectTransRelComp
  -- because CProjectTransRel is the base case of CProjectTransRelComp
  have h_mono : ∀ x y, (EQ2_closure CProjectTransRel) x y →
                       (EQ2_closure CProjectTransRelComp) x y := by
    intro x y h
    simp only [EQ2_closure] at h ⊢
    cases h with
    | inl hrel' =>
        left
        left -- CProjectTransRel is the base case of CProjectTransRelComp
        exact hrel'
    | inr heq' =>
        right
        exact heq'

  -- Apply EQ2F monotonicity
  exact EQ2F.mono h_mono _ _ hrel_f

end RumpsteakV2.Protocol.Projection.ProjectPaco
