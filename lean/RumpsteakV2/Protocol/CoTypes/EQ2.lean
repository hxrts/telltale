import RumpsteakV2.Protocol.CoTypes.EQ2.Core
import RumpsteakV2.Protocol.CoTypes.EQ2.TransBase

/-! # RumpsteakV2.Protocol.CoTypes.EQ2

Coinductive equality (EQ2) for local types.

## Expose

The following definitions form the semantic interface for proofs:

- `EQ2`: coinductive equality (greatest fixed point of EQ2F)
- `EQ2_refl`: reflexivity of EQ2
- `EQ2_symm`: symmetry of EQ2
- `EQ2_trans_wf`: transitivity of EQ2 (via Bisim, in EQ2Props.lean)
- `EQ2_equiv`: equivalence relation instance
- `EQ2_trans_via_end` / `EQ2_trans_via_var`: constructor-based transitivity helpers
- `EQ2_unfold_left`: left unfolding preserves EQ2
- `EQ2_unfold_right`: right unfolding preserves EQ2
- `EQ2_unfold`: bilateral unfolding preserves EQ2
- `EQ2_coind`: coinduction principle
-/
