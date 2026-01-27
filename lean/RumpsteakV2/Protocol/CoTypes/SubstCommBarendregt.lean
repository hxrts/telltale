import RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt.Predicates
import RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt.General
import RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt.SubstRel
import RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt.Main

/-! # SubstCommBarendregt: EQ2_substitute under Barendregt Convention

This module proves `EQ2_substitute_barendregt`, showing that EQ2 is preserved under
substitution when the Barendregt convention holds.

## Approach: Inductive SubstRel Closed Under Unfolding

The key insight is to define `SubstRel` as an inductive relation closed under unfolding,
then use a `flatten` lemma to reduce any witness to base form.
-/
