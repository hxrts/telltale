import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.EQ2Props
import RumpsteakV2.Protocol.CoTypes.Bisim
import RumpsteakV2.Protocol.CoTypes.Quotient

/-! # RumpsteakV2.Protocol.CoTypes

Coinductive types and quotients.

## Expose

The following definitions form the semantic interface for proofs:

- `EQ2`
- `QLocalTypeR`
- `QLocalTypeR.unfold`
-/

namespace RumpsteakV2.Protocol.CoTypes

export RumpsteakV2.Protocol.CoTypes.EQ2 (EQ2)
export RumpsteakV2.Protocol.CoTypes.EQ2Props (EQ2_trans_wf)
export RumpsteakV2.Protocol.CoTypes.Bisim (
  EQ2_transfer_observable
  EQ2_iff_observable_correspond
  ObservableRel.toEQ2
  ObservableRel.refl
  ObservableRel.symm
)
export RumpsteakV2.Protocol.CoTypes.Quotient (QLocalTypeR QLocalTypeR.unfold)

end RumpsteakV2.Protocol.CoTypes
