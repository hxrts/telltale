import Telltale.Protocol.CoTypes.EQ2
import Telltale.Protocol.CoTypes.EQ2Props
import Telltale.Protocol.CoTypes.Bisim
import Telltale.Protocol.CoTypes.Quotient

/-! # Telltale.Protocol.CoTypes

Coinductive types and quotients.

## Expose

The following definitions form the semantic interface for proofs:

- `EQ2`
- `QLocalTypeR`
- `QLocalTypeR.unfold`
-/

namespace Telltale.Protocol.CoTypes

export Telltale.Protocol.CoTypes.EQ2 (EQ2)
export Telltale.Protocol.CoTypes.EQ2Props (EQ2_trans_wf)
export Telltale.Protocol.CoTypes.Bisim (
  EQ2_transfer_observable
  EQ2_iff_observable_correspond
  ObservableRel.toEQ2
  ObservableRel.refl
  ObservableRel.symm
)
export Telltale.Protocol.CoTypes.Quotient (QLocalTypeR QLocalTypeR.unfold)

end Telltale.Protocol.CoTypes
