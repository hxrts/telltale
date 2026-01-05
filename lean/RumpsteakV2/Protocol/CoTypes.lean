import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.Quotient

/-! # RumpsteakV2.Protocol.CoTypes

Coinductive types and quotients for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `EQ2`
- `QLocalTypeR`
- `QLocalTypeR.unfold`
-/

namespace RumpsteakV2.Protocol.CoTypes

export RumpsteakV2.Protocol.CoTypes.EQ2 (EQ2)
export RumpsteakV2.Protocol.CoTypes.Quotient (QLocalTypeR QLocalTypeR.unfold)

end RumpsteakV2.Protocol.CoTypes
