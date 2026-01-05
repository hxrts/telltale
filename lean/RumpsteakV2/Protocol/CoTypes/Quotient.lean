import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.LocalTypeR

/-! # RumpsteakV2.Protocol.CoTypes.Quotient

Quotient of local types by EQ2.

## Expose

The following definitions form the semantic interface for proofs:

- `QLocalTypeR`
-/

namespace RumpsteakV2.Protocol.CoTypes.Quotient

open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.LocalTypeR

/-- Quotient of local types by EQ2. -/
abbrev QLocalTypeR : Type := Quot EQ2

/-- Inject a local type into the quotient. -/
def QLocalTypeR.ofLocal (t : LocalTypeR) : QLocalTypeR :=
  Quot.mk _ t

/-- Unfold on the quotient (well-defined by EQ2). -/
def QLocalTypeR.unfold : QLocalTypeR → QLocalTypeR :=
  Quot.map LocalTypeR.unfold (by
    intro a b h
    exact EQ2_unfold h)

/-- Unfolding agrees with representatives. -/
theorem QLocalTypeR.unfold_ofLocal (t : LocalTypeR) :
    QLocalTypeR.unfold (QLocalTypeR.ofLocal t) =
      QLocalTypeR.ofLocal (LocalTypeR.unfold t) := by
  rfl

end RumpsteakV2.Protocol.CoTypes.Quotient
