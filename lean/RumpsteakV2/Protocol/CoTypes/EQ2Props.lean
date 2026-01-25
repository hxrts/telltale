import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.Bisim

/-! # EQ2 Properties via Bisim

This module provides EQ2 lemmas that are provable via the Bisim development,
avoiding the EQ2.lean detours at the cost of explicit WellFormed hypotheses.
-/

namespace RumpsteakV2.Protocol.CoTypes.EQ2Props

open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.Bisim
open RumpsteakV2.Protocol.LocalTypeR

/-- EQ2 transitivity via Bisim (requires WellFormed witnesses). -/
theorem EQ2_trans_wf {a b c : LocalTypeR}
    (hab : EQ2 a b) (hbc : EQ2 b c)
    (hWFa : LocalTypeR.WellFormed a)
    (hWFb : LocalTypeR.WellFormed b)
    (hWFc : LocalTypeR.WellFormed c) : EQ2 a c :=
  EQ2_trans_via_Bisim hab hbc hWFa hWFb hWFc

end RumpsteakV2.Protocol.CoTypes.EQ2Props
