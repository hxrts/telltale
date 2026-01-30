import SessionCoTypes.EQ2
import SessionCoTypes.Bisim

/-! # EQ2 Properties via Bisim

This module provides EQ2 lemmas that are provable via the Bisim development,
avoiding the EQ2.lean detours at the cost of explicit LocalTypeR.WellFormed hypotheses.
-/

namespace SessionCoTypes.EQ2Props

open SessionCoTypes.EQ2
open SessionCoTypes.Bisim
open SessionTypes.LocalTypeR

/-- EQ2 transitivity via Bisim (requires LocalTypeR.WellFormed witnesses). -/
theorem EQ2_trans_wf {a b c : LocalTypeR}
    (hab : EQ2 a b) (hbc : EQ2 b c)
    (hWFa : LocalTypeR.WellFormed a)
    (hWFb : LocalTypeR.WellFormed b)
    (hWFc : LocalTypeR.WellFormed c) : EQ2 a c :=
  EQ2_trans_via_Bisim hab hbc hWFa hWFb hWFc

end SessionCoTypes.EQ2Props
