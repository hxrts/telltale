import SessionTypes.GlobalType.Core
import SessionTypes.ValType

/-! # SessionTypes.GlobalType.ValType

Bridge from payload sorts to local value types.
-/

namespace SessionTypes.GlobalType

open SessionTypes (ValType)

/-- Optional embedding of payload sorts into local value types.

`none` represents payloads that are not tracked (or not representable) at the local type level. -/
def PayloadSort.toValType? : PayloadSort → Option ValType
  | .unit => none
  | .nat => some .nat
  | .bool => some .bool
  | .string => some .string
  | .real => none
  | .vector _ => none
  | .prod a b =>
      match PayloadSort.toValType? a, PayloadSort.toValType? b with
      | some va, some vb => some (.prod va vb)
      | _, _ => none

theorem PayloadSort.toValType?_ne_chan (s : PayloadSort) (sid : Nat) (r : String) :
    PayloadSort.toValType? s ≠ some (.chan sid r) := by
  induction s with
  | unit | nat | bool | string | real | vector _ =>
      simp [PayloadSort.toValType?]
  | prod a b ih_a ih_b =>
      cases h1 : PayloadSort.toValType? a <;> cases h2 : PayloadSort.toValType? b <;>
        simp [PayloadSort.toValType?, h1, h2]

end SessionTypes.GlobalType
