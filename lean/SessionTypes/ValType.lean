/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Value Types for Session Types

Shared `ValType` definition used by both `LocalTypeR` (theory) and `LocalType` (runtime).
Represents the types of values carried in messages.
-/

namespace SessionTypes

/-- Value types for message payloads in session types.

- `unit`, `bool`, `nat`, `string`: base types
- `prod`: pair types
- `chan`: channel endpoint type (session id × role)
-/
inductive ValType where
  | unit : ValType
  | bool : ValType
  | nat : ValType
  | string : ValType
  | prod : ValType → ValType → ValType
  | chan : Nat → String → ValType  -- (session id, role)
  deriving Repr, DecidableEq, BEq, Inhabited

namespace ValType

/-- A value type is linear if it represents a channel endpoint. -/
def isLinear : ValType → Bool
  | .chan _ _ => true
  | _ => false

end ValType

end SessionTypes
