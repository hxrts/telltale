/-
Copyright (c) 2025 Telltale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Basic

/-!
# MPST Local Types

Local types describe the communication protocol from a single participant's
perspective. Unlike binary session types, actions are directed to/from
specific roles.

- `!r(T).L` - send value of type T to role r, continue as L
- `?r(T).L` - receive value of type T from role r, continue as L
- `⊕r{ℓᵢ: Lᵢ}` - select: send label ℓᵢ to role r, continue as Lᵢ
- `&r{ℓᵢ: Lᵢ}` - branch: receive label from role r, branch on it
- `end` - session terminated
- `μX.L` / `X` - recursive types (via fuel/unfolding)
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-- Value types for MPST (same as binary, but with LocalType for channels). -/
inductive ValType where
  | unit : ValType
  | bool : ValType
  | nat : ValType
  | string : ValType
  | prod : ValType → ValType → ValType
  | chan : SessionId → Role → ValType  -- channel endpoint for (sid, role)
  deriving Repr, DecidableEq

namespace ValType

/-- A value type is linear if it represents a channel endpoint. -/
def isLinear : ValType → Bool
  | .chan _ _ => true
  | _ => false

end ValType

/-- Local types for multiparty session types.

Each action is directed to/from a specific role:
- `send r T L`: send value of type T to role r, continue as L
- `recv r T L`: receive value of type T from role r, continue as L
- `select r bs`: select one of the branches to send to role r
- `branch r bs`: receive a label from role r and branch
- `end_`: terminated session
- `var n`: type variable for recursion (de Bruijn index)
- `mu L`: recursive type μX.L

Note: Using simple List (Label × LocalType) for branches. DecidableEq is
not automatically derivable due to the nested inductive structure.
-/
inductive LocalType where
  | send : Role → ValType → LocalType → LocalType
  | recv : Role → ValType → LocalType → LocalType
  | select : Role → List (Label × LocalType) → LocalType
  | branch : Role → List (Label × LocalType) → LocalType
  | end_ : LocalType
  | var : Nat → LocalType
  | mu : LocalType → LocalType
  deriving Repr

/-- A branch is a labeled continuation: (label, local type). -/
abbrev Branch := Label × LocalType

namespace LocalType

/-- Check if a local type is terminated. -/
def isEnd : LocalType → Bool
  | .end_ => true
  | _ => false

/-- Get the target role of the first action, if any. -/
def targetRole? : LocalType → Option Role
  | .send r _ _ => some r
  | .recv r _ _ => some r
  | .select r _ => some r
  | .branch r _ => some r
  | _ => none

/-- Substitute a type for variable n (structural recursion on continuation). -/
def subst (n : Nat) (replacement : LocalType) : LocalType → LocalType
  | .send r T L => .send r T (subst n replacement L)
  | .recv r T L => .recv r T (subst n replacement L)
  | .select r bs => .select r bs  -- simplified: doesn't descend into branches
  | .branch r bs => .branch r bs  -- simplified: doesn't descend into branches
  | .end_ => .end_
  | .var m => if m = n then replacement else .var m
  | .mu L => .mu (subst (n + 1) replacement L)

/-- Unfold a recursive type one level.
    For μ X. L, unfold gives L[μ X. L / X], i.e., substitute var 0 with the whole μ-type.
    NOTE: We use explicit function application since dot notation puts the receiver
    in the replacement position, not the type-to-substitute-in position. -/
def unfold : LocalType → LocalType
  | .mu L => LocalType.subst 0 (.mu L) L
  | L => L

/-- Check if a local type expects to send to role r next. -/
def canSendTo (r : Role) : LocalType → Bool
  | .send r' _ _ => r == r'
  | .select r' _ => r == r'
  | .mu L => L.canSendTo r
  | _ => false

/-- Check if a local type expects to receive from role r next. -/
def canRecvFrom (r : Role) : LocalType → Bool
  | .recv r' _ _ => r == r'
  | .branch r' _ => r == r'
  | .mu L => L.canRecvFrom r
  | _ => false

/-- Advance a send type after sending. -/
def advanceSend (r : Role) (T : ValType) : LocalType → Option LocalType
  | .send r' T' L => if r == r' && T == T' then some L else none
  | _ => none

/-- Advance a recv type after receiving. -/
def advanceRecv (r : Role) (T : ValType) : LocalType → Option LocalType
  | .recv r' T' L => if r == r' && T == T' then some L else none
  | _ => none

/-- Advance a select type after selecting a label. -/
def advanceSelect (r : Role) (ℓ : Label) : LocalType → Option LocalType
  | .select r' bs =>
    if r == r' then
      bs.find? (fun b => b.1 == ℓ) |>.map (·.2)
    else none
  | _ => none

/-- Advance a branch type after receiving a label. -/
def advanceBranch (r : Role) (ℓ : Label) : LocalType → Option LocalType
  | .branch r' bs =>
    if r == r' then
      bs.find? (fun b => b.1 == ℓ) |>.map (·.2)
    else none
  | _ => none

end LocalType

/-- Shorthand constructors -/
abbrev LocalType.send' (r : Role) (T : ValType) (L : LocalType) := LocalType.send r T L
abbrev LocalType.recv' (r : Role) (T : ValType) (L : LocalType) := LocalType.recv r T L

end
