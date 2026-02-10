/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Protocol.Basic

/-!
# MPST Local Types

Local types describe the communication protocol from a single participant's
perspective. Unlike binary session types, actions are directed to/from
specific roles.
-/

/-
The Problem. We need a representation of local session types that supports
directed communication (to/from specific roles), recursion, and value/channel
types. The representation must support decidable equality and efficient matching.

Solution Structure. We define:
1. `ValType`: value types including channel endpoints
2. `LocalType`: the local type grammar with send/recv/select/branch/mu/end
3. Helper functions for branch lookup, unfolding, and type traversal
The key insight is that actions are directed to specific roles, not just "dual".
-/

/-!
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

section

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

/-! ## Depth Measure for Weighted Liveness

The depth of a local type counts the maximum number of communication
actions to termination. This is used in the weighted liveness measure:

  W = 2 * Σ depth(L) + Σ buffer_size(e)

Key property: each communication action decreases depth by at least 1,
so send decreases W by 2*1 - 1 = 1 (buffer grows), recv by 2*1 + 1 = 3
(buffer shrinks), select by 1, branch by 3.
-/

mutual
  /-- Depth of a local type: maximum communication actions to termination.
      Uses `max` for branches since only one continuation is taken. -/
  def LocalType.depth : LocalType → Nat
    | .send _ _ L => 1 + L.depth
    | .recv _ _ L => 1 + L.depth
    | .select _ bs => 1 + LocalType.depthList bs
    | .branch _ bs => 1 + LocalType.depthList bs
    | .end_ => 0
    | .var _ => 0
    | .mu L => L.depth

  /-- Maximum depth across branch continuations. -/
  def LocalType.depthList : List (Label × LocalType) → Nat
    | [] => 0
    | (_, L) :: rest => max L.depth (LocalType.depthList rest)
end

namespace LocalType

/-! ### Depth Properties -/

@[simp] theorem depth_end : LocalType.depth .end_ = 0 := rfl
@[simp] theorem depth_var (n : Nat) : (LocalType.var n).depth = 0 := rfl

theorem depth_send_pos (r : Role) (T : ValType) (L : LocalType) :
    0 < (LocalType.send r T L).depth := by
  simp [LocalType.depth]

theorem depth_recv_pos (r : Role) (T : ValType) (L : LocalType) :
    0 < (LocalType.recv r T L).depth := by
  simp [LocalType.depth]

theorem depth_select_pos (r : Role) (bs : List (Label × LocalType)) :
    0 < (LocalType.select r bs).depth := by
  simp [LocalType.depth]

theorem depth_branch_pos (r : Role) (bs : List (Label × LocalType)) :
    0 < (LocalType.branch r bs).depth := by
  simp [LocalType.depth]

/-- Advancing through send decreases depth. -/
theorem depth_advance_send (r : Role) (T : ValType) (L : LocalType) :
    L.depth < (LocalType.send r T L).depth := by
  show L.depth < 1 + L.depth
  omega

/-- Advancing through recv decreases depth. -/
theorem depth_advance_recv (r : Role) (T : ValType) (L : LocalType) :
    L.depth < (LocalType.recv r T L).depth := by
  show L.depth < 1 + L.depth
  omega

/-- A branch continuation has depth at most the depthList. -/
theorem depthList_mem_le (ℓ : Label) (L : LocalType) (bs : List (Label × LocalType))
    (h : (ℓ, L) ∈ bs) :
    L.depth ≤ LocalType.depthList bs := by
  induction bs with
  | nil => cases h
  | cons hd tl ih =>
    obtain ⟨ℓ', L'⟩ := hd
    simp only [LocalType.depthList]
    rcases List.mem_cons.mp h with heq | hmem
    · have hL : L = L' := congrArg Prod.snd heq
      rw [hL]
      exact Nat.le_max_left _ _
    · have htl := ih hmem
      exact Nat.le_trans htl (Nat.le_max_right _ _)

/-- Selecting a branch strictly decreases depth. -/
theorem depth_advance_select (r : Role) (bs : List (Label × LocalType))
    (ℓ : Label) (L : LocalType) (h : (ℓ, L) ∈ bs) :
    L.depth < (LocalType.select r bs).depth := by
  show L.depth < 1 + LocalType.depthList bs
  have := depthList_mem_le ℓ L bs h
  omega

/-- Branching strictly decreases depth. -/
theorem depth_advance_branch (r : Role) (bs : List (Label × LocalType))
    (ℓ : Label) (L : LocalType) (h : (ℓ, L) ∈ bs) :
    L.depth < (LocalType.branch r bs).depth := by
  show L.depth < 1 + LocalType.depthList bs
  have := depthList_mem_le ℓ L bs h
  omega

end LocalType

/-- Shorthand constructors -/
abbrev LocalType.send' (r : Role) (T : ValType) (L : LocalType) := LocalType.send r T L
abbrev LocalType.recv' (r : Role) (T : ValType) (L : LocalType) := LocalType.recv r T L

end
