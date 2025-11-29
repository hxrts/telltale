-- Computes and reasons about per-role projections of a choreography.
import Rumpsteak.Choreography

/-! Projection logic abstracts the per-role local types that Lean verifies
    against exported choreography traces. -/

namespace Rumpsteak.Projection

open Rumpsteak  /- Re-use the Choreography helpers above. -/

/- LocalKind models the send/receive direction of each projected action. -/
inductive LocalKind
| send
| recv
deriving Inhabited, Repr, DecidableEq, BEq

/- LocalAction holds the basic triple seen by each role (kind, peer, label). -/
structure LocalAction where
  kind : LocalKind
  partner : String
  label : String
deriving Inhabited, Repr, DecidableEq, BEq

/- LocalType is a sequence of the role's actions after projection. -/
structure LocalType where
  actions : List LocalAction
deriving Inhabited, Repr, BEq

/- swap flips send ↔ recv. -/
def LocalKind.swap : LocalKind → LocalKind
  | LocalKind.send => LocalKind.recv
  | LocalKind.recv => LocalKind.send

/- Double-swap returns original kind. -/
theorem LocalKind.swapSwap (kind : LocalKind) : kind.swap.swap = kind := by
  cases kind <;> simp [LocalKind.swap]

/- Dualizing an action flips the kind but keeps metadata. -/
def LocalAction.dual (action : LocalAction) : LocalAction :=
  ⟨action.kind.swap, action.partner, action.label⟩

/- Double-dual yields the same action. -/
theorem LocalAction.dualDual (action : LocalAction) :
    LocalAction.dual (LocalAction.dual action) = action := by
  let ⟨kind, partner, label⟩ := action
  have swap_swap := LocalKind.swapSwap kind
  simp [LocalAction.dual]
  simp [swap_swap]

/- Dualize every action in the local type. -/
def LocalType.dual (lt : LocalType) : LocalType :=
  { actions := lt.actions.map LocalAction.dual }

theorem list_map_congr {α β : Type} {f g : α → β} (h : ∀ x, f x = g x) :
    ∀ xs : List α, xs.map f = xs.map g := by
  intro xs
  induction xs
  case nil => simp [List.map]
  case cons x xs ih =>
    simp [List.map, h x, ih]

/- Shows dual(dual(lt)) returns lt. -/
theorem LocalType.dualDual (lt : LocalType) : LocalType.dual (LocalType.dual lt) = lt := by
  let eq_actions : List.map (LocalAction.dual ∘ LocalAction.dual) lt.actions = lt.actions := by
    induction lt.actions
    case nil => simp
    case cons hd tl ih =>
      simp [List.map, LocalAction.dualDual hd, ih]
  simp [LocalType.dual]
  exact congrArg LocalType.mk eq_actions

/- Creates the local action that this role sees in the flat export. -/
def LocalAction.fromGlobal (act : Action) (roleName : String) : Option LocalAction :=
  match act with
  | ⟨origin, destination, label⟩ =>
    if origin == roleName then
      some { kind := LocalKind.send, partner := destination, label }
    else if destination == roleName then
      some { kind := LocalKind.recv, partner := origin, label }
    else
      none

/- Build the role’s local type by filtering the choreography trace. -/
def project (ch : Choreography) (role : Role) : LocalType :=
  -- Keep only the actions where this role participates.
  { actions := ch.actions.filterMap fun act => LocalAction.fromGlobal act role.name }

/- Extract labels from a local type; used in trace comparisons. -/
def labels (lt : LocalType) : List String :=
  lt.actions.map (·.label)

def subLabelsOf (lt : LocalType) (sup : LocalType) : Bool :=
  -- Every action in lt must appear somewhere in sup.
  lt.actions.all fun action => sup.actions.any fun b => decide (b = action)

/-- Helper: every element of a list is witnessed by `any` on the same list. -/
theorem all_any_self {α} [DecidableEq α] (xs : List α) :
    xs.all (fun a => xs.any fun b => decide (b = a)) = true := by
  simp [List.all_eq_true, List.any_eq_true]


/- Compare actual actions to an expected sequence. -/
def matchesActionTrace (lt : LocalType) (expected : List LocalAction) : Bool :=
  lt.actions == expected

/-- Reflexivity: every local type is a sublabel of itself. -/
theorem subLabelsOf_refl (lt : LocalType) : subLabelsOf lt lt = true := by
  unfold subLabelsOf
  simp [all_any_self]

def traceForRole (ch : Choreography) (roleName : String) : LocalType :=
  let role := findRole ch roleName
  match role with
  | some r => project ch r
  | none => { actions := [] }

 end Rumpsteak.Projection
