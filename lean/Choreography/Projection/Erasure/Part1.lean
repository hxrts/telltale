import SessionTypes.LocalTypeR

/-! # Choreography.Projection.Erasure.Part1

Erasure-based mergeability for local types.

## Expose

- `lookupBranch`: lookup a label in a branch list
- `labelIn`: label presence predicate for branch lists
- `sameLabels` / `unionLabels`: label-set predicates
- `Erases`: erasure relation (a common lower bound for two local types)
- `Erasable`: existence of an erasure witness
-/

namespace Choreography.Projection.Erasure

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

/-- Lookup a label in a branch list (first match). -/
def lookupBranch (lbl : Label) : List (Label × LocalTypeR) → Option LocalTypeR
  | [] => none
  | (l, t) :: rest => if l = lbl then some t else lookupBranch lbl rest

/-- Label presence predicate for a branch list. -/
def labelIn (lbl : Label) (branches : List (Label × LocalTypeR)) : Prop :=
  (lookupBranch lbl branches).isSome

/-- Two branch lists have the same set of labels. -/
def sameLabels (bs1 bs2 : List (Label × LocalTypeR)) : Prop :=
  ∀ lbl, labelIn lbl bs1 ↔ labelIn lbl bs2

/-- A branch list carries exactly the union of labels from two inputs. -/
def unionLabels (bs1 bs2 bs : List (Label × LocalTypeR)) : Prop :=
  ∀ lbl, labelIn lbl bs ↔ (labelIn lbl bs1 ∨ labelIn lbl bs2)

/-- Erasure relation: `Erases a b c` means `c` is a common lower bound of `a` and `b`.

Intuition:
- Sends must have identical labels and erase branch continuations pairwise.
- Receives may merge branches by taking the union of labels, erasing only where both sides define it.

Note: This relation is intended to be used under the usual invariant that branch labels are unique.
-/
inductive Erases : LocalTypeR → LocalTypeR → LocalTypeR → Prop where
  | end : Erases .end .end .end
  | var (v : String) : Erases (.var v) (.var v) (.var v)
  | mu (v : String) {a b c : LocalTypeR} :
      Erases a b c → Erases (.mu v a) (.mu v b) (.mu v c)
  | send {p : String} {bs1 bs2 bs : List (Label × LocalTypeR)} :
      sameLabels bs1 bs2 →
      sameLabels bs1 bs →
      (∀ lbl t1 t2 t,
        lookupBranch lbl bs1 = some t1 →
        lookupBranch lbl bs2 = some t2 →
        lookupBranch lbl bs = some t →
        Erases t1 t2 t) →
      Erases (.send p bs1) (.send p bs2) (.send p bs)
  | recv {p : String} {bs1 bs2 bs : List (Label × LocalTypeR)} :
      (∀ lbl t1 t2 t,
        lookupBranch lbl bs1 = some t1 →
        lookupBranch lbl bs2 = some t2 →
        lookupBranch lbl bs = some t →
        Erases t1 t2 t) →
      (∀ lbl t1,
        lookupBranch lbl bs1 = some t1 →
        lookupBranch lbl bs2 = none →
        lookupBranch lbl bs = some t1) →
      (∀ lbl t2,
        lookupBranch lbl bs1 = none →
        lookupBranch lbl bs2 = some t2 →
        lookupBranch lbl bs = some t2) →
      Erases (.recv p bs1) (.recv p bs2) (.recv p bs)

/-- Two local types are erasable if they have a common erasure. -/
def Erasable (a b : LocalTypeR) : Prop :=
  ∃ c, Erases a b c

end Choreography.Projection.Erasure
