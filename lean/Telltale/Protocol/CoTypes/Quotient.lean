import Telltale.Protocol.CoTypes.EQ2
import Telltale.Protocol.CoTypes.Dual
import Telltale.Protocol.CoTypes.Substitute
import Telltale.Protocol.LocalTypeR

/-! # Telltale.Protocol.CoTypes.Quotient

Quotient of local types by EQ2.

## Expose

The following definitions form the semantic interface for proofs:

- `QLocalTypeR`: quotient type for local types
- `QLocalTypeR.ofLocal`: inject local type into quotient
- `QLocalTypeR.unfold`: lifted unfold operation
- `QLocalTypeR.dual`: lifted duality
- `EQ2_dual`: duality respects EQ2

## Imports from Substitute Module

The following are imported from `Telltale.Protocol.CoTypes.Substitute`:

- `EQ2_substitute`: substitution respects EQ2
- `unfold_substitute_EQ2`: unfold/substitute confluence
-/

namespace Telltale.Protocol.CoTypes.Quotient

open Telltale.Protocol.CoTypes.EQ2
open Telltale.Protocol.CoTypes.Substitute
open Telltale.Protocol.GlobalType
open Telltale.Protocol.LocalTypeR

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

/-! ## Substitution Congruence (Deferred)

Substitution on the quotient is deferred because the current EQ2_substitute proof
requires Barendregt side conditions (notBoundAt + repl closed).
-/

/-! ## Duality Congruence -/

-- EQ2_dual is proved in CoTypes.Dual; we re-export a local alias here.
/-- Duality respects EQ2: if two types are EQ2-equivalent, their duals
    are also EQ2-equivalent. -/
theorem EQ2_dual (a b : LocalTypeR)
    (h : EQ2 a b) : EQ2 a.dual b.dual := by
  simpa using (Telltale.Protocol.CoTypes.EQ2.EQ2_dual h)

/-- Dual on the quotient (well-defined by EQ2_dual). -/
def QLocalTypeR.dual : QLocalTypeR → QLocalTypeR :=
  Quot.map LocalTypeR.dual (by
    intro a b h
    exact EQ2_dual a b h)

/-- Duality agrees with representatives. -/
theorem QLocalTypeR.dual_ofLocal (t : LocalTypeR) :
    QLocalTypeR.dual (QLocalTypeR.ofLocal t) =
      QLocalTypeR.ofLocal t.dual := by
  rfl

/-! ## Rewriting Lemmas -/

/-- Quotient equality from EQ2. -/
theorem QLocalTypeR.eq_of_EQ2 {a b : LocalTypeR} (h : EQ2 a b) :
    QLocalTypeR.ofLocal a = QLocalTypeR.ofLocal b :=
  Quot.sound h

/-- Quotient induction principle. -/
theorem QLocalTypeR.ind {P : QLocalTypeR → Prop}
    (h : ∀ t, P (QLocalTypeR.ofLocal t)) : ∀ q, P q :=
  Quot.ind h

/-- Lift a predicate that respects EQ2 to the quotient. -/
def QLocalTypeR.liftProp (P : LocalTypeR → Prop)
    (hresp : ∀ a b, EQ2 a b → (P a ↔ P b)) : QLocalTypeR → Prop :=
  Quot.lift P (by
    intro a b h
    exact propext (hresp a b h))

-- unfold_substitute_EQ2 is imported from Telltale.Protocol.CoTypes.Substitute.
-- See that module for detailed documentation of the proof strategy.

/-- Dual is an involution (on quotient). -/
theorem QLocalTypeR.dual_dual (q : QLocalTypeR) :
    q.dual.dual = q := by
  induction q using Quot.ind with
  | mk t =>
      show QLocalTypeR.ofLocal _ = QLocalTypeR.ofLocal _
      rw [t.dual_dual]

end Telltale.Protocol.CoTypes.Quotient
