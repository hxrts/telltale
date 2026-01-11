import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.Duality
import RumpsteakV2.Protocol.CoTypes.Substitute
import RumpsteakV2.Protocol.LocalTypeR

/-! # RumpsteakV2.Protocol.CoTypes.Quotient

Quotient of local types by EQ2.

## Expose

The following definitions form the semantic interface for proofs:

- `QLocalTypeR`: quotient type for local types
- `QLocalTypeR.ofLocal`: inject local type into quotient
- `QLocalTypeR.unfold`: lifted unfold operation
- `QLocalTypeR.substitute`: lifted substitution
- `QLocalTypeR.dual`: lifted duality
- `EQ2_dual`: duality respects EQ2

## Imports from Substitute Module

The following are imported from `RumpsteakV2.Protocol.CoTypes.Substitute`:

- `EQ2_substitute`: substitution respects EQ2
- `unfold_substitute_EQ2`: unfold/substitute confluence
-/

namespace RumpsteakV2.Protocol.CoTypes.Quotient

open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.Substitute
open RumpsteakV2.Protocol.GlobalType
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

/-! ## Substitution Congruence -/

-- EQ2_substitute is imported from RumpsteakV2.Protocol.CoTypes.Substitute
-- See that module for detailed documentation of the proof strategy.

/-- Substitute on the quotient (well-defined by EQ2_substitute). -/
def QLocalTypeR.substitute (q : QLocalTypeR) (var : String) (repl : LocalTypeR) : QLocalTypeR :=
  Quot.map (fun t => t.substitute var repl) (by
    intro a b h
    exact EQ2_substitute a b var repl h) q

/-- Substitution agrees with representatives. -/
theorem QLocalTypeR.substitute_ofLocal (t : LocalTypeR) (var : String) (repl : LocalTypeR) :
    QLocalTypeR.substitute (QLocalTypeR.ofLocal t) var repl =
      QLocalTypeR.ofLocal (t.substitute var repl) := by
  rfl

/-! ## Duality Congruence -/

-- EQ2_dual is proved in CoTypes.Duality; we re-export a local alias here.
/-- Duality respects EQ2: if two types are EQ2-equivalent, their duals
    are also EQ2-equivalent. -/
theorem EQ2_dual (a b : LocalTypeR)
    (h : EQ2 a b) : EQ2 a.dual b.dual := by
  simpa using (RumpsteakV2.Protocol.CoTypes.EQ2.EQ2_dual h)

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

-- unfold_substitute_EQ2 is imported from RumpsteakV2.Protocol.CoTypes.Substitute
-- See that module for detailed documentation of the proof strategy and
-- its circular dependency with EQ2_substitute.

/-- Unfold commutes with substitute (on quotient). -/
theorem QLocalTypeR.unfold_substitute (q : QLocalTypeR) (var : String) (repl : LocalTypeR) :
    (q.substitute var repl).unfold = (q.unfold).substitute var repl := by
  induction q using Quot.ind with
  | mk t =>
      show QLocalTypeR.ofLocal _ = QLocalTypeR.ofLocal _
      apply QLocalTypeR.eq_of_EQ2
      exact unfold_substitute_EQ2 t var repl

/-- Dual is an involution (on quotient). -/
theorem QLocalTypeR.dual_dual (q : QLocalTypeR) :
    q.dual.dual = q := by
  induction q using Quot.ind with
  | mk t =>
      show QLocalTypeR.ofLocal _ = QLocalTypeR.ofLocal _
      rw [t.dual_dual]

end RumpsteakV2.Protocol.CoTypes.Quotient
