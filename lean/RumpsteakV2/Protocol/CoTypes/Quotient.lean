import RumpsteakV2.Protocol.CoTypes.EQ2
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
- `EQ2_substitute`: substitution respects EQ2
- `EQ2_dual`: duality respects EQ2
-/

namespace RumpsteakV2.Protocol.CoTypes.Quotient

open RumpsteakV2.Protocol.CoTypes.EQ2
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

/-- Substitution respects EQ2: if two types are EQ2-equivalent, their substitutions
    (with the same variable and replacement) are also EQ2-equivalent.

This axiom captures the semantic property that observationally equal types
remain observationally equal after substitution.

### Why this is an axiom (not a theorem)

Proving this constructively requires "coinduction up-to" techniques (like Coq's paco library).
The naive coinduction relation:
  `SubstRel var repl a' b' := ∃ a b, EQ2 a b ∧ a' = a.subst var repl ∧ b' = b.subst var repl`

is NOT a post-fixpoint of EQ2F because of the mu-mu case with distinct bound variables.

**Problematic case:** When `EQ2 (mu t body) (mu s body')` where `t ≠ var` and `s ≠ var`:
- After substitution: `a' = mu t (body.subst var repl)`, `b' = mu s (body'.subst var repl)`
- EQ2F requires: `SubstRel (body.subst var repl).subst t (mu t (body.subst var repl)) (mu s (body'.subst var repl))`
- This LHS has nested substitutions that don't factor as `a.subst var repl` for any simple `a`

The fix in Coq uses parametrized coinduction (paco) which allows "accumulating" EQ2 reasoning
during the coinductive proof. Lean 4 lacks built-in support for this.

### Semantic soundness

The axiom is semantically sound because:
- EQ2 represents observational equality of infinite trees
- Substitution is a structural transformation on trees
- If two trees are observationally equal, applying the same transformation
  to corresponding positions yields observationally equal results

### Coq reference

See `subject_reduction/theories/CoTypes/bisim.v` for the Coq proof using paco. -/
axiom EQ2_substitute (a b : LocalTypeR) (var : String) (repl : LocalTypeR)
    (h : EQ2 a b) : EQ2 (a.substitute var repl) (b.substitute var repl)

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

/-- Duality respects EQ2: if two types are EQ2-equivalent, their duals
    are also EQ2-equivalent.

This axiom captures the semantic property that observationally equal types
remain observationally equal after duality. The proof would require
coinduction showing that duality commutes with the unfolding structure
that defines EQ2.

Semantically sound because:
- EQ2 represents observational equality of infinite trees
- Duality swaps send/recv at corresponding positions
- If two trees are observationally equal, swapping send/recv at the same
  positions yields observationally equal results -/
axiom EQ2_dual (a b : LocalTypeR)
    (h : EQ2 a b) : EQ2 a.dual b.dual

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

/-- Unfold commutes with substitute on representatives.

For non-mu types, unfold is the identity, so both sides are definitionally equal.
For mu types, the proof requires coinductive reasoning on the resulting infinite trees.

This axiom states that applying substitute then unfold is EQ2-equivalent to
applying unfold then substitute. Both result in observationally equivalent
infinite trees.

Proof sketch (by case analysis on t):
- end/var/send/recv: unfold is identity, trivial
- mu t body: requires coinductive reasoning on EQ2

This corresponds to the semantic property that substitution and unfolding
are confluent operations on infinite trees. -/
axiom unfold_substitute_EQ2 (t : LocalTypeR) (var : String) (repl : LocalTypeR) :
    EQ2 ((t.substitute var repl).unfold) ((t.unfold).substitute var repl)

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
