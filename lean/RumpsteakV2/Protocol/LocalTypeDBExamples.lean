import RumpsteakV2.Protocol.LocalTypeDB
import RumpsteakV2.Protocol.LocalTypeConv
import RumpsteakV2.Protocol.LocalTypeRDBBridge

/-! # Examples: Using De Bruijn Proofs

This file demonstrates how to use the de Bruijn infrastructure for proofs
that require clean substitution reasoning.

## Key Use Cases

1. **Proving contractiveness preservation under substitution**
2. **Proving unfold preservation properties**
3. **Reasoning about iterated unfolding**

All of these are PROVEN without placeholders in LocalTypeDB.lean!
-/

namespace RumpsteakV2.Protocol.LocalTypeDBExamples

open RumpsteakV2.Protocol.LocalTypeDB
open RumpsteakV2.Protocol.LocalTypeConv
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.GlobalType

/-! ## Example 1: Basic Substitution Preservation -/

/-- Example: Substituting a contractive term preserves contractiveness. -/
example (body e : LocalTypeDB) (h1 : body.isContractive = true) (h2 : e.isContractive = true) :
    (body.subst 0 e).isContractive = true :=
  isContractive_subst body e 0 h1 h2

/-- Example: Unfolding a contractive mu preserves contractiveness. -/
example (body : LocalTypeDB) (h : (LocalTypeDB.mu body).isContractive = true) :
    (LocalTypeDB.unfold (LocalTypeDB.mu body)).isContractive = true :=
  isContractive_unfold (LocalTypeDB.mu body) h

/-! ## Example 2: Full Unfolding Chain -/

/-- Example: After multiple unfolds, contractiveness is still preserved. -/
example (t : LocalTypeDB) (k : Nat) (h : t.isContractive = true) :
    ((LocalTypeDB.unfold)^[k] t).isContractive = true :=
  isContractive_iter_unfold k t h

/-- Example: Full unfolding (to observable form) preserves contractiveness. -/
example (t : LocalTypeDB) (h : t.isContractive = true) :
    t.fullUnfold.isContractive = true :=
  isContractive_fullUnfold t h

/-! ## Example 3: Complex Nesting -/

/-- Example: Substituting a mu into its own body (the unfold operation). -/
example (body : LocalTypeDB) (h_body : body.isContractive = true)
    (h_mu : (LocalTypeDB.mu body).isContractive = true) :
    (body.subst 0 (LocalTypeDB.mu body)).isContractive = true :=
  isContractive_subst_mu body h_body h_mu

/-! ## Example 4: Chain of Operations -/

/-- Example: Multiple operations compose correctly. -/
example (body : LocalTypeDB) (h : (LocalTypeDB.mu body).isContractive = true) :
    -- Unfold, then substitute, still contractive
    (LocalTypeDB.subst (LocalTypeDB.unfold (LocalTypeDB.mu body)) 0 (LocalTypeDB.mu body)).isContractive = true := by
  -- unfold = body.subst 0 (.mu body)
  simp [LocalTypeDB.unfold]
  have h_contr : (LocalTypeDB.mu body).isContractive = true := h
  simp [LocalTypeDB.isContractive, Bool.and_eq_true] at h_contr
  obtain ⟨_h_guard, h_body⟩ := h_contr
  have h_unfolded : (body.subst 0 (LocalTypeDB.mu body)).isContractive = true :=
    isContractive_subst_mu body h_body h
  exact isContractive_subst (body.subst 0 (LocalTypeDB.mu body)) (LocalTypeDB.mu body) 0 h_unfolded h

/-! ## Example 5: Using Bridge Theorems (Partial)

These examples show how to use the bridge theorems to connect
de Bruijn proofs back to named variables.

Note: These have legacy placeholders in the correspondence lemmas, but the
de Bruijn side is complete!
-/

/-- Example: Using the bridge theorem for mu-substitution. -/
example (body : LocalTypeR) (t : String)
    (hcov : Context.Covers [t] body)
    (h_body : body.isContractive = true)
    (h_mu : (LocalTypeR.mu t body).isContractive = true) :
    (body.substitute t (LocalTypeR.mu t body)).isContractive = true := by
  -- This uses the DB bridge theorem (via LocalTypeRDBBridge).
  exact LocalTypeR.isContractive_substitute_mu body t hcov h_body h_mu

/-- Example: Closedness discharges coverage automatically. -/
example (body : LocalTypeR) (t : String)
    (hclosed : body.isClosed = true)
    (h_body : body.isContractive = true)
    (h_mu : (LocalTypeR.mu t body).isContractive = true) :
    (body.substitute t (LocalTypeR.mu t body)).isContractive = true := by
  exact LocalTypeR.isContractive_substitute_mu_closed body t hclosed h_body h_mu

/-- Example: Mu-closedness discharges coverage automatically. -/
example (body : LocalTypeR) (t : String)
    (hclosed : (LocalTypeR.mu t body).isClosed = true)
    (h_body : body.isContractive = true)
    (h_mu : (LocalTypeR.mu t body).isContractive = true) :
    (body.substitute t (LocalTypeR.mu t body)).isContractive = true := by
  exact LocalTypeR.isContractive_substitute_mu_muClosed body t hclosed h_body h_mu

/-! ## Example 6: Direct DB Construction

You can also construct terms directly in de Bruijn form.
-/

/-- Example: A simple contractive mu. -/
def example_mu : LocalTypeDB :=
  LocalTypeDB.mu (LocalTypeDB.send "p" [(Label.mk "lab" PayloadSort.unit, LocalTypeDB.end)])

/-- The example mu is contractive. -/
example : example_mu.isContractive = true := by
  unfold example_mu
  simp [LocalTypeDB.isContractive, LocalTypeDB.isGuarded,
        isContractiveBranches, Bool.and_eq_true]

/-- Unfolding preserves contractiveness. -/
example : example_mu.unfold.isContractive = true := by
  unfold example_mu
  apply isContractive_unfold
  simp [LocalTypeDB.isContractive, LocalTypeDB.isGuarded,
        isContractiveBranches, Bool.and_eq_true]

/-! ## Example 7: Nested Mus -/

/-- Example: Nested mu types. -/
def example_nested : LocalTypeDB :=
  LocalTypeDB.mu (LocalTypeDB.mu (LocalTypeDB.send "p" [(Label.mk "lab" PayloadSort.unit, LocalTypeDB.var 0)]))

/-- Nested mus can be contractive. -/
example : example_nested.isContractive = true := by
  unfold example_nested
  simp [LocalTypeDB.isContractive, LocalTypeDB.isGuarded,
        isContractiveBranches, Bool.and_eq_true]

/-! ## Summary

The de Bruijn infrastructure provides COMPLETE, PROVEN theorems for:
- Substitution preservation of contractiveness
- Unfold preservation of contractiveness
- Iterated unfold preservation
- Full unfold preservation

These can be used directly in de Bruijn form, or connected back to
named variables via the bridge theorems (which have minimal placeholders
for context correspondence).

This is a significant improvement over the named variable approach,
where the mu case was fundamentally difficult to prove.
-/

end RumpsteakV2.Protocol.LocalTypeDBExamples
