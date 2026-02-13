import SessionCoTypes.SubstCommBarendregt.Predicates

/-! # General Substitution Commutation

Proves `subst_subst_comm_general` and corollaries `subst_mu_comm`, `unfold_subst_eq_subst_unfold`.
-/

/-
The Problem. Substitutions don't commute in general due to variable capture. We
need a generalized commutation lemma with precise conditions: variables differ,
first variable not bound, replacement closed, and a pre-substitution relationship.

Solution Structure. Proves `subst_subst_comm_general`: (e.substitute x rx).substitute y ry
equals (e.substitute y ry').substitute x rx when ry = ry'.substitute x rx, x ≠ y,
notBoundAt x e, and rx is closed. Derives `subst_mu_comm` and `unfold_subst_eq_subst_unfold`
as corollaries for mu-specific cases.
-/

namespace SessionCoTypes.SubstCommBarendregt
open SessionTypes.LocalTypeR
open SessionTypes.GlobalType
/-! ## General Substitution Commutation

The key insight is that substitutions commute when:
1. The variables are different (x ≠ y)
2. The first variable (x) is not bound in the term
3. The second replacement (ry) can be written as ry'.substitute x rx for some ry'
4. The first replacement (rx) is closed

This generalized form is needed because in the mu case, the "mu t body" term
gets transformed to "mu t (body.substitute var repl)" under var-substitution. -/

-- General Commutation Mutual Proofs

mutual
  /-- General substitution commutation lemma.

      (e.substitute x rx).substitute y ry = (e.substitute y ry').substitute x rx

      when ry'.substitute x rx = ry, x ≠ y, notBoundAt x e, and rx is closed.

      The key insight is that ry' is the "pre-x-substitution" version of ry. -/
  theorem subst_subst_comm_general (e : LocalTypeR) (x y : String) (rx ry ry' : LocalTypeR)
      (hxy : x ≠ y)
      (hx_not_bound : notBoundAt x e = true)
      (hrx_closed : ∀ v, isFreeIn v rx = false)
      (hry_rel : ry'.substitute x rx = ry) :
      (e.substitute x rx).substitute y ry = (e.substitute y ry').substitute x rx := by
    cases e with
    | «end» =>
        simp only [LocalTypeR.substitute]
    | var w =>
        -- Goal: ((.var w).substitute x rx).substitute y ry = ((.var w).substitute y ry').substitute x rx
        by_cases hwx : w == x
        · -- w == x: first substitution gives rx
          simp only [LocalTypeR.substitute, hwx, ↓reduceIte]
          simp only [beq_iff_eq] at hwx
          -- Since w = x and x ≠ y, we have w ≠ y
          have hwy : (w == y) = false := beq_eq_false_iff_ne.mpr (hwx ▸ hxy)
          simp only [hwy, Bool.false_eq_true, ↓reduceIte]
          simp only [LocalTypeR.substitute, ← hwx, beq_self_eq_true, ↓reduceIte]
          rw [substitute_not_free rx y ry (hrx_closed y)]
        · -- w != x
          by_cases hwy : w == y
          · -- w == y: second substitution gives ry (on LHS) or ry' (on RHS)
            simp only [LocalTypeR.substitute, hwx, Bool.false_eq_true, ↓reduceIte, hwy]
            -- LHS: ry, RHS: ry'.substitute x rx
            exact hry_rel.symm
          · -- w != y: both substitutions leave var w unchanged
            simp only [LocalTypeR.substitute, hwx, Bool.false_eq_true, ↓reduceIte, hwy]
    | send p bs =>
        simp only [LocalTypeR.substitute]
        congr 1
        exact subst_subst_comm_branches_general bs x y rx ry ry' hxy hx_not_bound hrx_closed hry_rel
    | recv p bs =>
        simp only [LocalTypeR.substitute]
        congr 1
        exact subst_subst_comm_branches_general bs x y rx ry ry' hxy hx_not_bound hrx_closed hry_rel
    | mu s inner =>
        simp only [notBoundAt] at hx_not_bound
        have ⟨hxs, hx_not_bound_inner⟩ := Bool.and_eq_true_iff.mp hx_not_bound
        have hxs' : x ≠ s := by simp only [bne_iff_ne, ne_eq] at hxs; exact hxs
        have hsx : (s == x) = false := beq_eq_false_iff_ne.mpr hxs'.symm
        by_cases hsy : s == y
        · simp only [LocalTypeR.substitute, hsx, Bool.false_eq_true, ↓reduceIte, hsy]
        · simp only [LocalTypeR.substitute, hsx, Bool.false_eq_true, ↓reduceIte, hsy]
          congr 1
          exact subst_subst_comm_general inner x y rx ry ry' hxy hx_not_bound_inner hrx_closed hry_rel
  termination_by sizeOf e

  -- General Commutation: Branch Lists

  /-- Branch version of subst_subst_comm_general. -/
  theorem subst_subst_comm_branches_general (bs : List BranchR) (x y : String)
      (rx ry ry' : LocalTypeR)
      (hxy : x ≠ y)
      (hx_not_bound : notBoundAtBranches x bs = true)
      (hrx_closed : ∀ v, isFreeIn v rx = false)
/- ## Structured Block 1 -/
      (hry_rel : ry'.substitute x rx = ry) :
      SessionTypes.LocalTypeR.substituteBranches (SessionTypes.LocalTypeR.substituteBranches bs x rx) y ry
      = SessionTypes.LocalTypeR.substituteBranches (SessionTypes.LocalTypeR.substituteBranches bs y ry') x rx := by
    match bs with
    | [] => rfl
    | (label, _vt, cont) :: rest =>
        simp only [SessionTypes.LocalTypeR.substituteBranches]
        simp only [notBoundAtBranches] at hx_not_bound
        have ⟨hx_not_bound_cont, hx_not_bound_rest⟩ := Bool.and_eq_true_iff.mp hx_not_bound
        congr 1
        · congr 1; congr 1
          exact subst_subst_comm_general cont x y rx ry ry' hxy hx_not_bound_cont hrx_closed hry_rel
        · exact subst_subst_comm_branches_general rest x y rx ry ry' hxy hx_not_bound_rest hrx_closed hry_rel
  termination_by sizeOf bs
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
    all_goals omega
end

-- μ-Substitution Commutation Corollary

/-- Key substitution commutation lemma.

When Barendregt convention holds:
- `notBoundAt var body = true` (var not shadowed in body)
- `∀ v, isFreeIn v repl = false` (repl is closed)
- `t ≠ var` (different variable names)

Then the order of substitution doesn't matter:
`(body.subst var repl).subst t X = (body.subst t X').subst var repl`

where X = `mu t (body.subst var repl)` and X' = `mu t body`.

**Proof Strategy:**

The proof proceeds by structural induction on body. The key cases are:

1. **end**: Both sides equal `.end`, trivial.

2. **var w**:
   - If `w == var`: LHS = `repl` (closed, unchanged by t-subst), RHS = `repl` (w ≠ t since t ≠ var)
   - If `w == t` (and w ≠ var): LHS = M, RHS = `N.subst var repl` = M (by `mu_subst_ne`)
   - Otherwise: Both sides = `var w`

3. **send/recv p bs**: Apply IH to each branch continuation.

4. **mu s inner** (where s ≠ var by Barendregt):
   - If `s == t`: Both sides = `mu s (inner.subst var repl)` (shadowed)
   - If `s ≠ t`: Need `(inner.subst var repl).subst t M' = (inner.subst t N').subst var repl`
     where `M' = mu t (mu s (inner.subst var repl))` and `N' = mu t (mu s inner)`.

     Crucially: `N'.subst var repl = M'` (by `mu_subst_ne` applied twice).

     The IH doesn't directly apply because the mu wraps `mu s inner`, not `inner`.
     A generalized commutation lemma is needed:
     ```
     (e.subst x rx).subst y ry_post = (e.subst y ry_pre).subst x rx
     ```
     when `rx` is closed, `x ≠ y`, `notBoundAt x e`, and `ry_pre.subst x rx = ry_post`.

**Status**: PROVEN using `subst_subst_comm_general`.

**Coq Reference**: `subst_EQ2_mut` in `subject_reduction/coLocal.v` proves this
using de Bruijn indices and autosubst, which avoids explicit variable management.

**Proof**: We instantiate `subst_subst_comm_general` with:
- x = var, y = t
- rx = repl (closed)
- ry = .mu t (body.substitute var repl)
- ry' = .mu t body
- hry_rel: (.mu t body).substitute var repl = .mu t (body.substitute var repl)
  (by mu_subst_ne since t ≠ var)
-/
theorem subst_mu_comm (body : LocalTypeR) (var t : String) (repl : LocalTypeR)
    (hbar : notBoundAt var body = true)
    (hfresh : ∀ v, isFreeIn v repl = false)
    (htne : t ≠ var) :
    (body.substitute var repl).substitute t (.mu t (body.substitute var repl))
    = (body.substitute t (.mu t body)).substitute var repl := by
  -- Use the general commutation lemma
  have hry_rel : (LocalTypeR.mu t body).substitute var repl = .mu t (body.substitute var repl) :=
    mu_subst_ne t body var repl htne
  exact subst_subst_comm_general body var t repl
    (.mu t (body.substitute var repl)) (.mu t body)
    (htne.symm) hbar hfresh hry_rel

/-! ## Unfold-Substitute Confluence

This lemma shows that unfold and substitute commute under the Barendregt convention. -/

/-- unfold is identity for non-mu types. -/
theorem unfold_non_mu_eq_self (lt : LocalTypeR) (hnomu : ∀ t body, lt ≠ .mu t body) :
    lt.unfold = lt := by
  cases lt with
  | «end» | var _ | send _ _ | recv _ _ => rfl
  | mu t body => exact absurd rfl (hnomu t body)

/-- Unfold and substitute confluence under Barendregt convention.

    For non-mu types, unfold is identity, so this is trivial.
    For mu types, this follows from subst_mu_comm.

    Note: The `t == var` case (where t is the mu binder) is impossible because
    `notBoundAt var a = true` means var cannot be the mu binder.

    The precondition `hnomu` requires `repl` to not be a mu type at the top level.
    This is needed for the var case where we substitute to `repl` and need
    `repl.unfold = repl`. For mu-typed `repl`, use `unfold_substitute_EQ2_via_Bisim`
    which gives EQ2 equivalence instead of syntactic equality. -/
theorem unfold_subst_eq_subst_unfold (a : LocalTypeR) (var : String) (repl : LocalTypeR)
    (hbar : notBoundAt var a = true) (hfresh : ∀ t, isFreeIn t repl = false)
    (hnomu : ∀ t body, repl ≠ .mu t body) :
    (a.substitute var repl).unfold = (a.unfold).substitute var repl := by
  cases a with
  | «end» =>
      -- end case: unfold is identity, both sides are definitionally .end
      rfl
  | var v =>
      -- var case: requires case split on v == var
      by_cases hvvar : v == var
      · -- v == var:
        -- LHS = ((.var v).substitute var repl).unfold = repl.unfold
        -- RHS = ((.var v).unfold).substitute var repl = (.var v).substitute var repl = repl
        -- Goal: repl.unfold = repl, which holds by unfold_non_mu_eq_self
        have heq1 : (LocalTypeR.var v).substitute var repl = repl := by
          simp only [LocalTypeR.substitute, hvvar, ↓reduceIte]
        have heq2 : (LocalTypeR.var v).unfold = .var v := rfl
        simp only [heq1, heq2]
        -- Goal: repl.unfold = repl
        exact unfold_non_mu_eq_self repl hnomu
      · -- v != var: both sides are .var v
        simp only [LocalTypeR.substitute, hvvar, Bool.false_eq_true, ↓reduceIte, LocalTypeR.unfold]
  | send _ _ | recv _ _ =>
      -- send/recv cases: unfold is identity
      rfl
  | mu t body =>
      -- notBoundAt var (.mu t body) = (var != t) && notBoundAt var body = true
      simp only [notBoundAt] at hbar
      have ⟨hvt, hbar_body⟩ := Bool.and_eq_true_iff.mp hbar
      have hvt' : var ≠ t := by simp only [bne_iff_ne, ne_eq] at hvt; exact hvt
      have htv' : t ≠ var := hvt'.symm
      -- LHS: ((.mu t body).substitute var repl).unfold
      --    = (.mu t (body.substitute var repl)).unfold  [since t != var]
      --    = (body.substitute var repl).substitute t (.mu t (body.substitute var repl))
      -- RHS: ((.mu t body).unfold).substitute var repl
      --    = (body.substitute t (.mu t body)).substitute var repl
      simp only [LocalTypeR.substitute]
      simp only [beq_eq_false_iff_ne.mpr htv', Bool.false_eq_true, ↓reduceIte, LocalTypeR.unfold]
      -- Goal: (body.substitute var repl).substitute t (.mu t (body.substitute var repl))
      --     = (body.substitute t (.mu t body)).substitute var repl
      exact subst_mu_comm body var t repl hbar_body hfresh htv'

end SessionCoTypes.SubstCommBarendregt
