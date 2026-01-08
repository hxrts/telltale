import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.LocalTypeR

/-! # SubstCommBarendregt: EQ2_substitute under Barendregt Convention

This module proves `EQ2_substitute_barendregt`, showing that EQ2 is preserved under
substitution when the Barendregt convention holds.

## Approach: Inductive SubstRel Closed Under Unfolding

The key insight is to define `SubstRel` as an inductive relation closed under unfolding,
then use a `flatten` lemma to reduce any witness to base form.
-/

namespace RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt

open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-! ## Barendregt Predicates -/

mutual
  /-- Check if a variable appears free in a type. -/
  def isFreeIn (v : String) : LocalTypeR → Bool
    | .end => false
    | .var w => v == w
    | .send _ bs => isFreeInBranches v bs
    | .recv _ bs => isFreeInBranches v bs
    | .mu t body => if v == t then false else isFreeIn v body

  /-- Check if a variable appears free in any branch. -/
  def isFreeInBranches (v : String) : List (Label × LocalTypeR) → Bool
    | [] => false
    | (_, cont) :: rest => isFreeIn v cont || isFreeInBranches v rest
end

mutual
  /-- Check that a variable is not used as a binder anywhere. -/
  def notBoundAt (v : String) : LocalTypeR → Bool
    | .end => true
    | .var _ => true
    | .send _ bs => notBoundAtBranches v bs
    | .recv _ bs => notBoundAtBranches v bs
    | .mu t body => (v != t) && notBoundAt v body

  /-- Check notBoundAt for branches. -/
  def notBoundAtBranches (v : String) : List (Label × LocalTypeR) → Bool
    | [] => true
    | (_, cont) :: rest => notBoundAt v cont && notBoundAtBranches v rest
end

mutual
  /-- notBoundAt is preserved through substitution when repl also satisfies it. -/
  theorem notBoundAt_subst (v var : String) (a repl : LocalTypeR)
      (hbar : notBoundAt v a = true)
      (hvarRepl : notBoundAt v repl = true) :
      notBoundAt v (a.substitute var repl) = true := by
    cases a with
    | «end» => simp [LocalTypeR.substitute, notBoundAt]
    | var w =>
        simp only [LocalTypeR.substitute]
        by_cases hwvar : w == var
        · simp only [hwvar, ↓reduceIte]; exact hvarRepl
        · simp only [hwvar, Bool.false_eq_true, ↓reduceIte, notBoundAt]
    | send p bs =>
        simp only [LocalTypeR.substitute, notBoundAt]
        exact notBoundAt_subst_branches v var bs repl (by unfold notBoundAt at hbar; exact hbar) hvarRepl
    | recv p bs =>
        simp only [LocalTypeR.substitute, notBoundAt]
        exact notBoundAt_subst_branches v var bs repl (by unfold notBoundAt at hbar; exact hbar) hvarRepl
    | mu t body =>
        simp only [LocalTypeR.substitute]
        by_cases htvar : t == var
        · -- Shadowed: substitution is identity
          simp only [htvar, ↓reduceIte]; exact hbar
        · -- Not shadowed: recurse
          simp only [htvar, Bool.false_eq_true, ↓reduceIte, notBoundAt]
          unfold notBoundAt at hbar
          have ⟨hvt, hbarBody⟩ := Bool.and_eq_true_iff.mp hbar
          exact Bool.and_eq_true_iff.mpr ⟨hvt, notBoundAt_subst v var body repl hbarBody hvarRepl⟩
  termination_by sizeOf a

  /-- notBoundAt for branches is preserved through substitution. -/
  theorem notBoundAt_subst_branches (v var : String) (bs : List (Label × LocalTypeR)) (repl : LocalTypeR)
      (hbar : notBoundAtBranches v bs = true)
      (hvarRepl : notBoundAt v repl = true) :
      notBoundAtBranches v (LocalTypeR.substituteBranches bs var repl) = true :=
    match bs, hbar with
    | [], _ => by simp [LocalTypeR.substituteBranches, notBoundAtBranches]
    | hd :: tl, hbar => by
        simp only [LocalTypeR.substituteBranches, notBoundAtBranches]
        unfold notBoundAtBranches at hbar
        have ⟨hbarHd, hbarTl⟩ := Bool.and_eq_true_iff.mp hbar
        exact Bool.and_eq_true_iff.mpr ⟨notBoundAt_subst v var hd.2 repl hbarHd hvarRepl,
          notBoundAt_subst_branches v var tl repl hbarTl hvarRepl⟩
  termination_by sizeOf bs
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
    all_goals omega
end

/-- notBoundAt is preserved through unfolding. -/
theorem notBoundAt_unfold (v : String) (a : LocalTypeR)
    (hbar : notBoundAt v a = true) :
    notBoundAt v a.unfold = true := by
  cases a with
  | «end» | var _ | send _ _ | recv _ _ =>
      -- Non-mu cases: unfold is identity
      simp only [LocalTypeR.unfold]; exact hbar
  | mu t body =>
      -- unfold (.mu t body) = body.substitute t (.mu t body)
      simp only [LocalTypeR.unfold]
      -- hbar : notBoundAt v (.mu t body) = true
      -- means: (v != t) && notBoundAt v body = true
      unfold notBoundAt at hbar
      have ⟨hvt, hbarBody⟩ := Bool.and_eq_true_iff.mp hbar
      -- Apply notBoundAt_subst: need notBoundAt v body and notBoundAt v (.mu t body)
      apply notBoundAt_subst v t body (.mu t body) hbarBody
      -- Need: notBoundAt v (.mu t body) = true
      unfold notBoundAt
      exact Bool.and_eq_true_iff.mpr ⟨hvt, hbarBody⟩

/-! ## Substitution Helper Lemmas -/

mutual
  /-- If x is not free in e, then substituting for x leaves e unchanged. -/
  theorem substitute_not_free (e : LocalTypeR) (x : String) (rx : LocalTypeR)
      (hnot_free : isFreeIn x e = false) :
      e.substitute x rx = e := by
    cases e with
    | «end» => rfl
    | var w =>
        simp only [LocalTypeR.substitute]
        simp only [isFreeIn] at hnot_free
        have hwx : (w == x) = false := by
          rw [beq_eq_false_iff_ne] at hnot_free ⊢; exact fun h => hnot_free h.symm
        simp only [hwx, Bool.false_eq_true, ↓reduceIte]
    | send p bs =>
        simp only [LocalTypeR.substitute]
        congr 1
        simp only [isFreeIn] at hnot_free
        exact substituteBranches_not_free bs x rx hnot_free
    | recv p bs =>
        simp only [LocalTypeR.substitute]
        congr 1
        simp only [isFreeIn] at hnot_free
        exact substituteBranches_not_free bs x rx hnot_free
    | mu t body =>
        simp only [LocalTypeR.substitute]
        by_cases hxt : t == x
        · simp only [hxt, ↓reduceIte]
        · simp only [hxt, Bool.false_eq_true, ↓reduceIte]
          congr 1
          simp only [isFreeIn] at hnot_free
          have hxt' : (x == t) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hxt (beq_iff_eq.mpr h.symm)
          simp only [hxt', Bool.false_eq_true, ↓reduceIte] at hnot_free
          exact substitute_not_free body x rx hnot_free
  termination_by sizeOf e

  /-- If x is not free in any branch, substituting for x leaves branches unchanged. -/
  theorem substituteBranches_not_free (bs : List (Label × LocalTypeR)) (x : String) (rx : LocalTypeR)
      (hnot_free : isFreeInBranches x bs = false) :
      LocalTypeR.substituteBranches bs x rx = bs := by
    match bs with
    | [] => rfl
    | (label, cont) :: rest =>
        simp only [LocalTypeR.substituteBranches]
        simp only [isFreeInBranches, Bool.or_eq_false_iff] at hnot_free
        have h1 : cont.substitute x rx = cont := substitute_not_free cont x rx hnot_free.1
        have h2 : LocalTypeR.substituteBranches rest x rx = rest := substituteBranches_not_free rest x rx hnot_free.2
        simp only [h1, h2]
  termination_by sizeOf bs
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
    all_goals omega
end

/-- Substituting into a closed type leaves it unchanged. -/
theorem substitute_closed (e : LocalTypeR) (x : String) (rx : LocalTypeR)
    (hclosed : ∀ v, isFreeIn v e = false) :
    e.substitute x rx = e :=
  substitute_not_free e x rx (hclosed x)

/-- A variable bound by mu is not free in the mu type. -/
theorem isFreeIn_mu_self (t : String) (body : LocalTypeR) :
    isFreeIn t (.mu t body) = false := by
  simp only [isFreeIn, beq_self_eq_true, ↓reduceIte]

mutual
  /-- If t is not free in repl, then t is not free in (e.substitute t repl).

      Key insight: Every occurrence of t in e gets replaced by repl,
      and t is not free in repl, so t cannot be free in the result. -/
  theorem isFreeIn_subst_self_general (e : LocalTypeR) (t : String) (repl : LocalTypeR)
      (hrepl : isFreeIn t repl = false) :
      isFreeIn t (e.substitute t repl) = false := by
    cases e with
    | «end» =>
        simp only [LocalTypeR.substitute, isFreeIn]
    | var w =>
        simp only [LocalTypeR.substitute]
        by_cases hwt : w == t
        · -- w == t: substitute returns repl
          simp only [hwt, ↓reduceIte]
          exact hrepl
        · -- w != t: substitute returns .var w
          simp only [hwt, Bool.false_eq_true, ↓reduceIte, isFreeIn, beq_eq_false_iff_ne, ne_eq]
          exact fun h => hwt (beq_iff_eq.mpr h.symm)
    | send p bs =>
        simp only [LocalTypeR.substitute, isFreeIn]
        exact isFreeInBranches_subst_self_general bs t repl hrepl
    | recv p bs =>
        simp only [LocalTypeR.substitute, isFreeIn]
        exact isFreeInBranches_subst_self_general bs t repl hrepl
    | mu s inner =>
        simp only [LocalTypeR.substitute]
        by_cases hst : s == t
        · -- s == t: substitution is shadowed, returns .mu s inner
          simp only [hst, ↓reduceIte, isFreeIn]
          simp only [beq_iff_eq] at hst
          simp only [← hst, beq_self_eq_true, ↓reduceIte]
        · -- s != t: returns .mu s (inner.substitute t repl)
          simp only [hst, Bool.false_eq_true, ↓reduceIte, isFreeIn]
          have hts : (t == s) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hst (beq_iff_eq.mpr h.symm)
          simp only [hts, Bool.false_eq_true, ↓reduceIte]
          exact isFreeIn_subst_self_general inner t repl hrepl
  termination_by sizeOf e

  /-- Branch version of isFreeIn_subst_self_general. -/
  theorem isFreeInBranches_subst_self_general (bs : List (Label × LocalTypeR)) (t : String)
      (repl : LocalTypeR) (hrepl : isFreeIn t repl = false) :
      isFreeInBranches t (LocalTypeR.substituteBranches bs t repl) = false := by
    match bs with
    | [] => simp only [LocalTypeR.substituteBranches, isFreeInBranches]
    | (label, cont) :: rest =>
        simp only [LocalTypeR.substituteBranches, isFreeInBranches, Bool.or_eq_false_iff]
        exact ⟨isFreeIn_subst_self_general cont t repl hrepl,
               isFreeInBranches_subst_self_general rest t repl hrepl⟩
  termination_by sizeOf bs
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
    all_goals omega
end

/-- After substituting t with (mu t body), the variable t is not free.

    This is a special case of isFreeIn_subst_self_general where repl = .mu t body. -/
theorem isFreeIn_subst_mu_self (body : LocalTypeR) (t : String) :
    isFreeIn t (body.substitute t (.mu t body)) = false :=
  isFreeIn_subst_self_general body t (.mu t body) (isFreeIn_mu_self t body)

/-- Key helper: (mu t body).substitute var repl = mu t (body.substitute var repl) when t ≠ var. -/
theorem mu_subst_ne (t : String) (body : LocalTypeR) (var : String) (repl : LocalTypeR)
    (htne : t ≠ var) :
    (LocalTypeR.mu t body).substitute var repl = .mu t (body.substitute var repl) := by
  simp only [LocalTypeR.substitute]
  simp only [beq_eq_false_iff_ne.mpr htne, Bool.false_eq_true, ↓reduceIte]

/-! ## General Substitution Commutation

The key insight is that substitutions commute when:
1. The variables are different (x ≠ y)
2. The first variable (x) is not bound in the term
3. The second replacement (ry) can be written as ry'.substitute x rx for some ry'
4. The first replacement (rx) is closed

This generalized form is needed because in the mu case, the "mu t body" term
gets transformed to "mu t (body.substitute var repl)" under var-substitution. -/

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

  /-- Branch version of subst_subst_comm_general. -/
  theorem subst_subst_comm_branches_general (bs : List (Label × LocalTypeR)) (x y : String)
      (rx ry ry' : LocalTypeR)
      (hxy : x ≠ y)
      (hx_not_bound : notBoundAtBranches x bs = true)
      (hrx_closed : ∀ v, isFreeIn v rx = false)
      (hry_rel : ry'.substitute x rx = ry) :
      LocalTypeR.substituteBranches (LocalTypeR.substituteBranches bs x rx) y ry
      = LocalTypeR.substituteBranches (LocalTypeR.substituteBranches bs y ry') x rx := by
    match bs with
    | [] => rfl
    | (label, cont) :: rest =>
        simp only [LocalTypeR.substituteBranches]
        simp only [notBoundAtBranches] at hx_not_bound
        have ⟨hx_not_bound_cont, hx_not_bound_rest⟩ := Bool.and_eq_true_iff.mp hx_not_bound
        congr 1
        · congr 1
          exact subst_subst_comm_general cont x y rx ry ry' hxy hx_not_bound_cont hrx_closed hry_rel
        · exact subst_subst_comm_branches_general rest x y rx ry ry' hxy hx_not_bound_rest hrx_closed hry_rel
  termination_by sizeOf bs
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
    all_goals omega
end

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

/-! ## Inductive SubstRel -/

/-- Relation for substitution congruence, closed under unfolding. -/
inductive SubstRel (var : String) (repl : LocalTypeR) : Rel where
  | base (a b : LocalTypeR) (hab : EQ2 a b)
      (hbarA : notBoundAt var a = true) (hbarB : notBoundAt var b = true) :
      SubstRel var repl (a.substitute var repl) (b.substitute var repl)
  | unfold_left {x y : LocalTypeR} :
      SubstRel var repl x y → SubstRel var repl x.unfold y
  | unfold_right {x y : LocalTypeR} :
      SubstRel var repl x y → SubstRel var repl x y.unfold

/-! ## The Flatten Lemma -/

/-- Flatten pushes unfolds into the EQ2 witnesses.

    Requires `hnomu : ∀ t body, repl ≠ .mu t body` (repl is not a mu type at top level).
    This is needed for the unfold_subst_eq_subst_unfold lemma when the witness is a var
    that matches the substitution variable. -/
theorem SubstRel.flatten {var : String} {repl : LocalTypeR}
    (hfresh : ∀ t, isFreeIn t repl = false)
    (hnomu : ∀ t body, repl ≠ .mu t body)
    {x y : LocalTypeR} (h : SubstRel var repl x y) :
    ∃ a b, EQ2 a b ∧
           notBoundAt var a = true ∧ notBoundAt var b = true ∧
           x = a.substitute var repl ∧ y = b.substitute var repl := by
  induction h with
  | base a b hab hbarA hbarB =>
    exact ⟨a, b, hab, hbarA, hbarB, rfl, rfl⟩
  | unfold_left _ ih =>
    obtain ⟨a, b, hab, hbarA, hbarB, hx, hy⟩ := ih
    use a.unfold, b
    refine ⟨EQ2_unfold_left hab, notBoundAt_unfold var a hbarA, hbarB, ?_, hy⟩
    rw [hx]
    exact unfold_subst_eq_subst_unfold a var repl hbarA hfresh hnomu
  | unfold_right _ ih =>
    obtain ⟨a, b, hab, hbarA, hbarB, hx, hy⟩ := ih
    use a, b.unfold
    refine ⟨EQ2_unfold_right hab, hbarA, notBoundAt_unfold var b hbarB, hx, ?_⟩
    rw [hy]
    exact unfold_subst_eq_subst_unfold b var repl hbarB hfresh hnomu

/-! ## Helper Lemmas for Substitution -/

/-- Substitute on mu when bound variable differs from substitution variable. -/
theorem mu_substitute_ne (t : String) (body : LocalTypeR) (var : String) (repl : LocalTypeR)
    (hne : (t == var) = false) :
    (LocalTypeR.mu t body).substitute var repl = .mu t (body.substitute var repl) := by
  simp only [LocalTypeR.substitute, hne, Bool.false_eq_true, ite_false]

/-- Substitute on var when variable equals substitution variable. -/
theorem var_substitute_eq (v : String) (var : String) (repl : LocalTypeR)
    (heq : (v == var) = true) :
    (LocalTypeR.var v).substitute var repl = repl := by
  simp only [LocalTypeR.substitute, heq, ite_true]

/-- Substitute on var when variable differs from substitution variable. -/
theorem var_substitute_ne (v : String) (var : String) (repl : LocalTypeR)
    (hne : (v == var) = false) :
    (LocalTypeR.var v).substitute var repl = .var v := by
  simp only [LocalTypeR.substitute, hne, Bool.false_eq_true, ite_false]

/-! ## EQ2F Reduction Lemmas -/

/-- EQ2F reduction for mu-end case. -/
@[simp] theorem EQ2F_mu_end (R : Rel) (t : String) (body : LocalTypeR) :
    EQ2F R (.mu t body) .end = R (body.substitute t (.mu t body)) .end := rfl

/-- EQ2F reduction for mu-var case. -/
@[simp] theorem EQ2F_mu_var (R : Rel) (t : String) (body : LocalTypeR) (v : String) :
    EQ2F R (.mu t body) (.var v) = R (body.substitute t (.mu t body)) (.var v) := rfl

/-- EQ2F reduction for mu-send case. -/
@[simp] theorem EQ2F_mu_send (R : Rel) (t : String) (body : LocalTypeR) (p : String)
    (bs : List (Label × LocalTypeR)) :
    EQ2F R (.mu t body) (.send p bs) = R (body.substitute t (.mu t body)) (.send p bs) := rfl

/-- EQ2F reduction for mu-recv case. -/
@[simp] theorem EQ2F_mu_recv (R : Rel) (t : String) (body : LocalTypeR) (p : String)
    (bs : List (Label × LocalTypeR)) :
    EQ2F R (.mu t body) (.recv p bs) = R (body.substitute t (.mu t body)) (.recv p bs) := rfl

/-- EQ2F reduction for end-mu case. -/
@[simp] theorem EQ2F_end_mu (R : Rel) (s : String) (body' : LocalTypeR) :
    EQ2F R .end (.mu s body') = R .end (body'.substitute s (.mu s body')) := rfl

/-- EQ2F reduction for var-mu case. -/
@[simp] theorem EQ2F_var_mu (R : Rel) (v : String) (s : String) (body' : LocalTypeR) :
    EQ2F R (.var v) (.mu s body') = R (.var v) (body'.substitute s (.mu s body')) := rfl

/-- EQ2F reduction for send-mu case. -/
@[simp] theorem EQ2F_send_mu (R : Rel) (p : String) (bs : List (Label × LocalTypeR))
    (s : String) (body' : LocalTypeR) :
    EQ2F R (.send p bs) (.mu s body') = R (.send p bs) (body'.substitute s (.mu s body')) := rfl

/-- EQ2F reduction for recv-mu case. -/
@[simp] theorem EQ2F_recv_mu (R : Rel) (p : String) (bs : List (Label × LocalTypeR))
    (s : String) (body' : LocalTypeR) :
    EQ2F R (.recv p bs) (.mu s body') = R (.recv p bs) (body'.substitute s (.mu s body')) := rfl

/-! ## Standard Case Analysis -/

/-- Helper: lift BranchesRel through substitution. -/
theorem BranchesRel_substitute (var : String) (repl : LocalTypeR)
    (bs cs : List (Label × LocalTypeR))
    (hbranches : BranchesRel EQ2 bs cs)
    (hbarBs : notBoundAtBranches var bs = true)
    (hbarCs : notBoundAtBranches var cs = true)
    (_hfresh : ∀ t, isFreeIn t repl = false) :
    BranchesRel (EQ2_closure (SubstRel var repl))
      (LocalTypeR.substituteBranches bs var repl) (LocalTypeR.substituteBranches cs var repl) := by
  induction hbranches with
  | nil => exact List.Forall₂.nil
  | @cons a b as bs' hhead _ ih =>
    unfold LocalTypeR.substituteBranches
    unfold notBoundAtBranches at hbarBs hbarCs
    have ⟨hbarA, hbarAs⟩ := Bool.and_eq_true_iff.mp hbarBs
    have ⟨hbarB, hbarBs'⟩ := Bool.and_eq_true_iff.mp hbarCs
    apply List.Forall₂.cons
    · constructor
      · exact hhead.1
      · exact Or.inl (SubstRel.base a.2 b.2 hhead.2 hbarA hbarB)
    · exact ih hbarAs hbarBs'

/-- Helper to convert htvar/hsvar proofs to the expected form. -/
private theorem bne_of_notBoundAt_mu {v t : String} {body : LocalTypeR}
    (hbar : notBoundAt v (.mu t body) = true) :
    (t == v) = false := by
  unfold notBoundAt at hbar
  have ⟨hvt, _⟩ := Bool.and_eq_true_iff.mp hbar
  simp only [bne_iff_ne, ne_eq] at hvt
  exact beq_eq_false_iff_ne.mpr (Ne.symm hvt)

/-- Standard one-step analysis for SubstRel after flattening. -/
theorem SubstRel_postfix_standard (var : String) (repl : LocalTypeR)
    (a b : LocalTypeR) (_hab : EQ2 a b)
    (hbarA : notBoundAt var a = true) (hbarB : notBoundAt var b = true)
    (hfresh : ∀ t, isFreeIn t repl = false)
    (hf : EQ2F EQ2 a b) :
    EQ2F (EQ2_closure (SubstRel var repl)) (a.substitute var repl) (b.substitute var repl) := by
  cases a <;> cases b
  -- end-end
  case end.end =>
    unfold LocalTypeR.substitute
    unfold EQ2F
    trivial
  -- var-var
  case var.var x y =>
    unfold LocalTypeR.substitute
    unfold EQ2F at hf ⊢
    by_cases hx : x == var
    · -- x == var
      simp only [hx, ite_true]
      by_cases hy : y == var
      · -- y == var, both become repl
        simp only [hy, ite_true]
        -- Goal: EQ2F (EQ2_closure (SubstRel var repl)) repl repl
        have hf' : EQ2F EQ2 repl repl := EQ2.destruct (EQ2_refl repl)
        exact EQ2F.mono (fun _ _ h => Or.inr h) repl repl hf'
      · -- y != var, x == var but hf says x = y
        simp only [hy, Bool.false_eq_true, ite_false]
        simp only [beq_iff_eq] at hx hy hf
        exact absurd (hf.symm.trans hx) hy
    · -- x != var
      simp only [hx, Bool.false_eq_true, ite_false]
      by_cases hy : y == var
      · simp only [hy, ite_true]
        simp only [beq_iff_eq] at hx hy hf
        exact absurd (hf.trans hy) hx
      · simp only [hy, Bool.false_eq_true, ite_false]
        exact hf
  -- send-send
  case send.send p bs q cs =>
    unfold LocalTypeR.substitute
    unfold EQ2F at hf ⊢
    unfold notBoundAt at hbarA hbarB
    obtain ⟨hp, hbranches⟩ := hf
    exact ⟨hp, BranchesRel_substitute var repl bs cs hbranches hbarA hbarB hfresh⟩
  -- recv-recv
  case recv.recv p bs q cs =>
    unfold LocalTypeR.substitute
    unfold EQ2F at hf ⊢
    unfold notBoundAt at hbarA hbarB
    obtain ⟨hp, hbranches⟩ := hf
    exact ⟨hp, BranchesRel_substitute var repl bs cs hbranches hbarA hbarB hfresh⟩
  -- mu-mu
  case mu.mu t body s body' =>
    unfold notBoundAt at hbarA hbarB
    have ⟨hvart, hbarBody⟩ := Bool.and_eq_true_iff.mp hbarA
    have ⟨hvars, hbarBody'⟩ := Bool.and_eq_true_iff.mp hbarB
    have htne : t ≠ var := Ne.symm (bne_iff_ne.mp hvart)
    have hsne : s ≠ var := Ne.symm (bne_iff_ne.mp hvars)
    have htvar : (t == var) = false := beq_eq_false_iff_ne.mpr htne
    have hsvar : (s == var) = false := beq_eq_false_iff_ne.mpr hsne
    -- notBoundAt for the mu constructors
    have hmu_t_bar : notBoundAt var (.mu t body) = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvart, hbarBody⟩
    have hmu_s_bar : notBoundAt var (.mu s body') = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvars, hbarBody'⟩
    -- Explicit substitution reductions
    have ha_subst := mu_substitute_ne t body var repl htvar
    have hb_subst := mu_substitute_ne s body' var repl hsvar
    simp only [ha_subst, hb_subst, EQ2F] at hf ⊢
    obtain ⟨hleft, hright⟩ := hf
    constructor
    · -- Left goal: SubstRel ((body.subst t (mu t body)).subst var repl) ((mu s body').subst var repl)
      rw [subst_mu_comm body var t repl hbarBody hfresh htne]
      apply Or.inl
      rw [← hb_subst]
      exact SubstRel.base _ _ hleft
        (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
        hmu_s_bar
    · -- Right goal: SubstRel ((mu t body).subst var repl) ((body'.subst s (mu s body')).subst var repl)
      rw [subst_mu_comm body' var s repl hbarBody' hfresh hsne]
      apply Or.inl
      rw [← ha_subst]
      exact SubstRel.base _ _ hright
        hmu_t_bar
        (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
  -- mu-end (unfolding on left)
  case mu.end t body =>
    have htvar := bne_of_notBoundAt_mu hbarA
    unfold notBoundAt at hbarA
    have ⟨hvart, hbarBody⟩ := Bool.and_eq_true_iff.mp hbarA
    have htne : t ≠ var := by simp only [bne_iff_ne, ne_eq] at hvart; exact fun h => hvart h.symm
    have hmu_t_bar : notBoundAt var (.mu t body) = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvart, hbarBody⟩
    have ha_subst := mu_substitute_ne t body var repl htvar
    have hb_subst : LocalTypeR.end.substitute var repl = .end := rfl
    simp only [ha_subst, hb_subst, EQ2F] at hf ⊢
    rw [subst_mu_comm body var t repl hbarBody hfresh htne]
    apply Or.inl
    exact SubstRel.base _ _ hf
      (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
      (by rfl)
  case mu.var t body v =>
    have htvar := bne_of_notBoundAt_mu hbarA
    unfold notBoundAt at hbarA
    have ⟨hvart, hbarBody⟩ := Bool.and_eq_true_iff.mp hbarA
    have htne : t ≠ var := by simp only [bne_iff_ne, ne_eq] at hvart; exact fun h => hvart h.symm
    have hmu_t_bar : notBoundAt var (.mu t body) = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvart, hbarBody⟩
    -- hf : EQ2F EQ2 (.mu t body) (.var v) = EQ2 (body.substitute t (.mu t body)) (.var v)
    simp only [EQ2F_mu_var] at hf
    -- Goal: EQ2F (EQ2_closure (SubstRel var repl)) ((.mu t body).substitute var repl) ((.var v).substitute var repl)
    -- Don't simp goal - instead use SubstRel.base directly with unfold_left
    -- SubstRel.base constructs: SubstRel var repl (a.subst var repl) (b.subst var repl)
    -- We need: EQ2F (EQ2_closure ...) ((.mu t body).subst var repl) ((.var v).subst var repl)
    -- By EQ2F_mu_var: this = EQ2_closure ... (((.mu t body).subst var repl).unfold) ((.var v).subst var repl)
    -- (.mu t body).subst var repl = .mu t (body.subst var repl) (since t ≠ var)
    -- unfold of that = (body.subst var repl).subst t (.mu t (body.subst var repl))
    have ha_subst := mu_substitute_ne t body var repl htvar
    -- Use EQ2F reduction on the substituted forms
    rw [ha_subst]
    -- Now goal: EQ2F (EQ2_closure ...) (.mu t (body.subst var repl)) ((.var v).subst var repl)
    by_cases hv : v == var
    · have hb_subst := var_substitute_eq v var repl hv
      rw [hb_subst]
      -- Goal: EQ2F (EQ2_closure ...) (.mu t (body.subst var repl)) repl
      -- repl is arbitrary, so we need to case-split on its constructor
      cases repl with
      | «end» =>
        simp only [EQ2F_mu_end]
        rw [subst_mu_comm body var t (.end) hbarBody (by intro t'; exact hfresh t') htne]
        apply Or.inl
        have hsr : SubstRel var .end ((body.substitute t (.mu t body)).substitute var .end)
            ((LocalTypeR.var v).substitute var .end) :=
          SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
            (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
            (by rfl : notBoundAt var (.var v) = true)
        rw [var_substitute_eq v var .end hv] at hsr
        exact hsr
      | var w =>
        simp only [EQ2F_mu_var]
        rw [subst_mu_comm body var t (.var w) hbarBody (by intro t'; exact hfresh t') htne]
        apply Or.inl
        have hsr : SubstRel var (.var w) ((body.substitute t (.mu t body)).substitute var (.var w))
            ((LocalTypeR.var v).substitute var (.var w)) :=
          SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
            (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
            (by rfl : notBoundAt var (.var v) = true)
        rw [var_substitute_eq v var (.var w) hv] at hsr
        exact hsr
      | send p bs =>
        simp only [EQ2F_mu_send]
        rw [subst_mu_comm body var t (.send p bs) hbarBody (by intro t'; exact hfresh t') htne]
        apply Or.inl
        have hsr : SubstRel var (.send p bs) ((body.substitute t (.mu t body)).substitute var (.send p bs))
            ((LocalTypeR.var v).substitute var (.send p bs)) :=
          SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
            (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
            (by rfl : notBoundAt var (.var v) = true)
        rw [var_substitute_eq v var (.send p bs) hv] at hsr
        exact hsr
      | recv p bs =>
        simp only [EQ2F_mu_recv]
        rw [subst_mu_comm body var t (.recv p bs) hbarBody (by intro t'; exact hfresh t') htne]
        apply Or.inl
        have hsr : SubstRel var (.recv p bs) ((body.substitute t (.mu t body)).substitute var (.recv p bs))
            ((LocalTypeR.var v).substitute var (.recv p bs)) :=
          SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
            (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
            (by rfl : notBoundAt var (.var v) = true)
        rw [var_substitute_eq v var (.recv p bs) hv] at hsr
        exact hsr
      | mu s body' =>
        -- mu-mu case is more complex - need both directions
        simp only [EQ2F]
        constructor
        · -- left goal: (body.subst var (.mu s body')).subst t (...) relates to (.mu s body')
          rw [subst_mu_comm body var t (.mu s body') hbarBody (by intro t'; exact hfresh t') htne]
          apply Or.inl
          have hsr : SubstRel var (.mu s body') ((body.substitute t (.mu t body)).substitute var (.mu s body'))
              ((LocalTypeR.var v).substitute var (.mu s body')) :=
            SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
              (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
              (by rfl : notBoundAt var (.var v) = true)
          rw [var_substitute_eq v var (.mu s body') hv] at hsr
          exact hsr
        · -- right goal: (.mu t (body.subst var (.mu s body'))) relates to (body'.subst s (.mu s body'))
          -- SubstRel.base gives us: SubstRel (.mu t (body.subst var repl)) repl
          -- We need to unfold the RHS: repl.unfold = body'.subst s (.mu s body')
          apply Or.inl
          have hab : EQ2 (.mu t body) (.var v) := by
            apply EQ2.construct
            simp only [EQ2F_mu_var]
            exact hf
          have hsr_base : SubstRel var (LocalTypeR.mu s body')
              ((LocalTypeR.mu t body).substitute var (LocalTypeR.mu s body'))
              ((LocalTypeR.var v).substitute var (LocalTypeR.mu s body')) :=
            SubstRel.base (LocalTypeR.mu t body) (LocalTypeR.var v) hab hmu_t_bar (by rfl : notBoundAt var (LocalTypeR.var v) = true)
          -- Reduce substitutions in hsr_base's type
          have hmu_subst : (LocalTypeR.mu t body).substitute var (LocalTypeR.mu s body')
              = LocalTypeR.mu t (body.substitute var (LocalTypeR.mu s body')) :=
            mu_substitute_ne t body var (LocalTypeR.mu s body') htvar
          have hvar_subst : (LocalTypeR.var v).substitute var (LocalTypeR.mu s body')
              = LocalTypeR.mu s body' :=
            var_substitute_eq v var (LocalTypeR.mu s body') hv
          -- The types are definitionally equal after reducing substitute
          -- Use cast with Eq.mpr to convert between them
          have hsr : SubstRel var (LocalTypeR.mu s body')
              (LocalTypeR.mu t (body.substitute var (LocalTypeR.mu s body')))
              (LocalTypeR.mu s body') := by
            have heq : SubstRel var (LocalTypeR.mu s body')
                ((LocalTypeR.mu t body).substitute var (LocalTypeR.mu s body'))
                ((LocalTypeR.var v).substitute var (LocalTypeR.mu s body'))
              = SubstRel var (LocalTypeR.mu s body')
                (LocalTypeR.mu t (body.substitute var (LocalTypeR.mu s body')))
                (LocalTypeR.mu s body') := by
              rw [hmu_subst, hvar_subst]
            exact heq ▸ hsr_base
          -- Apply unfold_right: (.mu s body').unfold = body'.substitute s (.mu s body')
          have hsr' := SubstRel.unfold_right hsr
          -- Reduce the unfold in the type
          simp only [LocalTypeR.unfold] at hsr'
          exact hsr'
    · have hv' : (v == var) = false := by cases h : v == var <;> simp_all
      have hb_subst := var_substitute_ne v var repl hv'
      rw [hb_subst]
      -- Goal: EQ2F (EQ2_closure ...) (.mu t (body.subst var repl)) (.var v)
      simp only [EQ2F_mu_var]
      rw [subst_mu_comm body var t repl hbarBody hfresh htne]
      apply Or.inl
      have hsr : SubstRel var repl ((body.substitute t (.mu t body)).substitute var repl)
          ((LocalTypeR.var v).substitute var repl) :=
        SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
          (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
          (by rfl : notBoundAt var (.var v) = true)
      rw [hb_subst] at hsr
      exact hsr
  case mu.send t body p bs =>
    have htvar := bne_of_notBoundAt_mu hbarA
    have hbarB_orig := hbarB  -- Save before unfolding
    unfold notBoundAt at hbarA hbarB
    have ⟨hvart, hbarBody⟩ := Bool.and_eq_true_iff.mp hbarA
    have htne : t ≠ var := by simp only [bne_iff_ne, ne_eq] at hvart; exact fun h => hvart h.symm
    have hmu_t_bar : notBoundAt var (.mu t body) = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvart, hbarBody⟩
    have ha_subst := mu_substitute_ne t body var repl htvar
    have hb_subst : (LocalTypeR.send p bs).substitute var repl = .send p (LocalTypeR.substituteBranches bs var repl) := rfl
    -- Use EQ2F reduction lemma
    simp only [EQ2F_mu_send] at hf
    simp only [ha_subst, hb_subst, EQ2F_mu_send]
    rw [subst_mu_comm body var t repl hbarBody hfresh htne]
    apply Or.inl
    have hsr : SubstRel var repl ((body.substitute t (.mu t body)).substitute var repl)
        ((LocalTypeR.send p bs).substitute var repl) :=
      SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.send p bs) hf
        (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
        hbarB_orig
    rw [hb_subst] at hsr
    exact hsr
  case mu.recv t body p bs =>
    have htvar := bne_of_notBoundAt_mu hbarA
    have hbarB_orig := hbarB  -- Save before unfolding
    unfold notBoundAt at hbarA hbarB
    have ⟨hvart, hbarBody⟩ := Bool.and_eq_true_iff.mp hbarA
    have htne : t ≠ var := by simp only [bne_iff_ne, ne_eq] at hvart; exact fun h => hvart h.symm
    have hmu_t_bar : notBoundAt var (.mu t body) = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvart, hbarBody⟩
    have ha_subst := mu_substitute_ne t body var repl htvar
    have hb_subst : (LocalTypeR.recv p bs).substitute var repl = .recv p (LocalTypeR.substituteBranches bs var repl) := rfl
    -- Use EQ2F reduction lemma
    simp only [EQ2F_mu_recv] at hf
    simp only [ha_subst, hb_subst, EQ2F_mu_recv]
    rw [subst_mu_comm body var t repl hbarBody hfresh htne]
    apply Or.inl
    have hsr : SubstRel var repl ((body.substitute t (.mu t body)).substitute var repl)
        ((LocalTypeR.recv p bs).substitute var repl) :=
      SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.recv p bs) hf
        (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
        hbarB_orig
    rw [hb_subst] at hsr
    exact hsr
  -- end-mu (unfolding on right)
  case end.mu s body' =>
    have hsvar := bne_of_notBoundAt_mu hbarB
    unfold notBoundAt at hbarB
    have ⟨hvars, hbarBody'⟩ := Bool.and_eq_true_iff.mp hbarB
    have hsne : s ≠ var := by simp only [bne_iff_ne, ne_eq] at hvars; exact fun h => hvars h.symm
    have hmu_s_bar : notBoundAt var (.mu s body') = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvars, hbarBody'⟩
    have ha_subst : LocalTypeR.end.substitute var repl = .end := rfl
    have hb_subst := mu_substitute_ne s body' var repl hsvar
    -- Use EQ2F reduction lemma
    simp only [EQ2F_end_mu] at hf
    simp only [ha_subst, hb_subst, EQ2F_end_mu]
    rw [subst_mu_comm body' var s repl hbarBody' hfresh hsne]
    apply Or.inl
    have hsr : SubstRel var repl (LocalTypeR.end.substitute var repl)
        ((body'.substitute s (.mu s body')).substitute var repl) :=
      SubstRel.base LocalTypeR.end (body'.substitute s (.mu s body')) hf
        (by rfl : notBoundAt var LocalTypeR.end = true)
        (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
    rw [ha_subst] at hsr
    exact hsr
  case var.mu v s body' =>
    have hsvar := bne_of_notBoundAt_mu hbarB
    unfold notBoundAt at hbarB
    have ⟨hvars, hbarBody'⟩ := Bool.and_eq_true_iff.mp hbarB
    have hsne : s ≠ var := by simp only [bne_iff_ne, ne_eq] at hvars; exact fun h => hvars h.symm
    have hmu_s_bar : notBoundAt var (.mu s body') = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvars, hbarBody'⟩
    have hb_subst := mu_substitute_ne s body' var repl hsvar
    -- Use EQ2F reduction lemma
    simp only [EQ2F_var_mu] at hf
    by_cases hv : v == var
    · -- v == var: LHS substitutes to repl
      have ha_subst := var_substitute_eq v var repl hv
      -- repl is arbitrary, so we need to case-split on its constructor
      cases repl with
      | «end» =>
        simp only [ha_subst, hb_subst, EQ2F_end_mu]
        rw [subst_mu_comm body' var s (.end) hbarBody' (by intro t'; exact hfresh t') hsne]
        apply Or.inl
        have hsr : SubstRel var .end ((LocalTypeR.var v).substitute var .end)
            ((body'.substitute s (.mu s body')).substitute var .end) :=
          SubstRel.base (LocalTypeR.var v) (body'.substitute s (.mu s body')) hf
            (by rfl : notBoundAt var (LocalTypeR.var v) = true)
            (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
        rw [var_substitute_eq v var .end hv] at hsr
        exact hsr
      | var w =>
        simp only [ha_subst, hb_subst, EQ2F_var_mu]
        rw [subst_mu_comm body' var s (.var w) hbarBody' (by intro t'; exact hfresh t') hsne]
        apply Or.inl
        have hsr : SubstRel var (.var w) ((LocalTypeR.var v).substitute var (.var w))
            ((body'.substitute s (.mu s body')).substitute var (.var w)) :=
          SubstRel.base (LocalTypeR.var v) (body'.substitute s (.mu s body')) hf
            (by rfl : notBoundAt var (LocalTypeR.var v) = true)
            (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
        rw [var_substitute_eq v var (.var w) hv] at hsr
        exact hsr
      | send p bs =>
        simp only [ha_subst, hb_subst, EQ2F_send_mu]
        rw [subst_mu_comm body' var s (.send p bs) hbarBody' (by intro t'; exact hfresh t') hsne]
        apply Or.inl
        have hsr : SubstRel var (.send p bs) ((LocalTypeR.var v).substitute var (.send p bs))
            ((body'.substitute s (.mu s body')).substitute var (.send p bs)) :=
          SubstRel.base (LocalTypeR.var v) (body'.substitute s (.mu s body')) hf
            (by rfl : notBoundAt var (LocalTypeR.var v) = true)
            (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
        rw [var_substitute_eq v var (.send p bs) hv] at hsr
        exact hsr
      | recv p bs =>
        simp only [ha_subst, hb_subst, EQ2F_recv_mu]
        rw [subst_mu_comm body' var s (.recv p bs) hbarBody' (by intro t'; exact hfresh t') hsne]
        apply Or.inl
        have hsr : SubstRel var (.recv p bs) ((LocalTypeR.var v).substitute var (.recv p bs))
            ((body'.substitute s (.mu s body')).substitute var (.recv p bs)) :=
          SubstRel.base (LocalTypeR.var v) (body'.substitute s (.mu s body')) hf
            (by rfl : notBoundAt var (LocalTypeR.var v) = true)
            (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
        rw [var_substitute_eq v var (.recv p bs) hv] at hsr
        exact hsr
      | mu t body =>
        -- mu-mu case: need both directions
        simp only [ha_subst, hb_subst, EQ2F]
        constructor
        · -- left goal: (body.subst t (.mu t body)) relates to (.mu s (body'.subst var (.mu t body)))
          -- SubstRel.base gives us: SubstRel (.mu t body) (.mu s (body'.subst var repl))
          -- We need to unfold the LHS: (.mu t body).unfold = body.subst t (.mu t body)
          apply Or.inl
          have hab : EQ2 (.var v) (.mu s body') := by
            apply EQ2.construct
            simp only [EQ2F_var_mu]
            exact hf
          have hsr_base : SubstRel var (LocalTypeR.mu t body)
              ((LocalTypeR.var v).substitute var (LocalTypeR.mu t body))
              ((LocalTypeR.mu s body').substitute var (LocalTypeR.mu t body)) :=
            SubstRel.base (LocalTypeR.var v) (LocalTypeR.mu s body') hab (by rfl : notBoundAt var (LocalTypeR.var v) = true) hmu_s_bar
          -- Reduce substitutions in hsr_base's type
          have hvar_subst : (LocalTypeR.var v).substitute var (LocalTypeR.mu t body)
              = LocalTypeR.mu t body :=
            var_substitute_eq v var (LocalTypeR.mu t body) hv
          have hmu_subst : (LocalTypeR.mu s body').substitute var (LocalTypeR.mu t body)
              = LocalTypeR.mu s (body'.substitute var (LocalTypeR.mu t body)) :=
            mu_substitute_ne s body' var (LocalTypeR.mu t body) hsvar
          -- The types are definitionally equal after reducing substitute
          -- Use cast with Eq.mpr to convert between them
          have hsr : SubstRel var (LocalTypeR.mu t body)
              (LocalTypeR.mu t body)
              (LocalTypeR.mu s (body'.substitute var (LocalTypeR.mu t body))) := by
            have heq : SubstRel var (LocalTypeR.mu t body)
                ((LocalTypeR.var v).substitute var (LocalTypeR.mu t body))
                ((LocalTypeR.mu s body').substitute var (LocalTypeR.mu t body))
              = SubstRel var (LocalTypeR.mu t body)
                (LocalTypeR.mu t body)
                (LocalTypeR.mu s (body'.substitute var (LocalTypeR.mu t body))) := by
              rw [hvar_subst, hmu_subst]
            exact heq ▸ hsr_base
          -- Apply unfold_left: (.mu t body).unfold = body.substitute t (.mu t body)
          have hsr' := SubstRel.unfold_left hsr
          -- Reduce the unfold in the type
          simp only [LocalTypeR.unfold] at hsr'
          exact hsr'
        · -- right goal: (.mu t body) relates to (body'.subst s (.mu s body')).subst var (.mu t body)
          rw [subst_mu_comm body' var s (.mu t body) hbarBody' (by intro t'; exact hfresh t') hsne]
          apply Or.inl
          have hsr : SubstRel var (.mu t body) ((LocalTypeR.var v).substitute var (.mu t body))
              ((body'.substitute s (.mu s body')).substitute var (.mu t body)) :=
            SubstRel.base (LocalTypeR.var v) (body'.substitute s (.mu s body')) hf
              (by rfl : notBoundAt var (LocalTypeR.var v) = true)
              (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
          rw [var_substitute_eq v var (.mu t body) hv] at hsr
          exact hsr
    · -- v != var: LHS stays as .var v
      have hv' : (v == var) = false := by cases h : v == var <;> simp_all
      have ha_subst := var_substitute_ne v var repl hv'
      simp only [ha_subst, hb_subst, EQ2F_var_mu]
      rw [subst_mu_comm body' var s repl hbarBody' hfresh hsne]
      apply Or.inl
      have hsr : SubstRel var repl ((LocalTypeR.var v).substitute var repl)
          ((body'.substitute s (LocalTypeR.mu s body')).substitute var repl) :=
        SubstRel.base (LocalTypeR.var v) (body'.substitute s (LocalTypeR.mu s body')) hf
          (by rfl : notBoundAt var (LocalTypeR.var v) = true)
          (notBoundAt_subst var s body' (LocalTypeR.mu s body') hbarBody' hmu_s_bar)
      rw [ha_subst] at hsr
      exact hsr
  case send.mu p bs s body' =>
    have hsvar := bne_of_notBoundAt_mu hbarB
    have hbarA_orig := hbarA  -- Save original before unfolding
    unfold notBoundAt at hbarA hbarB
    have ⟨hvars, hbarBody'⟩ := Bool.and_eq_true_iff.mp hbarB
    have hsne : s ≠ var := by simp only [bne_iff_ne, ne_eq] at hvars; exact fun h => hvars h.symm
    have hmu_s_bar : notBoundAt var (.mu s body') = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvars, hbarBody'⟩
    have ha_subst : (LocalTypeR.send p bs).substitute var repl = .send p (LocalTypeR.substituteBranches bs var repl) := rfl
    have hb_subst := mu_substitute_ne s body' var repl hsvar
    -- Use EQ2F reduction lemma
    simp only [EQ2F_send_mu] at hf
    simp only [ha_subst, hb_subst, EQ2F_send_mu]
    rw [subst_mu_comm body' var s repl hbarBody' hfresh hsne]
    apply Or.inl
    have hsr : SubstRel var repl ((LocalTypeR.send p bs).substitute var repl)
        ((body'.substitute s (.mu s body')).substitute var repl) :=
      SubstRel.base (LocalTypeR.send p bs) (body'.substitute s (.mu s body')) hf
        hbarA_orig
        (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
    rw [ha_subst] at hsr
    exact hsr
  case recv.mu p bs s body' =>
    have hsvar := bne_of_notBoundAt_mu hbarB
    have hbarA_orig := hbarA  -- Save original before unfolding
    unfold notBoundAt at hbarA hbarB
    have ⟨hvars, hbarBody'⟩ := Bool.and_eq_true_iff.mp hbarB
    have hsne : s ≠ var := by simp only [bne_iff_ne, ne_eq] at hvars; exact fun h => hvars h.symm
    have hmu_s_bar : notBoundAt var (.mu s body') = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvars, hbarBody'⟩
    have ha_subst : (LocalTypeR.recv p bs).substitute var repl = .recv p (LocalTypeR.substituteBranches bs var repl) := rfl
    have hb_subst := mu_substitute_ne s body' var repl hsvar
    -- Use EQ2F reduction lemma
    simp only [EQ2F_recv_mu] at hf
    simp only [ha_subst, hb_subst, EQ2F_recv_mu]
    rw [subst_mu_comm body' var s repl hbarBody' hfresh hsne]
    apply Or.inl
    have hsr : SubstRel var repl ((LocalTypeR.recv p bs).substitute var repl)
        ((body'.substitute s (.mu s body')).substitute var repl) :=
      SubstRel.base (LocalTypeR.recv p bs) (body'.substitute s (.mu s body')) hf
        hbarA_orig
        (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
    rw [ha_subst] at hsr
    exact hsr
  -- Impossible cases (structurally incompatible constructors)
  case end.var | end.send | end.recv =>
    unfold EQ2F at hf; exact hf.elim
  case var.end | var.send | var.recv =>
    unfold EQ2F at hf; exact hf.elim
  case send.end | send.var | send.recv =>
    unfold EQ2F at hf; exact hf.elim
  case recv.end | recv.var | recv.send =>
    unfold EQ2F at hf; exact hf.elim

/-! ## Main Theorem -/

/-- EQ2 is preserved under substitution when Barendregt conditions hold.

    This theorem requires:
    - `notBoundAt var a = true` and `notBoundAt var b = true`: var is not used as a binder
    - `hfresh`: repl is closed (no free variables)
    - `hnomu`: repl is not a mu type at top level (needed for unfold_subst_eq_subst_unfold)

    For general EQ2_substitute without the hnomu restriction, use the Bisim approach
    in `EQ2_substitute_via_Bisim` (Bisim.lean) which uses EQ2 instead of syntactic equality. -/
theorem EQ2_substitute_barendregt (a b : LocalTypeR) (var : String) (repl : LocalTypeR)
    (h : EQ2 a b)
    (hbarA : notBoundAt var a = true)
    (hbarB : notBoundAt var b = true)
    (hfresh : ∀ t, isFreeIn t repl = false)
    (hnomu : ∀ t body, repl ≠ .mu t body) :
    EQ2 (a.substitute var repl) (b.substitute var repl) := by
  apply EQ2_coind_upto (R := SubstRel var repl)
  · intro x y hsr
    obtain ⟨a', b', hab', hbarA', hbarB', hx, hy⟩ := hsr.flatten hfresh hnomu
    subst hx hy
    have hf : EQ2F EQ2 a' b' := EQ2.destruct hab'
    exact SubstRel_postfix_standard var repl a' b' hab' hbarA' hbarB' hfresh hf
  · exact SubstRel.base a b h hbarA hbarB

end RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt
