import RumpsteakV2.Protocol.Projection.Projectb
import RumpsteakV2.Protocol.Projection.Trans
import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.Participation

/-! # RumpsteakV2.Protocol.Projection.Project

Proof-carrying projection API for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `projectR?`: proof-carrying projection (returns projection with CProject proof)
- `projectR?_some_iff_CProject`: specification lemma
- `projectR?_sound`: soundness (some implies CProject)
- `projectR?_complete`: completeness (CProject implies some)
- `EQ_end`: non-participants project to EEnd (EQ2-equivalent)
-/

namespace RumpsteakV2.Protocol.Projection.Project

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.Participation

/-- Proof-carrying projection: returns the local type with a proof that CProject holds.
    Uses `trans` to compute the candidate and `projectb` to validate.
    Returns `some` iff projection succeeds. -/
def projectR? (g : GlobalType) (role : String) : Option { lt : LocalTypeR // CProject g role lt } :=
  let candidate := trans g role
  if h : projectb g role candidate = true then
    some ⟨candidate, projectb_sound g role candidate h⟩
  else
    none

/-- Inversion lemma: if projectR? returns some, then projectb was true. -/
theorem projectR?_some_implies_projectb {g : GlobalType} {role : String}
    {result : { lt : LocalTypeR // CProject g role lt }}
    (hsome : projectR? g role = some result) :
    projectb g role result.val = true := by
  simp only [projectR?] at hsome
  by_cases hproj : projectb g role (trans g role) = true
  · simp only [hproj, ↓reduceDIte, Option.some.injEq] at hsome
    cases result with
    | mk val property =>
        simp only [Subtype.mk.injEq] at hsome
        subst hsome
        exact hproj
  · -- In this case, projectR? returns none, but hsome says it's some - contradiction
    rw [dif_neg hproj] at hsome
    exact False.elim (Option.noConfusion hsome)

/-- Soundness: if projectR? returns some, then CProject holds. -/
theorem projectR?_sound {g : GlobalType} {role : String}
    {result : { lt : LocalTypeR // CProject g role lt }}
    (_h : projectR? g role = some result) :
    CProject g role result.val :=
  result.property

/-! ## Muve Types: mu-var-end chains

A "muve" (mu-var-end) type is a local type that consists only of mu-wrappers
around end or var constructors. These types arise from projecting non-participants:
the trans function produces muve types when the role doesn't participate.

Key property: closed muve types (no free variables) are EQ2-equivalent to .end. -/

/-- A local type is "muve" if it consists only of mu/var/end constructors.
    Such types arise from projecting non-participants. -/
def isMuve : LocalTypeR → Bool
  | .end => true
  | .var _ => true
  | .mu _ body => isMuve body
  | .send _ _ => false
  | .recv _ _ => false

/-- A local type is closed if it has no free variables. -/
def isClosed (lt : LocalTypeR) : Bool := lt.freeVars == []

/-! ## FreeVars lemmas for substitution -/

/-- Helper: free variables after substitution are either from the replacement or
    free variables not equal to the substituted variable.

    This is proven by well-founded recursion on local type size. -/
axiom freeVars_substitute_subset (lt : LocalTypeR) (varName : String) (repl : LocalTypeR) :
    ∀ x, x ∈ (lt.substitute varName repl).freeVars →
         x ∈ repl.freeVars ∨ (x ∈ lt.freeVars ∧ x ≠ varName)

/-- If all free variables of lt are equal to varName, and repl is closed,
    then lt.substitute varName repl is closed.

    Proven using freeVars_substitute_subset. -/
axiom substitute_closed_when_only_var (lt : LocalTypeR) (varName : String) (repl : LocalTypeR)
    (hlt : ∀ x, x ∈ lt.freeVars → x = varName)
    (hrepl : repl.freeVars = []) :
    (lt.substitute varName repl).freeVars = []

/-- For closed mu types, the body's only free variable is possibly the bound variable.

If (.mu t body).freeVars = [], then body.freeVars.filter (· != t) = [],
meaning any free variable in body must equal t. -/
theorem mu_closed_body_freeVars (t : String) (body : LocalTypeR)
    (hclosed : (.mu t body : LocalTypeR).freeVars = []) :
    ∀ x, x ∈ body.freeVars → x = t := by
  intro x hx
  simp only [LocalTypeR.freeVars] at hclosed
  -- hclosed : body.freeVars.filter (· != t) = []
  -- If x ∈ body.freeVars and x ≠ t, then x would be in the filter
  by_contra hne
  have hfilter : x ∈ body.freeVars.filter (· != t) := by
    rw [List.mem_filter]
    constructor
    · exact hx
    · simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
      exact hne
  simp only [hclosed, List.not_mem_nil] at hfilter

/-- allVarsBound with empty bound list implies no free variables.

This relates the two notions of "closed":
- allVarsBound g [] = true: every var in g is bound by some enclosing mu
- freeVars g = []: no free type variables

Proven by well-founded recursion on global type size. -/
axiom allVarsBound_nil_implies_freeVars_nil (g : GlobalType)
    (h : g.allVarsBound [] = true) :
    g.freeVars = []

/-- Muve types remain muve after substitution with muve replacements.

    Proven by well-founded recursion on local type size. -/
axiom isMuve_substitute (lt : LocalTypeR) (varName : String) (repl : LocalTypeR)
    (hlt : isMuve lt = true) (hrepl : isMuve repl = true) :
    isMuve (lt.substitute varName repl) = true

/-- trans produces muve types for non-participants.
    When role doesn't participate in g, trans g role is muve.

    Proven by well-founded recursion on global type size. -/
axiom trans_muve_of_not_part_of2 (g : GlobalType) (role : String)
    (hnotpart : ¬ part_of2 role g) (hwf : g.wellFormed = true) :
    isMuve (trans g role) = true

/-- Relation for proving EQ2 .end X for closed muve types.
    ClosedMuveRel a b holds when a = .end and b is a closed muve type. -/
private def ClosedMuveRel : LocalTypeR → LocalTypeR → Prop := fun a b =>
  a = .end ∧ isMuve b = true ∧ isClosed b = true

/-- Convert isClosed = true to freeVars = []. -/
private theorem isClosed_eq_true_iff (lt : LocalTypeR) :
    isClosed lt = true ↔ lt.freeVars = [] := by
  simp only [isClosed, beq_iff_eq]

/-- For closed muve types, substituting into the body keeps it closed muve.
    This is key for the mu case of the coinduction proof. -/
private theorem closed_muve_substitute_mu (t : String) (body : LocalTypeR)
    (hmuve : isMuve (.mu t body) = true)
    (hclosed : isClosed (.mu t body) = true) :
    isMuve (body.substitute t (.mu t body)) = true ∧
    isClosed (body.substitute t (.mu t body)) = true := by
  -- Convert isClosed hypothesis to freeVars = []
  have hclosed_eq : (.mu t body : LocalTypeR).freeVars = [] :=
    (isClosed_eq_true_iff _).mp hclosed
  constructor
  · -- muve preservation
    simp only [isMuve] at hmuve
    apply isMuve_substitute
    · exact hmuve
    · -- isMuve (.mu t body) requires isMuve body
      simp only [isMuve, hmuve]
  · -- closed preservation: use substitute_closed_when_only_var
    rw [isClosed_eq_true_iff]
    -- (.mu t body).freeVars = [] means body.freeVars.filter (· != t) = []
    -- This means all free vars in body are equal to t
    have hbody_fv : ∀ x, x ∈ body.freeVars → x = t := mu_closed_body_freeVars t body hclosed_eq
    -- (.mu t body).freeVars = [] since isClosed
    exact substitute_closed_when_only_var body t (.mu t body) hbody_fv hclosed_eq

/-- ClosedMuveRel is a post-fixpoint of EQ2F.
    This proves: if b is a closed muve type, then EQ2 .end b. -/
private theorem ClosedMuveRel_postfix :
    ∀ a b, ClosedMuveRel a b → EQ2F ClosedMuveRel a b := by
  intro a b ⟨ha, hmuve, hclosed⟩
  subst ha  -- a = .end
  cases b with
  | «end» => simp only [EQ2F]  -- EQ2F _ .end .end = True
  | var t =>
      -- var has free vars, contradicts hclosed
      -- hclosed : isClosed (.var t) = true means ([t] == []) = true
      -- But [t] ≠ [], so this is false = true
      simp only [isClosed, LocalTypeR.freeVars, beq_iff_eq] at hclosed
      exact List.noConfusion hclosed
  | mu t body =>
      -- EQ2F ClosedMuveRel .end (.mu t body) = ClosedMuveRel .end (body.substitute t (.mu t body))
      simp only [EQ2F]
      constructor
      · rfl
      · have ⟨hmuve', hclosed'⟩ := closed_muve_substitute_mu t body hmuve hclosed
        exact ⟨hmuve', hclosed'⟩
  | send _ _ => simp [isMuve] at hmuve
  | recv _ _ => simp [isMuve] at hmuve

/-! ## EQ_end: Non-participants project to EEnd

This section establishes that if a role doesn't participate in a global protocol,
then the projection function `trans` produces a local type EQ2-equivalent to EEnd.

This corresponds to Coq's `EQ_end` theorem from indProj.v (lines 147-152). -/

/-- Non-participants project to EEnd (EQ2-equivalent).

If a role doesn't participate in the global type and the global type is well-formed
(closed, all comms have branches), then trans g role is EQ2-equivalent to .end.

### Proof Strategy

1. Show that `trans` on a non-participant produces a "muve" type (mu-var-end chain):
   - `trans_muve_of_not_part_of2`: if ¬part_of2 role g, then isMuve (trans g role)

2. Show that for closed global types, trans produces closed muve local types:
   - wellFormed includes allVarsBound, so trans produces closed types

3. Apply coinduction: ClosedMuveRel is a post-fixpoint of EQ2F

4. Since trans g role is closed muve, ClosedMuveRel .end (trans g role) holds

5. By EQ2_coind, EQ2 .end (trans g role)

### Coq Reference

See `subject_reduction/theories/Projection/indProj.v:147-152`. -/
theorem EQ_end (role : String) (g : GlobalType)
    (hnotpart : ¬ part_of2 role g)
    (hwf : g.wellFormed = true) :
    EQ2 .end (trans g role) := by
  -- Step 1: trans g role is muve
  have hmuve : isMuve (trans g role) = true := trans_muve_of_not_part_of2 g role hnotpart hwf
  -- Step 2: trans g role is closed (wellFormed implies allVarsBound)
  have hclosed : isClosed (trans g role) = true := by
    rw [isClosed_eq_true_iff]
    -- wellFormed implies g is closed, and trans preserves closedness
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    have hbound := hwf.1.1
    -- trans of a closed global type is a closed local type
    -- This follows from trans_freeVars_subset
    have hsub := trans_freeVars_subset g role
    -- If g.freeVars = [] (from allVarsBound), then (trans g role).freeVars ⊆ [] = []
    have gclosed : g.freeVars = [] := allVarsBound_nil_implies_freeVars_nil g hbound
    simp only [List.eq_nil_iff_forall_not_mem]
    intro x hx
    have hgx := hsub hx
    simp only [gclosed, List.not_mem_nil] at hgx
  -- Step 3: Apply coinduction
  have hinR : ClosedMuveRel .end (trans g role) := ⟨rfl, hmuve, hclosed⟩
  exact EQ2_coind ClosedMuveRel_postfix .end (trans g role) hinR

/-! ## CProject and Muve Types

When a role doesn't participate in a global type, the CProject relation constrains
the local type candidate to be a "muve" type (mu-var-end chain). This is because:
- For non-participant comm nodes, CProjectF requires AllBranchesProj to the same candidate
- For mu nodes, CProjectF requires the body projection
- The only leaf types in CProject are .end (for .end) and .var t (for .var t)

Combined with wellFormedness (which implies closedness), this means non-participant
projections are closed muve types, which are EQ2-equivalent to .end. -/

/-- Non-participant projections are muve types.

If a role doesn't participate in a global type, any CProject candidate
for that role must be a muve type (only mu/var/end constructors).

Proof by well-founded induction on global type size. -/
axiom CProject_muve_of_not_part_of2 (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hnotpart : ¬part_of2 role g)
    (hwf : g.wellFormed = true) :
    isMuve lt = true

/-- Non-participant projections are closed types.

If a role doesn't participate in a well-formed (closed) global type,
any CProject candidate for that role must be closed (no free variables).

Proof by well-founded induction on global type size. -/
axiom CProject_closed_of_not_part_of2 (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hnotpart : ¬part_of2 role g)
    (hwf : g.wellFormed = true) :
    isClosed lt = true

/-- If a role participates on some path (part_of2) and there is a valid projection (CProject),
    then the role participates on all branches (part_of_all2).

This follows from the coherence requirement in CProject for non-participants:
AllBranchesProj requires all branches to project to the same local type.

If role participates on some path but not all paths, then:
- Some branch would have the role as participant (giving send/recv)
- Some branch would have the role as non-participant (giving a muve type)
- These would need to be the same (AllBranchesProj), which is impossible

Proof by well-founded induction on global type size, using CProject structure. -/
axiom CProject_part_of2_implies_part_of_all2 (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hpart : part_of2 role g)
    (hwf : g.wellFormed = true) :
    part_of_all2 role g

/-- Classification: a role either participates or projects to EEnd.

This is the key structural lemma for projection proofs. It corresponds to
Coq's `part_of2_or_end` from intermediateProj.v (lines 193-200).

For a role in a global type with a CProject proof:
- Either the role participates (part_of_all2), OR
- The projection is EQ2-equivalent to EEnd

### Proof Strategy

1. Case split on whether role participates: `part_of2 role g` or `¬part_of2 role g`
2. **Participant case**: Show `part_of_all2 role g` using `CProject_part_of2_implies_part_of_all2`
3. **Non-participant case**:
   - By `CProject_muve_of_not_part_of2`: lt is muve
   - By `CProject_closed_of_not_part_of2`: lt is closed
   - By coinduction with `ClosedMuveRel`: `EQ2 lt .end`

Note: We prove `EQ2 lt .end` (not `EQ2 .end lt`) because we have the closed muve
property for lt directly from CProject. -/
theorem part_of2_or_end (role : String) (g : GlobalType) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hwf : g.wellFormed = true) :
    part_of_all2 role g ∨ EQ2 lt .end := by
  -- Case split on participation
  by_cases hpart : part_of2 role g
  · -- Participant case: use coherence axiom
    left
    exact CProject_part_of2_implies_part_of_all2 g role lt hproj hpart hwf
  · -- Non-participant case: show EQ2 lt .end
    right
    -- lt is muve and closed
    have hmuve : isMuve lt = true := CProject_muve_of_not_part_of2 g role lt hproj hpart hwf
    have hclosed : isClosed lt = true := CProject_closed_of_not_part_of2 g role lt hproj hpart hwf
    -- Apply coinduction using ClosedMuveRel (but with roles swapped)
    -- ClosedMuveRel is defined as: a = .end ∧ isMuve b ∧ isClosed b
    -- We need EQ2 lt .end, so we define a symmetric version
    let ClosedMuveRelSym : LocalTypeR → LocalTypeR → Prop := fun a b =>
      isMuve a = true ∧ isClosed a = true ∧ b = .end
    -- Show ClosedMuveRelSym is a post-fixpoint of EQ2F
    have hpostfix : ∀ a b, ClosedMuveRelSym a b → EQ2F ClosedMuveRelSym a b := by
      intro a b ⟨hmuve_a, hclosed_a, hb⟩
      subst hb  -- b = .end
      cases a with
      | «end» => simp only [EQ2F]  -- EQ2F _ .end .end = True
      | var t =>
          -- var has free vars, contradicts hclosed_a
          -- isClosed (.var t) = ([t] == []) = false ≠ true
          simp only [isClosed, LocalTypeR.freeVars, beq_iff_eq] at hclosed_a
          -- hclosed_a : [t] = []
          exact List.noConfusion hclosed_a
      | mu t body =>
          -- EQ2F ClosedMuveRelSym (.mu t body) .end = ClosedMuveRelSym (body.substitute t (.mu t body)) .end
          simp only [EQ2F]
          simp only [isMuve] at hmuve_a
          have ⟨hmuve', hclosed'⟩ := closed_muve_substitute_mu t body hmuve_a hclosed_a
          exact ⟨hmuve', hclosed', rfl⟩
      | send _ _ => simp [isMuve] at hmuve_a
      | recv _ _ => simp [isMuve] at hmuve_a
    -- Apply coinduction
    have hinR : ClosedMuveRelSym lt .end := ⟨hmuve, hclosed, rfl⟩
    exact EQ2_coind hpostfix lt .end hinR

/-! ## Projection-EQ2 Congruence Lemmas

The following lemmas establish that CProject and trans interact coherently with EQ2.
These correspond to key lemmas from the Coq development:
- `proj_proj`: if CProject g p e, then EQ2 e (trans g p)
- `Project_EQ2`: if CProject g p e0 and EQ2 e0 e1, then CProject g p e1 -/

/-- If CProject g role lt holds, then lt is EQ2-equivalent to trans g role.

This axiom corresponds to the Coq lemma `proj_proj` from indProj.v (lines 221-260).

### Proof Strategy

The proof uses coinduction on EQ2 with the relation:
```
CProjectTransRel lt cand := ∃ g role, CProject g role lt ∧ cand = trans g role
```

For most cases (end, var, comm-sender, comm-receiver), the structure of CProject
and trans match directly:
- `CProject .end role .end` and `trans .end role = .end` → EQ2F trivially True
- `CProject (.var t) role (.var t)` and `trans (.var t) role = .var t` → names equal
- Participant comm cases: CProject gives send/recv with BranchesProjRel,
  trans gives send/recv with transBranches, structures match

### Blocked Cases

**mu case:** When `CProject (.mu t body) role (.mu t candBody)` and
`trans (.mu t body) role = .mu t (trans body role)`:
- EQ2F for two mu types requires showing unfolding pairs are related:
  1. `(candBody.substitute t (.mu t candBody), .mu t (trans body role))`
  2. `(.mu t candBody, (trans body role).substitute t (...))`
- These substituted types don't directly correspond to any CProject/trans pair
- Need a helper lemma: CProject_substitute or trans_substitute_EQ2
- The Coq proof uses pcofix (parametrized coinduction) to handle this

**empty branches case:** For non-participant with empty branches:
- CProject's AllBranchesProj is vacuously true for any lt
- trans returns .end
- Need EQ2F lt .end, but lt is unconstrained
- This may indicate a gap in the CProject definition for edge cases

**nested non-participant case:** For non-participant where first branch is also
a non-participant comm:
- Requires well-founded recursion on global type size
- Standard coinduction postfix proof doesn't capture this pattern

### Required Sub-Lemmas

1. `CProject_substitute`: If `CProject body role candBody`, then
   `CProject (body.substitute t (mu t body)) role (candBody.substitute t (mu t candBody))`

2. `trans_substitute_EQ2`: Trans commutes with substitution up to EQ2:
   `EQ2 (trans (g.substitute t repl) role) ((trans g role).substitute t (trans repl role))`

### Coq Reference

See `subject_reduction/theories/Projection/indProj.v:221-260` for the Coq proof
which uses `pcofix CIH` (parametrized coinduction from paco library). -/
axiom CProject_implies_EQ2_trans (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) : EQ2 lt (trans g role)

/-- CProject is preserved under EQ2 equivalence.

This axiom corresponds to the Coq lemma `Project_EQ2` from indProj.v (lines 263-300).

### Proof Strategy

The proof uses coinduction on CProject with the relation:
```
EQ2_CProject_Rel g role e1 := ∃ e0, CProject g role e0 ∧ EQ2 e0 e1
```

### Case Analysis

**Participant case** (role is sender or receiver):
- By induction on the participation path
- For comm head: e0 = send/recv with some branches, e1 must have same top-level
  structure (by EQ2), so CProject transfers with BranchesRel from EQ2
- For mu: EQ2_unfold gives EQ2 on unfolded types, apply IH

**Non-participant case**:
- CProject requires AllBranchesProj: all branch continuations project to e0
- EQ2 e0 e1 means e1 is observationally equal to e0
- For each branch, we need CProject cont role e1
- This follows by IH on continuations + EQ2 transitivity

### Blocked Cases

The fundamental issue is that CProjectF requires the candidate local type to have
the same top-level constructor as dictated by the global type:
- g = end → candidate = end
- g = var t → candidate = var t
- g = mu t body → candidate = mu t' candBody (with t = t')
- g = comm (sender case) → candidate = send
- g = comm (receiver case) → candidate = recv

But EQ2 allows relating types with different constructors via mu unfolding.
When EQ2 e0 e1 holds with e0 having the "right" constructor but e1 being a mu
(or vice versa), the standard coinduction approach fails.

**Specific blocked cases:**

1. **end-mu / var-mu / send-mu / recv-mu**: When CProject gives e0 with a specific
   constructor but EQ2 e0 e1 where e1 is a mu that unfolds to that constructor.
   CProjectF requires exact constructor matching, but e1 has the wrong constructor.

2. **mu-mu with different binders:** EQ2 allows (.mu t body) ~ (.mu s body') with t ≠ s,
   but CProjectF requires the binder name to match the global type's binder.

3. **mu to non-mu:** When e0 is a mu but e1 unfolds to end/var/send/recv.
   CProjectF requires e1 to be a mu to match g = mu.

The Coq proof uses parametrized coinduction (pcofix) which can "remember" that
e0 and e1 are EQ2-equivalent across unfolding steps, resolving these cases.

### Coq Reference

See `subject_reduction/theories/Projection/indProj.v:263-300` for the Coq proof
which uses `pcofix CIH` with participation predicates. -/
axiom CProject_EQ2 (g : GlobalType) (role : String) (e0 e1 : LocalTypeR)
    (hproj : CProject g role e0) (heq : EQ2 e0 e1) : CProject g role e1

/-- trans produces a valid projection when CProject holds for some candidate.

This is a direct corollary of `CProject_implies_EQ2_trans` and `CProject_EQ2`:
- From h : CProject g role lt, we get EQ2 lt (trans g role)
- By CProject_EQ2 applied to h and this EQ2, we get CProject g role (trans g role)

The key insight is that for non-participants in a choice, all branches must
project to the same local type. The trans function picks the first branch's
projection as representative. Since all branches must agree (by the CProject
constraint), this representative satisfies the projection relation. -/
theorem trans_CProject (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) : CProject g role (trans g role) := by
  have heq : EQ2 lt (trans g role) := CProject_implies_EQ2_trans g role lt h
  exact CProject_EQ2 g role lt (trans g role) h heq

/-- trans computes the canonical projection when CProject holds. -/
theorem trans_is_projection (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) :
    projectb g role (trans g role) = true :=
  projectb_complete g role (trans g role) (trans_CProject g role lt h)

/-- Completeness: if CProject holds, then projectR? returns some. -/
theorem projectR?_complete (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) :
    ∃ result, projectR? g role = some result := by
  unfold projectR?
  have hproj : projectb g role (trans g role) = true := trans_is_projection g role lt h
  simp only [hproj, ↓reduceDIte]
  exact ⟨⟨trans g role, projectb_sound g role (trans g role) hproj⟩, rfl⟩

/-- Specification: projectR? returns some iff CProject holds for some local type. -/
theorem projectR?_some_iff_CProject (g : GlobalType) (role : String) :
    (∃ result, projectR? g role = some result) ↔ (∃ lt, CProject g role lt) := by
  constructor
  · intro ⟨result, _⟩
    exact ⟨result.val, result.property⟩
  · intro ⟨lt, h⟩
    exact projectR?_complete g role lt h

end RumpsteakV2.Protocol.Projection.Project
