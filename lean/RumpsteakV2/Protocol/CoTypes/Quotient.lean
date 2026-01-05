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

**Alternative Coq technique (full_eunf):** Coq also uses `full_eunf` which completely unfolds
all mu binders before comparing. The key lemma `full_eunf_subst` states that full unfolding
is invariant under mu unfolding: `full_eunf (μt.body) = full_eunf (body[t := μt.body])`.
This eliminates nested substitutions by reasoning about the "leaf" structure after all mus
are removed. Implementing this in Lean would require termination proofs on contractive depth.

### Semantic soundness

The axiom is semantically sound because:
- EQ2 represents observational equality of infinite trees
- Substitution is a structural transformation on trees
- If two trees are observationally equal, applying the same transformation
  to corresponding positions yields observationally equal results

### Coq reference

- `subject_reduction/theories/CoTypes/bisim.v` — EQ2 bisimulation using paco
- `subject_reduction/theories/CoTypes/coLocal.v:56` — `full_eunf_subst` lemma -/
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

/-- Relation for duality: pairs that are duals of EQ2-equivalent types. -/
private def DualRel : Rel := fun a' b' =>
  ∃ a b, EQ2 a b ∧ a' = a.dual ∧ b' = b.dual

/-- BranchesRel lifts through dualBranches. -/
private theorem BranchesRel_dualBranches {bs cs : List (Label × LocalTypeR)}
    (h : BranchesRel EQ2 bs cs) :
    BranchesRel DualRel (dualBranches bs) (dualBranches cs) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b as bs' hhead _ ih =>
      -- hhead : a.1 = b.1 ∧ EQ2 a.2 b.2
      -- Goal: label = label' ∧ DualRel cont.dual cont'.dual
      apply List.Forall₂.cons
      · exact ⟨hhead.1, ⟨a.2, b.2, hhead.2, rfl, rfl⟩⟩
      · exact ih

/-- Convert BranchesRel DualRel to BranchesRel (EQ2_closure DualRel). -/
private theorem BranchesRel_DualRel_to_closure {bs cs : List (Label × LocalTypeR)}
    (h : BranchesRel DualRel bs cs) :
    BranchesRel (EQ2_closure DualRel) bs cs := by
  exact List.Forall₂.imp (fun _ _ hxy => ⟨hxy.1, Or.inl hxy.2⟩) h

/-- DualRel is a post-fixpoint of EQ2F up to EQ2 closure.

The proof uses dual_substitute to handle the mu case. -/
private theorem DualRel_postfix_upto :
    ∀ a' b', DualRel a' b' → EQ2F (EQ2_closure DualRel) a' b' := by
  intro a' b' ⟨a, b, hab, ha', hb'⟩
  subst ha' hb'
  have hf : EQ2F EQ2 a b := EQ2.destruct hab
  -- Case split on the structure revealed by EQ2F
  cases a <;> cases b <;> simp only [EQ2F] at hf ⊢ <;> try exact hf
  -- send-send case
  case send.send p bs q cs =>
    obtain ⟨hp, hbranches⟩ := hf
    simp only [LocalTypeR.dual]
    exact ⟨hp, BranchesRel_DualRel_to_closure (BranchesRel_dualBranches hbranches)⟩
  -- recv-recv case
  case recv.recv p bs q cs =>
    obtain ⟨hp, hbranches⟩ := hf
    simp only [LocalTypeR.dual]
    exact ⟨hp, BranchesRel_DualRel_to_closure (BranchesRel_dualBranches hbranches)⟩
  -- mu-mu case
  case mu.mu t body s body' =>
    obtain ⟨hleft, hright⟩ := hf
    simp only [LocalTypeR.dual]
    -- Need to show DualRel or EQ2 on unfolded pairs
    constructor
    · -- Left: (body.dual.subst t (mu t body.dual), (mu s body'.dual))
      -- Use dual_substitute to rewrite, then DualRel with the original EQ2
      left
      use body.substitute t (.mu t body), .mu s body'
      refine ⟨hleft, ?_, rfl⟩
      exact (LocalTypeR.dual_substitute body t (.mu t body)).symm
    · -- Right: (mu t body.dual, body'.dual.subst s (mu s body'.dual))
      left
      use .mu t body, body'.substitute s (.mu s body')
      refine ⟨hright, rfl, ?_⟩
      exact (LocalTypeR.dual_substitute body' s (.mu s body')).symm
  -- mu-other cases (unfolding on left)
  case mu.end t body =>
    simp only [LocalTypeR.dual]
    left
    use body.substitute t (.mu t body), .end
    exact ⟨hf, (LocalTypeR.dual_substitute body t (.mu t body)).symm, rfl⟩
  case mu.var t body v =>
    simp only [LocalTypeR.dual]
    left
    use body.substitute t (.mu t body), .var v
    exact ⟨hf, (LocalTypeR.dual_substitute body t (.mu t body)).symm, rfl⟩
  case mu.send t body p bs =>
    simp only [LocalTypeR.dual]
    left
    use body.substitute t (.mu t body), .send p bs
    exact ⟨hf, (LocalTypeR.dual_substitute body t (.mu t body)).symm, rfl⟩
  case mu.recv t body p bs =>
    simp only [LocalTypeR.dual]
    left
    use body.substitute t (.mu t body), .recv p bs
    exact ⟨hf, (LocalTypeR.dual_substitute body t (.mu t body)).symm, rfl⟩
  -- other-mu cases (unfolding on right)
  case end.mu s body' =>
    simp only [LocalTypeR.dual]
    left
    use .end, body'.substitute s (.mu s body')
    exact ⟨hf, rfl, (LocalTypeR.dual_substitute body' s (.mu s body')).symm⟩
  case var.mu v s body' =>
    simp only [LocalTypeR.dual]
    left
    use .var v, body'.substitute s (.mu s body')
    exact ⟨hf, rfl, (LocalTypeR.dual_substitute body' s (.mu s body')).symm⟩
  case send.mu p bs s body' =>
    simp only [LocalTypeR.dual]
    left
    use .send p bs, body'.substitute s (.mu s body')
    exact ⟨hf, rfl, (LocalTypeR.dual_substitute body' s (.mu s body')).symm⟩
  case recv.mu p bs s body' =>
    simp only [LocalTypeR.dual]
    left
    use .recv p bs, body'.substitute s (.mu s body')
    exact ⟨hf, rfl, (LocalTypeR.dual_substitute body' s (.mu s body')).symm⟩

/-- Duality respects EQ2: if two types are EQ2-equivalent, their duals
    are also EQ2-equivalent.

This theorem uses coinduction up-to with the DualRel relation.
The key insight is that dual commutes with substitute (dual_substitute),
which allows handling the mu cases in the coinduction. -/
theorem EQ2_dual (a b : LocalTypeR)
    (h : EQ2 a b) : EQ2 a.dual b.dual := by
  apply EQ2_coind_upto DualRel_postfix_upto
  exact ⟨a, b, h, rfl, rfl⟩

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

### Proof sketch (by case analysis on t)

- end/var/send/recv: unfold is identity, trivial
- mu t body: requires coinductive reasoning on EQ2

This corresponds to the semantic property that substitution and unfolding
are confluent operations on infinite trees.

### Connection to Coq's `full_eunf_subst`

This is a single-step version of the Coq lemma `full_eunf_subst` (coLocal.v:56) which states:
  `full_eunf (μt.body) = full_eunf (body[t := μt.body])`

Where `full_eunf` completely unfolds all mu binders. Our axiom is weaker (single step vs full
unfolding) but sufficient when combined with coinduction on EQ2. -/
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
