import SessionCoTypes.Bisim.UnfoldingLemmas

/-! # SessionCoTypes.Bisim.Bisimulation

Defines BisimF functor and proves Bisim is an equivalence relation.
-/

/-
The Problem. Proving Bisim is an equivalence relation requires showing reflexivity,
symmetry, and transitivity. The functor `BisimF` must support these proofs while
handling mu-unfolding correctly via membership predicates.

Solution Structure. Defines `BisimF` using membership predicates (`UnfoldsToEnd`,
`CanSend`, etc.) instead of constructor matching. Proves reflexivity by case
analysis on observables, symmetry by flipping the relation, and transitivity by
leveraging that BisimF doesn't require matching intermediate constructors.
-/

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

namespace SessionCoTypes.Bisim
open SessionTypes.LocalTypeR
open SessionTypes.GlobalType
open SessionCoTypes.Observable
open SessionCoTypes.CoinductiveRel
/-! ## Bisimulation Relation

Key insight is to define the bisimulation functor using membership predicates,
not constructor matching. This avoids the quotient elimination issues that block
standard coinduction. -/

/-- Relation on local types. -/
abbrev Rel := LocalTypeR → LocalTypeR → Prop

/-- Branch-wise relation for bisimulation using List.Forall₂. -/
def BranchesRelBisim (R : Rel) (bs cs : List BranchR) : Prop :=
  List.Forall₂ (fun b c => b.1 = c.1 ∧ R b.2.2 c.2.2) bs cs

/-- One-step bisimulation functor using membership predicates.

    Unlike EQ2F which matches on constructors, BisimF uses the membership
    predicates to describe observable behavior. This allows the relation R
    to contain pairs of types with different constructors, as long as they
    have matching observable behavior. -/
inductive BisimF (R : Rel) : Rel where
  | eq_end {a b : LocalTypeR} :
      UnfoldsToEnd a → UnfoldsToEnd b → BisimF R a b
  | eq_var {a b : LocalTypeR} {v : String} :
      UnfoldsToVar a v → UnfoldsToVar b v → BisimF R a b
  | eq_send {a b : LocalTypeR} {partner : String} {bsa bsb : List BranchR} :
      CanSend a partner bsa → CanSend b partner bsb →
      BranchesRelBisim R bsa bsb →
      BisimF R a b
  | eq_recv {a b : LocalTypeR} {partner : String} {bsa bsb : List BranchR} :
      CanRecv a partner bsa → CanRecv b partner bsb →
      BranchesRelBisim R bsa bsb →
      BisimF R a b

/-- Unfold the left-hand side of a BisimF step. -/
theorem BisimF.unfold_left {R : Rel} {a b : LocalTypeR} (h : BisimF R a b) :
    BisimF R (LocalTypeR.unfold a) b := by
  cases h with
  | eq_end ha hb =>
      rcases UnfoldsToEnd.cases ha with ha_end | ⟨t, body, ha_mu, ha'⟩
      · simpa [LocalTypeR.unfold, ha_end] using (BisimF.eq_end ha hb)
      · subst ha_mu
        simpa [LocalTypeR.unfold] using (BisimF.eq_end ha' hb)
  | eq_var ha hb =>
      rcases UnfoldsToVar.cases ha with ha_var | ⟨t, body, ha_mu, ha'⟩
      · simpa [LocalTypeR.unfold, ha_var] using (BisimF.eq_var ha hb)
      · subst ha_mu
        simpa [LocalTypeR.unfold] using (BisimF.eq_var ha' hb)
  | eq_send ha hb hbr =>
      rcases CanSend.cases ha with ha_send | ⟨t, body, ha_mu, ha'⟩
      · simpa [LocalTypeR.unfold, ha_send] using (BisimF.eq_send ha hb hbr)
      · subst ha_mu
        simpa [LocalTypeR.unfold] using (BisimF.eq_send ha' hb hbr)
  | eq_recv ha hb hbr =>
      rcases CanRecv.cases ha with ha_recv | ⟨t, body, ha_mu, ha'⟩
      · simpa [LocalTypeR.unfold, ha_recv] using (BisimF.eq_recv ha hb hbr)
      · subst ha_mu
        simpa [LocalTypeR.unfold] using (BisimF.eq_recv ha' hb hbr)

/-- Unfold the right-hand side of a BisimF step. -/
theorem BisimF.unfold_right {R : Rel} {a b : LocalTypeR} (h : BisimF R a b) :
    BisimF R a (LocalTypeR.unfold b) := by
  cases h with
  | eq_end ha hb =>
      rcases UnfoldsToEnd.cases hb with hb_end | ⟨t, body, hb_mu, hb'⟩
      · simpa [LocalTypeR.unfold, hb_end] using (BisimF.eq_end ha hb)
      · subst hb_mu
        simpa [LocalTypeR.unfold] using (BisimF.eq_end ha hb')
  | eq_var ha hb =>
      rcases UnfoldsToVar.cases hb with hb_var | ⟨t, body, hb_mu, hb'⟩
      · simpa [LocalTypeR.unfold, hb_var] using (BisimF.eq_var ha hb)
      · subst hb_mu
        simpa [LocalTypeR.unfold] using (BisimF.eq_var ha hb')
  | eq_send ha hb hbr =>
      rcases CanSend.cases hb with hb_send | ⟨t, body, hb_mu, hb'⟩
      · simpa [LocalTypeR.unfold, hb_send] using (BisimF.eq_send ha hb hbr)
      · subst hb_mu
        simpa [LocalTypeR.unfold] using (BisimF.eq_send ha hb' hbr)
  | eq_recv ha hb hbr =>
      rcases CanRecv.cases hb with hb_recv | ⟨t, body, hb_mu, hb'⟩
      · simpa [LocalTypeR.unfold, hb_recv] using (BisimF.eq_recv ha hb hbr)
      · subst hb_mu
        simpa [LocalTypeR.unfold] using (BisimF.eq_recv ha hb' hbr)

/-- Unfold both sides of a BisimF step. -/
theorem BisimF.unfold {R : Rel} {a b : LocalTypeR} (h : BisimF R a b) :
    BisimF R (LocalTypeR.unfold a) (LocalTypeR.unfold b) := by
  exact BisimF.unfold_right (BisimF.unfold_left h)

/-- Unfold the left-hand side for n steps. -/
theorem BisimF.unfold_left_iter {R : Rel} {a b : LocalTypeR} :
    ∀ n, BisimF R a b → BisimF R ((LocalTypeR.unfold)^[n] a) b := by
  intro n h
  induction n generalizing a with
  | zero =>
      simpa [Function.iterate_zero, id_eq] using h
  | succ n ih =>
      have h' : BisimF R (LocalTypeR.unfold a) b := BisimF.unfold_left h
      have h'' : BisimF R ((LocalTypeR.unfold)^[n] (LocalTypeR.unfold a)) b :=
        ih (a := LocalTypeR.unfold a) h'
      simpa [Function.iterate_succ_apply] using h''

/-- Unfold the right-hand side for n steps. -/
theorem BisimF.unfold_right_iter {R : Rel} {a b : LocalTypeR} :
    ∀ n, BisimF R a b → BisimF R a ((LocalTypeR.unfold)^[n] b) := by
  intro n h
  induction n generalizing b with
  | zero =>
      simpa [Function.iterate_zero, id_eq] using h
  | succ n ih =>
      have h' : BisimF R a (LocalTypeR.unfold b) := BisimF.unfold_right h
      have h'' : BisimF R a ((LocalTypeR.unfold)^[n] (LocalTypeR.unfold b)) :=
        ih (b := LocalTypeR.unfold b) h'
      simpa [Function.iterate_succ_apply] using h''

/-- Unfold both sides for n steps. -/
theorem BisimF.unfold_iter {R : Rel} {a b : LocalTypeR} :
    ∀ n, BisimF R a b → BisimF R ((LocalTypeR.unfold)^[n] a) ((LocalTypeR.unfold)^[n] b) := by
  intro n h
  have h' : BisimF R ((LocalTypeR.unfold)^[n] a) b := BisimF.unfold_left_iter (n := n) h
  exact BisimF.unfold_right_iter (n := n) h'

/-- BranchesRelBisim is monotone. -/
theorem BranchesRelBisim.mono {R S : Rel} (hrs : ∀ a b, R a b → S a b)
    {bs cs : List BranchR} (h : BranchesRelBisim R bs cs) :
    BranchesRelBisim S bs cs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih =>
    exact List.Forall₂.cons ⟨hbc.1, hrs _ _ hbc.2⟩ ih

/-- BisimF is monotone. -/
theorem BisimF.mono : Monotone BisimF := by
  intro R S hrs a b h
  cases h with
  | eq_end ha hb => exact BisimF.eq_end ha hb
  | eq_var ha hb => exact BisimF.eq_var ha hb
  | eq_send ha hb hbr =>
    exact BisimF.eq_send ha hb (BranchesRelBisim.mono hrs hbr)
  | eq_recv ha hb hbr =>
    exact BisimF.eq_recv ha hb (BranchesRelBisim.mono hrs hbr)

instance : CoinductiveRel Rel BisimF := ⟨BisimF.mono⟩

Shared coinduction aliases (see `CoinductiveRel`). -/
/-- Greatest fixed point of BisimF (coinductive bisimulation). -/
def Bisim_gfp : Rel := SessionCoTypes.CoinductiveRel.gfp (F := BisimF)

theorem Bisim_gfp_coind {R : Rel} (h : R ≤ BisimF R) : R ≤ Bisim_gfp := by
  exact SessionCoTypes.CoinductiveRel.coind (F := BisimF) h

theorem Bisim_gfp_unfold : Bisim_gfp ≤ BisimF Bisim_gfp := by
  exact SessionCoTypes.CoinductiveRel.unfold (F := BisimF)

theorem Bisim_gfp_fold : BisimF Bisim_gfp ≤ Bisim_gfp := by
  exact SessionCoTypes.CoinductiveRel.fold (F := BisimF)


/-- Membership-based weak bisimulation.

    `Bisim a b` holds when there exists a relation R such that:
    1. R a b holds
    2. R is a post-fixpoint of BisimF (i.e., R ⊆ BisimF R)

    This is defined as an existential to avoid Prop-valued structure issues. -/
def Bisim (a b : LocalTypeR) : Prop :=
  ∃ R : Rel, (∀ x y, R x y → BisimF R x y) ∧ R a b

namespace Bisim

/-! ## Bisim is an Equivalence Relation -/

/-- BranchesRelBisim is reflexive when the underlying relation is. -/
theorem BranchesRelBisim.refl {R : Rel} (hrefl : ∀ t, R t t)
    (bs : List BranchR) : BranchesRelBisim R bs bs := by
  induction bs with
  | nil => exact List.Forall₂.nil
  | cons b rest ih =>
    exact List.Forall₂.cons ⟨rfl, hrefl b.2.2⟩ ih



/-- BranchesRelBisim is symmetric when the underlying relation is. -/
theorem BranchesRelBisim.symm {R : Rel} (hsymm : ∀ a b, R a b → R b a)
    {bs cs : List BranchR} (h : BranchesRelBisim R bs cs) :
    BranchesRelBisim R cs bs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih =>
    exact List.Forall₂.cons ⟨hbc.1.symm, hsymm _ _ hbc.2⟩ ih

/-- Convert BranchesRelBisim R bs cs to BranchesRelBisim S cs bs where S is the flip of R.
    This is used in the symmetry proof where S x y = R y x. -/
theorem BranchesRelBisim.flip {R S : Rel} (hflip : ∀ a b, R a b → S b a)
    {bs cs : List BranchR} (h : BranchesRelBisim R bs cs) :
    BranchesRelBisim S cs bs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih =>
    exact List.Forall₂.cons ⟨hbc.1.symm, hflip _ _ hbc.2⟩ ih

/-- Bisim is symmetric. -/
theorem symm {a b : LocalTypeR} (h : Bisim a b) : Bisim b a := by
  obtain ⟨R, hpost, hab⟩ := h
  -- Use the flipped relation: S x y = R y x
  let S : Rel := fun x y => R y x
  use S
  constructor
  · -- Show S is a post-fixpoint of BisimF
    intro x y hxy
    have hyx : R y x := hxy
    have hf : BisimF R y x := hpost y x hyx
    -- Transform BisimF R y x into BisimF S x y
    cases hf with
    | eq_end ha hb => exact BisimF.eq_end hb ha
    | eq_var ha hb => exact BisimF.eq_var hb ha
    | eq_send ha hb hbr =>
      apply BisimF.eq_send hb ha
      -- Need BranchesRelBisim S bsb bsa from BranchesRelBisim R bsa bsb
      -- S x y = R y x, so flip gives us what we need
      exact BranchesRelBisim.flip (fun a b h => h) hbr
    | eq_recv ha hb hbr =>
      apply BisimF.eq_recv hb ha
      exact BranchesRelBisim.flip (fun a b h => h) hbr
  · -- Show S b a = R a b
    exact hab

/-- BranchesRelBisim is transitive when the underlying relation is. -/
theorem BranchesRelBisim.trans {R : Rel}
    (htrans : ∀ a b c, R a b → R b c → R a c)
    {as bs cs : List BranchR}
    (hab : BranchesRelBisim R as bs) (hbc : BranchesRelBisim R bs cs) :
    BranchesRelBisim R as cs := by
  induction hab generalizing cs with
  | nil => cases hbc; exact List.Forall₂.nil
  | cons h _ ih =>
    cases hbc with
    | cons h' hbc' =>
      exact List.Forall₂.cons ⟨h.1.trans h'.1, htrans _ _ _ h.2 h'.2⟩ (ih hbc')

/-- Compose two BranchesRelBisim proofs with different relations into one with composed relation.
    Given R1 as bs and R2 bs cs, produce R3 as cs where R3 a c := ∃ b, R1 a b ∧ R2 b c. -/
theorem BranchesRelBisim.compose {R1 R2 R3 : Rel}
    (hcomp : ∀ a b c, R1 a b → R2 b c → R3 a c)
    {as bs cs : List BranchR}
    (hab : BranchesRelBisim R1 as bs) (hbc : BranchesRelBisim R2 bs cs) :
    BranchesRelBisim R3 as cs := by
  induction hab generalizing cs with
  | nil => cases hbc; exact List.Forall₂.nil
  | cons h _ ih =>
    cases hbc with
    | cons h' hbc' =>
      exact List.Forall₂.cons ⟨h.1.trans h'.1, hcomp _ _ _ h.2 h'.2⟩ (ih hbc')



/-- Bisim is transitive.

    This is the key result that works where EQ2_trans previously required an extra assumption.
    The proof works because BisimF uses membership predicates, allowing
    the intermediate element to have any structure. -/
theorem trans {a b c : LocalTypeR} (hab : Bisim a b) (hbc : Bisim b c) : Bisim a c := by
  obtain ⟨R1, hpost1, hab'⟩ := hab
  obtain ⟨R2, hpost2, hbc'⟩ := hbc
  -- Use the transitive composition
  let R : Rel := fun x z => ∃ y, R1 x y ∧ R2 y z
  use R
  constructor
  · -- Show R is a post-fixpoint of BisimF
    intro x z ⟨y, hxy, hyz⟩
    have hf_xy : BisimF R1 x y := hpost1 x y hxy
    have hf_yz : BisimF R2 y z := hpost2 y z hyz
    -- Case analysis on the observable behavior of x~y
    cases hf_xy with
    | eq_end hx hy =>
      -- x unfolds to end, y unfolds to end
      -- y~z must also show y unfolds to something compatible with end
      cases hf_yz with
      | eq_end _ hz => exact BisimF.eq_end hx hz
      | eq_var hy' _ => exact absurd hy (UnfoldsToVar.not_end_of_var hy')
      | eq_send hy' _ _ => exact absurd hy (CanSend.not_end hy')
      | eq_recv hy' _ _ => exact absurd hy (CanRecv.not_end hy')
    | eq_var hx hy =>
      -- x unfolds to var v, y unfolds to var v
      cases hf_yz with
      | eq_end hy' _ => exact absurd hy' (UnfoldsToVar.not_end_of_var hy)
      | eq_var hy' hz =>
        have heq := UnfoldsToVar.deterministic hy hy'
        subst heq
        exact BisimF.eq_var hx hz
      | eq_send hy' _ _ => exact absurd hy (CanSend.not_var hy' _)
      | eq_recv hy' _ _ => exact absurd hy (CanRecv.not_var hy' _)
    | eq_send hx hy hbr_xy =>
      -- x can send to partner with branches, y can send to same partner
      cases hf_yz with
      | eq_end hy' _ => exact absurd hy' (CanSend.not_end hy)
      | eq_var hy' _ => exact absurd hy' (CanSend.not_var hy _)
      | eq_send hy' hz hbr_yz =>
        have ⟨heq_p, heq_bs⟩ := CanSend.deterministic hy hy'
        subst heq_p heq_bs
        apply BisimF.eq_send hx hz
        -- Compose the branch relations: R1 and R2 into R where R a c = ∃ b, R1 a b ∧ R2 b c
        exact BranchesRelBisim.compose (fun a b c hab hbc => ⟨b, hab, hbc⟩) hbr_xy hbr_yz
      | eq_recv hy' _ _ => exact absurd hy' (CanSend.not_recv hy)
    | eq_recv hx hy hbr_xy =>
      cases hf_yz with
      | eq_end hy' _ => exact absurd hy' (CanRecv.not_end hy)
      | eq_var hy' _ => exact absurd hy' (CanRecv.not_var hy _)
      | eq_send hy' _ _ =>
        -- hy : CanRecv y partner bsa, hy' : CanSend y partner' bsb'
        -- These contradict because same type can't both send and recv
        exact (CanSend.not_recv hy' hy).elim
      | eq_recv hy' hz hbr_yz =>
        have ⟨heq_p, heq_bs⟩ := CanRecv.deterministic hy hy'
        subst heq_p heq_bs
        apply BisimF.eq_recv hx hz
        exact BranchesRelBisim.compose (fun a b c hab hbc => ⟨b, hab, hbc⟩) hbr_xy hbr_yz
  · -- Show R a c
    exact ⟨b, hab', hbc'⟩

end Bisim

end SessionCoTypes.Bisim
