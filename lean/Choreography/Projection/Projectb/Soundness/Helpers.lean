import Choreography.Projection.Projectb.Coinductive

namespace Choreography.Projection.Projectb
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.Participation
open SessionCoTypes.CoinductiveRel

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-! # Choreography.Projection.Projectb.Soundness

Soundness and completeness of `projectb` with respect to `CProject`.
-/

/-
The Problem. The boolean checker `projectb` must be proven sound: when it returns
true for a candidate, that candidate must satisfy the CProject relation. This
ensures the checker only accepts valid projections.

Solution Structure. We prove soundness by structural induction on global types:
1. Helper lemmas for BEq-to-Prop conversions (String, PayloadSort, Label)
2. Case analysis matching `projectb` and `CProjectF` structure
3. Branch helpers for send/recv with Forall₂ witnesses
-/

/-! ## Soundness and Completeness

These theorems establish the correspondence between the boolean checker `projectb`
and the coinductive relation `CProject`. -/

/-! ## Equality Conversion Helpers -/

/-- Helper: convert BEq equality to Prop equality for String. -/
theorem string_beq_eq_true_to_eq {a b : String} (h : (a == b) = true) : a = b := by
  exact eq_of_beq h

/-- Helper: PayloadSort BEq true implies equality.
    Proven by induction since PayloadSort has recursive prod constructor. -/
theorem payloadSort_beq_eq_true_to_eq {a b : PayloadSort} (h : (a == b) = true) : a = b := by
  induction a generalizing b with
  | unit => cases b <;> simp_all [reduceBEq]
  | nat => cases b <;> simp_all [reduceBEq]
  | bool => cases b <;> simp_all [reduceBEq]
  | string => cases b <;> simp_all [reduceBEq]
  | real => cases b <;> simp_all [reduceBEq]
  | vector n =>
      cases b with
      | vector m =>
          simp only [reduceBEq, beq_iff_eq] at h
          simp only [h]
      | _ => simp_all [reduceBEq]
  | prod s1 s2 ih1 ih2 =>
      cases b with
      | prod t1 t2 =>
          simp only [reduceBEq, Bool.and_eq_true] at h
          obtain ⟨h1, h2⟩ := h
          simp only [ih1 h1, ih2 h2]
      | _ => simp_all [reduceBEq]

/-- Helper: convert BEq equality to Prop equality for Label.
    Uses reduceBEq simproc to unfold derived BEq to component-wise form. -/
theorem label_beq_eq_true_to_eq {a b : Label} (h : (a == b) = true) : a = b := by
  -- Destruct Label to access components
  cases a with | mk n1 s1 =>
  cases b with | mk n2 s2 =>
  -- Use reduceBEq to unfold the derived BEq to (n1 == n2) && (s1 == s2)
  simp only [reduceBEq, Bool.and_eq_true] at h
  obtain ⟨hn, hs⟩ := h
  -- String has LawfulBEq, so eq_of_beq works
  have heq_n : n1 = n2 := eq_of_beq hn
  -- PayloadSort: use our helper
  have heq_s : s1 = s2 := payloadSort_beq_eq_true_to_eq hs
  simp only [heq_n, heq_s]

/-! ## ValType and Option-ValType Helpers -/

/-- Helper: ValType BEq true implies equality (avoid LawfulBEq instance). -/
theorem valType_beq_eq_true_to_eq
    {a b : SessionTypes.ValType} (h : (a == b) = true) : a = b := by
  induction a generalizing b with
  | unit =>
      cases b with
      | unit => rfl
      | _ =>
          have : False := by simpa [reduceBEq] using h
          exact this.elim
  | bool =>
      cases b with
      | bool => rfl
      | _ =>
          have : False := by simpa [reduceBEq] using h
          exact this.elim
  | nat =>
      cases b with
      | nat => rfl
      | _ =>
          have : False := by simpa [reduceBEq] using h
          exact this.elim
  | string =>
      cases b with
      | string => rfl
      | _ =>
          have : False := by simpa [reduceBEq] using h
          exact this.elim
  | prod a1 a2 ih1 ih2 =>
      cases b with
      | prod b1 b2 =>
          simp [reduceBEq, Bool.and_eq_true] at h
          obtain ⟨h1, h2⟩ := h
          have ha1 : a1 = b1 := ih1 h1
          have ha2 : a2 = b2 := ih2 h2
          simp [ha1, ha2]
      | _ =>
          simp [reduceBEq] at h
  | chan sid r =>
      cases b with
      | chan sid' r' =>
          simp [reduceBEq, Bool.and_eq_true] at h
          obtain ⟨hsid, hr⟩ := h
          have hsid' : sid = sid' := by simpa using hsid
          have hr' : r = r' := by simpa using hr
          simp [hsid', hr']
      | _ =>
          simp [reduceBEq] at h

/-! ## Option-ValType and Label Reflexivity Helpers -/

/-- Helper: Option ValType BEq true implies equality (avoid LawfulBEq instance). -/
theorem optionValType_beq_eq_true_to_eq
    {a b : Option SessionTypes.ValType} (h : (a == b) = true) : a = b := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some _ =>
          have hfalse : False := by
            simpa using h
          exact hfalse.elim
  | some a =>
      cases b with
      | none =>
          have hfalse : False := by
            simpa using h
          exact hfalse.elim
      | some b =>
          have h' : (a == b) = true := by simpa using h
          have hab : a = b := valType_beq_eq_true_to_eq h'
          simp [hab]

/-- Helper: PayloadSort beq is reflexive. -/
theorem payloadSort_beq_refl (s : PayloadSort) : (s == s) = true := by
  induction s with
  | unit => rfl
  | nat => rfl
  | bool => rfl
  | string => rfl
  | real => rfl
  | vector n => simp only [reduceBEq, beq_self_eq_true]
  | prod s1 s2 ih1 ih2 =>
      simp only [reduceBEq, Bool.and_eq_true]
      exact ⟨ih1, ih2⟩

/-- Helper: convert Prop equality to BEq equality for Label. -/
theorem eq_to_label_beq_eq_true {a b : Label} (h : a = b) : (a == b) = true := by
  subst h
  cases a with | mk n s =>
  simp only [reduceBEq, beq_self_eq_true, Bool.true_and, payloadSort_beq_refl]

/-! ## SoundRel Core Helpers -/

/-- Relation for coinduction in projectb_sound: pairs where projectb returns true. -/
def SoundRel : ProjRel := fun g role cand => projectb g role cand = true

/-- Helper: split Bool.and = true into two parts. -/
theorem bool_and_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

/-! ## Branch and All-Branch Reflection Helpers -/

/-- Helper: projectbBranches true implies BranchesProjRel SoundRel. -/
theorem projectbBranches_to_SoundRel
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List BranchR)
    (h : projectbBranches gbs role lbs = true) :
    BranchesProjRel SoundRel gbs role lbs := by
  induction gbs generalizing lbs with
  | nil =>
      cases lbs with
      | nil => exact List.Forall₂.nil
      | cons _ _ =>
          unfold projectbBranches at h
          exact False.elim (Bool.false_ne_true h)
  | cons ghd gtl ih =>
      cases lbs with
      | nil =>
          unfold projectbBranches at h
          exact False.elim (Bool.false_ne_true h)
      | cons lhd ltl =>
          unfold projectbBranches at h
          split_ifs at h with hlabel hnone
          -- Only one goal: both tests must succeed to get true.
          have ⟨hproj, hrest⟩ := bool_and_true h
          have hlabel' : ghd.1 = lhd.1 := label_beq_eq_true_to_eq hlabel
          have hnone' : lhd.2.1 = none := by
            cases lhd with
            | mk lbl rest =>
                cases rest with
                | mk vt cont =>
                    cases vt with
                    | none => rfl
                    | some t =>
                        cases (Bool.false_ne_true hnone)
          exact List.Forall₂.cons ⟨hlabel', hnone', hproj⟩ (ih ltl hrest)

/-- Helper: projectbAllBranches true implies AllBranchesProj SoundRel. -/
theorem projectbAllBranches_to_SoundRel
    (gbs : List (Label × GlobalType)) (role : String) (cand : LocalTypeR)
    (h : projectbAllBranches gbs role cand = true) :
    AllBranchesProj SoundRel gbs role cand := by
  induction gbs with
  | nil =>
      intro gb hgb
      cases hgb
  | cons ghd gtl ih =>
      intro gb hgb
      unfold projectbAllBranches at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hhead, hrest⟩ := h
      cases hgb with
      | head _ => exact hhead
      | tail _ hmem => exact ih hrest gb hmem


end Choreography.Projection.Projectb
