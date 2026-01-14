import Mathlib
import Mathlib.Data.List.Forall2
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Observable
import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.CoTypes.CoinductiveRel

set_option linter.dupNamespace false

/-
The Problem. Projection extracts a local type for a role from a global protocol.
For coinductive types, projection must be defined as a greatest fixed point to
handle infinite/recursive protocols correctly.

The difficulty is that both global and local types can unfold through mu nodes,
so the projection relation must be stable under unfolding on both sides. The
standard approach is to allow finite unfolding before matching the head shape.

Solution Structure.
1. UnfoldsG/UnfoldsToG define global type unfolding (mu substitution)
2. BranchesProjRelC aligns branches with label equality
3. ProjectC_step is the one-step generator allowing finite unfolding
4. ProjectC is the greatest fixed point via CoinductiveRel
5. ProjectC_unfoldG/unfoldC show stability under mu-unfolding
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.CoTypes.CoinductiveRel

/-! ## Global type unfolding -/

/-- One-step global unfolding: µt.G ↦ G[µt.G/t]. -/
def UnfoldsG (g g' : GlobalType) : Prop :=
  ∃ t body, g = .mu t body ∧ g' = body.substitute t g

/-- Finite global unfolding closure. -/
def UnfoldsToG (g g' : GlobalType) : Prop :=
  Relation.ReflTransGen UnfoldsG g g'

/-! ## Branch relations -/

/-- Projection relation type (global × role × coinductive local). -/
abbrev ProjRelC := GlobalType → String → LocalTypeC → Prop

/-- Branch-wise projection alignment with label equality. -/
def BranchesProjRelC (R : ProjRelC) (gbs : List (Label × GlobalType)) (role : String)
    (lbs : List (Label × LocalTypeC)) : Prop :=
  List.Forall₂ (fun gb lb => gb.1 = lb.1 ∧ R gb.2 role lb.2) gbs lbs

/-- All branches project to the same candidate (non-participant case). -/
def AllBranchesProjC (R : ProjRelC) (gbs : List (Label × GlobalType)) (role : String)
    (cand : LocalTypeC) : Prop :=
  ∀ gb ∈ gbs, R gb.2 role cand

private lemma BranchesProjRelC_mono {R S : ProjRelC}
    (h : ∀ g role cand, R g role cand → S g role cand) :
    ∀ {gbs lbs role}, BranchesProjRelC R gbs role lbs → BranchesProjRelC S gbs role lbs := by
  intro gbs lbs role hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons hhead htail ih =>
      refine List.Forall₂.cons ?_ ih
      exact ⟨hhead.1, h _ _ _ hhead.2⟩

private lemma AllBranchesProjC_mono {R S : ProjRelC}
    (h : ∀ g role cand, R g role cand → S g role cand) :
    ∀ {gbs role cand}, AllBranchesProjC R gbs role cand → AllBranchesProjC S gbs role cand := by
  intro gbs role cand hall gb hmem
  exact h _ _ _ (hall gb hmem)

/-! ## Projection step generator -/

private def ProjectC_comm (R : ProjRelC) (sender receiver : String)
    (gbs : List (Label × GlobalType)) (role : String) (l' : LocalTypeC) : Prop :=
  (role = sender ∧
      ∃ labels, head l' = .send receiver labels ∧
        BranchesProjRelC R gbs role (branchesOf l')) ∨
  (role = receiver ∧
      ∃ labels, head l' = .recv sender labels ∧
        BranchesProjRelC R gbs role (branchesOf l')) ∨
  (role ≠ sender ∧ role ≠ receiver ∧ AllBranchesProjC R gbs role l')

private lemma ProjectC_comm_mono {R S : ProjRelC}
    (h : ∀ g role cand, R g role cand → S g role cand) :
    ∀ {sender receiver gbs role l'},
      ProjectC_comm R sender receiver gbs role l' →
        ProjectC_comm S sender receiver gbs role l' := by
  intro sender receiver gbs role l' hcomm
  cases hcomm with
  | inl hsender =>
      rcases hsender with ⟨hrole, labels, hhead, hbr⟩
      exact Or.inl ⟨hrole, labels, hhead, BranchesProjRelC_mono h hbr⟩
  | inr hrest =>
      cases hrest with
      | inl hreceiver =>
          rcases hreceiver with ⟨hrole, labels, hhead, hbr⟩
          exact Or.inr (Or.inl ⟨hrole, labels, hhead, BranchesProjRelC_mono h hbr⟩)
      | inr hother =>
          rcases hother with ⟨hns, hnr, hall⟩
          exact Or.inr (Or.inr ⟨hns, hnr, AllBranchesProjC_mono h hall⟩)

/-- One-step generator for coinductive projection, unfolding both sides finitely. -/
def ProjectC_step (R : ProjRelC) : ProjRelC := fun g role cand =>
  ∃ g' l', UnfoldsToG g g' ∧ UnfoldsToC cand l' ∧
    match g' with
    | .end => head l' = .end
    | .var t => head l' = .var t
    | .mu _ _ => False
    | .comm sender receiver gbs => ProjectC_comm R sender receiver gbs role l'

private theorem ProjectC_step_mono : Monotone ProjectC_step := by
  intro R S h g role cand hrel
  rcases hrel with ⟨g', l', hg, hl, hstep⟩
  refine ⟨g', l', hg, hl, ?_⟩
  cases g' with
  | «end» =>
      simpa using hstep
  | var t =>
      simpa using hstep
  | mu t body =>
      cases hstep
  | comm sender receiver gbs =>
      cases hstep with
      | inl hsender =>
          rcases hsender with ⟨hrole, labels, hhead, hbr⟩
          exact Or.inl ⟨hrole, labels, hhead, BranchesProjRelC_mono h hbr⟩
      | inr hrest =>
          cases hrest with
          | inl hreceiver =>
              rcases hreceiver with ⟨hrole, labels, hhead, hbr⟩
              exact Or.inr (Or.inl ⟨hrole, labels, hhead, BranchesProjRelC_mono h hbr⟩)
          | inr hother =>
              rcases hother with ⟨hns, hnr, hall⟩
              exact Or.inr (Or.inr ⟨hns, hnr, AllBranchesProjC_mono h hall⟩)

instance : CoinductiveRel ProjRelC ProjectC_step := ⟨ProjectC_step_mono⟩

/-! ## Coinductive projection -/

/-- Coinductive projection as the greatest fixed point of `ProjectC_step`. -/
def ProjectC : ProjRelC :=
  RumpsteakV2.Protocol.CoTypes.CoinductiveRel.gfp (F := ProjectC_step)

/-! ## Fixed-point helpers -/

theorem ProjectC_destruct {g : GlobalType} {role : String} {cand : LocalTypeC}
    (h : ProjectC g role cand) : ProjectC_step ProjectC g role cand := by
  have hle : ProjectC ≤ ProjectC_step ProjectC :=
    (RumpsteakV2.Protocol.CoTypes.CoinductiveRel.unfold (F := ProjectC_step))
  exact hle _ _ _ h

theorem ProjectC_fold {g : GlobalType} {role : String} {cand : LocalTypeC}
    (h : ProjectC_step ProjectC g role cand) : ProjectC g role cand := by
  have hle : ProjectC_step ProjectC ≤ ProjectC :=
    (RumpsteakV2.Protocol.CoTypes.CoinductiveRel.fold (F := ProjectC_step))
  exact hle _ _ _ h

/-! ## Unfolding utilities -/

private lemma UnfoldsG_rightUnique : Relator.RightUnique UnfoldsG := by
  intro a b c hab hac
  rcases hab with ⟨t1, body1, rfl, rfl⟩
  rcases hac with ⟨t2, body2, hmu, rfl⟩
  cases hmu
  rfl

private lemma UnfoldsToG_eq_of_nonmu {g g' : GlobalType} (h : UnfoldsToG g g')
    (hn : ∀ t body, g ≠ .mu t body) : g' = g := by
  induction h with
  | refl => rfl
  | tail h1 hstep ih =>
      cases ih
      rcases hstep with ⟨t, body, hmu, _⟩
      exact (False.elim (hn t body hmu))

private lemma UnfoldsToG_compare_nonmu {g g1 g' : GlobalType} (hg1 : UnfoldsToG g g1)
    (hg' : UnfoldsToG g g') (hn : ∀ t body, g1 ≠ .mu t body) : UnfoldsToG g' g1 := by
  have htot := Relation.ReflTransGen.total_of_right_unique (U := UnfoldsG_rightUnique) hg1 hg'
  cases htot with
  | inl h1 =>
      have hEq : g' = g1 := UnfoldsToG_eq_of_nonmu h1 hn
      cases hEq
      exact Relation.ReflTransGen.refl
  | inr h2 => exact h2

private lemma UnfoldsC_head_mu {t u : LocalTypeC} (h : UnfoldsC t u) : ∃ x, head t = .mu x := by
  rcases h with ⟨x, f, hdest, _⟩
  refine ⟨x, ?_⟩
  simp [head, hdest]

private lemma UnfoldsC_rightUnique : Relator.RightUnique UnfoldsC := by
  intro a b c hab hac
  rcases hab with ⟨x, f, hdest, rfl⟩
  rcases hac with ⟨y, g, hdest', rfl⟩
  have hpair :
      (⟨LocalTypeHead.mu x, f⟩ : LocalTypeF LocalTypeC) =
        ⟨LocalTypeHead.mu y, g⟩ := by
    exact hdest.symm.trans hdest'
  cases hpair
  rfl

private lemma UnfoldsToC_eq_of_head_ne_mu {l l' : LocalTypeC} (h : UnfoldsToC l l')
    (hn : ∀ x, head l ≠ .mu x) : l' = l := by
  rcases (Relation.ReflTransGen.cases_head h) with (hEq | hstep)
  · cases hEq
    rfl
  · rcases hstep with ⟨c, hstep, _⟩
    rcases UnfoldsC_head_mu hstep with ⟨x, hmu⟩
    exact (False.elim (hn x hmu))

private lemma UnfoldsToC_total {l l1 l2 : LocalTypeC} (h1 : UnfoldsToC l l1) (h2 : UnfoldsToC l l2) :
    UnfoldsToC l1 l2 ∨ UnfoldsToC l2 l1 :=
  Relation.ReflTransGen.total_of_right_unique (U := UnfoldsC_rightUnique) h1 h2

/-! ## Unfolding stability -/

theorem ProjectC_unfoldG {g g' : GlobalType} {role : String} {l : LocalTypeC}
    (hproj : ProjectC g role l) (hg : UnfoldsToG g g') : ProjectC g' role l := by
  rcases ProjectC_destruct hproj with ⟨g1, l1, hg1, hl1, hmatch⟩
  cases g1 with
  | mu t body =>
      cases hmatch
  | «end» =>
      have hcomp : UnfoldsToG g' .end :=
        UnfoldsToG_compare_nonmu hg1 hg (by intro t body hmu; cases hmu)
      exact ProjectC_fold ⟨.end, l1, hcomp, hl1, by simpa using hmatch⟩
  | var t =>
      have hcomp : UnfoldsToG g' (.var t) :=
        UnfoldsToG_compare_nonmu hg1 hg (by intro t' body hmu; cases hmu)
      exact ProjectC_fold ⟨.var t, l1, hcomp, hl1, by simpa using hmatch⟩
  | comm sender receiver gbs =>
      have hcomp : UnfoldsToG g' (.comm sender receiver gbs) :=
        UnfoldsToG_compare_nonmu hg1 hg (by intro t body hmu; cases hmu)
      exact ProjectC_fold ⟨.comm sender receiver gbs, l1, hcomp, hl1, by simpa using hmatch⟩

theorem ProjectC_unfoldC {g : GlobalType} {role : String} {l l' : LocalTypeC}
    (hproj : ProjectC g role l) (hl : UnfoldsToC l l') : ProjectC g role l' := by
  let R : ProjRelC := fun g role cand => ∃ l, ProjectC g role l ∧ UnfoldsToC l cand
  have hinc : ∀ g role cand, ProjectC g role cand → R g role cand := by
    intro g role cand hproj
    exact ⟨cand, hproj, Relation.ReflTransGen.refl⟩
  have hpost : ∀ g role cand, R g role cand → ProjectC_step R g role cand := by
    intro g role cand hR
    rcases hR with ⟨l0, hproj0, hstep0⟩
    rcases ProjectC_destruct hproj0 with ⟨g1, l1, hg1, hl1, hmatch⟩
    have hcomp := UnfoldsToC_total hl1 hstep0
    cases hcomp with
    | inr h_cand_l1 =>
        refine ⟨g1, l1, hg1, h_cand_l1, ?_⟩
        cases g1 with
        | mu t body =>
            cases hmatch
        | «end» =>
            simpa using hmatch
        | var t =>
            simpa using hmatch
        | comm sender receiver gbs =>
            exact ProjectC_comm_mono hinc hmatch
    | inl h_l1_cand =>
        cases g1 with
        | mu t body =>
            cases hmatch
        | «end» =>
            have hne : ∀ x, head l1 ≠ .mu x := by
              intro x hx
              simp_all
            have hEq : cand = l1 := UnfoldsToC_eq_of_head_ne_mu h_l1_cand hne
            subst cand
            exact ⟨.end, l1, hg1, Relation.ReflTransGen.refl, by simpa using hmatch⟩
        | var t =>
            have hne : ∀ x, head l1 ≠ .mu x := by
              intro x hx
              simp_all
            have hEq : cand = l1 := UnfoldsToC_eq_of_head_ne_mu h_l1_cand hne
            subst cand
            exact ⟨.var t, l1, hg1, Relation.ReflTransGen.refl, by simpa using hmatch⟩
        | comm sender receiver gbs =>
            cases hmatch with
            | inl hsender =>
                rcases hsender with ⟨hrole, labels, hhead, hbr⟩
                have hne : ∀ x, head l1 ≠ .mu x := by
                  intro x hx
                  simp_all
                have hEq : cand = l1 := UnfoldsToC_eq_of_head_ne_mu h_l1_cand hne
                subst cand
                refine ⟨.comm sender receiver gbs, l1, hg1, Relation.ReflTransGen.refl, ?_⟩
                exact Or.inl ⟨hrole, labels, hhead, BranchesProjRelC_mono hinc hbr⟩
            | inr hrest =>
                cases hrest with
                | inl hreceiver =>
                    rcases hreceiver with ⟨hrole, labels, hhead, hbr⟩
                    have hne : ∀ x, head l1 ≠ .mu x := by
                      intro x hx
                      simp_all
                    have hEq : cand = l1 := UnfoldsToC_eq_of_head_ne_mu h_l1_cand hne
                    subst cand
                    refine ⟨.comm sender receiver gbs, l1, hg1, Relation.ReflTransGen.refl, ?_⟩
                    exact Or.inr (Or.inl ⟨hrole, labels, hhead, BranchesProjRelC_mono hinc hbr⟩)
                | inr hother =>
                    rcases hother with ⟨hns, hnr, hall⟩
                    have hall' : AllBranchesProjC R gbs role cand := by
                      intro gb hmem
                      exact ⟨l1, hall gb hmem, h_l1_cand⟩
                    refine ⟨.comm sender receiver gbs, cand, hg1, Relation.ReflTransGen.refl, ?_⟩
                    exact Or.inr (Or.inr ⟨hns, hnr, hall'⟩)
  have hle : R ≤ ProjectC_step R := by
    intro g role cand hR
    exact hpost g role cand hR
  have hco : R ≤ ProjectC := by
    simpa [ProjectC] using (RumpsteakV2.Protocol.CoTypes.CoinductiveRel.coind (F := ProjectC_step) hle)
  exact hco _ _ _ ⟨l, hproj, hl⟩

theorem ProjectC_mu_lift {g : GlobalType} {role : String} {x : String} {body : LocalTypeC}
    (hproj : ProjectC g role (mkMu x body)) : ProjectC g role body := by
  have hstep : UnfoldsC (mkMu x body) body := by
    refine ⟨x, (fun _ => body), ?_, rfl⟩
    simp [mkMu, PFunctor.M.dest_mk]
  exact ProjectC_unfoldC hproj (Relation.ReflTransGen.single hstep)

end RumpsteakV2.Coinductive
