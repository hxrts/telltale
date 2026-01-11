import Mathlib.Order.FixedPoints
import RumpsteakV2.Protocol.CoTypes.CoinductiveRel
import RumpsteakV2.Protocol.Projection.Projectb

/-! # RumpsteakV2.Protocol.Projection.Embed

Coinductive embedding relation for local-to-global types.

This is the symmetric companion to `CProject`: if `CProject` projects a global
protocol to a local view, `CEmbed` embeds a local view back into a global protocol
for a fixed role. Unlike projection, embedding is intentionally partial: we only
embed participant roles (sender/receiver), and we do not provide a non-participant
case. This avoids the known counterexample for "project-then-embed" on non-participants.
-/

namespace RumpsteakV2.Protocol.Projection.Embed

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.CoTypes.CoinductiveRel
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.Projection.Trans (lcontractive)

/-- Ternary relation for embedding. -/
abbrev EmbedRel := LocalTypeR → String → GlobalType → Prop

/-- Branch-wise embedding relation for send/recv. -/
def BranchesEmbedRel (R : EmbedRel)
    (lbs : List (Label × LocalTypeR)) (role : String) (gbs : List (Label × GlobalType)) : Prop :=
  List.Forall₂ (fun lb gb => lb.1 = gb.1 ∧ R lb.2 role gb.2) lbs gbs

/-- One-step generator for CEmbed. -/
def CEmbedF (R : EmbedRel) : EmbedRel := fun e role g =>
  match e, g with
  | .end, .end => True
  | .var t, .var t' => t = t'
  | .mu t body, .mu t' gbody =>
      t = t' ∧ lcontractive gbody ∧ R body role gbody
  | .send receiver lbs, .comm sender receiver' gbs =>
      role = sender ∧ role ≠ receiver' ∧ receiver = receiver' ∧ BranchesEmbedRel R lbs role gbs
  | .recv sender lbs, .comm sender' receiver gbs =>
      role = receiver ∧ sender' ≠ role ∧ sender = sender' ∧ BranchesEmbedRel R lbs role gbs
  | _, _ => False

private theorem BranchesEmbedRel_mono {R S : EmbedRel}
    (h : ∀ e r g, R e r g → S e r g) :
    ∀ {lbs gbs role}, BranchesEmbedRel R lbs role gbs → BranchesEmbedRel S lbs role gbs := by
  intro lbs gbs role hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons hpair _ ih =>
      exact List.Forall₂.cons ⟨hpair.1, h _ _ _ hpair.2⟩ ih

private theorem CEmbedF_mono : Monotone CEmbedF := by
  intro R S h e role g hrel
  cases e <;> cases g <;> simp only [CEmbedF] at hrel ⊢
  all_goals
    first
    | exact hrel
    | (obtain ⟨h1, h2, h3⟩ := hrel; exact ⟨h1, h2, h _ _ _ h3⟩)
    | (obtain ⟨h1, h2, h3, h4⟩ := hrel;
       exact ⟨h1, h2, h3, BranchesEmbedRel_mono (fun _ _ _ hr => h _ _ _ hr) h4⟩)

instance : CoinductiveRel EmbedRel CEmbedF := ⟨CEmbedF_mono⟩

/-- CEmbed as the greatest fixed point of CEmbedF. -/
def CEmbed : EmbedRel :=
  OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩

/-- Alias: CEmbed as gfp via CoinductiveRel. -/
theorem CEmbed_gfp : CEmbed = RumpsteakV2.Protocol.CoTypes.CoinductiveRel.gfp (F := CEmbedF) := rfl

/-- Alias: coinduction via CoinductiveRel for CEmbed. -/
theorem CEmbed_coind' {R : EmbedRel} (h : R ≤ CEmbedF R) : R ≤ CEmbed := by
  exact RumpsteakV2.Protocol.CoTypes.CoinductiveRel.coind (F := CEmbedF) h

/-- Alias: unfold via CoinductiveRel for CEmbed. -/
theorem CEmbed_unfold' : CEmbed ≤ CEmbedF CEmbed := by
  change (OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩) ≤
    CEmbedF (OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩)
  exact RumpsteakV2.Protocol.CoTypes.CoinductiveRel.unfold (F := CEmbedF)

/-- Alias: fold via CoinductiveRel for CEmbed. -/
theorem CEmbed_fold' : CEmbedF CEmbed ≤ CEmbed := by
  change CEmbedF (OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩) ≤
    OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩
  exact RumpsteakV2.Protocol.CoTypes.CoinductiveRel.fold (F := CEmbedF)

private theorem CEmbed_fixed : CEmbedF CEmbed = CEmbed := by
  change CEmbedF (OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩) =
    OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩
  exact RumpsteakV2.Protocol.CoTypes.CoinductiveRel.gfp_fixed (F := CEmbedF)

/-- Destruct CEmbed: if CEmbed holds, then CEmbedF CEmbed holds. -/
theorem CEmbed_destruct {e : LocalTypeR} {role : String} {g : GlobalType}
    (h : CEmbed e role g) : CEmbedF CEmbed e role g := by
  have hfix : CEmbedF CEmbed = CEmbed := CEmbed_fixed
  exact Eq.mp (congrArg (fun R => R e role g) hfix.symm) h

/-! ## Embedding implies projection -/

/-- Convert BranchesEmbedRel into BranchesProjRel with swapped arguments. -/
private theorem BranchesEmbedRel_to_Proj {lbs : List (Label × LocalTypeR)}
    {gbs : List (Label × GlobalType)} {role : String}
    (h : BranchesEmbedRel CEmbed lbs role gbs) :
    BranchesProjRel (fun g r e => CEmbed e r g) gbs role lbs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hpair _ ih =>
      exact List.Forall₂.cons ⟨hpair.1.symm, hpair.2⟩ ih

/-- Embedding implies projection (CEmbed ⊆ CProject with swapped arguments). -/
theorem CEmbed_implies_CProject {e : LocalTypeR} {role : String} {g : GlobalType}
    (h : CEmbed e role g) : CProject g role e := by
  -- Coinduction on CProject using the relation R g role e := CEmbed e role g.
  have hpost : ∀ g role e, (fun g r e => CEmbed e r g) g role e →
      CProjectF (fun g r e => CEmbed e r g) g role e := by
    intro g role e he
    have hF := CEmbed_destruct he
    cases e with
    | «end» =>
        cases g with
        | «end» =>
            simp [CProjectF]
        | var _ | mu _ _ | comm _ _ _ =>
            simp [CEmbedF] at hF
            cases hF
    | var t =>
        cases g with
        | var t' =>
            simp [CEmbedF] at hF
            exact hF.symm
        | «end» | mu _ _ | comm _ _ _ =>
            simp [CEmbedF] at hF
            cases hF
    | mu t body =>
        cases g with
        | mu t' gbody =>
            simp [CEmbedF] at hF
            rcases hF with ⟨ht, hcontr, hbody⟩
            exact ⟨ht.symm, hcontr, hbody⟩
        | «end» | var _ | comm _ _ _ =>
            simp [CEmbedF] at hF
            cases hF
    | send receiver lbs =>
        cases g with
        | comm sender receiver' gbs =>
            simp [CEmbedF] at hF
            rcases hF with ⟨hrole, _, hrecv, hbr⟩
            subst hrole
            have hbr' : BranchesProjRel (fun g r e => CEmbed e r g) gbs role lbs :=
              BranchesEmbedRel_to_Proj hbr
            simp [CProjectF]
            exact ⟨hrecv, hbr'⟩
        | «end» | var _ | mu _ _ =>
            simp [CEmbedF] at hF
            cases hF
    | recv sender lbs =>
        cases g with
        | comm sender' receiver gbs =>
            simp [CEmbedF] at hF
            rcases hF with ⟨hrole, hneq, hsend, hbr⟩
            subst hrole
            have hneq' : role ≠ sender' := by
              intro hrole'
              exact hneq hrole'.symm
            have hbr' : BranchesProjRel (fun g r e => CEmbed e r g) gbs role lbs :=
              BranchesEmbedRel_to_Proj hbr
            simp [CProjectF, hneq']
            exact ⟨hsend, hbr'⟩
        | «end» | var _ | mu _ _ =>
            simp [CEmbedF] at hF
            cases hF
  exact CProject_coind (R := fun g r e => CEmbed e r g) hpost g role e h

/-- Alias: embedding implies projection. -/
theorem CEmbed_has_project {e : LocalTypeR} {role : String} {g : GlobalType}
    (h : CEmbed e role g) : CProject g role e :=
  CEmbed_implies_CProject h

end RumpsteakV2.Protocol.Projection.Embed
