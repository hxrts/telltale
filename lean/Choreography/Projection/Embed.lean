import Mathlib.Order.FixedPoints
import SessionCoTypes.CoinductiveRel
import Choreography.Projection.Projectb

/-
The Problem. Given a local session type for a specific role, can we embed it
back into a global type? This is the inverse of projection. The challenge is
that embedding is partial: not all local types correspond to valid global types,
and non-participant roles create ambiguity.

We must define CEmbed such that:
1. CEmbed e role g implies CProject g role e (embedding sound for projection)
2. Only participant roles (sender/receiver) are embedded
3. Avoids the known counterexample for project-then-embed on non-participants

Solution Structure. Define CEmbedF as a one-step generator matching participants
only, prove it's monotone, take the greatest fixed point, and prove embedding
implies projection via coinduction.
-/

/-! # Choreography.Projection.Embed

Coinductive embedding relation for local-to-global types.

This is the symmetric companion to `CProject`: if `CProject` projects a global
protocol to a local view, `CEmbed` embeds a local view back into a global protocol
for a fixed role. Unlike projection, embedding is intentionally partial: we only
embed participant roles (sender/receiver), and we do not provide a non-participant
case. This avoids the known counterexample for "project-then-embed" on non-participants.
-/

namespace Choreography.Projection.Embed

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionCoTypes.CoinductiveRel
open Choreography.Projection.Projectb
open Choreography.Projection.Project (lcontractive)

/-! ## Embedding Relations -/

/-- Ternary relation for embedding: LocalType → Role → GlobalType → Prop. -/
abbrev EmbedRel := LocalTypeR → String → GlobalType → Prop

/-- Branch-wise embedding relation for send/recv.

Labels must match and each branch continuation must embed under R. -/
def BranchesEmbedRel (R : EmbedRel)
    (lbs : List BranchR) (role : String) (gbs : List (Label × GlobalType)) : Prop :=
  List.Forall₂ (fun lb gb => lb.1 = gb.1 ∧ lb.2.1 = none ∧ R lb.2.2 role gb.2) lbs gbs

/-! ## One-Step Generator -/

/-- One-step generator for CEmbed.

This defines the structural embedding rules:
- end embeds in end
- var embeds in matching var
- mu embeds in mu with matching variable and guardedness
- send embeds as comm sender (participant role)
- recv embeds as comm receiver (participant role)
- No non-participant case (intentionally partial) -/
def CEmbedF (R : EmbedRel) : EmbedRel := fun e role g =>
  match e, g with
  | .end, .end => True
  | .var t, .var t' => t = t'
  | .mu t body, .mu t' gbody =>
      -- Match CProjectF: check body.isGuarded t (local type guardedness)
      t = t' ∧ body.isGuarded t ∧ R body role gbody
  | .send receiver lbs, .comm sender receiver' gbs =>
      role = sender ∧ role ≠ receiver' ∧ receiver = receiver' ∧ BranchesEmbedRel R lbs role gbs
  | .recv sender lbs, .comm sender' receiver gbs =>
      role = receiver ∧ sender' ≠ role ∧ sender = sender' ∧ BranchesEmbedRel R lbs role gbs
  | _, _ => False

/-! ## Monotonicity -/

private theorem BranchesEmbedRel_mono {R S : EmbedRel}
    (h : ∀ e r g, R e r g → S e r g) :
    ∀ {lbs gbs role}, BranchesEmbedRel R lbs role gbs → BranchesEmbedRel S lbs role gbs := by
  intro lbs gbs role hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons hpair _ ih =>
      exact List.Forall₂.cons ⟨hpair.1, hpair.2.1, h _ _ _ hpair.2.2⟩ ih

/-- CEmbedF is monotone, enabling coinductive definition. -/
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

/-! ## Coinductive Definition -/

/-- CEmbed as the greatest fixed point of CEmbedF. -/
def CEmbed : EmbedRel :=
  OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩

/-! ## Fixed Point Properties -/

/-- Alias: CEmbed as gfp via CoinductiveRel. -/
theorem CEmbed_gfp : CEmbed = SessionCoTypes.CoinductiveRel.gfp (F := CEmbedF) := rfl

/-- Coinduction principle for CEmbed. -/
theorem CEmbed_coind' {R : EmbedRel} (h : R ≤ CEmbedF R) : R ≤ CEmbed := by
  exact SessionCoTypes.CoinductiveRel.coind (F := CEmbedF) h

/-- Unfold CEmbed one step. -/
theorem CEmbed_unfold' : CEmbed ≤ CEmbedF CEmbed := by
  change (OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩) ≤
    CEmbedF (OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩)
  exact SessionCoTypes.CoinductiveRel.unfold (F := CEmbedF)

/-- Fold CEmbedF CEmbed back to CEmbed. -/
theorem CEmbed_fold' : CEmbedF CEmbed ≤ CEmbed := by
  change CEmbedF (OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩) ≤
    OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩
  exact SessionCoTypes.CoinductiveRel.fold (F := CEmbedF)

/-- CEmbed is a fixed point. -/
private theorem CEmbed_fixed : CEmbedF CEmbed = CEmbed := by
  change CEmbedF (OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩) =
    OrderHom.gfp ⟨CEmbedF, CEmbedF_mono⟩
  exact SessionCoTypes.CoinductiveRel.gfp_fixed (F := CEmbedF)

/-- Destruct CEmbed: if CEmbed holds, then CEmbedF CEmbed holds. -/
theorem CEmbed_destruct {e : LocalTypeR} {role : String} {g : GlobalType}
    (h : CEmbed e role g) : CEmbedF CEmbed e role g := by
  have hfix : CEmbedF CEmbed = CEmbed := CEmbed_fixed
  exact Eq.mp (congrArg (fun R => R e role g) hfix.symm) h

/-! ## Embedding implies projection -/

/-- Convert BranchesEmbedRel into BranchesProjRel with swapped arguments. -/
private theorem BranchesEmbedRel_to_Proj {lbs : List BranchR}
    {gbs : List (Label × GlobalType)} {role : String}
    (h : BranchesEmbedRel CEmbed lbs role gbs) :
    BranchesProjRel (fun g r e => CEmbed e r g) gbs role lbs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hpair _ ih =>
      exact List.Forall₂.cons ⟨hpair.1.symm, hpair.2.1, hpair.2.2⟩ ih

/-- Helper: embed implies project for end case. -/
private theorem embed_implies_project_end {g : GlobalType} {role : String}
    (hF : CEmbedF CEmbed LocalTypeR.end role g) :
    CProjectF (fun g r e => CEmbed e r g) g role LocalTypeR.end := by
  cases g with
  | «end» => simp [CProjectF]
  | var _ | mu _ _ | comm _ _ _ | delegate _ _ _ _ _ => simp [CEmbedF] at hF

/-- Helper: embed implies project for var case. -/
private theorem embed_implies_project_var {t : String} {g : GlobalType} {role : String}
    (hF : CEmbedF CEmbed (LocalTypeR.var t) role g) :
    CProjectF (fun g r e => CEmbed e r g) g role (LocalTypeR.var t) := by
  cases g with
  | var t' => simp [CEmbedF] at hF; exact hF.symm
  | «end» | mu _ _ | comm _ _ _ | delegate _ _ _ _ _ => simp [CEmbedF] at hF

/-- Helper: embed implies project for mu case. -/
private theorem embed_implies_project_mu {t : String} {body : LocalTypeR}
    {g : GlobalType} {role : String}
    (hF : CEmbedF CEmbed (LocalTypeR.mu t body) role g) :
    CProjectF (fun g r e => CEmbed e r g) g role (LocalTypeR.mu t body) := by
  cases g with
  | mu t' gbody =>
      simp [CEmbedF] at hF
      rcases hF with ⟨ht, hcontr, hbody⟩
      use body
      constructor
      · exact hbody
      · left
        subst ht
        exact ⟨hcontr, rfl⟩
  | «end» | var _ | comm _ _ _ | delegate _ _ _ _ _ => simp [CEmbedF] at hF

/-- Helper: embed implies project for send case. -/
private theorem embed_implies_project_send {receiver : String}
    {lbs : List BranchR} {g : GlobalType} {role : String}
    (hF : CEmbedF CEmbed (LocalTypeR.send receiver lbs) role g) :
    CProjectF (fun g r e => CEmbed e r g) g role (LocalTypeR.send receiver lbs) := by
  cases g with
  | comm sender receiver' gbs =>
      simp [CEmbedF] at hF
      rcases hF with ⟨hrole, _, hrecv, hbr⟩
      subst hrole
      simp [CProjectF]
      exact ⟨hrecv, BranchesEmbedRel_to_Proj hbr⟩
  | «end» | var _ | mu _ _ | delegate _ _ _ _ _ => simp [CEmbedF] at hF

/-- Helper: embed implies project for recv case. -/
private theorem embed_implies_project_recv {sender : String}
    {lbs : List BranchR} {g : GlobalType} {role : String}
    (hF : CEmbedF CEmbed (LocalTypeR.recv sender lbs) role g) :
    CProjectF (fun g r e => CEmbed e r g) g role (LocalTypeR.recv sender lbs) := by
  cases g with
  | comm sender' receiver gbs =>
      simp [CEmbedF] at hF
      rcases hF with ⟨hrole, hneq, hsend, hbr⟩
      subst hrole
      have hneq' : role ≠ sender' := fun h => hneq h.symm
      simp [CProjectF, hneq']
      exact ⟨hsend, BranchesEmbedRel_to_Proj hbr⟩
  | «end» | var _ | mu _ _ | delegate _ _ _ _ _ => simp [CEmbedF] at hF

/-- Embedding implies projection (CEmbed ⊆ CProject with swapped arguments). -/
theorem CEmbed_implies_CProject {e : LocalTypeR} {role : String} {g : GlobalType}
    (h : CEmbed e role g) : CProject g role e := by
  have hpost : ∀ g role e, (fun g r e => CEmbed e r g) g role e →
      CProjectF (fun g r e => CEmbed e r g) g role e := by
    intro g role e he
    have hF := CEmbed_destruct he
    cases e with
    | «end» => exact embed_implies_project_end hF
    | var t => exact embed_implies_project_var hF
    | mu t body => exact embed_implies_project_mu hF
    | send receiver lbs => exact embed_implies_project_send hF
    | recv sender lbs => exact embed_implies_project_recv hF
  exact CProject_coind (R := fun g r e => CEmbed e r g) hpost g role e h

/-- Alias: embedding implies projection. -/
theorem CEmbed_has_project {e : LocalTypeR} {role : String} {g : GlobalType}
    (h : CEmbed e role g) : CProject g role e :=
  CEmbed_implies_CProject h

end Choreography.Projection.Embed
