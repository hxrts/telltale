import SessionTypes.GlobalType.Closedness.SubstitutionLemmas

/-! # SessionTypes.GlobalType.Closedness.Unfolding

Unfolding definitions and μ-height lemmas for global types.
-/

/-
The Problem. Later proofs require executable unfolding operators with basic
termination/identity properties tied to μ-height.

Solution Structure. Defines unfolding iterations and proves core μ-height
lemmas used by projection and exactness developments.
-/

set_option linter.dupNamespace false

namespace SessionTypes.GlobalType

/-! ## Unfolding for GlobalType (Coq-style `full_unf`) -/

/-! ## Unfolding for GlobalType (Coq-style `full_unf`)

These helpers mirror LocalTypeR.fullUnfold and are used by the unfolding-
insensitive projection refactor (CProjectU). -/

/-- Unfold one level of recursion: μt.G ↦ G[μt.G/t]. -/
def GlobalType.unfold : GlobalType → GlobalType
  | g@(.mu t body) => body.substitute t g
  | g => g

/-- Height of leading mu binders. -/
def GlobalType.muHeight : GlobalType → Nat
  | .mu _ body => 1 + body.muHeight
  | _ => 0

/-- Fully unfold a global type by iterating `unfold` exactly `muHeight` times.
    This matches the Coq `full_unf` definition used in the reference proofs. -/
def GlobalType.fullUnfoldIter (g : GlobalType) : GlobalType :=
  Nat.rec (motive := fun _ => GlobalType) g
    (fun _ acc => GlobalType.unfold acc) g.muHeight

/-- Fully unfold a global type by iterating unfold until non-mu form.
    Defined via `fullUnfoldIter` to ensure termination. -/
abbrev GlobalType.fullUnfold (g : GlobalType) : GlobalType :=
  g.fullUnfoldIter

theorem GlobalType.muHeight_non_mu :
    ∀ g : GlobalType, (∀ (t : String) (body : GlobalType), g ≠ .mu t body) →
      g.muHeight = 0 := by
  intro g h
  cases g with
  | mu t body =>
      have : False := h t body rfl
      exact this.elim
  | _ =>
      simp [GlobalType.muHeight]

theorem GlobalType.fullUnfoldIter_muHeight_zero {g : GlobalType} (hmu : g.muHeight = 0) :
    GlobalType.fullUnfoldIter g = g := by
  simp [GlobalType.fullUnfoldIter, hmu]

end SessionTypes.GlobalType
