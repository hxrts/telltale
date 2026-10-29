import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # Distributed.Families.PartialSynchrony.Rounds

A concrete view-based partial-synchrony model and its post-GST progress theorem.

Model:
- `n` parties `0 … n-1`; view `v` occupies times `[v·L, (v+1)·L)` and has
  rotating leader `v % n`,
- in view `v` the leader's proposal takes `proposeDelay v` and the vote
  replies take `voteDelay v` time units,
- after GST every message delay is at most `Δ` (`Admissible`),
- a view decides iff its leader is honest and the proposal/vote round trip
  completes within the view (`ViewDecides`); the decision is observed at the
  end of the view.

Theorem `decided_after_gst`: if some party is honest, `0 < n`, `0 < L` and
`2Δ ≤ L`, then a decision is observed by time `gst + (2n+1)·L`.
-/

namespace Distributed
namespace PartialSynchrony
namespace Rounds

/-! ## Model -/

/-- Timing parameters. -/
structure Params where
  n : Nat
  viewLen : Nat
  delta : Nat
  gst : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Timing condition: nonempty party set, positive view length, and a view long
enough for one proposal/vote round trip under the post-GST bound. -/
def Params.TimingOK (P : Params) : Prop :=
  0 < P.n ∧ 0 < P.viewLen ∧ 2 * P.delta ≤ P.viewLen

instance (P : Params) : Decidable P.TimingOK := by unfold Params.TimingOK; infer_instance

/-- Run data: honesty of each party and the actual per-view message delays. -/
structure RoundRun where
  honest : Nat → Bool
  proposeDelay : Nat → Nat
  voteDelay : Nat → Nat

/-- Rotating leader of view `v`. -/
def leader (P : Params) (v : Nat) : Nat := v % P.n

/-- Post-GST delay bound: views starting at or after GST see delays `≤ Δ`. -/
def Admissible (P : Params) (R : RoundRun) : Prop :=
  ∀ v, P.gst ≤ v * P.viewLen → R.proposeDelay v ≤ P.delta ∧ R.voteDelay v ≤ P.delta

/-- Some party is honest. -/
def HasHonest (P : Params) (R : RoundRun) : Prop := ∃ p, p < P.n ∧ R.honest p = true

/-- Protocol rule: view `v` decides iff its leader is honest and the round trip
fits in the view. -/
def ViewDecides (P : Params) (R : RoundRun) (v : Nat) : Prop :=
  R.honest (leader P v) = true ∧ R.proposeDelay v + R.voteDelay v ≤ P.viewLen

/-- A decision has been observed by time `t`. -/
def DecidedBy (P : Params) (R : RoundRun) (t : Nat) : Prop :=
  ∃ v, ViewDecides P R v ∧ (v + 1) * P.viewLen ≤ t

/-- Bound on decision latency after GST. -/
def latencyBound (P : Params) : Nat := (2 * P.n + 1) * P.viewLen

/-! ## Arithmetic Helpers -/

/-- The view `(a/n + 1)·n + p` has leader `p` for `p < n`. -/
theorem leader_target (P : Params) (a p : Nat) (hp : p < P.n) :
    leader P ((a / P.n + 1) * P.n + p) = p := by
  unfold leader
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

/-- The target view lies in `[a, a + 2n)`. -/
theorem target_range (n a p : Nat) (hn : 0 < n) (hp : p < n) :
    a ≤ (a / n + 1) * n + p ∧ (a / n + 1) * n + p < a + 2 * n := by
  have h1 := Nat.div_mul_le_self a n
  have h2 := Nat.lt_div_mul_add (a := a) hn
  rw [Nat.add_mul, Nat.one_mul]
  constructor <;> omega

/-- First post-GST view index `gst/L + 1` starts strictly after GST. -/
theorem first_view_after_gst (gst L : Nat) (hL : 0 < L) (v : Nat)
    (hv : gst / L + 1 ≤ v) : gst ≤ v * L := by
  have h2 := Nat.lt_div_mul_add (a := gst) hL
  have h3 : (gst / L + 1) * L ≤ v * L := Nat.mul_le_mul_right L hv
  rw [Nat.add_mul, Nat.one_mul] at h3
  omega

/-- End of a view below `gst/L + 1 + 2n` is within the latency bound. -/
theorem view_end_le (gst L n v : Nat) (hv : v < gst / L + 1 + 2 * n) :
    (v + 1) * L ≤ gst + (2 * n + 1) * L := by
  have h1 := Nat.div_mul_le_self gst L
  have h3 : (v + 1) * L ≤ (gst / L + (2 * n + 1)) * L := Nat.mul_le_mul_right L (by omega)
  rw [Nat.add_mul (gst / L) (2 * n + 1) L] at h3
  omega

/-! ## Progress -/

/-- A view after GST with an honest leader decides. -/
theorem honest_view_decides (P : Params) (R : RoundRun) (hT : P.TimingOK)
    (hA : Admissible P R) {v : Nat} (hv : P.gst ≤ v * P.viewLen)
    (hH : R.honest (leader P v) = true) : ViewDecides P R v := by
  obtain ⟨h1, h2⟩ := hA v hv
  exact ⟨hH, by have := hT.2.2; omega⟩

/-- Post-GST progress: a decision is observed by `gst + latencyBound`. -/
theorem decided_after_gst (P : Params) (R : RoundRun) (hT : P.TimingOK)
    (hA : Admissible P R) (hH : HasHonest P R) :
    DecidedBy P R (P.gst + latencyBound P) := by
  obtain ⟨p, hp, hHon⟩ := hH
  set a := P.gst / P.viewLen + 1
  obtain ⟨hlo, hhi⟩ := target_range P.n a p hT.1 hp
  refine ⟨(a / P.n + 1) * P.n + p, ?_, view_end_le _ _ _ _ hhi⟩
  apply honest_view_decides P R hT hA (first_view_after_gst _ _ hT.2.1 _ hlo)
  rw [leader_target P a p hp]; exact hHon

/-- Decisions persist: `DecidedBy` is monotone in time. -/
theorem decidedBy_mono {P : Params} {R : RoundRun} {t t' : Nat} (h : t ≤ t')
    (hd : DecidedBy P R t) : DecidedBy P R t' := by
  obtain ⟨v, hv, hle⟩ := hd
  exact ⟨v, hv, le_trans hle h⟩

end Rounds
end PartialSynchrony
end Distributed
