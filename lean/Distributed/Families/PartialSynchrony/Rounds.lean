import Distributed.Families.QuorumGeometry.Core
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # Distributed.Families.PartialSynchrony.Rounds

A concrete view-based partial-synchrony protocol with vote quorums, its
post-GST progress theorem, and its agreement theorem.

Protocol (single-shot, `n = 3f+1` parties `0 … n-1`, quorum `q = 2f+1`):
- view `v` occupies times `[v·L, (v+1)·L)`; its leader is `v % n`,
- the leader sends a proposal to every party; `proposalTo v p` is the value
  party `p` receives and `proposeDelay v p` its delivery delay. An honest
  leader sends the same value to everybody (`HonestLeaderRule`); a Byzantine
  leader may equivocate,
- an honest party `p` votes in view `v` for the value it received, and its vote
  counts iff proposal + vote delivery fit in the view
  (`proposeDelay v p + voteDelay v p ≤ L`); a Byzantine party's vote is
  arbitrary (`byzVote`),
- view `v` decides `x` iff at least `q` parties' votes for `x` count
  (`ViewDecides`); the decision is observed at the end of the view,
- after GST every message delay is at most `Δ` (`Admissible`); at most `f`
  parties are Byzantine (`FaultBound`).

Theorems:
- `decided_after_gst` (progress): under `2Δ ≤ L`, some view decides by
  `gst + (2n+1)·L` — proved from the vote rule, not assumed,
- `view_agreement` (safety within a view): two decisions of one view agree,
  via `QuorumGeometry.honest_in_inter`,
- `first_decision_unique` (safety of the run's decision): the run's decision
  is the value of the first deciding view and is unique.

Honest narrowing: parties halt on the first decision (the decision
certificate is the output). Cross-view locking for protocols that continue
after a decision is not modelled, so agreement is proved for the first
deciding view and per view, not for arbitrary pairs of views.
-/

namespace Distributed
namespace PartialSynchrony
namespace Rounds

/-! ## Model -/

/-- Timing and fault parameters. -/
structure Params where
  n : Nat
  f : Nat
  viewLen : Nat
  delta : Nat
  gst : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Sizing and timing condition: `n = 3f+1`, positive view length, and a view
long enough for one proposal/vote round trip under the post-GST bound. -/
def Params.TimingOK (P : Params) : Prop :=
  P.n = 3 * P.f + 1 ∧ 0 < P.viewLen ∧ 2 * P.delta ≤ P.viewLen

instance (P : Params) : Decidable P.TimingOK := by unfold Params.TimingOK; infer_instance

/-- Vote quorum size `2f+1`. -/
def quorum (P : Params) : Nat := 2 * P.f + 1

/-- Run data: honesty, proposals received, per-message delays, Byzantine votes. -/
structure RoundRun where
  honest : Nat → Bool
  proposalTo : Nat → Nat → Nat
  proposeDelay : Nat → Nat → Nat
  voteDelay : Nat → Nat → Nat
  byzVote : Nat → Nat → Option Nat

/-- Rotating leader of view `v`. -/
def leader (P : Params) (v : Nat) : Nat := v % P.n

/-- Post-GST delay bound: in views starting at or after GST, every proposal
and vote delay is at most `Δ`. -/
def Admissible (P : Params) (R : RoundRun) : Prop :=
  ∀ v p, P.gst ≤ v * P.viewLen →
    R.proposeDelay v p ≤ P.delta ∧ R.voteDelay v p ≤ P.delta

/-- Honest parties. -/
def honestSet (P : Params) (R : RoundRun) : Finset Nat :=
  (Finset.range P.n).filter (fun p => R.honest p = true)

/-- Byzantine parties. -/
def byzSet (P : Params) (R : RoundRun) : Finset Nat :=
  (Finset.range P.n).filter (fun p => ¬ R.honest p = true)

/-- At most `f` parties are Byzantine. -/
def FaultBound (P : Params) (R : RoundRun) : Prop := (byzSet P R).card ≤ P.f

/-- Honest leaders send one proposal to everybody. -/
def HonestLeaderRule (P : Params) (R : RoundRun) : Prop :=
  ∀ v p, R.honest (leader P v) = true → R.proposalTo v p = R.proposalTo v (leader P v)

/-- Well-formed run: fault bound plus the honest-leader rule. -/
def WellFormed (P : Params) (R : RoundRun) : Prop := FaultBound P R ∧ HonestLeaderRule P R

/-- Whether party `p`'s vote for `x` counts in view `v` (protocol vote rule). -/
def votes (P : Params) (R : RoundRun) (v p x : Nat) : Bool :=
  if R.honest p then
    R.proposalTo v p == x && decide (R.proposeDelay v p + R.voteDelay v p ≤ P.viewLen)
  else R.byzVote v p == some x

/-- Parties whose vote for `x` counts in view `v`. -/
def voters (P : Params) (R : RoundRun) (v x : Nat) : Finset Nat :=
  (Finset.range P.n).filter (fun p => votes P R v p x = true)

/-- View `v` decides `x`: a quorum of counted votes for `x`. -/
def ViewDecides (P : Params) (R : RoundRun) (v x : Nat) : Prop :=
  quorum P ≤ (voters P R v x).card

instance (P : Params) (R : RoundRun) (v x : Nat) : Decidable (ViewDecides P R v x) := by
  unfold ViewDecides; infer_instance

/-- A decision has been observed by time `t`. -/
def DecidedBy (P : Params) (R : RoundRun) (t : Nat) : Prop :=
  ∃ v x, ViewDecides P R v x ∧ (v + 1) * P.viewLen ≤ t

/-- `x` is the run's decision: decided in view `v`, and no earlier view decided. -/
def FirstDecision (P : Params) (R : RoundRun) (v x : Nat) : Prop :=
  ViewDecides P R v x ∧ ∀ w < v, ∀ y, ¬ ViewDecides P R w y

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

/-! ## Counting -/

/-- Honest and Byzantine parties partition `0 … n-1`. -/
theorem honest_card (P : Params) (R : RoundRun) :
    (honestSet P R).card + (byzSet P R).card = P.n := by
  unfold honestSet byzSet
  rw [Finset.card_filter_add_card_filter_not, Finset.card_range]

/-- Under the fault bound and `n = 3f+1`, at least `2f+1` parties are honest. -/
theorem quorum_le_honest (P : Params) (R : RoundRun) (hT : P.TimingOK)
    (hF : FaultBound P R) : quorum P ≤ (honestSet P R).card := by
  have := honest_card P R; have := hT.1; unfold FaultBound at hF; unfold quorum; omega

/-- Some party is honest. -/
theorem exists_honest (P : Params) (R : RoundRun) (hT : P.TimingOK) (hF : FaultBound P R) :
    ∃ p, p < P.n ∧ R.honest p = true := by
  obtain ⟨p, hp⟩ : (honestSet P R).Nonempty := by
    rw [← Finset.card_pos]; have := quorum_le_honest P R hT hF; unfold quorum at this; omega
  simp only [honestSet, Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨p, hp⟩

/-! ## Progress -/

/-- After GST, under an honest leader every honest party's vote for the
leader's proposal counts. -/
theorem honest_votes_post_gst (P : Params) (R : RoundRun) (hT : P.TimingOK)
    (hA : Admissible P R) (hL : HonestLeaderRule P R) {v p : Nat}
    (hv : P.gst ≤ v * P.viewLen) (hH : R.honest (leader P v) = true)
    (hp : R.honest p = true) : votes P R v p (R.proposalTo v (leader P v)) = true := by
  obtain ⟨h1, h2⟩ := hA v p hv
  have := hT.2.2
  simp only [votes, hp, ite_true, hL v p hH, beq_self_eq_true, Bool.true_and]
  exact decide_eq_true (by omega)

/-- A view after GST with an honest leader decides the leader's proposal. -/
theorem honest_view_decides (P : Params) (R : RoundRun) (hT : P.TimingOK)
    (hA : Admissible P R) (hW : WellFormed P R) {v : Nat} (hv : P.gst ≤ v * P.viewLen)
    (hH : R.honest (leader P v) = true) :
    ViewDecides P R v (R.proposalTo v (leader P v)) := by
  refine le_trans (quorum_le_honest P R hT hW.1) (Finset.card_le_card ?_)
  intro p hp
  simp only [honestSet, voters, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, honest_votes_post_gst P R hT hA hW.2 hv hH hp.2⟩

/-- Post-GST progress: a decision is observed by `gst + latencyBound`. -/
theorem decided_after_gst (P : Params) (R : RoundRun) (hT : P.TimingOK)
    (hA : Admissible P R) (hW : WellFormed P R) :
    DecidedBy P R (P.gst + latencyBound P) := by
  obtain ⟨p, hp, hHon⟩ := exists_honest P R hT hW.1
  have hn : 0 < P.n := by have := hT.1; omega
  set a := P.gst / P.viewLen + 1
  obtain ⟨hlo, hhi⟩ := target_range P.n a p hn hp
  have hv := first_view_after_gst _ _ hT.2.1 _ hlo
  have hH : R.honest (leader P ((a / P.n + 1) * P.n + p)) = true := by
    rw [leader_target P a p hp]; exact hHon
  exact ⟨_, _, honest_view_decides P R hT hA hW hv hH, view_end_le _ _ _ _ hhi⟩

/-- Decisions persist: `DecidedBy` is monotone in time. -/
theorem decidedBy_mono {P : Params} {R : RoundRun} {t t' : Nat} (h : t ≤ t')
    (hd : DecidedBy P R t) : DecidedBy P R t' := by
  obtain ⟨v, x, hv, hle⟩ := hd
  exact ⟨v, x, hv, le_trans hle h⟩

/-! ## Safety -/

/-- Two quorums of counted votes in one view share an honest party
(`QuorumGeometry.honest_in_inter`, using `n + f < 2q`). -/
theorem honest_common_voter (P : Params) (R : RoundRun) (hT : P.TimingOK)
    (hF : FaultBound P R) {v x y : Nat}
    (hx : ViewDecides P R v x) (hy : ViewDecides P R v y) :
    ∃ p, R.honest p = true ∧ R.proposalTo v p = x ∧ R.proposalTo v p = y := by
  have hsub : ∀ z, voters P R v z ⊆ Finset.range P.n := fun _ => Finset.filter_subset _ _
  obtain ⟨p, hpx, hpy, hpB⟩ := QuorumGeometry.honest_in_inter _ _ _ (byzSet P R) P.n P.f
    (quorum P) (hsub x) (hsub y) (Finset.card_range _) hF hx hy
    (by have := hT.1; unfold quorum; omega)
  simp only [voters, Finset.mem_filter, Finset.mem_range] at hpx hpy
  have hH : R.honest p = true := by
    by_contra h; exact hpB (by simp [byzSet, hpx.1, h])
  simp only [votes, hH, ite_true, Bool.and_eq_true, beq_iff_eq] at hpx hpy
  exact ⟨p, hH, hpx.2.1, hpy.2.1⟩

/-- Validity: a decided value was received as a proposal by an honest party. -/
theorem decided_value_proposed (P : Params) (R : RoundRun) (hT : P.TimingOK)
    (hF : FaultBound P R) {v x : Nat} (hx : ViewDecides P R v x) :
    ∃ p, R.honest p = true ∧ R.proposalTo v p = x := by
  obtain ⟨p, hH, h, _⟩ := honest_common_voter P R hT hF hx hx
  exact ⟨p, hH, h⟩

/-- Agreement within a view: the shared honest voter's single vote fixes the value. -/
theorem view_agreement (P : Params) (R : RoundRun) (hT : P.TimingOK)
    (hF : FaultBound P R) {v x y : Nat}
    (hx : ViewDecides P R v x) (hy : ViewDecides P R v y) : x = y := by
  obtain ⟨p, _, h1, h2⟩ := honest_common_voter P R hT hF hx hy
  exact h1.symm.trans h2

/-- The run's decision is unique: two first decisions are in the same view
and carry the same value. -/
theorem first_decision_unique (P : Params) (R : RoundRun) (hT : P.TimingOK)
    (hF : FaultBound P R) {v w x y : Nat}
    (hx : FirstDecision P R v x) (hy : FirstDecision P R w y) : v = w ∧ x = y := by
  rcases Nat.lt_trichotomy v w with h | rfl | h
  · exact absurd hx.1 (hy.2 v h x)
  · exact ⟨rfl, view_agreement P R hT hF hx.1 hy.1⟩
  · exact absurd hy.1 (hx.2 w h y)

end Rounds
end PartialSynchrony
end Distributed
