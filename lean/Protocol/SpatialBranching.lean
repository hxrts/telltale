import Protocol.SpatialCore
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-! # MPST Spatial Type System (Branching)

Branching feasibility via confusability graphs and capacity-style characterizations.
-/

/-
The Problem. Determine when branch labels are deployable over a topology.

Solution Structure. Define confusability/capacity objects and prove feasibility characterizations.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open SpatialNotation
/-! ## Branching Feasibility

Connection between topology and branching feasibility. Determines when
a branching choice can be correctly deployed on a given topology.

**Key insight**: A branching choice is feasible if the topology provides
sufficient channel capacity to distinguish all branch labels. This is
captured by the confusability graph: labels l₁ and l₂ are confusable
if they can reach the same observable state via the same channel.

Ported from Aristotle files 07, 07b (complete).
-/

/-- Channel capacity in bits (logarithmic). -/
abbrev ChannelCapacity := Nat

/-- A confusability relation between labels.
    Labels are confusable if they can be confused by an observer. -/
def Confusable (L : Type*) := L → L → Prop

/-- Two labels are trivially not confusable if they're different and
    the channel has sufficient capacity to distinguish them. -/
def notConfusableByCapacity (numLabels capacity : Nat) : Prop :=
  numLabels ≤ 2 ^ capacity

/-- Minimum channel capacity needed to distinguish n labels. -/
def minCapacity (numLabels : Nat) : Nat :=
  Nat.clog 2 numLabels

/-- minCapacity is sufficient. -/
theorem min_capacity_sufficient (n : Nat) (_hn : 0 < n) :
    notConfusableByCapacity n (minCapacity n) := by
  simp only [notConfusableByCapacity, minCapacity]
  exact Nat.le_pow_clog (by omega) n

/-- The confusability graph for a set of branch labels.
    Labels l₁ and l₂ are in the same clique if they can be confused. -/
structure ConfusabilityGraph (L : Type*) where
  /-- The labels. -/
  labels : List L
  /-- Confusability relation (symmetric). -/
  confusable : L → L → Bool
  /-- Symmetry of confusability. -/
  symm : ∀ l₁ l₂, confusable l₁ l₂ = confusable l₂ l₁

/-- A graph is distinguishable if no two distinct labels are confusable. -/
def ConfusabilityGraph.distinguishable {L : Type*} (g : ConfusabilityGraph L) : Prop :=
  ∀ l₁ l₂, l₁ ∈ g.labels → l₂ ∈ g.labels → l₁ ≠ l₂ → g.confusable l₁ l₂ = false

/-- Boolean check for distinguishability. -/
def ConfusabilityGraph.distinguishableBool {L : Type*} [DecidableEq L]
    (g : ConfusabilityGraph L) : Bool :=
  g.labels.all fun l₁ =>
    g.labels.all fun l₂ =>
      l₁ = l₂ || g.confusable l₁ l₂ = false

/-- Boolean distinguishability reflects the propositional version. -/
theorem ConfusabilityGraph.distinguishable_bool_iff {L : Type*} [DecidableEq L]
    (g : ConfusabilityGraph L) :
    g.distinguishableBool = true ↔ g.distinguishable := by
  simp only [distinguishableBool, distinguishable, List.all_eq_true, Bool.or_eq_true]
  constructor
  · intro h l₁ l₂ h₁ h₂ hne
    have := h l₁ h₁ l₂ h₂
    cases this with
    | inl heq =>
      simp only [decide_eq_true_eq] at heq
      exact absurd heq hne
    | inr hconf =>
      simp only [decide_eq_true_eq] at hconf
      exact hconf
  · intro h l₁ h₁ l₂ h₂
    by_cases heq : l₁ = l₂
    · left; simp only [decide_eq_true_eq]; exact heq
    · right; simp only [decide_eq_true_eq]; exact h l₁ l₂ h₁ h₂ heq


/-! ## Confusability as a Simple Graph -/

/-- The confusability graph as a Mathlib simple graph on label positions:
    two positions are adjacent iff they carry distinct, confusable labels. -/
def ConfusabilityGraph.toSimpleGraph {L : Type*} (g : ConfusabilityGraph L) :
    SimpleGraph (Fin g.labels.length) :=
  SimpleGraph.fromRel fun i j => g.labels[i] ≠ g.labels[j] ∧ g.confusable g.labels[i] g.labels[j] = true

/-- Unfolding of adjacency in `toSimpleGraph`. -/
theorem ConfusabilityGraph.to_simple_graph_adj {L : Type*} (g : ConfusabilityGraph L)
    (i j : Fin g.labels.length) :
    g.toSimpleGraph.Adj i j ↔ i ≠ j ∧
      ((g.labels[i] ≠ g.labels[j] ∧ g.confusable g.labels[i] g.labels[j] = true) ∨
       (g.labels[j] ≠ g.labels[i] ∧ g.confusable g.labels[j] g.labels[i] = true)) :=
  Iff.rfl

/-- Genuine chromatic number of the confusability graph (Mathlib
    `SimpleGraph.chromaticNumber`): the least number of codewords such that
    any two distinct confusable labels receive distinct codewords. -/
noncomputable def ConfusabilityGraph.chromaticNumberProp {L : Type*}
    (g : ConfusabilityGraph L) : ℕ∞ :=
  g.toSimpleGraph.chromaticNumber

/-- A distinguishable graph has no edges, so one colour suffices: `χ(G) ≤ 1`. -/
theorem ConfusabilityGraph.chromatic_le_one_of_distinguishable {L : Type*}
    (g : ConfusabilityGraph L) (h : g.distinguishable) : g.chromaticNumberProp ≤ 1 := by
  unfold chromaticNumberProp
  rw [← Nat.cast_one, SimpleGraph.chromaticNumber_le_iff_colorable]
  refine ⟨SimpleGraph.Coloring.mk (fun _ => 0) ?_⟩
  intro i j hadj
  exfalso
  rcases (g.to_simple_graph_adj i j).1 hadj with ⟨_, ⟨hne, hc⟩ | ⟨hne, hc⟩⟩
  · rw [h _ _ (by simp) (by simp) hne] at hc; exact Bool.false_ne_true hc
  · rw [h _ _ (by simp) (by simp) hne] at hc; exact Bool.false_ne_true hc

/-- Every pair of distinct labels is confusable and labels are duplicate-free. -/
def ConfusabilityGraph.fullyConfusable {L : Type*} (g : ConfusabilityGraph L) : Prop :=
  g.labels.Nodup ∧
    ∀ l₁ l₂, l₁ ∈ g.labels → l₂ ∈ g.labels → l₁ ≠ l₂ → g.confusable l₁ l₂ = true

/-- A fully confusable graph is the complete graph on label positions. -/
theorem ConfusabilityGraph.to_simple_graph_eq_top {L : Type*} (g : ConfusabilityGraph L)
    (h : g.fullyConfusable) : g.toSimpleGraph = ⊤ := by
  ext i j
  rw [g.to_simple_graph_adj, SimpleGraph.top_adj]
  refine ⟨fun hadj => hadj.1, fun hne => ⟨hne, Or.inl ?_⟩⟩
  have hl : g.labels[i] ≠ g.labels[j] := fun heq =>
    hne (Fin.ext ((List.Nodup.getElem_inj_iff h.1).1 heq))
  exact ⟨hl, h.2 _ _ (by simp) (by simp) hl⟩

/-- For a fully confusable graph, `χ(G) = |labels|`. -/
theorem ConfusabilityGraph.chromatic_eq_length_of_fully_confusable {L : Type*}
    (g : ConfusabilityGraph L) (h : g.fullyConfusable) :
    g.chromaticNumberProp = g.labels.length := by
  unfold chromaticNumberProp
  rw [g.to_simple_graph_eq_top h, SimpleGraph.chromaticNumber_top, Fintype.card_fin]

/-- `χ(G)` never exceeds the number of labels. -/
theorem ConfusabilityGraph.chromatic_le_length {L : Type*} (g : ConfusabilityGraph L) :
    g.chromaticNumberProp ≤ g.labels.length := by
  unfold chromaticNumberProp
  calc g.toSimpleGraph.chromaticNumber ≤ (Fintype.card (Fin g.labels.length) : ℕ∞) :=
        SimpleGraph.chromaticNumber_le_card
    _ = g.labels.length := by rw [Fintype.card_fin]

/-! ## Branch Feasibility Objects -/

/-- A branching choice is feasible on a topology if the channel capacity
    is sufficient to distinguish all branch labels. -/
structure BranchFeasibility (L : Type*) where
  /-- The branch labels. -/
  labels : List L
  /-- Required channel capacity (in bits). -/
  requiredCapacity : Nat := minCapacity labels.length
  /-- The sending role. -/
  sender : RoleName
  /-- The receiving role. -/
  receiver : RoleName

/-- Per-edge channel capacity (bits per branch decision) between two sites. -/
abbrev CapacityMap := Site → Site → ChannelCapacity

/-- Capacity of the channel from `sender` to `receiver`: the declared edge
    capacity if a reliable edge exists, and `0` otherwise. -/
def Topology.channelCapacity (topo : Topology) (cap : CapacityMap)
    (sender receiver : RoleName) : ChannelCapacity :=
  if topo.hasEdge (topo.siteOf sender) (topo.siteOf receiver) then
    cap (topo.siteOf sender) (topo.siteOf receiver)
  else 0

/-- The channel carries enough bits for both the declared requirement and
    `⌈log₂ |labels|⌉` (enough to encode every label distinctly). -/
def Topology.hasSufficientCapacity {L : Type*} (topo : Topology) (cap : CapacityMap)
    (b : BranchFeasibility L) : Prop :=
  b.requiredCapacity ≤ topo.channelCapacity cap b.sender b.receiver ∧
    minCapacity b.labels.length ≤ topo.channelCapacity cap b.sender b.receiver

/-- A topology supports a branching choice if the edge is reliable and its
    capacity suffices to encode all labels. -/
def Topology.supportsBranch {L : Type*} (topo : Topology) (cap : CapacityMap)
    (b : BranchFeasibility L) : Prop :=
  (topo ⊨ .reliableEdge b.sender b.receiver) ∧ topo.hasSufficientCapacity cap b

/-- Spatial requirement for a branching choice. -/
def branchReq {L : Type*} (b : BranchFeasibility L) : SpatialReq :=
  .reliableEdge b.sender b.receiver

/-- Feasibility splits into the spatial requirement and the capacity bound. -/
theorem branch_feasible_iff_satisfies {L : Type*} (topo : Topology) (cap : CapacityMap)
    (b : BranchFeasibility L) :
    topo.supportsBranch cap b ↔ (topo ⊨ branchReq b) ∧ topo.hasSufficientCapacity cap b :=
  Iff.rfl

/-- The `⌈log₂ n⌉` bound is equivalent to `n ≤ 2^capacity`. -/
theorem min_capacity_le_iff (n c : Nat) :
    minCapacity n ≤ c ↔ notConfusableByCapacity n c :=
  Nat.clog_le_iff_le_pow (by norm_num)

/-! ## Confusability and Distinguishability -/

/-- Two labels are distinguishable if they're not confusable. -/
def distinguishable {L : Type*} (g : ConfusabilityGraph L) (l₁ l₂ : L) : Prop :=
  g.confusable l₁ l₂ = false

/-- A branching choice is deployable if all labels are pairwise distinguishable. -/
def BranchFeasibility.deployable {L : Type*} [DecidableEq L]
    (b : BranchFeasibility L) (g : ConfusabilityGraph L) : Prop :=
  g.distinguishable ∧ g.labels = b.labels

/-- If a branching choice is deployable, the confusability graph is empty. -/
theorem deployable_empty_confusability {L : Type*} [DecidableEq L]
    (b : BranchFeasibility L) (g : ConfusabilityGraph L)
    (hDep : b.deployable g) :
    ∀ l₁ l₂, l₁ ∈ b.labels → l₂ ∈ b.labels → l₁ ≠ l₂ → g.confusable l₁ l₂ = false := by
  intro l₁ l₂ h₁ h₂ hne
  have hDist := hDep.1
  rw [← hDep.2] at h₁ h₂
  exact hDist l₁ l₂ h₁ h₂ hne

/-! ## Capacity Bounds -/

/-- Sufficient capacity for more than one label forces a reliable edge
    (absent edges have capacity `0`), hence feasibility. -/
theorem sufficient_capacity_implies_feasible {L : Type*} (topo : Topology) (cap : CapacityMap)
    (b : BranchFeasibility L) (hCap : topo.hasSufficientCapacity cap b)
    (hPos : 1 < b.labels.length) :
    topo.supportsBranch cap b := by
  refine ⟨?_, hCap⟩
  simp only [Satisfies]
  by_contra hNo
  have hMin : 0 < minCapacity b.labels.length := Nat.clog_pos (by omega) hPos
  have h2 := hCap.2
  unfold Topology.channelCapacity at h2
  rw [if_neg hNo] at h2
  omega

/-! ## Independence Number and Feasibility Characterization

The independence number of a graph is the size of the largest independent set
(set of vertices with no edges between them). For confusability graphs:
- An independent set = labels that are pairwise distinguishable
- Branching is feasible iff independence number ≥ number of labels
-/

/-- An independent set in a confusability graph: no two vertices are confusable. -/
def ConfusabilityGraph.IsIndependentSet {L : Type*} (g : ConfusabilityGraph L) (S : List L) : Prop :=
  ∀ l₁ ∈ S, ∀ l₂ ∈ S, l₁ ≠ l₂ → g.confusable l₁ l₂ = false

/-- Independence number: maximum size of an independent set.
    For a distinguishable graph (no confusable pairs), this equals |labels|. -/
def ConfusabilityGraph.independenceNumber {L : Type*} [DecidableEq L]
    (g : ConfusabilityGraph L) : Nat :=
  if g.distinguishableBool then g.labels.length else 0

/-- A distinguishable graph has independence number equal to label count. -/
theorem distinguishable_independence_eq_length {L : Type*} [DecidableEq L]
    (g : ConfusabilityGraph L) (h : g.distinguishable) :
    g.independenceNumber = g.labels.length := by
  simp only [ConfusabilityGraph.independenceNumber]
  rw [if_pos (g.distinguishable_bool_iff.mpr h)]

/-- The full label set is an independent set when the graph is distinguishable. -/
theorem distinguishable_labels_independent {L : Type*} [DecidableEq L]
    (g : ConfusabilityGraph L) (h : g.distinguishable) :
    g.IsIndependentSet g.labels := by
  intro l₁ h₁ l₂ h₂ hne
  exact h l₁ l₂ h₁ h₂ hne

/-! ## Main Characterization Theorems -/

/-- Branching is deployable with distinguishable labels iff the independence
    number covers all labels and the topology supports the branch. -/
theorem branching_deployable_iff {L : Type*} [DecidableEq L]
    (topo : Topology) (cap : CapacityMap) (b : BranchFeasibility L) (g : ConfusabilityGraph L)
    (hLabels : g.labels = b.labels) :
    (g.distinguishable ∧ topo.supportsBranch cap b) ↔
      (g.independenceNumber ≥ b.labels.length ∧ topo.supportsBranch cap b) := by
  constructor
  · rintro ⟨hDist, hSupp⟩
    exact ⟨by rw [distinguishable_independence_eq_length g hDist, hLabels], hSupp⟩
  · rintro ⟨hInd, hSupp⟩
    refine ⟨?_, hSupp⟩
    intro l₁ l₂ h₁ h₂ hne
    simp only [ConfusabilityGraph.independenceNumber] at hInd
    split_ifs at hInd with hDistBool
    · exact (g.distinguishable_bool_iff.mp hDistBool) l₁ l₂ h₁ h₂ hne
    · have hLen : b.labels.length = 0 := Nat.le_zero.mp hInd
      rw [hLabels, List.length_eq_zero_iff.mp hLen] at h₁
      simp at h₁

/-! ## Chromatic (Zero-Error) Feasibility -/

/-- Zero-error branch deployment: a reliable edge whose `2^capacity`
    codewords suffice to colour the confusability graph (`χ(G) ≤ 2^capacity`). -/
def Topology.supportsBranchVia {L : Type*} (topo : Topology) (cap : CapacityMap)
    (b : BranchFeasibility L) (g : ConfusabilityGraph L) : Prop :=
  g.labels = b.labels ∧ (topo ⊨ .reliableEdge b.sender b.receiver) ∧
    g.chromaticNumberProp ≤ ((2 ^ topo.channelCapacity cap b.sender b.receiver : ℕ) : ℕ∞)

/-- `χ(G) ≤ k` iff there is an encoding of label positions into `k` codewords
    separating every pair of distinct confusable labels. -/
theorem chromatic_le_iff_encoding {L : Type*} (g : ConfusabilityGraph L) (k : ℕ) :
    g.chromaticNumberProp ≤ k ↔
      ∃ enc : Fin g.labels.length → Fin k, ∀ i j,
        g.labels[i] ≠ g.labels[j] → g.confusable g.labels[i] g.labels[j] = true → enc i ≠ enc j := by
  unfold ConfusabilityGraph.chromaticNumberProp
  rw [SimpleGraph.chromaticNumber_le_iff_colorable]
  constructor
  · rintro ⟨C⟩
    refine ⟨fun i => C i, fun i j hne hc => C.valid ?_⟩
    exact (g.to_simple_graph_adj i j).2 ⟨by rintro rfl; exact hne rfl, Or.inl ⟨hne, hc⟩⟩
  · rintro ⟨enc, henc⟩
    refine ⟨SimpleGraph.Coloring.mk enc ?_⟩
    intro i j hadj
    rcases (g.to_simple_graph_adj i j).1 hadj with ⟨_, ⟨hne, hc⟩ | ⟨hne, hc⟩⟩
    · exact henc i j hne hc
    · exact (henc j i hne hc).symm

/-- Chromatic characterization: zero-error branching is feasible iff the
    edge is reliable and the labels admit a separating `2^capacity`-ary code. -/
theorem branching_iff_chromatic_capacity {L : Type*}
    (topo : Topology) (cap : CapacityMap) (b : BranchFeasibility L) (g : ConfusabilityGraph L) :
    topo.supportsBranchVia cap b g ↔
      g.labels = b.labels ∧ (topo ⊨ .reliableEdge b.sender b.receiver) ∧
        ∃ enc : Fin g.labels.length → Fin (2 ^ topo.channelCapacity cap b.sender b.receiver),
          ∀ i j, g.labels[i] ≠ g.labels[j] →
            g.confusable g.labels[i] g.labels[j] = true → enc i ≠ enc j := by
  unfold Topology.supportsBranchVia
  rw [chromatic_le_iff_encoding]

/-- Distinguishable labels over a reliable edge are always deployable:
    `χ(G) ≤ 1 ≤ 2^capacity`. -/
theorem branching_feasible_of_distinguishable {L : Type*}
    (topo : Topology) (cap : CapacityMap) (b : BranchFeasibility L) (g : ConfusabilityGraph L)
    (hLabels : g.labels = b.labels) (hDist : g.distinguishable)
    (hEdge : topo ⊨ .reliableEdge b.sender b.receiver) :
    topo.supportsBranchVia cap b g := by
  refine ⟨hLabels, hEdge, le_trans (g.chromatic_le_one_of_distinguishable hDist) ?_⟩
  exact_mod_cast Nat.one_le_two_pow

/-- Capacity-based support implies zero-error support for any confusability graph. -/
theorem supports_branch_via_of_supports {L : Type*}
    (topo : Topology) (cap : CapacityMap) (b : BranchFeasibility L) (g : ConfusabilityGraph L)
    (hLabels : g.labels = b.labels) (h : topo.supportsBranch cap b) :
    topo.supportsBranchVia cap b g := by
  refine ⟨hLabels, h.1, le_trans g.chromatic_le_length ?_⟩
  have hLen := (min_capacity_le_iff _ _).1 h.2.2
  rw [hLabels]
  exact_mod_cast hLen

/-- For fully confusable labels the two notions coincide (given the declared requirement). -/
theorem supports_branch_of_via_fully_confusable {L : Type*}
    (topo : Topology) (cap : CapacityMap) (b : BranchFeasibility L) (g : ConfusabilityGraph L)
    (hFull : g.fullyConfusable) (hReq : b.requiredCapacity ≤ topo.channelCapacity cap b.sender b.receiver)
    (h : topo.supportsBranchVia cap b g) :
    topo.supportsBranch cap b := by
  obtain ⟨hLabels, hEdge, hChi⟩ := h
  rw [g.chromatic_eq_length_of_fully_confusable hFull, hLabels] at hChi
  refine ⟨hEdge, hReq, (min_capacity_le_iff _ _).2 ?_⟩
  exact_mod_cast hChi

/-! ## Summary

1. **ConfusabilityGraph** / `toSimpleGraph`: confusable labels as a Mathlib graph
2. **chromaticNumberProp**: genuine chromatic number (`SimpleGraph.chromaticNumber`)
3. **supportsBranch**: reliable edge + capacity `≥ ⌈log₂ |labels|⌉` and requirement
4. **branching_iff_chromatic_capacity**: zero-error feasibility iff `χ(G) ≤ 2^capacity`
   iff a separating code exists
5. **supports_branch_via_of_supports** / **supports_branch_of_via_fully_confusable**:
   counting and chromatic notions agree on fully confusable label sets

Note: `independenceNumber` above remains a coarse proxy (all labels or zero),
not the graph-theoretic independence number.
-/
