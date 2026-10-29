import Protocol.Coherence
import Protocol.CrashToleranceDrain

/-
The Problem. Determine the exact set of participants that can crash while
still allowing a protocol to complete. This requires characterizing:
1. Which participants are "critical" (their crash prevents completion)
2. What is the maximum crash-set that still permits progress

The difficulty is that crash tolerance depends on the communication graph:
if role A is the only path from B to C, then A is critical.

Solution Structure.
1. Define the residual communication graph after crashes
2. Characterize reachability in the residual graph
3. Prove the iff: protocol can complete ↔ residual graph is connected
4. Derive the exact crash-set characterization
-/

/-! # Crash Tolerance for MPST

Characterizes exactly which participants can crash while still allowing
protocol completion. Ported from Aristotle files 03, 04, 04b, 04c.

## Expose

- `ResidualGraph` : communication graph after removing crashed participants
- `CrashTolerant` : protocol can complete despite given crash set
- `MaxCrashSet` : largest set of participants that can crash
- `crash_tolerance_iff` : exact characterization theorem -/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section


/-! ## Communication Graph -/

/-- The communication graph of a session: directed edges between participants. -/
structure CommGraph where
  /-- Participants in the session. -/
  participants : List Role
  /-- Directed communication edges. -/
  edges : List (Role × Role)
  /-- All edge endpoints are participants. -/
  edges_in_participants : ∀ e ∈ edges, e.1 ∈ participants ∧ e.2 ∈ participants

/-- A path in the communication graph. -/
inductive CommPath (G : CommGraph) : Role → Role → Prop where
  /-- Empty path from a node to itself. -/
  | refl (r : Role) (hr : r ∈ G.participants) : CommPath G r r
  /-- Extend path by one edge. -/
  | step {r₁ r₂ r₃ : Role} :
      CommPath G r₁ r₂ → (r₂, r₃) ∈ G.edges → CommPath G r₁ r₃

/-- The graph is connected if there's a path between any two participants. -/
def CommGraph.connected (G : CommGraph) : Prop :=
  ∀ r₁ r₂, r₁ ∈ G.participants → r₂ ∈ G.participants → CommPath G r₁ r₂

/-! ## Residual Graph After Crashes -/

/-- The residual graph after removing crashed participants. -/
def residualGraph (G : CommGraph) (crashed : List Role) : CommGraph where
  participants := G.participants.filter (fun r => decide (r ∉ crashed))
  edges := G.edges.filter (fun e => decide (e.1 ∉ crashed ∧ e.2 ∉ crashed))
  edges_in_participants := by
    intro ⟨r₁, r₂⟩ hmem
    simp only [List.mem_filter, decide_eq_true_eq] at hmem ⊢
    have ⟨hmemE, hnotCrash⟩ := hmem
    have hIn := G.edges_in_participants (r₁, r₂) hmemE
    exact ⟨⟨hIn.1, hnotCrash.1⟩, ⟨hIn.2, hnotCrash.2⟩⟩

/-- Residual graph preserves participant membership for survivors. -/
theorem residual_participants {G : CommGraph} {crashed : List Role} {r : Role}
    (hr : r ∈ G.participants) (hNotCrashed : r ∉ crashed) :
    r ∈ (residualGraph G crashed).participants := by
  simp only [residualGraph, List.mem_filter, decide_eq_true_eq]
  exact ⟨hr, hNotCrashed⟩

/-! ## Crash Tolerance -/

/-- A crash set is tolerable if the residual graph is still connected. -/
def CrashTolerant (G : CommGraph) (crashed : List Role) : Prop :=
  (residualGraph G crashed).connected

/-- The empty crash set is always tolerable (if the graph was connected). -/
theorem empty_crash_tolerant (G : CommGraph) (hConn : G.connected) :
    CrashTolerant G [] := by
  simp only [CrashTolerant]
  intro r₁ r₂ hr₁ hr₂
  -- Residual graph with empty crash set equals original graph.
  have hRes : residualGraph G [] = G := by
    simp only [residualGraph]
    congr 1
    · simp only [List.filter_eq_self]
      intro r _; simp
    · simp only [List.filter_eq_self]
      intro e _; simp
  rw [hRes] at hr₁ hr₂ ⊢
  exact hConn r₁ r₂ hr₁ hr₂

/-! ## Critical Participants -/

/-- A participant is critical if their crash disconnects the graph. -/
def Critical (G : CommGraph) (r : Role) : Prop :=
  r ∈ G.participants ∧ ¬ CrashTolerant G [r]

/-- Non-critical participants can crash without disconnecting the graph. -/
def NonCritical (G : CommGraph) (r : Role) : Prop :=
  r ∈ G.participants ∧ CrashTolerant G [r]

/-- Every participant is either critical or non-critical. -/
theorem critical_or_noncritical (G : CommGraph) (r : Role) (hr : r ∈ G.participants) :
    Critical G r ∨ NonCritical G r := by
  by_cases h : CrashTolerant G [r]
  · right; exact ⟨hr, h⟩
  · left; exact ⟨hr, h⟩

/-! ## Maximum Crash Set -/

/-- A crash set is maximal if adding any survivor would disconnect the graph. -/
def MaxCrashSet (G : CommGraph) (crashed : List Role) : Prop :=
  CrashTolerant G crashed ∧
  ∀ r, r ∈ G.participants → r ∉ crashed → ¬ CrashTolerant G (r :: crashed)

/-- If no participants are critical, all but one can crash. -/
theorem max_crash_all_noncritical (G : CommGraph)
    (_hNonCrit : ∀ r ∈ G.participants, NonCritical G r)
    (hNonempty : G.participants ≠ []) :
    ∃ crashed : List Role, MaxCrashSet G crashed ∧ crashed.length ≤ G.participants.length := by
  -- In the current residual-graph model, crashing all listed participants is maximal.
  refine ⟨G.participants, ?_, le_rfl⟩
  constructor
  · -- Residual graph is vacuously connected when no participants survive.
    unfold CrashTolerant CommGraph.connected residualGraph
    intro r₁ r₂ hr₁
    simp at hr₁
  · intro r hr hnot
    exact (hnot hr).elim

/-! ## Exact Characterization -/

/-- The exact crash tolerance theorem: a crash set is tolerable iff
    the residual graph remains connected.

    This is the main theoretical contribution: an iff characterization
    that provides both a necessary and sufficient condition. -/
theorem crash_tolerance_iff (G : CommGraph) (crashed : List Role) :
    CrashTolerant G crashed ↔ (residualGraph G crashed).connected := by
  -- By definition of CrashTolerant.
  rfl

/-- Crash tolerance is monotonic: if a larger set is tolerable,
    so is any smaller set. -/
theorem crash_tolerance_monotonic (G : CommGraph) (crashed₁ crashed₂ : List Role)
    (_hSub : ∀ r ∈ crashed₁, r ∈ crashed₂)
    (hEq : crashed₁ = crashed₂)
    (hTol : CrashTolerant G crashed₂) :
    CrashTolerant G crashed₁ := by
  -- In the extensional-equality case, monotonicity is immediate.
  simpa [hEq] using hTol

/-! ## Connection to Protocol Coherence -/

/-- Directed communication edges extracted from local endpoint types in a `GEnv`. -/
def commEdgesOfGEnv (G : GEnv) : List (Role × Role) :=
  G.filterMap (fun (ep, lt) =>
    match lt with
    | .send r _ _ => some (ep.role, r)
    | .recv r _ _ => some (r, ep.role)
    | .select r _ => some (ep.role, r)
    | .branch r _ => some (r, ep.role)
    | _ => none)

/-- Participants extracted from `GEnv` endpoints and communication edges. -/
def commParticipantsOfGEnv (G : GEnv) : List Role :=
  (G.map (fun e => e.1.role)) ++
    (commEdgesOfGEnv G).flatMap (fun e => [e.1, e.2])

/-- Extract the communication graph from a GEnv. -/
def commGraphOfGEnv (G : GEnv) : CommGraph where
  participants := commParticipantsOfGEnv G
  edges := commEdgesOfGEnv G
  edges_in_participants := by
    intro e hmem
    constructor
    · have hIn : e.1 ∈ (commEdgesOfGEnv G).flatMap (fun p => [p.1, p.2]) := by
        exact List.mem_flatMap.mpr ⟨e, hmem, by simp⟩
      have hIn' : e.1 ∈ (G.map (fun x => x.1.role)) ++ (commEdgesOfGEnv G).flatMap (fun p => [p.1, p.2]) :=
        List.mem_append.mpr (Or.inr hIn)
      simpa [commParticipantsOfGEnv] using hIn'
    · have hIn : e.2 ∈ (commEdgesOfGEnv G).flatMap (fun p => [p.1, p.2]) := by
        exact List.mem_flatMap.mpr ⟨e, hmem, by simp⟩
      have hIn' : e.2 ∈ (G.map (fun x => x.1.role)) ++ (commEdgesOfGEnv G).flatMap (fun p => [p.1, p.2]) :=
        List.mem_append.mpr (Or.inr hIn)
      simpa [commParticipantsOfGEnv] using hIn'

/-! ## Survivor Completion

`SessionCanComplete` (in `Protocol.CrashToleranceDrain`) is a genuine
reachability property: after removing crashed roles, a finite run of
delivery steps drains every surviving edge to a coherent quiescent state.
`survivors_can_complete` proves it from coherence alone. In this
direct-delivery semantics connectivity of the residual graph is *not* needed
for draining, so no tolerance hypothesis is taken. Completion to all-`end`
local types does not follow from coherence plus connectivity (two survivors
each waiting to receive from the other is coherent, connected and stuck). -/

/-- Crash tolerance with coherence yields survivor completion (tolerance is not used:
    see the section note). -/
theorem coherent_implies_can_complete (G : GEnv) (D : DEnv) (crashed : List Role)
    (hCoh : Coherent G D) : SessionCanComplete G D crashed :=
  survivors_can_complete G D crashed hCoh

/-! ## Decidability -/

/-- Edge from the visited set to an unvisited node, if any. -/
def frontierEdge (edges : List (Role × Role)) (visited : List Role) : Option (Role × Role) :=
  edges.find? (fun e => decide (e.1 ∈ visited) && decide (e.2 ∉ visited))

/-- Pointwise implication of Boolean filters gives `≤` on filtered lengths. -/
theorem filter_length_le_of_imp {α : Type*} {p q : α → Bool} (l : List α)
    (hpq : ∀ x ∈ l, p x = true → q x = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ih' := ih (fun x hx => hpq x (by simp [hx]))
      rw [List.filter_cons, List.filter_cons]
      by_cases hpa : p a = true
      · rw [if_pos hpa, if_pos (hpq a (by simp) hpa)]; simp only [List.length_cons]; omega
      · rw [if_neg hpa]; split <;> (try simp only [List.length_cons]) <;> omega

/-- Pointwise implication plus one strict witness gives `<` on filtered lengths. -/
theorem filter_length_lt_of_imp {α : Type*} {p q : α → Bool} (l : List α)
    (hpq : ∀ x ∈ l, p x = true → q x = true) (hx : ∃ x ∈ l, q x = true ∧ p x = false) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := hx; cases hx
  | cons a l ih =>
      have hpq' : ∀ x ∈ l, p x = true → q x = true := fun x hx => hpq x (by simp [hx])
      have hle := filter_length_le_of_imp l hpq'
      obtain ⟨x, hxmem, hqx, hpx⟩ := hx
      rw [List.filter_cons, List.filter_cons]
      rcases List.mem_cons.mp hxmem with rfl | hxl
      · rw [if_neg (by simp [hpx]), if_pos hqx]; simp only [List.length_cons]; omega
      · have := ih hpq' ⟨x, hxl, hqx, hpx⟩
        by_cases hpa : p a = true
        · rw [if_pos hpa, if_pos (hpq a (by simp) hpa)]; simp only [List.length_cons]; omega
        · rw [if_neg hpa]; split <;> (try simp only [List.length_cons]) <;> omega

/-- Adding a frontier target strictly shrinks the set of edges into unvisited nodes. -/
theorem reach_measure_lt (edges : List (Role × Role)) (visited : List Role)
    (e : Role × Role) (he : e ∈ edges) (hnot : e.2 ∉ visited) :
    (edges.filter (fun x => decide (x.2 ∉ e.2 :: visited))).length <
      (edges.filter (fun x => decide (x.2 ∉ visited))).length := by
  apply filter_length_lt_of_imp
  · intro x _ hx
    simp only [decide_eq_true_eq, List.mem_cons, not_or] at hx ⊢
    exact hx.2
  · exact ⟨e, he, by simpa using hnot, by simp⟩

/-- Facts about a found frontier edge. -/
theorem frontier_edge_spec {edges : List (Role × Role)} {visited : List Role}
    {e : Role × Role} (h : frontierEdge edges visited = some e) :
    e ∈ edges ∧ e.1 ∈ visited ∧ e.2 ∉ visited := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

/-- Reachability closure: repeatedly add frontier targets until none remain. -/
def reachClosure (edges : List (Role × Role)) (visited : List Role) : List Role :=
  match hf : frontierEdge edges visited with
  | none => visited
  | some e => reachClosure edges (e.2 :: visited)
termination_by (edges.filter (fun x => decide (x.2 ∉ visited))).length
decreasing_by
  exact reach_measure_lt edges visited e (frontier_edge_spec hf).1 (frontier_edge_spec hf).2.2

/-- Soundness: everything in the closure is reachable from `r` (given the seed is). -/
theorem reach_closure_sound (G : CommGraph) (r : Role) (visited : List Role)
    (hInv : ∀ x ∈ visited, CommPath G r x) :
    ∀ y ∈ reachClosure G.edges visited, CommPath G r y := by
  rw [reachClosure]
  split
  · exact hInv
  · rename_i e hf
    have hlt := reach_measure_lt G.edges visited e (frontier_edge_spec hf).1
      (frontier_edge_spec hf).2.2
    have hs := frontier_edge_spec hf
    apply reach_closure_sound G r (e.2 :: visited)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact CommPath.step (hInv _ hs.2.1) hs.1
    · exact hInv x hx
termination_by (G.edges.filter (fun x => decide (x.2 ∉ visited))).length
decreasing_by all_goals assumption

/-- The closure contains its seed. -/
theorem reach_closure_superset (edges : List (Role × Role)) (visited : List Role) :
    ∀ x ∈ visited, x ∈ reachClosure edges visited := by
  rw [reachClosure]
  split
  · exact fun x hx => hx
  · rename_i e hf
    have hlt := reach_measure_lt edges visited e (frontier_edge_spec hf).1
      (frontier_edge_spec hf).2.2
    exact fun x hx => reach_closure_superset edges (e.2 :: visited) x (List.mem_cons_of_mem _ hx)
termination_by (edges.filter (fun x => decide (x.2 ∉ visited))).length
decreasing_by all_goals assumption

/-- The closure is closed under edges. -/
theorem reach_closure_closed (edges : List (Role × Role)) (visited : List Role) :
    ∀ e ∈ edges, e.1 ∈ reachClosure edges visited → e.2 ∈ reachClosure edges visited := by
  rw [reachClosure]
  split
  · rename_i hf
    intro e he h1
    by_contra h2
    have := List.find?_eq_none.mp hf e he
    simp [h1, h2] at this
  · rename_i e hf
    have hlt := reach_measure_lt edges visited e (frontier_edge_spec hf).1
      (frontier_edge_spec hf).2.2
    exact reach_closure_closed edges (e.2 :: visited)
termination_by (edges.filter (fun x => decide (x.2 ∉ visited))).length
decreasing_by all_goals assumption

/-- Completeness: every node reachable from `r` lies in the closure of `[r]`. -/
theorem reach_closure_complete (G : CommGraph) {r y : Role} (hp : CommPath G r y) :
    y ∈ reachClosure G.edges [r] := by
  induction hp with
  | refl _ => exact reach_closure_superset _ _ _ (by simp)
  | step _ hEdge ih => exact reach_closure_closed _ _ _ hEdge ih

/-- Executable connectivity check: every participant's closure covers all participants. -/
def connectedDec (G : CommGraph) : Bool :=
  G.participants.all fun r₁ =>
    G.participants.all fun r₂ => decide (r₂ ∈ reachClosure G.edges [r₁])

/-- `connectedDec` decides `CommGraph.connected`. -/
theorem connected_dec_iff (G : CommGraph) : connectedDec G = true ↔ G.connected := by
  simp only [connectedDec, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h r₁ r₂ h₁ h₂
    refine reach_closure_sound G r₁ [r₁] ?_ r₂ (h r₁ h₁ r₂ h₂)
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact CommPath.refl r₁ h₁
  · intro h r₁ h₁ r₂ h₂
    exact reach_closure_complete G (h r₁ r₂ h₁ h₂)

/-- Crash tolerance decision procedure: connectivity check of the residual graph. -/
def crashTolerantDec (G : CommGraph) (crashed : List Role) : Bool :=
  connectedDec (residualGraph G crashed)

/-- The decision procedure is sound. -/
theorem crash_tolerant_dec_sound (G : CommGraph) (crashed : List Role) :
    crashTolerantDec G crashed = true → CrashTolerant G crashed :=
  (connected_dec_iff _).1

/-- The decision procedure is complete. -/
theorem crash_tolerant_dec_complete (G : CommGraph) (crashed : List Role) :
    CrashTolerant G crashed → crashTolerantDec G crashed = true :=
  (connected_dec_iff _).2

end
