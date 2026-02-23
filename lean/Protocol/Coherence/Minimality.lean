import Protocol.Coherence.ErasureCharacterization

/-! # Protocol.Coherence.Minimality

Coherence lemmas and invariants for session-environment evolution.
-/

/-
The Problem. Show that Coherence is a minimal invariant: any weakening that
ignores some active edges admits well-typed but incoherent states.

Solution Structure.
1. Define a weaker predicate `WeakCoherent` that checks only blocked receivers.
2. Build a concrete counterexample that is weakly coherent but not coherent.
3. Derive consequences for delegation and invariant conservativity.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Weak Coherence -/

/-- Receiver-local "blocked" shape: waiting for an incoming message/label. -/
def isBlockedLocal : LocalType -> Prop
  | .recv _ _ _ => True
  | .branch _ _ => True
  | _ => False

/-- An edge is blocked when its receiver endpoint is currently in a blocked shape. -/
def BlockedEdge (G : GEnv) (e : Edge) : Prop :=
  match lookupG G { sid := e.sid, role := e.receiver } with
  | some L => isBlockedLocal L
  | none => False

/-- Weak coherence checks only active edges whose receiver is blocked. -/
def WeakCoherent (G : GEnv) (D : DEnv) : Prop :=
  ∀ e, ActiveEdge G e → BlockedEdge G e → EdgeCoherent G D e

/-- Coherence implies weak coherence. -/
theorem coherent_implies_weak_coherent (G : GEnv) (D : DEnv) :
    Coherent G D -> WeakCoherent G D := by
  intro hCoh e hActive _hBlocked
  exact hCoh e hActive

/-! ## Counterexample Witness -/

/-- Simple witness config used to show strictness (`WeakCoherent` is strictly weaker). -/
def minimalityAEndpoint : Endpoint := { sid := 0, role := "A" }
def minimalityBEndpoint : Endpoint := { sid := 0, role := "B" }
def minimalityBType : LocalType := .send "C" .unit (.recv "A" .unit .end_)

def minimalityCounterexampleG : GEnv :=
  updateG
    (updateG (∅ : GEnv) minimalityAEndpoint .end_)
    minimalityBEndpoint
    minimalityBType

/-- In-flight trace for the strictness witness: one message on A -> B. -/
def minimalityCounterexampleD : DEnv :=
  updateD (∅ : DEnv) { sid := 0, sender := "A", receiver := "B" } [.unit]

/-- Distinguished edge for the strictness witness. -/
def minimalityEdgeAB : Edge := { sid := 0, sender := "A", receiver := "B" }

/-! ## Witness Lookup Lemmas -/

/-- The witness has no blocked receivers at all. -/
theorem lookup_minimality_counterexample_b :
    lookupG minimalityCounterexampleG minimalityBEndpoint = some minimalityBType := by
  simp [minimalityCounterexampleG, minimalityBEndpoint, minimalityBType]

theorem lookup_minimality_counterexample_a :
    lookupG minimalityCounterexampleG minimalityAEndpoint = some .end_ := by
  unfold minimalityCounterexampleG
  have hNe : minimalityAEndpoint ≠ minimalityBEndpoint := by
    decide
  simpa [minimalityAEndpoint] using
    (lookup_g_update_g_ne
      (env := updateG (∅ : GEnv) minimalityAEndpoint .end_)
      (e := minimalityBEndpoint)
      (e' := minimalityAEndpoint)
      (L := minimalityBType)
      hNe)

theorem lookup_minimality_counterexample_other (ep : Endpoint)
    (hA : ep ≠ minimalityAEndpoint) (hB : ep ≠ minimalityBEndpoint) :
    lookupG minimalityCounterexampleG ep = none := by
  unfold minimalityCounterexampleG
  have hStep1 :
      lookupG
          (updateG (updateG (∅ : GEnv) minimalityAEndpoint .end_) minimalityBEndpoint minimalityBType)
          ep =
        lookupG (updateG (∅ : GEnv) minimalityAEndpoint .end_) ep := by
    exact
      lookup_g_update_g_ne
        (env := updateG (∅ : GEnv) minimalityAEndpoint .end_)
        (e := minimalityBEndpoint)
        (e' := ep)
        (L := minimalityBType)
        hB
  rw [hStep1]
  have hStep2 :
      lookupG (updateG (∅ : GEnv) minimalityAEndpoint .end_) ep = lookupG (∅ : GEnv) ep := by
    exact
      lookup_g_update_g_ne
        (env := (∅ : GEnv))
        (e := minimalityAEndpoint)
        (e' := ep)
        (L := .end_)
        hA
  rw [hStep2]
  simp [lookupG]

/-! ## No Blocked Receivers -/

theorem minimality_counterexample_no_blocked (e : Edge) :
    ¬ BlockedEdge minimalityCounterexampleG e := by
  let ep : Endpoint := { sid := e.sid, role := e.receiver }
  by_cases hA : ep = minimalityAEndpoint
  · have hLookup : lookupG minimalityCounterexampleG ep = some .end_ := by
      calc
        lookupG minimalityCounterexampleG ep
            = lookupG minimalityCounterexampleG minimalityAEndpoint := by simpa [hA]
        _ = some .end_ := lookup_minimality_counterexample_a
    have hLookup' :
        lookupG minimalityCounterexampleG { sid := e.sid, role := e.receiver } = some .end_ := by
      simpa [ep] using hLookup
    simpa [BlockedEdge, isBlockedLocal, hLookup']
  · by_cases hB : ep = minimalityBEndpoint
    · have hLookup : lookupG minimalityCounterexampleG ep = some minimalityBType := by
        calc
          lookupG minimalityCounterexampleG ep
              = lookupG minimalityCounterexampleG minimalityBEndpoint := by simpa [hB]
          _ = some minimalityBType := lookup_minimality_counterexample_b
      have hLookup' :
          lookupG minimalityCounterexampleG { sid := e.sid, role := e.receiver } = some minimalityBType := by
        simpa [ep] using hLookup
      simpa [BlockedEdge, isBlockedLocal, minimalityBType, hLookup']
    · have hLookup := lookup_minimality_counterexample_other ep hA hB
      have hLookup' :
          lookupG minimalityCounterexampleG { sid := e.sid, role := e.receiver } = none := by
        simpa [ep] using hLookup
      simpa [BlockedEdge, hLookup']

/-! ## Weak Coherence Holds Vacuously -/

/-- The witness satisfies weak coherence (vacuously, since no receiver is blocked). -/
theorem minimality_counterexample_weak_coherent :
    WeakCoherent minimalityCounterexampleG minimalityCounterexampleD := by
  intro e _hActive hBlocked
  exact (False.elim ((minimality_counterexample_no_blocked e) hBlocked))

/-! ## Witness Violates Full Coherence -/

/-- The witness is not coherent: edge A -> B cannot consume its non-empty trace. -/
theorem minimality_counterexample_not_coherent :
    ¬ Coherent minimalityCounterexampleG minimalityCounterexampleD := by
  intro hCoh
  have hActive : ActiveEdge minimalityCounterexampleG minimalityEdgeAB := by
    have hSender :
        lookupG minimalityCounterexampleG
            { sid := minimalityEdgeAB.sid, role := minimalityEdgeAB.sender } = some .end_ := by
      simpa [minimalityEdgeAB, minimalityAEndpoint] using lookup_minimality_counterexample_a
    have hReceiver :
        lookupG minimalityCounterexampleG
            { sid := minimalityEdgeAB.sid, role := minimalityEdgeAB.receiver } = some minimalityBType := by
      simpa [minimalityEdgeAB, minimalityBEndpoint] using lookup_minimality_counterexample_b
    refine ⟨?_, ?_⟩
    · simpa [hSender] using congrArg Option.isSome hSender
    · simpa [hReceiver] using congrArg Option.isSome hReceiver
  have hEdge := hCoh minimalityEdgeAB hActive
  have hRecv :
      lookupG minimalityCounterexampleG { sid := 0, role := "B" } =
        some minimalityBType := by
    simpa [minimalityBEndpoint, minimalityBType] using
      lookup_minimality_counterexample_b
  rcases hEdge _ hRecv with ⟨_Lsender, _hSender, hConsume⟩
  have hTrace :
      lookupD minimalityCounterexampleD minimalityEdgeAB = [.unit] := by
    simp [minimalityCounterexampleD, minimalityEdgeAB, lookup_d_update_eq]
  have : False := by
    have hConsumeBool :
        (Consume "A" minimalityBType [.unit]).isSome = true := by
      simpa [minimalityEdgeAB, hTrace, minimalityBType] using hConsume
    simp [minimalityBType, Consume, consumeOne] at hConsumeBool
  exact this

/-! ## Strictness Theorem -/

/-- Ported strictness witness: weak coherence does not imply coherence. -/
theorem coherence_minimal_witness :
    ∃ G D, WeakCoherent G D ∧ ¬ Coherent G D := by
  refine ⟨minimalityCounterexampleG, minimalityCounterexampleD, ?_, ?_⟩
  · exact minimality_counterexample_weak_coherent
  · exact minimality_counterexample_not_coherent

/-! ## Delegation Consequence -/

/-- The strictness witness satisfies delegation side conditions for A -> C in session 0. -/
theorem minimality_counterexample_delegation_wf :
    DelegationWF minimalityCounterexampleG 0 "A" "C" := by
  have hAin : lookupG minimalityCounterexampleG { sid := 0, role := "A" } = some .end_ := by
    simpa [minimalityAEndpoint] using lookup_minimality_counterexample_a
  refine
    { A_in_session := ?_
      B_not_in_session := ?_
      A_ne_B := ?_ }
  · simpa [hAin] using congrArg Option.isSome hAin
  · have hA : ({ sid := 0, role := "C" } : Endpoint) ≠ minimalityAEndpoint := by
      decide
    have hB : ({ sid := 0, role := "C" } : Endpoint) ≠ minimalityBEndpoint := by
      decide
    simpa using lookup_minimality_counterexample_other { sid := 0, role := "C" } hA hB
  · decide

/-- Delegation connection:
    weak coherence (plus WF side conditions) is not enough to establish safe delegation. -/
theorem weak_coherent_not_sufficient_for_safe_delegation :
    WeakCoherent minimalityCounterexampleG minimalityCounterexampleD ∧
      DelegationWF minimalityCounterexampleG 0 "A" "C" ∧
      (∀ G' D',
        ¬ SafeDelegation
          minimalityCounterexampleG G'
          minimalityCounterexampleD D'
          0 "A" "C") := by
  refine ⟨minimality_counterexample_weak_coherent, minimality_counterexample_delegation_wf, ?_⟩
  intro G' D' hSafe
  exact minimality_counterexample_not_coherent hSafe.1

/-! ## Invariant Non-Conservativeness -/

/-- As a configuration-level invariant, weak coherence is not conservative to coherence. -/
def WeakInvariant : CoherenceInvariant :=
  fun C => WeakCoherent C.G C.D

theorem weak_invariant_not_conservative :
    ¬ ConservativeToCoherence WeakInvariant := by
  intro hConservative
  have hWeak : WeakInvariant ⟨minimalityCounterexampleG, minimalityCounterexampleD⟩ :=
    minimality_counterexample_weak_coherent
  have hCoh : Coherent minimalityCounterexampleG minimalityCounterexampleD :=
    hConservative ⟨minimalityCounterexampleG, minimalityCounterexampleD⟩ hWeak
  exact minimality_counterexample_not_coherent hCoh

end
