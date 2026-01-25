import Effects.Monitor
import Effects.DeadlockFreedom
import Effects.Spatial
import Effects.Determinism

/-!
# MPST Deployed Protocol Bundle

This module defines the structure for a deployed protocol: a bundle containing
the protocol specification, projected local types, initial monitor state, and
all required certificates for safe execution.

## Overview

A **deployed protocol** is the artifact produced when a developer:
1. Defines a protocol (currently as local types, later as global type)
2. Provides proofs of well-formedness
3. Sets up initial monitor state
4. Declares the protocol's interface for composition

## Key Structures

- `InterfaceType`: What a protocol exports/imports for composition
- `DeployedProtocol`: Complete bundle with all certificates
- `ProtocolBundle`: Lightweight bundle without proofs (for runtime)

## Composition

Two deployed protocols can be composed if their interfaces are compatible:
- Disjoint session IDs
- Matching exports/imports
- Merged environments remain coherent

See Phase 12 for the full linking judgment.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Environment Merging

Merge operations for composing protocol environments.
-/

/-- Merge two GEnvs (disjoint union). -/
def mergeGEnv (G₁ G₂ : GEnv) : GEnv := G₁ ++ G₂

/-- Merge two DEnvs (disjoint union). -/
def mergeDEnv (D₁ D₂ : DEnv) : DEnv := D₁ ++ D₂

/-- Merge two buffer maps (disjoint union). -/
def mergeBufs (B₁ B₂ : Buffers) : Buffers := B₁ ++ B₂

/-- Merge two linear contexts (disjoint union). -/
def mergeLin (L₁ L₂ : LinCtx) : LinCtx := L₁ ++ L₂

/-! ### Merge Lookup Lemmas -/

/-- Lookup in merged GEnv prefers the left environment. -/
theorem MergeGEnv_Left (G₁ G₂ : GEnv) (e : Endpoint) (L : LocalType) :
    lookupG G₁ e = some L →
    lookupG (mergeGEnv G₁ G₂) e = some L := by
  intro h
  have hLookup : G₁.lookup e = some L := by
    simpa [lookupG] using h
  calc
    lookupG (mergeGEnv G₁ G₂) e
        = (G₁.lookup e).or (G₂.lookup e) := by
            simp [mergeGEnv, lookupG, List.lookup_append]
    _ = some L := by
            simp [hLookup]

/-- Lookup in merged GEnv falls back to the right when left is missing. -/
theorem MergeGEnv_Right (G₁ G₂ : GEnv) (e : Endpoint) :
    lookupG G₁ e = none →
    lookupG (mergeGEnv G₁ G₂) e = lookupG G₂ e := by
  intro h
  have hLookup : G₁.lookup e = none := by
    simpa [lookupG] using h
  calc
    lookupG (mergeGEnv G₁ G₂) e
        = (G₁.lookup e).or (G₂.lookup e) := by
            simp [mergeGEnv, lookupG, List.lookup_append]
    _ = lookupG G₂ e := by
            simp [hLookup, lookupG]

axiom MergeDEnv_Left (D₁ D₂ : DEnv) (edge : Edge) :
    lookupD D₁ edge ≠ [] →
    lookupD (mergeDEnv D₁ D₂) edge = lookupD D₁ edge

axiom MergeDEnv_Right (D₁ D₂ : DEnv) (edge : Edge) :
    D₁.find? edge = none →
    lookupD (mergeDEnv D₁ D₂) edge = lookupD D₂ edge

/-- Lookup in merged buffers prefers the left environment when it provides a buffer. -/
theorem MergeBufs_Left (B₁ B₂ : Buffers) (edge : Edge) :
    lookupBuf B₁ edge ≠ [] →
    lookupBuf (mergeBufs B₁ B₂) edge = lookupBuf B₁ edge := by
  intro h
  unfold lookupBuf mergeBufs
  cases hLookup : B₁.lookup edge with
  | none =>
      have : lookupBuf B₁ edge = [] := by
        simp [lookupBuf, hLookup]
      exact (h this).elim
  | some buf =>
      simp [List.lookup_append, hLookup]

/-- Lookup in merged buffers falls back to the right when the left has no entry. -/
theorem MergeBufs_Right (B₁ B₂ : Buffers) (edge : Edge) :
    B₁.lookup edge = none →
    lookupBuf (mergeBufs B₁ B₂) edge = lookupBuf B₂ edge := by
  intro h
  simp [lookupBuf, mergeBufs, List.lookup_append, h]

/-- Full linking judgment (6.7.2): Propositional version with all conditions.

Two deployed protocols can be safely composed when:
1. Their session IDs are disjoint (no interference)
2. p₁'s exports are compatible with p₂'s imports (dual types)
3. p₂'s exports are compatible with p₁'s imports (dual types)
4. The merged environments remain coherent
-/
def LinkOKFull (p₁ p₂ : DeployedProtocol) : Prop :=
  -- 1. Disjoint sessions
  InterfaceType.DisjointSessions p₁.interface p₂.interface ∧
  -- 2. p₁'s exports compatible with p₂'s imports
  InterfaceType.ExportsCompatibleWithImports p₁.interface p₂.interface ∧
  -- 3. p₂'s exports compatible with p₁'s imports
  InterfaceType.ExportsCompatibleWithImports p₂.interface p₁.interface ∧
  -- 4. Merged environments remain coherent
  Coherent (mergeGEnv p₁.initGEnv p₂.initGEnv) (mergeDEnv p₁.initDEnv p₂.initDEnv)

/-- LinkOKFull implies the basic LinkOK (useful for backwards compatibility). -/
theorem LinkOKFull_implies_disjoint (p₁ p₂ : DeployedProtocol)
    (h : LinkOKFull p₁ p₂) :
    InterfaceType.DisjointSessions p₁.interface p₂.interface := h.1

/-- LinkOKFull gives us merged coherence directly. -/
theorem LinkOKFull_coherent (p₁ p₂ : DeployedProtocol)
    (h : LinkOKFull p₁ p₂) :
    Coherent (mergeGEnv p₁.initGEnv p₂.initGEnv) (mergeDEnv p₁.initDEnv p₂.initDEnv) := h.2.2.2

/-! ## Protocol Composition

Compose two protocols into a single protocol bundle.
-/

/-- Compose two monitor states into one. -/
def composeMonitorState (ms₁ ms₂ : MonitorState) : MonitorState where
  G := mergeGEnv ms₁.G ms₂.G
  D := mergeDEnv ms₁.D ms₂.D
  bufs := mergeBufs ms₁.bufs ms₂.bufs
  Lin := mergeLin ms₁.Lin ms₂.Lin
  supply := max ms₁.supply ms₂.supply

/-- Compose two protocol bundles into one.

Note: This creates a combined bundle without proofs. For a full
DeployedProtocol, additional certificates would need to be constructed.
-/
def composeBundle (p₁ p₂ : ProtocolBundle) : ProtocolBundle where
  name := p₁.name ++ "+" ++ p₂.name
  roles := p₁.roles ++ p₂.roles
  localTypes := fun r =>
    if p₁.roles.elem r then p₁.localTypes r
    else if p₂.roles.elem r then p₂.localTypes r
    else .end_
  sessionId := max p₁.sessionId p₂.sessionId + 1  -- New session for composed
  interface := p₁.interface.merge p₂.interface
  spatialReq := p₁.spatialReq &&& p₂.spatialReq

/-! ## Linking Theorems -/

/-! ### Helper Lemmas for Merge Operations -/

/-- Merged buffers preserve typing when sessions are disjoint. -/
theorem mergeBufs_typed (G₁ G₂ : GEnv) (D₁ D₂ : DEnv) (B₁ B₂ : Buffers)
    (hTyped₁ : BuffersTyped G₁ D₁ B₁)
    (hTyped₂ : BuffersTyped G₂ D₂ B₂)
    (hDisjoint : ∀ e, (∃ L, (e, L) ∈ G₁) → ∀ L', (e, L') ∉ G₂) :
    BuffersTyped (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) (mergeBufs B₁ B₂) := by
  intro e
  simp only [BufferTyped, mergeGEnv, mergeDEnv, mergeBufs, lookupBuf, lookupD]
  -- For each edge, either it's in D₁/B₁ or D₂/B₂ (or neither)
  simp only [List.lookup_append]
  sorry  -- Requires case analysis on which session the edge belongs to

/-- Merged linear context is valid when sessions are disjoint. -/
theorem mergeLin_valid (G₁ G₂ : GEnv) (L₁ L₂ : LinCtx)
    (hValid₁ : ∀ e S, (e, S) ∈ L₁ → lookupG G₁ e = some S)
    (hValid₂ : ∀ e S, (e, S) ∈ L₂ → lookupG G₂ e = some S)
    (hDisjoint : ∀ e, (∃ S, (e, S) ∈ L₁) → ∀ S', (e, S') ∉ L₂) :
    ∀ e S, (e, S) ∈ mergeLin L₁ L₂ → lookupG (mergeGEnv G₁ G₂) e = some S := by
  intro e S hMem
  simp only [mergeLin, List.mem_append] at hMem
  simp only [mergeGEnv, lookupG, List.lookup_append]
  cases hMem with
  | inl h₁ =>
    have hLookup := hValid₁ e S h₁
    simp only [lookupG] at hLookup
    simp only [hLookup, Option.some_or]
  | inr h₂ =>
    have hLookup := hValid₂ e S h₂
    simp only [lookupG] at hLookup
    -- Need to show lookup in G₁ fails (disjoint sessions)
    sorry  -- Requires showing e not in G₁ by disjointness

/-- Merged linear context preserves uniqueness when sessions are disjoint. -/
theorem mergeLin_unique (L₁ L₂ : LinCtx)
    (hUnique₁ : L₁.Pairwise (fun a b => a.1 ≠ b.1))
    (hUnique₂ : L₂.Pairwise (fun a b => a.1 ≠ b.1))
    (hDisjoint : ∀ e, (∃ S, (e, S) ∈ L₁) → ∀ S', (e, S') ∉ L₂) :
    (mergeLin L₁ L₂).Pairwise (fun a b => a.1 ≠ b.1) := by
  simp only [mergeLin, List.pairwise_append]
  refine ⟨hUnique₁, hUnique₂, ?_⟩
  intro a ha b hb
  -- a is in L₁, b is in L₂, so a.1 ≠ b.1 by disjointness
  intro heq
  have hEx : ∃ S, (a.1, S) ∈ L₁ := ⟨a.2, by rw [Prod.eta]; exact ha⟩
  have hNotIn := hDisjoint a.1 hEx b.2
  rw [heq] at hNotIn
  exact hNotIn (by rw [Prod.eta]; exact hb)

/-- Linking preserves well-typedness (legacy version). -/
theorem link_preserves_WTMon (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂)
    (hWT₁ : WTMon p₁.initMonitorState)
    (hWT₂ : WTMon p₂.initMonitorState) :
    WTMon (composeMonitorState p₁.initMonitorState p₂.initMonitorState) := by
  -- The key insight is that disjoint sessions maintain coherence independently
  -- Each session's endpoints and edges don't interfere with the other
  sorry  -- Full proof requires showing merge preserves invariants

/-- Linking preserves well-typedness (full version with merged coherence). -/
theorem link_preserves_WTMon_full (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hWT₁ : WTMon p₁.initMonitorState)
    (hWT₂ : WTMon p₂.initMonitorState) :
    WTMon (composeMonitorState p₁.initMonitorState p₂.initMonitorState) := by
  simp only [composeMonitorState, DeployedProtocol.initMonitorState]
  constructor
  · -- coherent: Follows directly from LinkOKFull
    exact hLink.2.2.2
  · -- headCoherent
    sorry  -- Requires merged HeadCoherent
  · -- validLabels
    sorry  -- Requires merged ValidLabels
  · -- buffers_typed
    sorry  -- Requires mergeBufs_typed with session disjointness
  · -- lin_valid
    sorry  -- Requires mergeLin_valid with session disjointness
  · -- lin_unique
    sorry  -- Requires mergeLin_unique with session disjointness
  · -- supply_fresh
    sorry  -- Requires showing max supply maintains freshness
  · -- supply_fresh_G
    sorry  -- Requires showing merged G entries are fresh

/-! ## Composition Preserves Deadlock Freedom

The key theorem for safe composition: if both protocols are deadlock-free,
their composition is also deadlock-free.
-/

/-- Disjoint sessions maintain independence. -/
theorem disjoint_sessions_independent (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂) :
    p₁.sessionId ≠ p₂.sessionId := by
  -- From disjointSessions: all of p₁'s sessions are not in p₂'s sessions
  obtain ⟨hDisjoint, _, _⟩ := hLink
  intro heq
  -- p₁.sessionId ∈ p₁.interface.sessionIds
  have h₁ := p₁.sessionId_in_interface
  -- p₂.sessionId ∈ p₂.interface.sessionIds
  have h₂ := p₂.sessionId_in_interface
  -- disjointSessions means all s in p₁'s list are not in p₂'s list
  unfold InterfaceType.disjointSessions at hDisjoint
  -- p₁.sessionId is in p₁.interface.sessionIds, so it should not be in p₂'s
  have hAll := List.all_eq_true.mp hDisjoint p₁.sessionId h₁
  -- hAll : !(p₂.interface.sessionIds.contains p₁.sessionId) = true
  -- i.e., p₂.interface.sessionIds.contains p₁.sessionId = false
  have hNotContains : p₂.interface.sessionIds.contains p₁.sessionId = false := by
    simpa using hAll
  -- But if p₁.sessionId = p₂.sessionId, and p₂.sessionId ∈ p₂.interface.sessionIds,
  -- then p₂.interface.sessionIds.contains p₁.sessionId = true - contradiction
  have hContains : p₂.interface.sessionIds.contains p₁.sessionId = true := by
    rw [heq, List.contains_iff_exists_mem_beq]
    exact ⟨p₂.sessionId, h₂, beq_self_eq_true _⟩
  rw [hNotContains] at hContains
  exact Bool.false_ne_true hContains

/-- Composition preserves deadlock freedom.

If both protocols can reach communication independently,
the composed protocol can also make progress.
-/
theorem compose_deadlock_free (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂)
    (hDF₁ : ∀ r, r ∈ p₁.roles → ReachesComm (p₁.localTypes r))
    (hDF₂ : ∀ r, r ∈ p₂.roles → ReachesComm (p₂.localTypes r)) :
    ∀ r, r ∈ p₁.roles ++ p₂.roles →
      ReachesComm ((composeBundle (ProtocolBundle.fromDeployed p₁) (ProtocolBundle.fromDeployed p₂)).localTypes r) := by
  intro r hr
  simp only [composeBundle, ProtocolBundle.fromDeployed]
  by_cases h₁ : r ∈ p₁.roles
  · -- r is in p₁.roles
    simp only [h₁, List.elem_eq_mem, ↓reduceIte]
    exact hDF₁ r h₁
  · -- r is in p₂.roles
    have h₂ : r ∈ p₂.roles := by
      simp only [List.mem_append] at hr
      cases hr with
      | inl h => exact absurd h h₁
      | inr h => exact h
    simp only [h₁, List.elem_eq_mem, Bool.false_eq_true, ↓reduceIte, h₂]
    exact hDF₂ r h₂

end
