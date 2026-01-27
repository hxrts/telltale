import Effects.Deployment.Part1
import Effects.Typing.Part3a
import Effects.Coherence.Part9

/-! # Effects.Deployment.Part2a

Environment merging, role completeness, and protocol bundle composition.
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

/-- Disjoint sessions: left session IDs do not appear on the right. -/
private theorem sid_not_in_right_of_left {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {s : SessionId} (hIn : s ∈ SessionsOf G₁) : s ∉ SessionsOf G₂ := by
  -- Use disjointness to rule out shared session IDs.
  intro hIn2
  have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hIn2⟩
  have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := hDisj
  have : s ∈ (∅ : Set SessionId) := by
    simpa [hEmpty] using hInter
  exact this.elim

/-- If a session is not in G, buffers have no entries for it. -/
private theorem BConsistent_lookup_none_of_notin_sessions
    {G : GEnv} {B : Buffers} {e : Edge}
    (hCons : BConsistent G B) (hNot : e.sid ∉ SessionsOf G) :
    B.lookup e = none := by
  -- A buffer entry would witness membership in SessionsOf G.
  by_contra hSome
  cases hFind : B.lookup e with
  | none => exact (hSome hFind)
  | some buf =>
      have hSid : e.sid ∈ SessionsOf G := hCons e buf hFind
      exact (hNot hSid)

/-- If a session is not in G, DEnv has no entry for it. -/
private theorem DEnv_find_none_of_notin_sessions
    {G : GEnv} {D : DEnv} {e : Edge}
    (hCons : DConsistent G D) (hNot : e.sid ∉ SessionsOf G) :
    D.find? e = none := by
  -- Any D entry would contradict the session consistency.
  by_contra hSome
  cases hFind : D.find? e with
  | none => exact (hSome hFind)
  | some ts =>
      have hSid : e.sid ∈ SessionsOfD D := ⟨e, ts, hFind, rfl⟩
      have hSidG : e.sid ∈ SessionsOf G := hCons hSid
      exact (hNot hSidG)

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

/-- Invert lookup in a merged GEnv. -/
theorem MergeGEnv_inv {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    lookupG (mergeGEnv G₁ G₂) e = some L →
    lookupG G₁ e = some L ∨ (lookupG G₁ e = none ∧ lookupG G₂ e = some L) := by
  -- Decide whether the left lookup succeeds.
  intro h
  have hLookup : (G₁.lookup e).or (G₂.lookup e) = some L := by
    simpa [mergeGEnv, lookupG, List.lookup_append] using h
  cases hLeft : G₁.lookup e with
  | none =>
      right
      have hRight : G₂.lookup e = some L := by
        simpa [hLeft] using hLookup
      exact ⟨by simpa [lookupG] using hLeft, by simpa [lookupG] using hRight⟩
  | some L₁ =>
      left
      have hEq : L₁ = L := by
        simpa [hLeft] using hLookup
      simpa [lookupG, hEq] using hLeft

/-- Right lookup in a merged GEnv always yields some entry. -/
theorem MergeGEnv_some_of_right (G₁ G₂ : GEnv) (e : Endpoint) {L : LocalType} :
    lookupG G₂ e = some L →
    ∃ L', lookupG (mergeGEnv G₁ G₂) e = some L' := by
  -- If the left is empty we use the right; otherwise the left wins.
  intro hRight
  by_cases hLeft : lookupG G₁ e = none
  · refine ⟨L, ?_⟩
    simpa [MergeGEnv_Right G₁ G₂ e hLeft] using hRight
  · cases hLeft' : lookupG G₁ e with
    | none => exact (hLeft hLeft').elim
    | some L₁ =>
        refine ⟨L₁, ?_⟩
        exact MergeGEnv_Left G₁ G₂ e L₁ hLeft'

/-! ## Role Completeness -/

/-- RoleComplete is preserved by GEnv merge. -/
theorem RoleComplete_mergeGEnv (G₁ G₂ : GEnv)
    (hC₁ : RoleComplete G₁) (hC₂ : RoleComplete G₂) :
    RoleComplete (mergeGEnv G₁ G₂) := by
  -- Split on which side supplied the lookup.
  intro e L hLookup
  cases hTarget : LocalType.targetRole? L with
  | none =>
      -- No target role: the obligation is trivial.
      simp
  | some r =>
      have hInv := MergeGEnv_inv (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hLookup
      cases hInv with
      | inl hLeft =>
          -- Left case: use role-completeness of G₁.
          have hComp : ∃ L', lookupG G₁ ⟨e.sid, r⟩ = some L' := by
            simpa [RoleComplete, hTarget] using hC₁ e L hLeft
          rcases hComp with ⟨L', hL'⟩
          exact ⟨L', MergeGEnv_Left G₁ G₂ ⟨e.sid, r⟩ L' hL'⟩
      | inr hRight =>
          -- Right case: use role-completeness of G₂.
          have hComp : ∃ L', lookupG G₂ ⟨e.sid, r⟩ = some L' := by
            simpa [RoleComplete, hTarget] using hC₂ e L hRight.2
          rcases hComp with ⟨L', hL'⟩
          exact MergeGEnv_some_of_right G₁ G₂ ⟨e.sid, r⟩ hL'
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

/-- Merged DEnv follows the left when the session is absent on the right. -/
private theorem lookupD_merge_left_of_notin_right
    {G₂ : GEnv} {D₁ D₂ : DEnv} {e : Edge}
    (hCons₂ : DConsistent G₂ D₂) (hNot : e.sid ∉ SessionsOf G₂) :
    lookupD (mergeDEnv D₁ D₂) e = lookupD D₁ e := by
  -- Exclude the right entry via DConsistent, then use left-biased lookup.
  have hNone : D₂.find? e = none :=
    DEnv_find_none_of_notin_sessions (G:=G₂) (D:=D₂) hCons₂ hNot
  exact lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂) (e:=e) hNone

/-- Merged DEnv follows the right when the session is absent on the left. -/
private theorem lookupD_merge_right_of_notin_left
    {G₁ : GEnv} {D₁ D₂ : DEnv} {e : Edge}
    (hCons₁ : DConsistent G₁ D₁) (hNot : e.sid ∉ SessionsOf G₁) :
    lookupD (mergeDEnv D₁ D₂) e = lookupD D₂ e := by
  -- Exclude the left entry via DConsistent, then use right-biased lookup.
  have hNone : D₁.find? e = none :=
    DEnv_find_none_of_notin_sessions (G:=G₁) (D:=D₁) hCons₁ hNot
  exact lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hNone

/-- Merged buffers follow the left when the session is absent on the right. -/
private theorem lookupBuf_merge_left_of_notin_right
    {G₂ : GEnv} {B₁ B₂ : Buffers} {e : Edge}
    (hCons₂ : BConsistent G₂ B₂) (hNot : e.sid ∉ SessionsOf G₂) :
    lookupBuf (mergeBufs B₁ B₂) e = lookupBuf B₁ e := by
  -- Exclude the right buffer entry, then simplify lookup on append.
  have hNone : B₂.lookup e = none :=
    BConsistent_lookup_none_of_notin_sessions (G:=G₂) (B:=B₂) hCons₂ hNot
  simp [lookupBuf, mergeBufs, List.lookup_append, hNone]

/-- Merged buffers follow the right when the session is absent on the left. -/
private theorem lookupBuf_merge_right_of_notin_left
    {G₁ : GEnv} {B₁ B₂ : Buffers} {e : Edge}
    (hCons₁ : BConsistent G₁ B₁) (hNot : e.sid ∉ SessionsOf G₁) :
    lookupBuf (mergeBufs B₁ B₂) e = lookupBuf B₂ e := by
  -- Exclude the left buffer entry, then simplify lookup on append.
  have hNone : B₁.lookup e = none :=
    BConsistent_lookup_none_of_notin_sessions (G:=G₁) (B:=B₁) hCons₁ hNot
  simp [lookupBuf, mergeBufs, List.lookup_append, hNone]

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


end
