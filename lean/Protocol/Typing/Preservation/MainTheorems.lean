
import Protocol.Typing.Preservation.BufferTypingFrames

/-! # Main Preservation Theorems

Top-level preservation theorems combining buffer, store, and typing
preservation under framed typed steps. -/

/-
The Problem. The main preservation theorem requires showing that all
components of a typed configuration (GEnv, DEnv, SEnv, store, buffers)
are preserved through typed steps in a framed context.

Solution Structure. Prove `buffers_typed_preserved_frame_left` by
induction on `TypedStep`. Dispatch each constructor to its specific
preservation lemma from the component-level files.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Buffer Preservation Under Framing

set_option maxHeartbeats 2000000 in
theorem buffers_typed_preserved_frame_left
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {G₂ : GEnv} {D₂ : DEnv} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (G' ++ G₂) (D' ++ D₂) bufs' := by
  intro hTS hDisj hCons hBT
  induction hTS generalizing G₂ D₂ with
  -- Left Frame Case: `send`
  | send =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
        hk hx hG hS hv hRecvReady hEdge hGout hDout hBufsOut
      have hBT' :=
        buffers_typed_send_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂)
          (e:=e) (target:=target) (T:=T) (L:=L) (v:=v) (sendEdge:=sendEdge)
          hG hv hEdge hDisj hCons hBT
      have hEq : ∀ e', lookupD (updateD (D ++ D₂) sendEdge (lookupD D sendEdge ++ [T])) e' =
        lookupD ((appendD D sendEdge T) ++ D₂) e' := by
          intro e'
          unfold appendD
          exact
            lookup_d_update_d_append_left (D:=D) (D₂:=D₂) (e:=sendEdge) (e':=e')
              (ts:=lookupD D sendEdge ++ [T])
      have hBT'' := buffers_typed_rewrite_d hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  -- Left Frame Case: `recv`
  | recv =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
        hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      have hBT' :=
        buffers_typed_recv_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂)
          (e:=e) (source:=source) (T:=T) (L:=L) (v:=v) (vs:=vs) (recvEdge:=recvEdge)
          hG hBuf hTrace hEdge hDisj hCons hBT
      have hEq : ∀ e', lookupD (updateD (D ++ D₂) recvEdge (lookupD D recvEdge).tail) e' =
        lookupD (updateD D recvEdge (lookupD D recvEdge).tail ++ D₂) e' := by
          intro e'
          exact
            lookup_d_update_d_append_left (D:=D) (D₂:=D₂) (e:=recvEdge) (e':=e')
              (ts:=(lookupD D recvEdge).tail)
/- ## Structured Block 2 -/
      have hBT'' := buffers_typed_rewrite_d hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  -- Left Frame Case: `select`
  | select =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
        hk hG hFind hTargetReady hEdge hGout hDout hBufsOut
      have hBT' :=
        buffers_typed_select_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂)
          (e:=e) (target:=target) (bs:=bs) (ℓ:=ℓ) (L:=L) (selectEdge:=selectEdge)
          hG hFind hEdge hDisj hCons hBT
      have hEq : ∀ e', lookupD (updateD (D ++ D₂) selectEdge (lookupD D selectEdge ++ [.string])) e' =
        lookupD ((appendD D selectEdge .string) ++ D₂) e' := by
          intro e'
          unfold appendD
          exact
            lookup_d_update_d_append_left (D:=D) (D₂:=D₂) (e:=selectEdge) (e':=e')
              (ts:=lookupD D selectEdge ++ [.string])
      have hBT'' := buffers_typed_rewrite_d hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  -- Left Frame Case: `branch`
  | branch =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
        hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut
      have hBT' :=
        buffers_typed_branch_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂)
          (e:=e) (source:=source) (bs:=bs) (ℓ:=ℓ) (L:=L) (vs:=vs) (branchEdge:=branchEdge)
          hG hFindT hBuf hTrace hEdge hDisj hCons hBT
      have hEq : ∀ e', lookupD (updateD (D ++ D₂) branchEdge (lookupD D branchEdge).tail) e' =
        lookupD (updateD D branchEdge (lookupD D branchEdge).tail ++ D₂) e' := by
          intro e'
          exact
            lookup_d_update_d_append_left (D:=D) (D₂:=D₂) (e:=branchEdge) (e':=e')
              (ts:=(lookupD D branchEdge).tail)
      have hBT'' := buffers_typed_rewrite_d hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  -- Left Frame Structural Cases
  | assign =>
      rename_i G D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut
      simpa using hBT
  | seq_step hTS ih =>
      exact ih hDisj hCons hBT
  | seq_skip =>
      simpa using hBT
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
/- ## Structured Block 3 -/
      exact ih hDisj hCons hBT
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih hDisj hCons hBT
  | par_skip_left =>
      simpa using hBT
  | par_skip_right =>
      simpa using hBT

-- Buffer Preservation Under Right Framing

set_option maxHeartbeats 2000000 in
theorem buffers_typed_preserved_frame_right
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {G₁ : GEnv} {D₁ : DEnv} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ G') (D₁ ++ D') bufs' := by
  intro hTS hDisj hCons hBT
  induction hTS generalizing G₁ D₁ with
  -- Right Frame Case: `send`
  | send =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
        hk hx hG hS hv hRecvReady hEdge hGout hDout hBufsOut
      have hBT' :=
        buffers_typed_send_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁)
          (e:=e) (target:=target) (T:=T) (L:=L) (v:=v) (sendEdge:=sendEdge)
          hG hv hEdge hDisj hCons hBT
      have hSid : sendEdge.sid ∈ SessionsOf G := by
        rcases hEdge with rfl
        exact ⟨e, .send target T L, hG, rfl⟩
      have hNone : D₁.find? sendEdge = none :=
        lookup_d_none_of_disjoint_g (G₁:=G) (G₂:=G₁) (D₂:=D₁) (disjoint_g_symm hDisj) hCons
          hSid
      have hEq : ∀ e', lookupD (updateD (D₁ ++ D) sendEdge (lookupD D sendEdge ++ [T])) e' =
        lookupD (D₁ ++ appendD D sendEdge T) e' := by
          intro e'
          unfold appendD
          exact
            lookup_d_update_d_append_right (D₁:=D₁) (D:=D) (e:=sendEdge) (e':=e')
              (ts:=lookupD D sendEdge ++ [T]) hNone
      have hBT'' := buffers_typed_rewrite_d hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  -- Right Frame Case: `recv`
  | recv =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
        hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      have hBT' :=
        buffers_typed_recv_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁)
          (e:=e) (source:=source) (T:=T) (L:=L) (v:=v) (vs:=vs) (recvEdge:=recvEdge)
          hG hBuf hTrace hEdge hDisj hCons hBT
/- ## Structured Block 4 -/
      have hSid : recvEdge.sid ∈ SessionsOf G := by
        rcases hEdge with rfl
        exact ⟨e, .recv source T L, hG, rfl⟩
      have hNone : D₁.find? recvEdge = none :=
        lookup_d_none_of_disjoint_g (G₁:=G) (G₂:=G₁) (D₂:=D₁) (disjoint_g_symm hDisj) hCons
          hSid
      have hEq : ∀ e', lookupD (updateD (D₁ ++ D) recvEdge (lookupD D recvEdge).tail) e' =
        lookupD (D₁ ++ updateD D recvEdge (lookupD D recvEdge).tail) e' := by
          intro e'
          exact
            lookup_d_update_d_append_right (D₁:=D₁) (D:=D) (e:=recvEdge) (e':=e')
              (ts:=(lookupD D recvEdge).tail) hNone
      have hBT'' := buffers_typed_rewrite_d hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  -- Right Frame Case: `select`
  | select =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
        hk hG hFind hTargetReady hEdge hGout hDout hBufsOut
      have hBT' :=
        buffers_typed_select_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁)
          (e:=e) (target:=target) (bs:=bs) (ℓ:=ℓ) (L:=L) (selectEdge:=selectEdge)
          hG hFind hEdge hDisj hCons hBT
      have hSid : selectEdge.sid ∈ SessionsOf G := by
        rcases hEdge with rfl
        exact ⟨e, .select target bs, hG, rfl⟩
      have hNone : D₁.find? selectEdge = none :=
        lookup_d_none_of_disjoint_g (G₁:=G) (G₂:=G₁) (D₂:=D₁) (disjoint_g_symm hDisj) hCons
          hSid
      have hEq : ∀ e', lookupD (updateD (D₁ ++ D) selectEdge (lookupD D selectEdge ++ [.string])) e' =
        lookupD (D₁ ++ appendD D selectEdge .string) e' := by
          intro e'
          unfold appendD
          exact
            lookup_d_update_d_append_right (D₁:=D₁) (D:=D) (e:=selectEdge) (e':=e')
              (ts:=lookupD D selectEdge ++ [.string]) hNone
      have hBT'' := buffers_typed_rewrite_d hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  -- Right Frame Case: `branch`
  | branch =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
        hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut
      have hBT' :=
        buffers_typed_branch_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁)
          (e:=e) (source:=source) (bs:=bs) (ℓ:=ℓ) (L:=L) (vs:=vs) (branchEdge:=branchEdge)
          hG hFindT hBuf hTrace hEdge hDisj hCons hBT
      have hSid : branchEdge.sid ∈ SessionsOf G := by
/- ## Structured Block 5 -/
        rcases hEdge with rfl
        exact ⟨e, .branch source bs, hG, rfl⟩
      have hNone : D₁.find? branchEdge = none :=
        lookup_d_none_of_disjoint_g (G₁:=G) (G₂:=G₁) (D₂:=D₁) (disjoint_g_symm hDisj) hCons
          hSid
      have hEq : ∀ e', lookupD (updateD (D₁ ++ D) branchEdge (lookupD D branchEdge).tail) e' =
        lookupD (D₁ ++ updateD D branchEdge (lookupD D branchEdge).tail) e' := by
          intro e'
          exact
            lookup_d_update_d_append_right (D₁:=D₁) (D:=D) (e:=branchEdge) (e':=e')
              (ts:=(lookupD D branchEdge).tail) hNone
      have hBT'' := buffers_typed_rewrite_d hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  -- Right Frame Structural Cases
  | assign =>
      simpa using hBT
  | seq_step hTS ih =>
      exact ih hDisj hCons hBT
  | seq_skip =>
      simpa using hBT
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih hDisj hCons hBT
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih hDisj hCons hBT
  | par_skip_left =>
      simpa using hBT
  | par_skip_right =>
      simpa using hBT

-- Empty-Trace Helpers and Unframed Corollary

lemma sessions_of_d_empty : SessionsOfD (∅ : DEnv) = ∅ := by
  ext s; constructor
  · intro h
    rcases h with ⟨e, ts, hFind, hSid⟩
    have : (∅ : DEnv).find? e = none := by
      simp [DEnv.find?, d_env_map_find?_empty]
    cases hFind
  · intro h; cases h

lemma d_consistent_empty (G : GEnv) : DConsistent G (∅ : DEnv) := by
  simp [DConsistent, sessions_of_d_empty]

theorem buffers_typed_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Coherent G D →
    BuffersTyped G D bufs →
    BuffersTyped G' D' bufs' := by
  intro hTS _ hBT
  have hEqD : ∀ e, lookupD (D ++ (∅ : DEnv)) e = lookupD D e := by
    intro e
    have hNone : (∅ : DEnv).find? e = none := by
/- ## Structured Block 6 -/
      simp [DEnv.find?, d_env_map_find?_empty]
    exact lookup_d_append_left_of_right_none (D₁:=D) (D₂:=∅) (e:=e) hNone
  have hBT' :
      BuffersTyped (G ++ []) (D ++ (∅ : DEnv)) bufs := by
    have hBTD : BuffersTyped G (D ++ (∅ : DEnv)) bufs :=
      buffers_typed_rewrite_d (D:=D) (D':=D ++ (∅ : DEnv)) (by
        intro e; symm; exact hEqD e) hBT
    apply buffers_typed_mono (G:=G) (G':=G ++ []) (D:=D ++ (∅ : DEnv)) (bufs:=bufs)
    · intro ep L hLookup
      exact lookup_g_append_left (G₁:=G) (G₂:=[]) hLookup
    · exact hBTD
  have hDisj : DisjointG G ([] : GEnv) := disjoint_g_right_empty G
  have hCons : DConsistent ([] : GEnv) (∅ : DEnv) := d_consistent_empty []
  have hBT'' :=
    buffers_typed_preserved_frame_left (G₂:=[]) (D₂:=∅) hTS hDisj hCons hBT'
  have hBT''' : BuffersTyped G' (D' ++ (∅ : DEnv)) bufs' := by
    simpa [List.append_nil] using hBT''
  have hEqD' : ∀ e, lookupD (D' ++ (∅ : DEnv)) e = lookupD D' e := by
    intro e
    have hNone : (∅ : DEnv).find? e = none := by
      simp [DEnv.find?, d_env_map_find?_empty]
    exact lookup_d_append_left_of_right_none (D₁:=D') (D₂:=∅) (e:=e) hNone
  exact buffers_typed_rewrite_d (D:=D' ++ (∅ : DEnv)) (D':=D') hEqD' hBT'''

end
