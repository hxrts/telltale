
import Protocol.Preservation.CoreHelpers

/-! # Valid Labels and HeadCoherent Lemmas

Associativity lemmas for DEnv lookup and valid-label propagation for
HeadCoherent preservation through environment operations. -/

/-
The Problem. HeadCoherent requires buffer heads to match expected types.
When composing environments with `++`, we need lookup associativity and
valid-label preservation lemmas to reason about the composed config.

Solution Structure. Prove `lookup_d_append_assoc` for DEnv associativity.
Provide valid-label lemmas showing HeadCoherent is preserved when
environments are split or merged.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

-- DEnv Associativity

lemma lookup_d_swap_left {D₁ D₂ D₃ : DEnv} (hDisj : DisjointD D₁ D₂) :
    ∀ e, lookupD ((D₁ ++ D₂) ++ D₃) e = lookupD ((D₂ ++ D₁) ++ D₃) e := by
  intro e
  have hInv := find_d_comm_of_disjoint (D₁:=D₁) (D₂:=D₂) hDisj e
  cases hLeft : (D₁ ++ D₂).find? e with
  | some ts =>
      have hA := find_d_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) hLeft
      have hLeft' : (D₂ ++ D₁).find? e = some ts := by
        simpa [hInv] using hLeft
      have hB := find_d_append_left (D₁:=D₂ ++ D₁) (D₂:=D₃) (e:=e) (ts:=ts) hLeft'
      simp [lookupD, hA, hB]
  | none =>
      have hA := find_d_append_right (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) hLeft
      have hLeft' : (D₂ ++ D₁).find? e = none := by
        simpa [hInv] using hLeft
      have hB := find_d_append_right (D₁:=D₂ ++ D₁) (D₂:=D₃) (e:=e) hLeft'
      simp [lookupD, hA, hB]

-- DEnv Update over Left Append
lemma find_d_update_d_append_left {D D₂ : DEnv} {e e' : Edge} {ts : List ValType} :
    (updateD (D ++ D₂) e ts).find? e' = (updateD D e ts ++ D₂).find? e' := by
  by_cases hEq : e' = e
  · cases hEq
    have hLeft : (updateD (D ++ D₂) e ts).find? e = some ts := find_d_update_eq (env:=D ++ D₂) (e:=e) (ts:=ts)
    have hFind : (updateD D e ts).find? e = some ts := find_d_update_eq (env:=D) (e:=e) (ts:=ts)
    have hRight := find_d_append_left (D₁:=updateD D e ts) (D₂:=D₂) (e:=e) (ts:=ts) hFind
    simp [hLeft, hRight]
  · have hLeft : (updateD (D ++ D₂) e ts).find? e' = (D ++ D₂).find? e' :=
      find_d_update_neq (env:=D ++ D₂) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      find_d_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft' : D.find? e' with
    | some ts' =>
        have hLeft'' : (updateD D e ts).find? e' = some ts' := by
          simpa [hLeft'] using hfind
        have hA := find_d_append_left (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') (ts:=ts') hLeft''
        have hB := find_d_append_left (D₁:=D) (D₂:=D₂) (e:=e') (ts:=ts') hLeft'
        have hRight : (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simp [hA, hB]
        simp [hLeft, hRight]
    | none =>
        have hLeft'' : (updateD D e ts).find? e' = none := by
          simp [hLeft'] at hfind
          exact hfind
/- ## Structured Block 2 -/
        have hA := find_d_append_right (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') hLeft''
        have hB := find_d_append_right (D₁:=D) (D₂:=D₂) (e:=e') hLeft'
        have hRight : (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simp [hA, hB]
        simp [hLeft, hRight]

-- DEnv Update over Right Append
lemma find_d_update_d_append_right {D₁ D : DEnv} {e e' : Edge} {ts : List ValType}
    (hNone : D₁.find? e = none) :
    (updateD (D₁ ++ D) e ts).find? e' = (D₁ ++ updateD D e ts).find? e' := by
  by_cases hEq : e' = e
  · cases hEq
    have hLeft : (updateD (D₁ ++ D) e ts).find? e = some ts := find_d_update_eq (env:=D₁ ++ D) (e:=e) (ts:=ts)
    have hRight : (D₁ ++ updateD D e ts).find? e = some ts := by
      have hFind : (updateD D e ts).find? e = some ts := find_d_update_eq (env:=D) (e:=e) (ts:=ts)
      have hRight' := find_d_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e) hNone
      simp [hRight', hFind]
    simp [hLeft, hRight]
  · have hLeft : (updateD (D₁ ++ D) e ts).find? e' = (D₁ ++ D).find? e' :=
      find_d_update_neq (env:=D₁ ++ D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      find_d_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft' : D₁.find? e' with
    | some ts' =>
        have hA := find_d_append_left (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') (ts:=ts') hLeft'
        have hB := find_d_append_left (D₁:=D₁) (D₂:=D) (e:=e') (ts:=ts') hLeft'
        have hRight : (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          simp [hA, hB]
        simp [hLeft, hRight]
    | none =>
        have hA := find_d_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') hLeft'
        have hB := find_d_append_right (D₁:=D₁) (D₂:=D) (e:=e') hLeft'
        have hRight : (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          simp [hA, hB, hfind]
        simp [hLeft, hRight]

-- DEnv updateD Append Equalities
lemma update_d_append_left (D D₂ : DEnv) (e : Edge) (ts : List ValType) :
    updateD (D ++ D₂) e ts = updateD D e ts ++ D₂ := by
  apply d_env_ext
  intro e'
  exact find_d_update_d_append_left (D:=D) (D₂:=D₂) (e:=e) (e':=e') (ts:=ts)

lemma update_d_append_right (D₁ D : DEnv) (e : Edge) (ts : List ValType)
    (hNone : D₁.find? e = none) :
    updateD (D₁ ++ D) e ts = D₁ ++ updateD D e ts := by
  apply d_env_ext
  intro e'
  exact find_d_update_d_append_right (D₁:=D₁) (D:=D) (e:=e) (e':=e') (ts:=ts) hNone

-- GEnv Update over Right Append
lemma update_g_append_right_hit {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType}
    (hNone : lookupG G₁ e = none) :
    updateG (G₁ ++ G₂) e L = G₁ ++ updateG G₂ e L := by
  induction G₁ with
/- ## Structured Block 3 -/
  | nil =>
      simp
  | cons hd tl ih =>
      cases hd with
      | mk e' L' =>
          cases hEqb : (e == e') with
          | true =>
              have hLookup : lookupG ((e', L') :: tl) e = some L' := by
                simp [lookupG, List.lookup, hEqb]
              simp [hLookup] at hNone
          | false =>
              have hNone' : lookupG tl e = none := by
                simpa [lookupG, List.lookup, hEqb] using hNone
              have hne : e ≠ e' := by
                exact beq_eq_false_iff_ne.mp hEqb
              have ih' := ih hNone'
              simp [updateG, hne, ih']

-- ValidLabels Preservation (framed)

theorem valid_labels_preserved_frame_left
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Gfr Dfr} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DisjointG G Gfr →
    DConsistent Gfr Dfr →
    ValidLabels (G ++ Gfr) (D ++ Dfr) bufs →
    Coherent (G ++ Gfr) (D ++ Dfr) →
    BuffersTyped (G ++ Gfr) (D ++ Dfr) bufs →
    ValidLabels (G' ++ Gfr) (D' ++ Dfr) bufs' := by
  intro hTS hDisj hConsFr hValid hCoh hBT
  induction hTS generalizing Gfr Dfr with
  -- ValidLabels Framing Preservation: Send Case
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      subst hEdge hGout hDout hBufsOut
      set recvEp : Endpoint := { sid := e.sid, role := target }
      have hSid : e.sid ∈ SessionsOf G := ⟨e, .send target T L, hG, rfl⟩
      have hNotIn : e.sid ∉ SessionsOf Gfr := by
        intro hIn
        have hInter : e.sid ∈ SessionsOf G ∩ SessionsOf Gfr := ⟨hSid, hIn⟩
        have hEmpty : SessionsOf G ∩ SessionsOf Gfr = (∅ : Set SessionId) := hDisj
        simp [hEmpty] at hInter
      have hDfrNone :
          Dfr.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
        lookup_d_none_of_disjoint_g (G₁:=G) (G₂:=Gfr) (D₂:=Dfr) hDisj hConsFr hSid
      have hLookupD :
          lookupD (D ++ Dfr) { sid := e.sid, sender := e.role, receiver := target } =
            lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
        lookup_d_append_left_of_right_none (D₁:=D) (D₂:=Dfr) (e:={ sid := e.sid, sender := e.role, receiver := target }) hDfrNone
      have hGfrNone : lookupG Gfr recvEp = none := lookup_g_none_of_not_session hNotIn
      have hRecvReady' :
          ∀ Lrecv, lookupG (G ++ Gfr) recvEp = some Lrecv →
            ∃ L', Consume e.role Lrecv (lookupD (D ++ Dfr) { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
                  (Consume e.role L' [T]).isSome := by
/- ## Structured Block 4 -/
        intro Lrecv hLookup
        cases lookup_g_append_inv (G₁:=G) (G₂:=Gfr) (e:=recvEp) hLookup with
        | inl hLeft =>
            rcases hRecvReady Lrecv hLeft with ⟨L', hConsume, hConsumeT⟩
            refine ⟨L', ?_, hConsumeT⟩
            simpa [hLookupD] using hConsume
        | inr hRight =>
            cases hRight with
            | intro _ hRight =>
                simp [hGfrNone] at hRight
      have hG' : lookupG (G ++ Gfr) e = some (.send target T L) :=
        lookup_g_append_left (G₁:=G) (G₂:=Gfr) hG
      have hValid' :=
        valid_labels_send_preserved (G:=G ++ Gfr) (D:=D ++ Dfr) (bufs:=bufs)
          (senderEp:=e) (receiverRole:=target) (T:=T) (L:=L) (v:=v)
          hValid hCoh hBT hG' hRecvReady'
      simpa [update_g_append_left_hit hG, enqueueBuf, List.append_assoc] using hValid'
  -- ValidLabels Framing Preservation: Recv Case
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      subst hEdge hGout hDout hSout hStoreOut hBufsOut
      have hG' : lookupG (G ++ Gfr) e = some (.recv source T L) :=
        lookup_g_append_left (G₁:=G) (G₂:=Gfr) hG
      have hv' : HasTypeVal (G ++ Gfr) v T :=
        has_type_val_mono G (G ++ Gfr) v T hv (by
          intro ep L hLookup
          exact lookup_g_append_left (G₁:=G) (G₂:=Gfr) hLookup)
      have hValid' :=
        valid_labels_recv_preserved (G:=G ++ Gfr) (D:=D ++ Dfr) (bufs:=bufs)
          (receiverEp:=e) (senderRole:=source) (T:=T) (L:=L) (v:=v) (vs:=vs)
          hValid hCoh hBT hBuf hv' hG'
      simpa [ValidLabels, update_g_append_left_hit hG, List.append_assoc] using hValid'
  -- ValidLabels Framing Preservation: Select Case
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      subst hEdge hGout hDout hBufsOut
      set recvEp : Endpoint := { sid := e.sid, role := target }
      have hSid : e.sid ∈ SessionsOf G := ⟨e, .select target bs, hG, rfl⟩
      have hNotIn : e.sid ∉ SessionsOf Gfr := by
        intro hIn
        have hInter : e.sid ∈ SessionsOf G ∩ SessionsOf Gfr := ⟨hSid, hIn⟩
        have hEmpty : SessionsOf G ∩ SessionsOf Gfr = (∅ : Set SessionId) := hDisj
        simp [hEmpty] at hInter
      have hDfrNone :
          Dfr.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
        lookup_d_none_of_disjoint_g (G₁:=G) (G₂:=Gfr) (D₂:=Dfr) hDisj hConsFr hSid
      have hLookupD :
          lookupD (D ++ Dfr) { sid := e.sid, sender := e.role, receiver := target } =
            lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
        lookup_d_append_left_of_right_none (D₁:=D) (D₂:=Dfr) (e:={ sid := e.sid, sender := e.role, receiver := target }) hDfrNone
      have hGfrNone : lookupG Gfr recvEp = none := lookup_g_none_of_not_session hNotIn
      have hReady' :
/- ## Structured Block 5 -/
          ∀ Ltarget, lookupG (G ++ Gfr) recvEp = some Ltarget →
            ∃ L', Consume e.role Ltarget (lookupD (D ++ Dfr) { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
                  (Consume e.role L' [.string]).isSome := by
        intro Ltarget hLookup
        cases lookup_g_append_inv (G₁:=G) (G₂:=Gfr) (e:=recvEp) hLookup with
        | inl hLeft =>
            rcases hReady Ltarget hLeft with ⟨L', hConsume, hConsumeT⟩
            refine ⟨L', ?_, hConsumeT⟩
            simpa [hLookupD] using hConsume
        | inr hRight =>
            cases hRight with
            | intro _ hRight =>
                simp [hGfrNone] at hRight
      have hG' : lookupG (G ++ Gfr) e = some (.select target bs) :=
        lookup_g_append_left (G₁:=G) (G₂:=Gfr) hG
      have hValid' :=
        valid_labels_select_preserved (G:=G ++ Gfr) (D:=D ++ Dfr) (bufs:=bufs)
          (selectorEp:=e) (targetRole:=target) (selectBranches:=bs) (ℓ:=ℓ) (L:=L)
          hValid hCoh hBT hG' hFind hReady'
      simpa [ValidLabels, update_g_append_left_hit hG, enqueueBuf, List.append_assoc] using hValid'
  -- ValidLabels Framing Preservation: Branch Case
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      subst hEdge hGout hDout hBufsOut
      have hG' : lookupG (G ++ Gfr) e = some (.branch source bs) :=
        lookup_g_append_left (G₁:=G) (G₂:=Gfr) hG
      have hValid' :=
        valid_labels_branch_preserved (G:=G ++ Gfr) (D:=D ++ Dfr) (bufs:=bufs)
          (brancherEp:=e) (senderRole:=source) (branchOptions:=bs) (ℓ:=ℓ) (L:=L) (vs:=vs)
          hValid hCoh hBT hG' hFindT hBuf
      simpa [ValidLabels, update_g_append_left_hit hG, List.append_assoc] using hValid'
  -- ValidLabels Framing Preservation: Structural Cases
  | assign =>
      simpa using hValid
  | seq_step _ ih =>
      exact ih hDisj hConsFr hValid hCoh hBT
  | seq_skip =>
      simpa using hValid
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih hDisj hConsFr hValid hCoh hBT
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih hDisj hConsFr hValid hCoh hBT
  | par_skip_left =>
      simpa using hValid
  | par_skip_right =>
      simpa using hValid

-- ValidLabels Preservation without Extra Frame
theorem valid_labels_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    ValidLabels G D bufs →
    Coherent G D →
    BuffersTyped G D bufs →
/- ## Structured Block 6 -/
    ValidLabels G' D' bufs' := by
  intro hTS hValid hCoh hBT
  have hDisj : DisjointG G [] := disjoint_g_right_empty G
  have hConsFr : DConsistent ([] : GEnv) (∅ : DEnv) := d_consistent_empty []
  have hValid' :=
    valid_labels_preserved_frame_left (Gfr:=[]) (Dfr:=∅) hTS hDisj hConsFr
      (by simpa [List.append_nil, d_env_append_empty_right] using hValid)
      (by simpa [List.append_nil, d_env_append_empty_right] using hCoh)
      (by simpa [List.append_nil, d_env_append_empty_right] using hBT)
  simpa [List.append_nil, d_env_append_empty_right] using hValid'


end
