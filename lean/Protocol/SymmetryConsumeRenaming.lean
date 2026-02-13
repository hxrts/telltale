import Protocol.SymmetryCore

/-! # Protocol.SymmetryConsumeRenaming

Consume renaming commutation and symmetry consequences for branching/coherence.
-/

/-
The Problem. Show Consume/coherence invariants are preserved by protocol renaming.

Solution Structure. Prove type/role renaming injectivity and commutation, then lift to coherence.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section
-- Consume Renaming

/-- Renaming value types is injective. -/
theorem renameValTypePR_inj (σ : ProtocolRenaming) :
    Function.Injective (renameValTypePR σ) := by
  intro T1 T2 h
  induction T1 generalizing T2 with
  -- Injectivity: unit constructor
  | unit =>
      cases T2 with
      | unit => rfl
      | bool =>
          cases h
      | nat =>
          cases h
      | string =>
          cases h
      | prod _ _ =>
          cases h
      | chan _ _ =>
          cases h
  -- Injectivity: bool constructor
  | bool =>
      cases T2 with
      | bool => rfl
      | unit =>
          cases h
      | nat =>
          cases h
      | string =>
          cases h
      | prod _ _ =>
          cases h
      | chan _ _ =>
          cases h
  -- Injectivity: nat constructor
  | nat =>
      cases T2 with
      | nat => rfl
      | unit =>
          cases h
      | bool =>
          cases h
      | string =>
          cases h
      | prod _ _ =>
          cases h
      | chan _ _ =>
          cases h
  -- Injectivity: string constructor
  | string =>
      cases T2 with
      | string => rfl
      | unit =>
          cases h
      | bool =>
          cases h
      | nat =>
          cases h
      | prod _ _ =>
          cases h
      | chan _ _ =>
          cases h
  -- Injectivity: product constructor
  | prod T1 T2 ih1 ih2 =>
      cases T2 <;> simp [renameValTypePR] at h
      case prod T1' T2' =>
        rcases h with ⟨h1, h2⟩
        have h1' := ih1 h1
        have h2' := ih2 h2
        simp [h1', h2']
  -- Injectivity: channel constructor
  | chan sid role =>
      cases T2 <;> simp [renameValTypePR] at h
      case chan sid2 role2 =>
        rcases h with ⟨hsid, hrole⟩
        have hrole' : role = role2 := σ.roleMap_inj _ _ hrole
        subst hsid
        subst hrole'
        rfl

/-- Role equality is preserved under protocol renaming. -/
theorem roleMap_beq (σ : ProtocolRenaming) (a b : Role) :
    (σ.roleMap a == σ.roleMap b) = (a == b) := by
  by_cases h : a = b
  · simp [h]
  · have h' : σ.roleMap a ≠ σ.roleMap b := by
      intro hEq
      exact h (σ.roleMap_inj _ _ hEq)
    have hbeq : (a == b) = false := beq_eq_false_iff_ne.mpr h
    have hbeq' : (σ.roleMap a == σ.roleMap b) = false := beq_eq_false_iff_ne.mpr h'
    simp [hbeq, hbeq']

/-- Value-type equality is preserved under protocol renaming. -/
theorem renameValTypePR_beq (σ : ProtocolRenaming) (T T' : ValType) :
    (renameValTypePR σ T == renameValTypePR σ T') = (T == T') := by
  by_cases h : T = T'
  · simp [h]
  · have h' : renameValTypePR σ T ≠ renameValTypePR σ T' := by
      intro hEq
      exact h (renameValTypePR_inj σ hEq)
    have hbeq : (T == T') = false := beq_eq_false_iff_ne.mpr h
    have hbeq' : (renameValTypePR σ T == renameValTypePR σ T') = false :=
      beq_eq_false_iff_ne.mpr h'
    simp [hbeq, hbeq']

/-- Renaming commutes with a single consume step. -/
theorem consumeOne_renamePR (σ : ProtocolRenaming) (from_ : Role) (T : ValType) (L : LocalType) :
    consumeOne (σ.roleMap from_) (renameValTypePR σ T) (renameLocalTypePR σ L) =
      (consumeOne from_ T L).map (renameLocalTypePR σ) := by
  cases L <;>
    simp [consumeOne, renameLocalTypePR, roleMap_beq, renameValTypePR_beq]

/-- Renaming commutes with Consume over a trace. -/
theorem Consume_renamePR (σ : ProtocolRenaming) (from_ : Role) (L : LocalType) (ts : List ValType) :
    Consume (σ.roleMap from_) (renameLocalTypePR σ L) (ts.map (renameValTypePR σ)) =
      (Consume from_ L ts).map (renameLocalTypePR σ) := by
  induction ts generalizing L with
  | nil =>
      simp [Consume]
  | cons t ts ih =>
      simp [Consume]
      cases h : consumeOne from_ t L with
      | none =>
          simp [consumeOne_renamePR, h]
      | some L' =>
          simp [consumeOne_renamePR, h, ih]

-- Branch Symmetry Consequences

/-- Labels are renamed pointwise inside branch lists. -/
theorem branch_labels_renamed (σ : ProtocolRenaming) (bs : List (Label × LocalType)) :
    List.map Prod.fst (renameBranchesPR σ bs) =
      List.map σ.labelMap (List.map Prod.fst bs) := by
  induction bs with
  | nil =>
      simp [renameBranchesPR]
  | cons hd tl ih =>
      cases hd with
      | mk l L =>
          simp [renameBranchesPR, ih]

/-- Branch labels remain duplicate-free under injective label renaming. -/
theorem branch_labels_nodup_preserved (σ : ProtocolRenaming)
    {bs : List (Label × LocalType)}
    (hNodup : List.Nodup (List.map Prod.fst bs)) :
    List.Nodup (List.map Prod.fst (renameBranchesPR σ bs)) := by
  induction bs with
  | nil =>
      simp [renameBranchesPR]
  | cons hd tl ih =>
      cases hd with
      | mk l L =>
          have hNodup' : List.Nodup (l :: List.map Prod.fst tl) := by
            simpa using hNodup
          rcases (List.nodup_cons).1 hNodup' with ⟨hNotMem, hTail⟩
          have hTail' : List.Nodup (List.map Prod.fst (renameBranchesPR σ tl)) :=
            ih hTail
          have hNotMem' :
              σ.labelMap l ∉ List.map Prod.fst (renameBranchesPR σ tl) := by
            intro hmem
            have hmem' :
                σ.labelMap l ∈ List.map σ.labelMap (List.map Prod.fst tl) := by
              simpa [branch_labels_renamed] using hmem
            rcases List.mem_map.1 hmem' with ⟨l', hl', hmap⟩
            have hl'Eq : l' = l := σ.labelMap_inj _ _ hmap
            exact hNotMem (by simpa [hl'Eq] using hl')
          have hNodupRen :
              List.Nodup (σ.labelMap l :: List.map Prod.fst (renameBranchesPR σ tl)) := by
            exact (List.nodup_cons).2 ⟨hNotMem', hTail'⟩
          simpa [renameBranchesPR] using hNodupRen

-- Branch Renaming Structural Facts

/-- Label permutation preserves branching structure.
    If a branch has labels l₁, ..., lₙ, the renamed branch has labels σ(l₁), ..., σ(lₙ). -/
theorem branches_length_preserved (σ : ProtocolRenaming) (bs : List (Label × LocalType)) :
    (renameBranchesPR σ bs).length = bs.length := by
  induction bs with
  | nil => simp [renameBranchesPR]
  | cons hd tl ih =>
      cases hd with
      | mk l L =>
          simp [renameBranchesPR, ih]

/-- Lookup in renamed DEnv: renaming commutes with lookup. -/
private theorem lookupD_renamePR_foldl (σ : ProtocolRenaming) :
    ∀ (l : List (Edge × Trace)) (acc : DEnv) (e : Edge)
      (hNodup : List.Nodup (List.map Prod.fst l)),
      lookupD
          (l.foldl
            (fun acc p =>
              updateD acc (renameEdgePR σ p.1) (p.2.map (renameValTypePR σ)))
            acc)
          (renameEdgePR σ e) =
        match l.lookup e with
        | some ts => ts.map (renameValTypePR σ)
        | none => lookupD acc (renameEdgePR σ e) := by
  intro l acc e hNodup
  induction l generalizing acc e with
  -- DEnv Lookup/Fold: empty list
  | nil =>
      simp [lookupD]
  -- DEnv Lookup/Fold: non-empty list
  | cons hd tl ih =>
      have hNodup' : List.Nodup (hd.1 :: List.map Prod.fst tl) := by
        simpa using hNodup
      rcases (List.nodup_cons).1 hNodup' with ⟨hNotMem, hNodupTl⟩
      -- DEnv Lookup/Fold: hit head edge
      by_cases hEq : e = hd.1
      · subst hEq
        have hNotMem' : ∀ p ∈ tl, p.1 ≠ hd.1 := by
          intro p hp hEq'
          have hmem : hd.1 ∈ List.map Prod.fst tl := by
            have hmem' : p.1 ∈ List.map Prod.fst tl :=
              List.mem_map.mpr ⟨p, hp, rfl⟩
            simpa [hEq'] using hmem'
          exact hNotMem hmem
        have hLookupTl : tl.lookup hd.1 = none :=
          lookup_eq_none_of_forall_ne hNotMem'
        -- Use IH on tail with updated accumulator.
        have hIH :=
          ih (acc:=updateD acc (renameEdgePR σ hd.1) (hd.2.map (renameValTypePR σ)))
            (e:=hd.1) hNodupTl
        -- Simplify using tail lookup = none.
        simp [hLookupTl, lookupD_update_eq] at hIH
        simpa [List.lookup] using hIH
      -- DEnv Lookup/Fold: miss head edge
      · have hEq' : renameEdgePR σ e ≠ renameEdgePR σ hd.1 := by
          intro hcontra
          exact hEq (renameEdgePR_inj σ _ _ hcontra)
        have hEq'' : renameEdgePR σ hd.1 ≠ renameEdgePR σ e := Ne.symm hEq'
        have hIH :=
          ih (acc:=updateD acc (renameEdgePR σ hd.1) (hd.2.map (renameValTypePR σ)))
            (e:=e) hNodupTl
        -- For the none case, rewrite the updated lookup back to acc.
        have hAcc :
            lookupD (updateD acc (renameEdgePR σ hd.1) (hd.2.map (renameValTypePR σ)))
              (renameEdgePR σ e) = lookupD acc (renameEdgePR σ e) := by
          exact lookupD_update_neq _ _ _ _ hEq''
        have hbeq : (e == hd.1) = false := beq_eq_false_iff_ne.mpr hEq
        simpa [List.foldl, List.lookup, hbeq, hAcc] using hIH

/-- Lookup in renamed DEnv: renaming commutes with lookup. -/
theorem lookupD_renamePR (σ : ProtocolRenaming) (D : DEnv) (e : Edge) :
    lookupD (renameDEnvPR σ D) (renameEdgePR σ e) =
      (lookupD D e).map (renameValTypePR σ) := by
  -- DEnv Lookup Renaming: nodup keys
  -- Reduce lookup to list-based form.
  have hNodup : List.Nodup (List.map Prod.fst D.list) := by
    -- D.list is pairwise ordered, so keys are distinct.
    -- Pairwise strict order implies no duplicate keys.
    -- Use the list-of-keys view for a direct nodup proof.
    have hPair := D.sorted
    revert hPair
    induction D.list with
    | nil =>
        intro _; simp
    | cons hd tl ih =>
        intro hPair
        simp only [List.pairwise_cons] at hPair
        rcases hPair with ⟨hHd, hTl⟩
        have hNotMem : hd.1 ∉ List.map Prod.fst tl := by
          intro hmem
          rcases List.mem_map.1 hmem with ⟨p, hp, hpEq⟩
          have hLt : edgeCmpLT hd p := hHd p hp
          have hNe : hd.1 ≠ p.1 := by
            intro hEq
            have hlt : compare hd.1 p.1 = .lt := edgeCmpLT_eq_lt hLt
            have hEqCmp : compare hd.1 p.1 = .eq :=
              (Edge.compare_eq_iff_eq hd.1 p.1).2 hEq
            have : (Ordering.lt : Ordering) = .eq := hlt.symm.trans hEqCmp
            cases this
          exact hNe hpEq.symm
        have hTail : List.Nodup (List.map Prod.fst tl) := ih hTl
        exact (List.nodup_cons).2 ⟨hNotMem, hTail⟩
  -- DEnv Lookup Renaming: foldl transport
  -- Use foldl lookup lemma on the underlying list.
  have hFold :=
    lookupD_renamePR_foldl (σ:=σ) (l:=D.list) (acc:=(∅ : DEnv)) (e:=e) hNodup
  -- Rewrite lookupD D e using list lookup.
  have hLookup : lookupD D e =
      match D.list.lookup e with
      | some ts => ts
      | none => [] := by
    cases h : D.list.lookup e <;> simp [lookupD, DEnv_find?_eq_lookup, h]
  -- DEnv Lookup Renaming: finish by cases
  -- Finish by rewriting the match.
  cases h : D.list.lookup e with
  | none =>
      simp [h] at hFold
      simpa [hLookup, h] using hFold
  | some ts =>
      simp [h] at hFold
      simpa [hLookup, h] using hFold

/-- The coherence invariant is preserved under protocol renaming.
    This is the main conservation theorem. -/
theorem coherence_protocol_renaming_preserved (σ : ProtocolRenaming) (G : GEnv) (D : DEnv)
    (hCoh : Coherent G D) :
    Coherent (renameGEnvPR σ G) (renameDEnvPR σ D) := by
  -- Coherence Under Renaming: receiver preimage
  -- Proof sketch: coherence depends on structural relationships between
  -- sender types, receiver types, and buffer contents. Protocol renaming
  -- preserves these relationships since it's injective on roles/labels.
  intro e hActive Lrecv hGrecv
  -- Receiver preimage
  obtain ⟨recvEp, Lrecv0, hRecvLookup, hRecvEq, hLrecvEq⟩ :=
    lookupG_renamePR_inv σ G { sid := e.sid, role := e.receiver } Lrecv hGrecv
  have hRecvSid : recvEp.sid = e.sid := by
    have := congrArg Endpoint.sid hRecvEq
    simp [renameEndpointPR] at this
    exact this.symm
  have hRecvRole : σ.roleMap recvEp.role = e.receiver := by
    have := congrArg Endpoint.role hRecvEq
    simp [renameEndpointPR] at this
    exact this.symm
  -- Coherence Under Renaming: sender preimage
  -- Sender preimage from ActiveEdge
  rcases hActive with ⟨hSenderSome, _⟩
  rcases (Option.isSome_iff_exists).1 hSenderSome with ⟨LsenderRen, hGsenderRen⟩
  obtain ⟨sendEp, Lsender0, hSendLookup, hSendEq, hLsenderEq⟩ :=
    lookupG_renamePR_inv σ G { sid := e.sid, role := e.sender } LsenderRen hGsenderRen
  have hSendSid : sendEp.sid = e.sid := by
    have := congrArg Endpoint.sid hSendEq
    simp [renameEndpointPR] at this
    exact this.symm
  have hSendRole : σ.roleMap sendEp.role = e.sender := by
    have := congrArg Endpoint.role hSendEq
    simp [renameEndpointPR] at this
    exact this.symm
  -- Coherence Under Renaming: preimage edge and activity
  -- Preimage edge
  let e0 : Edge := { sid := e.sid, sender := sendEp.role, receiver := recvEp.role }
  have hSendEqEp : ({ sid := e.sid, role := sendEp.role } : Endpoint) = sendEp := by
    cases sendEp with
    | mk sid0 role0 =>
        cases hSendSid
        rfl
  have hRecvEqEp : ({ sid := e.sid, role := recvEp.role } : Endpoint) = recvEp := by
    cases recvEp with
    | mk sid0 role0 =>
        cases hRecvSid
        rfl
  have hActive0 : ActiveEdge G e0 :=
    ActiveEdge_of_endpoints (G:=G) (e:=e0) (Lsender:=Lsender0) (Lrecv:=Lrecv0)
      (by
        -- sender lookup
        have hEq : ({ sid := e0.sid, role := e0.sender } : Endpoint) = sendEp := by
          simpa [e0] using hSendEqEp
        simpa [hEq] using hSendLookup)
      (by
        -- receiver lookup
        have hEq : ({ sid := e0.sid, role := e0.receiver } : Endpoint) = recvEp := by
          simpa [e0] using hRecvEqEp
        simpa [hEq] using hRecvLookup)
  -- Coherence on preimage edge
  have hRecvLookup0 : lookupG G { sid := e0.sid, role := e0.receiver } = some Lrecv0 := by
    simpa [e0, hRecvEqEp] using hRecvLookup
  obtain ⟨Lsender0', hSender0', hConsume0⟩ := hCoh e0 hActive0 Lrecv0 hRecvLookup0
  have hSender0'' :
      lookupG G { sid := e.sid, role := sendEp.role } = some Lsender0' := by
    simpa [e0] using hSender0'
  -- Sender lookup after renaming
  have hSenderRen :
      lookupG (renameGEnvPR σ G) { sid := e.sid, role := e.sender } =
        some (renameLocalTypePR σ Lsender0') := by
    have hEq : renameEndpointPR σ { sid := e.sid, role := sendEp.role } =
        ({ sid := e.sid, role := e.sender } : Endpoint) := by
      simp [renameEndpointPR, hSendRole]
    have hLookup := lookupG_renamePR σ G { sid := e.sid, role := sendEp.role }
    simpa [hEq, hSender0''] using hLookup
  -- Coherence Under Renaming: trace lookup transport
  -- Trace lookup after renaming
  have hEdgeEq : renameEdgePR σ e0 = e := by
    simp [renameEdgePR, e0, hSendRole, hRecvRole]
  have hTrace :
      lookupD (renameDEnvPR σ D) e =
        (lookupD D e0).map (renameValTypePR σ) := by
    simpa [hEdgeEq] using (lookupD_renamePR (σ:=σ) (D:=D) (e:=e0))
  -- Coherence Under Renaming: consume transport
  -- Consume preserved by renaming
  have hConsumeRen :
      (Consume e.sender Lrecv (lookupD (renameDEnvPR σ D) e)).isSome := by
    -- Use Consume_renamePR on the preimage data
    have hCons :=
      Consume_renamePR (σ:=σ) (from_:=sendEp.role) (L:=Lrecv0) (ts:=lookupD D e0)
    -- Rewrite roles/types/traces
    have hSenderEq : σ.roleMap sendEp.role = e.sender := hSendRole
    have hRecvEq : Lrecv = renameLocalTypePR σ Lrecv0 := by
      simpa using hLrecvEq
    -- Apply isSome on the renamed consume
    cases hC : Consume sendEp.role Lrecv0 (lookupD D e0) with
    | none =>
        have : (Consume sendEp.role Lrecv0 (lookupD D e0)).isSome = true := by
          simpa using hConsume0
        simp [hC] at this
    | some L' =>
        -- hConsume0 implies the original consume succeeds
        have hCons' : Consume sendEp.role Lrecv0 (lookupD D e0) = some L' := by
          simp [hC]
        have hConsRen :
            Consume (σ.roleMap sendEp.role) (renameLocalTypePR σ Lrecv0)
              ((lookupD D e0).map (renameValTypePR σ)) =
              some (renameLocalTypePR σ L') := by
          simpa [hCons'] using hCons
        -- Transfer to the renamed edge
        have hConsRen' :
            Consume e.sender (renameLocalTypePR σ Lrecv0)
              ((lookupD D e0).map (renameValTypePR σ)) =
              some (renameLocalTypePR σ L') := by
          simpa [hSenderEq] using hConsRen
        -- Conclude isSome
        have : (Consume e.sender (renameLocalTypePR σ Lrecv0)
          ((lookupD D e0).map (renameValTypePR σ))).isSome = true := by
          simp [hConsRen']
        simpa [hRecvEq, hTrace] using this
  -- Coherence Under Renaming: conclude
  refine ⟨renameLocalTypePR σ Lsender0', hSenderRen, ?_⟩
  simpa [hTrace] using hConsumeRen


end
