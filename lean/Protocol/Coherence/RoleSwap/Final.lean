
import Protocol.Coherence.RoleSwap.LookupConsume

/-! # Protocol.Coherence.RoleSwap.Final

Final coherence and exchangeability theorems for role swaps.
-/

/-
The Problem. Final role-swap results package coherence preservation for single
and list-based swaps.

Solution Structure. Proves final coherence and exchangeability theorems.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

-- Coherence Preservation for Role Swap

-- Single-Swap Coherence Theorem

/-- Coherence is preserved under swapping two roles within a session. -/
theorem CoherentRoleSwap (s : SessionId) (A B : Role) (G : GEnv) (D : DEnv)
    (hCoh : Coherent G D) :
    Coherent (swapGEnvRole s A B G) (swapDEnvRole s A B D) := by
  intro e hActive Lrecv hGrecv
  by_cases hSid : e.sid = s
  · -- Session-local swap case.
    -- CoherentRoleSwap: Session-Local Edge Case
    let e' : Edge := swapEdgeRole s A B e
    let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    let senderEp : Endpoint := { sid := e.sid, role := e.sender }
    let recvEp' : Endpoint := { sid := e'.sid, role := e'.receiver }
    let senderEp' : Endpoint := { sid := e'.sid, role := e'.sender }
    have hRecvEp : swapEndpointRole s A B recvEp' = recvEp := by
      simp [recvEp, recvEp', e', swapEdgeRole, swapEndpointRole, hSid, swapRole_involutive]
    have hSenderEp : swapEndpointRole s A B senderEp' = senderEp := by
      simp [senderEp, senderEp', e', swapEdgeRole, swapEndpointRole, hSid, swapRole_involutive]
    -- CoherentRoleSwap: Translate Endpoint Lookups
    have hLookupRecvMap :
        lookupG (swapGEnvRole s A B G) recvEp =
          (lookupG G recvEp').map (swapLocalTypeRole s A B) := by
      have hSid' : recvEp'.sid = s := by
        simp [recvEp', e', swapEdgeRole, hSid]
      simpa [hRecvEp, hSid'] using
        (lookupG_swap (s:=s) (A:=A) (B:=B) (G:=G) (e:=recvEp'))
    have hLookupRecvEq :
        (lookupG G recvEp').map (swapLocalTypeRole s A B) = some Lrecv := by
      calc
        (lookupG G recvEp').map (swapLocalTypeRole s A B)
            = lookupG (swapGEnvRole s A B G) recvEp := by
              symm
              exact hLookupRecvMap
        _ = some Lrecv := hGrecv
    cases hLookupR : lookupG G recvEp' with
    | none =>
        have : False := by
          simp [hLookupR] at hLookupRecvEq
        exact this.elim
    | some Lrecv0 =>
        have hLrecv : Lrecv = swapLocalTypeRole s A B Lrecv0 := by
          have : some (swapLocalTypeRole s A B Lrecv0) = some Lrecv := by
            simpa [hLookupR] using hLookupRecvEq
          exact (Option.some.inj this).symm
        have hGrecv0 : lookupG G recvEp' = some Lrecv0 := hLookupR
        -- CoherentRoleSwap: Recover Sender Preimage Lookup
        have hLookupSenderMap :
            lookupG (swapGEnvRole s A B G) senderEp =
              (lookupG G senderEp').map (swapLocalTypeRole s A B) := by
          have hSid' : senderEp'.sid = s := by
/- ## Structured Block 2 -/
            simp [senderEp', e', swapEdgeRole, hSid]
          simpa [hSenderEp, hSid'] using
            (lookupG_swap (s:=s) (A:=A) (B:=B) (G:=G) (e:=senderEp'))
        rcases (Option.isSome_iff_exists).1 hActive.1 with ⟨LsenderSwapped, hGsenderSwapped⟩
        have hLookupSenderEq :
            (lookupG G senderEp').map (swapLocalTypeRole s A B) =
              some LsenderSwapped := by
          calc
            (lookupG G senderEp').map (swapLocalTypeRole s A B)
                = lookupG (swapGEnvRole s A B G) senderEp := by
                  symm
                  exact hLookupSenderMap
            _ = some LsenderSwapped := hGsenderSwapped
        have hGsender0 : ∃ Lsender0, lookupG G senderEp' = some Lsender0 := by
          cases hLookupS : lookupG G senderEp' with
          | none =>
              have : False := by
                simp [hLookupS] at hLookupSenderEq
              exact this.elim
          | some Lsender0 =>
              exact ⟨Lsender0, rfl⟩
        rcases hGsender0 with ⟨Lsender0, hGsender0⟩
        -- CoherentRoleSwap: Pull Back Coherence Witness
        have hActive' : ActiveEdge G e' :=
          ActiveEdge_of_endpoints (e:=e') hGsender0 hGrecv0
        have hCoh' := hCoh e' hActive' Lrecv0 hGrecv0
        rcases hCoh' with ⟨Lsender1, hGsender1, hConsume⟩
        have hLookupSender' :
            lookupG (swapGEnvRole s A B G) senderEp =
              some (swapLocalTypeRole s A B Lsender1) := by
          have : (lookupG G senderEp').map (swapLocalTypeRole s A B) =
              some (swapLocalTypeRole s A B Lsender1) := by
            rw [hGsender1]
            rfl
          exact (by
            calc
              lookupG (swapGEnvRole s A B G) senderEp
                  = (lookupG G senderEp').map (swapLocalTypeRole s A B) := hLookupSenderMap
              _ = some (swapLocalTypeRole s A B Lsender1) := this)
        rcases (Option.isSome_iff_exists).1 hConsume with ⟨Lafter, hConsumeEq⟩
        -- CoherentRoleSwap: Push Consume Through Swap
        have hConsumeSwap :
            Consume (swapRole A B e'.sender) (swapLocalTypeRole s A B Lrecv0)
                ((lookupD D e').map (swapValTypeRole s A B)) =
              some (swapLocalTypeRole s A B Lafter) := by
          exact Consume_swap (s:=s) (A:=A) (B:=B) (from_:=e'.sender)
            (L:=Lrecv0) (ts:=lookupD D e') (L':=Lafter) hConsumeEq
        have hTrace :
            lookupD (swapDEnvRole s A B D) e =
              (lookupD D e').map (swapValTypeRole s A B) := by
          have hLookup :=
            lookupD_swap (s:=s) (A:=A) (B:=B) (D:=D) (e:=e')
/- ## Structured Block 3 -/
          have hSwap : swapEdgeRole s A B e' = e := by
            simp [e', swapEdgeRole_involutive]
          have hSid' : e'.sid = s := by
            simp [e', swapEdgeRole, hSid]
          simpa [hSwap, hSid'] using hLookup
        have hSenderEq : e.sender = swapRole A B e'.sender := by
          simp [e', swapEdgeRole, hSid, swapRole_involutive]
        have hConsumeSwapped :
            Consume e.sender Lrecv (lookupD (swapDEnvRole s A B D) e) =
              some (swapLocalTypeRole s A B Lafter) := by
          simpa [hSenderEq, hLrecv, hTrace] using hConsumeSwap
        refine ⟨swapLocalTypeRole s A B Lsender1, hLookupSender', ?_⟩
        simp [hConsumeSwapped]
  -- CoherentRoleSwap: Non-Target Session Edge
  · -- Other-session edges are unchanged.
    have hSidNe : e.sid ≠ s := hSid
    let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    let senderEp : Endpoint := { sid := e.sid, role := e.sender }
    have hSwapRecv : swapEndpointRole s A B recvEp = recvEp := by
      simp [swapEndpointRole, recvEp, hSid]
    have hSwapSender : swapEndpointRole s A B senderEp = senderEp := by
      simp [swapEndpointRole, senderEp, hSid]
    have hGrecv' : lookupG G recvEp = some Lrecv := by
      have hLookup :=
        lookupG_swap (s:=s) (A:=A) (B:=B) (G:=G) (e:=recvEp)
      have hMap : lookupG (swapGEnvRole s A B G) recvEp =
          lookupG G recvEp := by
        simpa [hSid, hSwapRecv, recvEp] using hLookup
      calc
        lookupG G recvEp = lookupG (swapGEnvRole s A B G) recvEp := by
          symm
          exact hMap
        _ = some Lrecv := by
          simpa using hGrecv
    have hActive' : ActiveEdge G e := by
      have hLookupSender :=
        lookupG_swap (s:=s) (A:=A) (B:=B) (G:=G) (e:=senderEp)
      have hMap :
          lookupG (swapGEnvRole s A B G) senderEp =
            lookupG G senderEp := by
        simpa [hSid, hSwapSender, senderEp] using hLookupSender
      have hSenderSome : (lookupG G senderEp).isSome := by
        simpa [hMap, senderEp] using hActive.1
      have hRecvSome : (lookupG G recvEp).isSome := by
        exact (Option.isSome_iff_exists.mpr ⟨Lrecv, hGrecv'⟩)
      exact ⟨hSenderSome, hRecvSome⟩
    have hCoh' := hCoh e hActive' Lrecv hGrecv'
    rcases hCoh' with ⟨Lsender, hGsender, hConsume⟩
    have hLookupSender' :
        lookupG (swapGEnvRole s A B G) senderEp = some Lsender := by
      have hLookup :=
/- ## Structured Block 4 -/
        lookupG_swap (s:=s) (A:=A) (B:=B) (G:=G) (e:=senderEp)
      simpa [hSid, hSwapSender, hGsender, senderEp] using hLookup
    have hTrace :
        lookupD (swapDEnvRole s A B D) e = lookupD D e := by
      have hLookup :=
        lookupD_swap (s:=s) (A:=A) (B:=B) (D:=D) (e:=e)
      have hSwap : swapEdgeRole s A B e = e := by
        simp [swapEdgeRole, hSid]
      simpa [hSid, hSwap] using hLookup
    refine ⟨Lsender, hLookupSender', ?_⟩
    simpa [hTrace] using hConsume

-- Role Swap Sequences (Exchangeability Primitive)

/-- Apply a list of role swaps to a role. -/
def swapRoleList (pairs : List (Role × Role)) (r : Role) : Role :=
  pairs.foldl (fun acc p => swapRole p.1 p.2 acc) r

/-- Apply a list of role swaps to a GEnv, session-local. -/
def swapGEnvRoleList (s : SessionId) (pairs : List (Role × Role)) (G : GEnv) : GEnv :=
  pairs.foldl (fun acc p => swapGEnvRole s p.1 p.2 acc) G

/-- Apply a list of role swaps to a DEnv, session-local. -/
def swapDEnvRoleList (s : SessionId) (pairs : List (Role × Role)) (D : DEnv) : DEnv :=
  pairs.foldl (fun acc p => swapDEnvRole s p.1 p.2 acc) D

/-- Coherence is preserved under any finite sequence of role swaps in a session. -/
theorem CoherentRoleSwap_list (s : SessionId) (pairs : List (Role × Role)) (G : GEnv) (D : DEnv)
    (hCoh : Coherent G D) :
    Coherent (swapGEnvRoleList s pairs G) (swapDEnvRoleList s pairs D) := by
  induction pairs generalizing G D with
  | nil =>
      simpa [swapGEnvRoleList, swapDEnvRoleList] using hCoh
  | cons hd tl ih =>
      have hCoh' : Coherent (swapGEnvRole s hd.1 hd.2 G) (swapDEnvRole s hd.1 hd.2 D) :=
        CoherentRoleSwap (s:=s) (A:=hd.1) (B:=hd.2) (G:=G) (D:=D) hCoh
      simpa [swapGEnvRoleList, swapDEnvRoleList, List.foldl] using
        ih (G:=swapGEnvRole s hd.1 hd.2 G) (D:=swapDEnvRole s hd.1 hd.2 D) hCoh'

/-- Exchangeability corollary: any finite swap sequence preserves coherence. -/
theorem Coherent_exchangeable (s : SessionId) (pairs : List (Role × Role)) (G : GEnv) (D : DEnv)
    (hCoh : Coherent G D) :
    Coherent (swapGEnvRoleList s pairs G) (swapDEnvRoleList s pairs D) := by
  simpa using CoherentRoleSwap_list (s := s) (pairs := pairs) (G := G) (D := D) hCoh

end
