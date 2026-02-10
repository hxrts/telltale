import Runtime.VM.Semantics.InstrSpec
import Protocol.Coherence.EdgeCoherence
import Protocol.Coherence.Preservation
import Protocol.Coherence.SelectPreservation
import Protocol.Coherence.ConfigEquiv
import Protocol.Coherence.Delegation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# VM Instruction Specification Proofs

Preservation theorems connecting VM instruction specs to Protocol-level coherence.
-/

/-
The Problem. VM instructions (send, recv, select, branch, delegate) must preserve
the Protocol coherence invariant. Each instruction has a spec defining pre/post
conditions that need to be connected to the coherence preservation theorems.

Solution Structure. For each instruction type, defines a preservation theorem
(e.g., `SendSpec_preserves_Coherent`) that extracts preconditions from the spec
and applies the corresponding Protocol-level preservation lemma. Uses SendReady,
buffer head evidence, and label matching to satisfy preconditions.
-/

open scoped Classical

section

/-! ## Preservation Theorems -/

/-- Send preserves Coherence when SendReady holds.

    The proof extracts the sender type from the spec and constructs the
    receiver-readiness evidence required by `Coherent_send_preserved`. -/
theorem SendSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {senderEp : Endpoint} {receiverRole : Role} {T : ValType}
    (hSpec : SendSpec G G' D D' senderEp receiverRole T)
    (hCoh : Coherent G D)
    (hReady : SendReady G D) :
    Coherent G' D' := by
  -- Extract sender type from spec
  obtain ⟨L', hSenderType⟩ := hSpec.sender_type
  -- SendReady gives us the receiver readiness condition
  have hRecvReady : ∀ Lrecv, lookupG G { sid := senderEp.sid, role := receiverRole } = some Lrecv →
      ∃ L'', Consume senderEp.role Lrecv
        (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L'' ∧
        (Consume senderEp.role L'' [T]).isSome := by
    intro Lrecv hLrecv
    exact hReady senderEp receiverRole T L' hSenderType Lrecv hLrecv
  -- The spec tells us G' and D' are the result of the update
  -- Apply Protocol-level preservation
  have hResult := Coherent_send_preserved G D senderEp receiverRole T L' hCoh hSenderType hRecvReady
  -- Need to show G' = updateG G senderEp L' and D' = updateD D edge (trace ++ [T])
  have hGUpdate : G' = updateG G senderEp L' := hSpec.type_updated L' hSenderType
  rw [hGUpdate, hSpec.trace_extended]
  exact hResult

/-- Receive preserves Coherence.

    The proof uses the buffer head evidence from the spec to satisfy
    the precondition of `Coherent_recv_preserved`. -/
theorem RecvSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {receiverEp : Endpoint} {senderRole : Role} {T : ValType}
    (hSpec : RecvSpec G G' D D' receiverEp senderRole T)
    (hCoh : Coherent G D) :
    Coherent G' D' := by
  -- Extract receiver type and buffer data from spec
  obtain ⟨L', hRecvType⟩ := hSpec.receiver_type
  obtain ⟨rest, hBuffer⟩ := hSpec.buffer_has_data
  -- Construct the trace head evidence
  let edge : Edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
  have hTraceHead : (lookupD D edge).head? = some T := by
    simp only [edge, hBuffer, List.head?_cons]
  -- Apply Protocol-level preservation
  have hResult := Coherent_recv_preserved G D receiverEp senderRole T L' hCoh hRecvType hTraceHead
  -- The spec tells us G' and D' are the result of the update
  have hGUpdate : G' = updateG G receiverEp L' := hSpec.type_updated L' hRecvType
  obtain ⟨rest', hTraceEq, hDUpdate⟩ := hSpec.trace_consumed
  -- Show rest = rest' (both come from the same buffer)
  have hRestEq : rest = rest' := by
    have h1 : T :: rest = lookupD D edge := hBuffer.symm
    have h2 : T :: rest' = lookupD D edge := hTraceEq.symm
    have h3 : T :: rest = T :: rest' := h1.trans h2.symm
    exact List.tail_eq_of_cons_eq h3
  rw [hGUpdate, hDUpdate, ← hRestEq]
  -- Align the trace tail with `rest`
  simpa [edge, hBuffer, List.tail_cons] using hResult

/-- Select preserves Coherence when SelectReady holds.

    Similar to send, but uses SelectReady for the receiver's ability
    to accept a label message. -/
theorem SelectSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {senderEp : Endpoint} {receiverRole : Role} {chosen : Label}
    (hSpec : SelectSpec G G' D D' senderEp receiverRole chosen)
    (hCoh : Coherent G D)
    (hReady : SelectReady G D) :
    Coherent G' D' := by
  -- Extract sender type from spec
  obtain ⟨branches, L', hSenderType, hFind⟩ := hSpec.sender_type
  -- SelectReady gives us the receiver readiness condition
  have hTargetReady : ∀ Ltarget, lookupG G { sid := senderEp.sid, role := receiverRole } = some Ltarget →
      ∃ L'', Consume senderEp.role Ltarget
        (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L'' ∧
        (Consume senderEp.role L'' [.string]).isSome := by
    intro Ltarget hLtarget
    exact hReady senderEp receiverRole branches chosen L' hSenderType hFind Ltarget hLtarget
  -- Apply Protocol-level preservation
  have hResult := Coherent_select_preserved G D senderEp receiverRole branches chosen L'
    hCoh hSenderType hFind hTargetReady
  -- The spec tells us G' and D' are the result of the update
  have hGUpdate : G' = updateG G senderEp L' := hSpec.type_updated branches L' hSenderType hFind
  rw [hGUpdate, hSpec.trace_extended]
  exact hResult

/-- Branch preserves Coherence.

    Similar to receive, but the buffer head is a label (.string) value. -/
theorem BranchSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {receiverEp : Endpoint} {senderRole : Role} {received : Label}
    (hSpec : BranchSpec G G' D D' receiverEp senderRole received)
    (hCoh : Coherent G D) :
    Coherent G' D' := by
  -- Extract receiver type and buffer data from spec
  obtain ⟨branches, L', hRecvType, hFind⟩ := hSpec.receiver_type
  obtain ⟨rest, hBuffer⟩ := hSpec.buffer_has_label
  -- Construct the trace head evidence
  let edge : Edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
  have hTraceHead : (lookupD D edge).head? = some .string := by
    simp only [edge, hBuffer, List.head?_cons]
  -- Apply Protocol-level preservation
  have hResult := Coherent_branch_preserved G D receiverEp senderRole branches received L'
    hCoh hRecvType hFind hTraceHead
  -- The spec tells us G' and D' are the result of the update
  have hGUpdate : G' = updateG G receiverEp L' := hSpec.type_updated branches L' hRecvType hFind
  obtain ⟨rest', hTraceEq, hDUpdate⟩ := hSpec.trace_consumed
  -- Show rest = rest'
  have hRestEq : rest = rest' := by
    have h1 : ValType.string :: rest = lookupD D edge := hBuffer.symm
    have h2 : ValType.string :: rest' = lookupD D edge := hTraceEq.symm
    have h3 : ValType.string :: rest = ValType.string :: rest' := h1.trans h2.symm
    exact List.tail_eq_of_cons_eq h3
  rw [hGUpdate, hDUpdate, ← hRestEq]
  simpa [edge, hBuffer, List.tail_cons] using hResult

/-- Open preserves Coherence (new session is Coherent by construction).

    The key insight is that:
    1. Old edges (in sessions ≠ s) are unchanged by the frame property
    2. New edges (in session s) have empty traces, so Consume L [] = some L -/
theorem OpenSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {s : SessionId} {roles : List Role}
    (hSpec : OpenSpec G G' D D' s roles)
    (hCoh : Coherent G D) :
    Coherent G' D' := by
  intro e hActive
  -- Case split: is this edge in the new session or an old session?
  by_cases hSid : e.sid = s
  · -- New session edge: trace is empty, so EdgeCoherent is trivial
    intro Lrecv hGrecv
    -- Trace is empty for new session edges
    have hTraceEmpty : lookupD D' e = [] := hSpec.traces_empty e hSid
    -- Sender exists in G' (by ActiveEdge)
    rcases (Option.isSome_iff_exists).1 hActive.1 with ⟨Lsender, hLsender⟩
    -- EdgeCoherent with empty trace: Consume L [] = some L
    refine ⟨Lsender, hLsender, ?_⟩
    simp [hTraceEmpty, Consume]
  · -- Old session edge: preserved by frame property
    -- G' agrees with G on old sessions
    have hGFrame : lookupG G' { sid := e.sid, role := e.receiver } =
        lookupG G { sid := e.sid, role := e.receiver } := hSpec.frame_G _ (by simp [hSid])
    have hGFrameSender : lookupG G' { sid := e.sid, role := e.sender } =
        lookupG G { sid := e.sid, role := e.sender } := hSpec.frame_G _ (by simp [hSid])
    have hDFrame : lookupD D' e = lookupD D e := hSpec.frame_D e hSid
    -- ActiveEdge in G' implies ActiveEdge in G
    have hActiveOld : ActiveEdge G e := by
      simp only [ActiveEdge] at hActive ⊢
      rw [hGFrame, hGFrameSender] at hActive
      exact hActive
    -- Apply original coherence
    intro Lrecv hGrecv
    rw [hGFrame] at hGrecv
    obtain ⟨Lsender, hLsender, hConsume⟩ := hCoh e hActiveOld Lrecv hGrecv
    use Lsender
    constructor
    · rw [hGFrameSender]; exact hLsender
    · rw [hDFrame]; exact hConsume

/-- Close preserves Coherence (edges become inactive).

    Removing an endpoint at `End` with empty traces makes edges involving
    that endpoint inactive (no receiver in G'), so they're skipped in Coherent. -/
theorem CloseSpec_preserves_Coherent {G G' : GEnv} {D : DEnv}
    {ep : Endpoint}
    (hSpec : CloseSpec G G' D ep)
    (hCoh : Coherent G D) :
    Coherent G' D := by
  intro e hActive
  -- If edge involves ep as receiver, then ActiveEdge fails after close
  by_cases hRecv : e.sid = ep.sid ∧ e.receiver = ep.role
  · -- Edge has ep as receiver, but ep is removed
    exfalso
    simp only [ActiveEdge] at hActive
    obtain ⟨hSid, hRole⟩ := hRecv
    have hEpRemoved : lookupG G' ep = none := hSpec.endpoint_removed
    have hRecvEp : { sid := e.sid, role := e.receiver : Endpoint } = ep := by
      cases ep with
      | mk epSid epRole =>
          cases e with
          | mk sid sender receiver =>
              cases hSid
              cases hRole
              rfl
    rw [hRecvEp] at hActive
    simp [hEpRemoved] at hActive
  · -- Edge doesn't have ep as receiver, preserved by frame
    push_neg at hRecv
    have hFrame : lookupG G' { sid := e.sid, role := e.receiver } =
        lookupG G { sid := e.sid, role := e.receiver } := by
      apply hSpec.frame_G
      intro hEq
      have hSid : e.sid = ep.sid := by
        simpa using congrArg Endpoint.sid hEq
      have hRole : e.receiver = ep.role := by
        simpa using congrArg Endpoint.role hEq
      exact (hRecv hSid) (by simpa using hRole)
    have hFrameSender : lookupG G' { sid := e.sid, role := e.sender } =
        lookupG G { sid := e.sid, role := e.sender } := by
      apply hSpec.frame_G
      intro hEq
      -- If sender = ep, then G'[ep] = none (endpoint removed)
      -- But ActiveEdge requires lookupG G' sender to be some _, contradiction
      exfalso
      simp only [ActiveEdge] at hActive
      have hEpRemoved : lookupG G' ep = none := hSpec.endpoint_removed
      have hSenderEp : { sid := e.sid, role := e.sender : Endpoint } = ep := hEq
      rw [hSenderEp] at hActive
      simp [hEpRemoved] at hActive
    -- ActiveEdge in G' implies ActiveEdge in G
    have hActiveOld : ActiveEdge G e := by
      simp only [ActiveEdge] at hActive ⊢
      rw [hFrame, hFrameSender] at hActive
      exact hActive
    -- Apply original coherence
    intro Lrecv hGrecv
    rw [hFrame] at hGrecv
    obtain ⟨Lsender, hLsender, hConsume⟩ := hCoh e hActiveOld Lrecv hGrecv
    use Lsender
    constructor
    · rw [hFrameSender]; exact hLsender
    · exact hConsume

/-- Acquire preserves Coherence (uses delegation_preserves_coherent).

    The spec includes a DelegationStep, which directly provides coherence
    preservation via the proved `delegation_preserves_coherent` theorem. -/
theorem AcquireSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {receiverEp : Endpoint} {senderRole : Role}
    {delegatedSession : SessionId} {delegatedRole : Role}
    (hSpec : AcquireSpec G G' D D' receiverEp senderRole delegatedSession delegatedRole)
    (hCoh : Coherent G D) :
    Coherent G' D' := by
  -- The spec includes a DelegationStep, which preserves coherence
  exact delegation_preserves_coherent G G' D D' delegatedSession senderRole receiverEp.role
    hCoh hSpec.delegation_applied

/-! ## Quotient-Respecting Theorems (ConfigEquiv)

Each instruction spec is equivariant under session renaming. This ensures that
instructions are true morphisms on the quotient space S/G (configurations
modulo session ID renaming).

The pattern: if Spec holds for (G, D, ep, params...), then the renamed spec
holds for (renameGEnv ρ G, renameDEnv ρ D, renameEndpoint ρ ep, renameParams ρ params...).

From this equivariance, ConfigEquiv preservation follows:
if C₁ ≈ C₂ and we apply the same instruction to both, then C₁' ≈ C₂'.

**Note:** These theorems require "update commutes with renaming" lemmas
(renameGEnv_updateG, renameDEnv_updateD) which are infrastructure gaps. -/

/-- Send is equivariant under session renaming.

    If a send spec holds, then the same spec holds on renamed environments
    with renamed operands. -/
theorem SendSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv} {ep : Endpoint} {r : Role} {T : ValType}
    (hSpec : SendSpec G G' D D' ep r T) :
    SendSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
             (renameEndpoint ρ ep) r (renameValType ρ T) where
  sender_type := by
    obtain ⟨L', hSender⟩ := hSpec.sender_type
    use renameLocalType ρ L'
    rw [lookupG_rename, hSender]
    simp only [Option.map_some, renameLocalType]
  type_updated := by
    intro L'_renamed hSender_renamed
    rw [lookupG_rename] at hSender_renamed
    obtain ⟨L', hSender⟩ := hSpec.sender_type
    rw [hSender] at hSender_renamed
    simp only [Option.map_some, renameLocalType] at hSender_renamed
    have hL'_eq : L'_renamed = renameLocalType ρ L' := by
      cases hSender_renamed
      rfl
    have hG' := hSpec.type_updated L' hSender
    rw [hG', renameGEnv_updateG, hL'_eq]
  trace_extended := by
    have hD' := hSpec.trace_extended
    simp only at hD'
    simp only [renameEndpoint]
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    congr 1
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := ep.role, receiver := r })
    simp only [renameEdge] at hLookup
    rw [List.map_append, List.map, hLookup]
    simp
  frame_G := by
    intro ep' hne
    obtain ⟨L', hSender⟩ := hSpec.sender_type
    have hG' := hSpec.type_updated L' hSender
    rw [hG', renameGEnv_updateG]
    exact lookupG_update_neq (renameGEnv ρ G) (renameEndpoint ρ ep) ep'
      (renameLocalType ρ L') hne.symm
  frame_D := by
    intro e hne
    have hD' := hSpec.trace_extended
    simp only at hD'
    simp only [renameEndpoint] at hne ⊢
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    exact lookupD_update_neq (renameDEnv ρ D)
      { sid := ρ.f ep.sid, sender := ep.role, receiver := r } e
      ((lookupD D { sid := ep.sid, sender := ep.role, receiver := r } ++ [T]).map (renameValType ρ))
      hne.symm

/-- Send respects ConfigEquiv: equivalent configs produce equivalent results. -/
theorem SendSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {T : ValType}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : SendSpec G₁ G₁' D₁ D₁' ep r T)
    (hSpec₂ : SendSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r
              (renameValType hEquiv.choose.toRenaming T)) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by
  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  -- Witness: the same σ works for the output.
  refine ⟨σ, ?_, ?_⟩
  -- G condition: lookupG G₂' (rename e') = (lookupG G₁' e').map rename
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the updated endpoint)
      obtain ⟨L', hSender₁⟩ := hSpec₁.sender_type
      have hG₁' := hSpec₁.type_updated L' hSender₁
      obtain ⟨L'₂, hSender₂⟩ := hSpec₂.sender_type
      have hG₂' := hSpec₂.type_updated L'₂ hSender₂
      -- Get the renamed sender type in G₂ to determine L'₂
      have hSender₂_raw := hG_equiv ep
      rw [hSender₁] at hSender₂_raw
      simp only [Option.map_some, renameLocalType] at hSender₂_raw
      rw [hSender₂_raw] at hSender₂
      simp only [Option.some.injEq, LocalType.send.injEq] at hSender₂
      obtain ⟨_, _, hL'₂_eq⟩ := hSender₂
      -- Compute both sides using he : e' = ep
      calc lookupG G₂' (renameEndpoint ρ e')
          = lookupG G₂' (renameEndpoint ρ ep) := by rw [he]
        _ = lookupG (updateG G₂ (renameEndpoint ρ ep) L'₂) (renameEndpoint ρ ep) := by rw [hG₂']
        _ = some L'₂ := lookupG_update_eq _ _ _
        _ = some (renameLocalType ρ L') := by rw [hL'₂_eq]
        _ = (some L').map (renameLocalType ρ) := by simp only [Option.map_some]
        _ = (lookupG (updateG G₁ ep L') ep).map (renameLocalType ρ) := by
            rw [lookupG_update_eq]
        _ = (lookupG G₁' ep).map (renameLocalType ρ) := by rw [← hG₁']
        _ = (lookupG G₁' e').map (renameLocalType ρ) := by rw [← he]
    · -- Case: e' ≠ ep (frame)
      have hne₂ : renameEndpoint ρ e' ≠ renameEndpoint ρ ep := by
        intro heq
        exact he (renameEndpoint_inj ρ e' ep heq)
      rw [hSpec₁.frame_G e' he, hSpec₂.frame_G (renameEndpoint ρ e') hne₂]
      exact hG_equiv e'
  -- D condition: lookupD D₂' (rename e') = (lookupD D₁' e').map rename
  · intro e'
    let sendEdge : Edge := { sid := ep.sid, sender := ep.role, receiver := r }
    by_cases he : e' = sendEdge
    · -- Case: e' = sendEdge (the updated edge)
      have hD₁' := hSpec₁.trace_extended
      have hD₂' := hSpec₂.trace_extended
      simp only at hD₁' hD₂'
      simp only [renameEndpoint] at hD₂'
      have hTrace := hD_equiv sendEdge
      simp only [renameEdge] at hTrace
      -- Rewrite goal with he, then use the update equations
      rw [he]
      simp only [renameEdge]
      rw [hD₁', hD₂', lookupD_update_eq, lookupD_update_eq]
      -- Now show: (trace ++ [T]).map rename = (trace.map rename) ++ [rename T]
      simp only [List.map_append, List.map_cons, List.map_nil]
      -- Apply hTrace to match the trace lookups
      rw [hTrace]
    · -- Case: e' ≠ sendEdge (frame)
      have hne₂ : renameEdge ρ e' ≠ renameEdge ρ sendEdge := by
        intro heq
        exact he (renameEdge_inj ρ e' sendEdge heq)
      simp only [renameEdge] at hne₂
      rw [hSpec₁.frame_D e' he, hSpec₂.frame_D (renameEdge ρ e') hne₂]
      exact hD_equiv e'

/-- Receive is equivariant under session renaming. -/
theorem RecvSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv} {ep : Endpoint} {r : Role} {T : ValType}
    (hSpec : RecvSpec G G' D D' ep r T) :
    RecvSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
             (renameEndpoint ρ ep) r (renameValType ρ T) where
  receiver_type := by
    obtain ⟨L', hRecv⟩ := hSpec.receiver_type
    use renameLocalType ρ L'
    rw [lookupG_rename, hRecv]
    simp only [Option.map_some, renameLocalType]
  buffer_has_data := by
    obtain ⟨rest, hBuffer⟩ := hSpec.buffer_has_data
    use rest.map (renameValType ρ)
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := r, receiver := ep.role })
    simp only [renameEdge] at hLookup
    rw [hLookup, hBuffer]
    simp only [List.map_cons]
  type_updated := by
    intro L'_renamed hRecv_renamed
    rw [lookupG_rename] at hRecv_renamed
    obtain ⟨L', hRecv⟩ := hSpec.receiver_type
    rw [hRecv] at hRecv_renamed
    simp only [Option.map_some, renameLocalType] at hRecv_renamed
    have hL'_eq : L'_renamed = renameLocalType ρ L' := by
      cases hRecv_renamed
      rfl
    have hG' := hSpec.type_updated L' hRecv
    rw [hG', renameGEnv_updateG, hL'_eq]
  trace_consumed := by
    obtain ⟨rest, hBuffer, hD'⟩ := hSpec.trace_consumed
    use rest.map (renameValType ρ)
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := r, receiver := ep.role })
    simp only [renameEdge] at hLookup
    constructor
    · rw [hLookup, hBuffer]
      simp only [List.map_cons]
    · rw [hD', renameDEnv_updateD]
      simp only [renameEdge]
  frame_G := by
    intro ep' hne
    obtain ⟨L', hRecv⟩ := hSpec.receiver_type
    have hG' := hSpec.type_updated L' hRecv
    rw [hG', renameGEnv_updateG]
    exact lookupG_update_neq (renameGEnv ρ G) (renameEndpoint ρ ep) ep'
      (renameLocalType ρ L') hne.symm
  frame_D := by
    intro e hne
    obtain ⟨rest, _, hD'⟩ := hSpec.trace_consumed
    simp only [renameEndpoint] at hne ⊢
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    exact lookupD_update_neq (renameDEnv ρ D)
      { sid := ρ.f ep.sid, sender := r, receiver := ep.role } e
      (rest.map (renameValType ρ)) hne.symm

/-- Receive respects ConfigEquiv. -/
theorem RecvSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {T : ValType}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : RecvSpec G₁ G₁' D₁ D₁' ep r T)
    (hSpec₂ : RecvSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r
              (renameValType hEquiv.choose.toRenaming T)) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by
  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩
  -- G condition
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the updated endpoint)
      obtain ⟨L', hRecv₁⟩ := hSpec₁.receiver_type
      have hG₁' := hSpec₁.type_updated L' hRecv₁
      obtain ⟨L'₂, hRecv₂⟩ := hSpec₂.receiver_type
      have hG₂' := hSpec₂.type_updated L'₂ hRecv₂
      -- Determine L'₂ from input equivalence
      have hRecv₂_raw := hG_equiv ep
      rw [hRecv₁] at hRecv₂_raw
      simp only [Option.map_some, renameLocalType] at hRecv₂_raw
      rw [hRecv₂_raw] at hRecv₂
      simp only [Option.some.injEq, LocalType.recv.injEq] at hRecv₂
      obtain ⟨_, _, hL'₂_eq⟩ := hRecv₂
      -- Compute both sides
      calc lookupG G₂' (renameEndpoint ρ e')
          = lookupG G₂' (renameEndpoint ρ ep) := by rw [he]
        _ = lookupG (updateG G₂ (renameEndpoint ρ ep) L'₂) (renameEndpoint ρ ep) := by rw [hG₂']
        _ = some L'₂ := lookupG_update_eq _ _ _
        _ = some (renameLocalType ρ L') := by rw [hL'₂_eq]
        _ = (some L').map (renameLocalType ρ) := by simp only [Option.map_some]
        _ = (lookupG (updateG G₁ ep L') ep).map (renameLocalType ρ) := by rw [lookupG_update_eq]
        _ = (lookupG G₁' ep).map (renameLocalType ρ) := by rw [← hG₁']
        _ = (lookupG G₁' e').map (renameLocalType ρ) := by rw [← he]
    · -- Case: e' ≠ ep (frame)
      have hne₂ : renameEndpoint ρ e' ≠ renameEndpoint ρ ep := by
        intro heq; exact he (renameEndpoint_inj ρ e' ep heq)
      rw [hSpec₁.frame_G e' he, hSpec₂.frame_G (renameEndpoint ρ e') hne₂]
      exact hG_equiv e'
  -- D condition
  · intro e'
    let recvEdge : Edge := { sid := ep.sid, sender := r, receiver := ep.role }
    by_cases he : e' = recvEdge
    · -- Case: e' = recvEdge (the updated edge)
      obtain ⟨rest₁, hBuf₁, hD₁'⟩ := hSpec₁.trace_consumed
      obtain ⟨rest₂, hBuf₂, hD₂'⟩ := hSpec₂.trace_consumed
      simp only [renameEndpoint] at hD₂' hBuf₂
      have hTrace := hD_equiv recvEdge
      simp only [renameEdge] at hTrace
      -- Rewrite goal
      rw [he]
      simp only [renameEdge]
      rw [hD₁', hD₂', lookupD_update_eq, lookupD_update_eq]
      -- rest₁ and rest₂ are the tails after consuming T
      -- From hBuf₁: lookupD D₁ recvEdge = T :: rest₁
      -- From hTrace: lookupD D₂ (rename recvEdge) = (lookupD D₁ recvEdge).map rename
      --            = (T :: rest₁).map rename = renameT :: rest₁.map rename
      -- From hBuf₂: lookupD D₂ (rename recvEdge) = renameT :: rest₂
      -- So rest₂ = rest₁.map rename
      rw [hBuf₁, List.map_cons] at hTrace
      rw [hBuf₂] at hTrace
      simp only [List.cons.injEq] at hTrace
      rw [hTrace.2]
    · -- Case: e' ≠ recvEdge (frame)
      have hne₂ : renameEdge ρ e' ≠ renameEdge ρ recvEdge := by
        intro heq; exact he (renameEdge_inj ρ e' recvEdge heq)
      simp only [renameEdge] at hne₂
      rw [hSpec₁.frame_D e' he, hSpec₂.frame_D (renameEdge ρ e') hne₂]
      exact hD_equiv e'

/-- Select is equivariant under session renaming. -/
theorem SelectSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv} {ep : Endpoint} {r : Role} {chosen : Label}
    (hSpec : SelectSpec G G' D D' ep r chosen) :
    SelectSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
               (renameEndpoint ρ ep) r chosen where
  sender_type := by
    obtain ⟨branches, L', hSender, hFind⟩ := hSpec.sender_type
    use renameBranches ρ branches, renameLocalType ρ L'
    constructor
    · rw [lookupG_rename, hSender]
      simp only [Option.map_some, renameLocalType]
    · rw [find_renameBranches, hFind]
      simp
  type_updated := by
    intro branches_renamed L'_renamed hSender_renamed hFind_renamed
    rw [lookupG_rename] at hSender_renamed
    obtain ⟨branches, L', hSender, hFind⟩ := hSpec.sender_type
    rw [hSender] at hSender_renamed
    simp only [Option.map_some, renameLocalType] at hSender_renamed
    have hBranches_eq : branches_renamed = renameBranches ρ branches := by
      cases hSender_renamed
      rfl
    have hL'_eq : L'_renamed = renameLocalType ρ L' := by
      rw [hBranches_eq, find_renameBranches, hFind] at hFind_renamed
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hFind_renamed
      exact hFind_renamed.2.symm
    have hG' := hSpec.type_updated branches L' hSender hFind
    rw [hG', renameGEnv_updateG, hL'_eq]
  trace_extended := by
    have hD' := hSpec.trace_extended
    simp only at hD'
    simp only [renameEndpoint]
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    congr 1
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := ep.role, receiver := r })
    simp only [renameEdge] at hLookup
    rw [List.map_append, List.map, hLookup, renameValType]
    simp
  frame_G := by
    intro ep' hne
    obtain ⟨branches, L', hSender, hFind⟩ := hSpec.sender_type
    have hG' := hSpec.type_updated branches L' hSender hFind
    rw [hG', renameGEnv_updateG]
    exact lookupG_update_neq (renameGEnv ρ G) (renameEndpoint ρ ep) ep'
      (renameLocalType ρ L') hne.symm
  frame_D := by
    intro e hne
    have hD' := hSpec.trace_extended
    simp only at hD'
    simp only [renameEndpoint] at hne ⊢
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    exact lookupD_update_neq (renameDEnv ρ D)
      { sid := ρ.f ep.sid, sender := ep.role, receiver := r } e
      ((lookupD D { sid := ep.sid, sender := ep.role, receiver := r } ++ [ValType.string]).map (renameValType ρ))
      hne.symm

/-- Select respects ConfigEquiv. -/
theorem SelectSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {chosen : Label}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : SelectSpec G₁ G₁' D₁ D₁' ep r chosen)
    (hSpec₂ : SelectSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r chosen) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by
  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩
  -- G condition
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the updated endpoint)
      obtain ⟨branches₁, L'₁, hSender₁, hFind₁⟩ := hSpec₁.sender_type
      have hG₁' := hSpec₁.type_updated branches₁ L'₁ hSender₁ hFind₁
      obtain ⟨branches₂, L'₂, hSender₂, hFind₂⟩ := hSpec₂.sender_type
      have hG₂' := hSpec₂.type_updated branches₂ L'₂ hSender₂ hFind₂
      -- Determine L'₂ from input equivalence
      have hSender₂_raw := hG_equiv ep
      rw [hSender₁] at hSender₂_raw
      simp only [Option.map_some, renameLocalType] at hSender₂_raw
      rw [hSender₂_raw] at hSender₂
      simp only [Option.some.injEq, LocalType.select.injEq] at hSender₂
      obtain ⟨_, hBranches₂_eq⟩ := hSender₂
      -- Get L'₂ = renameLocalType ρ L'₁ from find correspondence
      have hL'₂_eq : L'₂ = renameLocalType ρ L'₁ := by
        subst hBranches₂_eq
        rw [find_renameBranches, hFind₁] at hFind₂
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hFind₂
        exact hFind₂.2.symm
      -- Compute both sides
      calc lookupG G₂' (renameEndpoint ρ e')
          = lookupG G₂' (renameEndpoint ρ ep) := by rw [he]
        _ = lookupG (updateG G₂ (renameEndpoint ρ ep) L'₂) (renameEndpoint ρ ep) := by rw [hG₂']
        _ = some L'₂ := lookupG_update_eq _ _ _
        _ = some (renameLocalType ρ L'₁) := by rw [hL'₂_eq]
        _ = (some L'₁).map (renameLocalType ρ) := by simp only [Option.map_some]
        _ = (lookupG (updateG G₁ ep L'₁) ep).map (renameLocalType ρ) := by rw [lookupG_update_eq]
        _ = (lookupG G₁' ep).map (renameLocalType ρ) := by rw [← hG₁']
        _ = (lookupG G₁' e').map (renameLocalType ρ) := by rw [← he]
    · -- Case: e' ≠ ep (frame)
      have hne₂ : renameEndpoint ρ e' ≠ renameEndpoint ρ ep := by
        intro heq; exact he (renameEndpoint_inj ρ e' ep heq)
      rw [hSpec₁.frame_G e' he, hSpec₂.frame_G (renameEndpoint ρ e') hne₂]
      exact hG_equiv e'
  -- D condition
  · intro e'
    let sendEdge : Edge := { sid := ep.sid, sender := ep.role, receiver := r }
    by_cases he : e' = sendEdge
    · -- Case: e' = sendEdge (the updated edge)
      have hD₁' := hSpec₁.trace_extended
      have hD₂' := hSpec₂.trace_extended
      simp only [renameEndpoint] at hD₂'
      have hTrace := hD_equiv sendEdge
      simp only [renameEdge] at hTrace
      -- Rewrite goal: lookupD D₂' (renameEdge ρ e') = (lookupD D₁' e').map (renameValType ρ)
      rw [he]
      simp only [renameEdge]
      rw [hD₁', hD₂', lookupD_update_eq, lookupD_update_eq]
      -- Goal: lookupD D₂ (...) ++ [string] = (lookupD D₁ sendEdge ++ [string]).map (renameValType ρ)
      rw [List.map_append, List.map_singleton, renameValType, hTrace]
    · -- Case: e' ≠ sendEdge (frame)
      have hne₂ : renameEdge ρ e' ≠ renameEdge ρ sendEdge := by
        intro heq; exact he (renameEdge_inj ρ e' sendEdge heq)
      simp only [renameEdge] at hne₂
      rw [hSpec₁.frame_D e' he, hSpec₂.frame_D (renameEdge ρ e') hne₂]
      exact hD_equiv e'

/-- Branch is equivariant under session renaming. -/
theorem BranchSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv} {ep : Endpoint} {r : Role} {received : Label}
    (hSpec : BranchSpec G G' D D' ep r received) :
    BranchSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
               (renameEndpoint ρ ep) r received where
  receiver_type := by
    obtain ⟨branches, L', hRecv, hFind⟩ := hSpec.receiver_type
    use renameBranches ρ branches, renameLocalType ρ L'
    constructor
    · rw [lookupG_rename, hRecv]
      simp only [Option.map_some, renameLocalType]
    · rw [find_renameBranches, hFind]
      simp
  buffer_has_label := by
    obtain ⟨rest, hBuffer⟩ := hSpec.buffer_has_label
    use rest.map (renameValType ρ)
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := r, receiver := ep.role })
    simp only [renameEdge] at hLookup
    rw [hLookup, hBuffer]
    simp only [List.map_cons, renameValType]
  type_updated := by
    intro branches_renamed L'_renamed hRecv_renamed hFind_renamed
    rw [lookupG_rename] at hRecv_renamed
    obtain ⟨branches, L', hRecv, hFind⟩ := hSpec.receiver_type
    rw [hRecv] at hRecv_renamed
    simp only [Option.map_some, renameLocalType] at hRecv_renamed
    have hBranches_eq : branches_renamed = renameBranches ρ branches := by
      cases hRecv_renamed
      rfl
    have hL'_eq : L'_renamed = renameLocalType ρ L' := by
      rw [hBranches_eq, find_renameBranches, hFind] at hFind_renamed
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hFind_renamed
      exact hFind_renamed.2.symm
    have hG' := hSpec.type_updated branches L' hRecv hFind
    rw [hG', renameGEnv_updateG, hL'_eq]
  trace_consumed := by
    obtain ⟨rest, hBuffer, hD'⟩ := hSpec.trace_consumed
    use rest.map (renameValType ρ)
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := r, receiver := ep.role })
    simp only [renameEdge] at hLookup
    constructor
    · rw [hLookup, hBuffer]
      simp only [List.map_cons, renameValType]
    · rw [hD', renameDEnv_updateD]
      simp only [renameEdge]
  frame_G := by
    intro ep' hne
    obtain ⟨branches, L', hRecv, hFind⟩ := hSpec.receiver_type
    have hG' := hSpec.type_updated branches L' hRecv hFind
    rw [hG', renameGEnv_updateG]
    exact lookupG_update_neq (renameGEnv ρ G) (renameEndpoint ρ ep) ep'
      (renameLocalType ρ L') hne.symm
  frame_D := by
    intro e hne
    obtain ⟨rest, _, hD'⟩ := hSpec.trace_consumed
    simp only [renameEndpoint] at hne ⊢
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    exact lookupD_update_neq (renameDEnv ρ D)
      { sid := ρ.f ep.sid, sender := r, receiver := ep.role } e
      (rest.map (renameValType ρ)) hne.symm

/-- Branch respects ConfigEquiv. -/
theorem BranchSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {received : Label}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : BranchSpec G₁ G₁' D₁ D₁' ep r received)
    (hSpec₂ : BranchSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r received) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by
  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩
  -- G condition
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the updated endpoint)
      obtain ⟨branches₁, L'₁, hRecv₁, hFind₁⟩ := hSpec₁.receiver_type
      have hG₁' := hSpec₁.type_updated branches₁ L'₁ hRecv₁ hFind₁
      obtain ⟨branches₂, L'₂, hRecv₂, hFind₂⟩ := hSpec₂.receiver_type
      have hG₂' := hSpec₂.type_updated branches₂ L'₂ hRecv₂ hFind₂
      -- Determine L'₂ from input equivalence
      have hRecv₂_raw := hG_equiv ep
      rw [hRecv₁] at hRecv₂_raw
      simp only [Option.map_some, renameLocalType] at hRecv₂_raw
      rw [hRecv₂_raw] at hRecv₂
      simp only [Option.some.injEq, LocalType.branch.injEq] at hRecv₂
      obtain ⟨_, hBranches₂_eq⟩ := hRecv₂
      -- Get L'₂ = renameLocalType ρ L'₁ from find correspondence
      have hL'₂_eq : L'₂ = renameLocalType ρ L'₁ := by
        subst hBranches₂_eq
        rw [find_renameBranches, hFind₁] at hFind₂
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hFind₂
        exact hFind₂.2.symm
      -- Compute both sides
      calc lookupG G₂' (renameEndpoint ρ e')
          = lookupG G₂' (renameEndpoint ρ ep) := by rw [he]
        _ = lookupG (updateG G₂ (renameEndpoint ρ ep) L'₂) (renameEndpoint ρ ep) := by rw [hG₂']
        _ = some L'₂ := lookupG_update_eq _ _ _
        _ = some (renameLocalType ρ L'₁) := by rw [hL'₂_eq]
        _ = (some L'₁).map (renameLocalType ρ) := by simp only [Option.map_some]
        _ = (lookupG (updateG G₁ ep L'₁) ep).map (renameLocalType ρ) := by rw [lookupG_update_eq]
        _ = (lookupG G₁' ep).map (renameLocalType ρ) := by rw [← hG₁']
        _ = (lookupG G₁' e').map (renameLocalType ρ) := by rw [← he]
    · -- Case: e' ≠ ep (frame)
      have hne₂ : renameEndpoint ρ e' ≠ renameEndpoint ρ ep := by
        intro heq; exact he (renameEndpoint_inj ρ e' ep heq)
      rw [hSpec₁.frame_G e' he, hSpec₂.frame_G (renameEndpoint ρ e') hne₂]
      exact hG_equiv e'
  -- D condition
  · intro e'
    let recvEdge : Edge := { sid := ep.sid, sender := r, receiver := ep.role }
    by_cases he : e' = recvEdge
    · -- Case: e' = recvEdge (the updated edge)
      obtain ⟨rest₁, hBuf₁, hD₁'⟩ := hSpec₁.trace_consumed
      obtain ⟨rest₂, hBuf₂, hD₂'⟩ := hSpec₂.trace_consumed
      simp only [renameEndpoint] at hD₂' hBuf₂
      have hTrace := hD_equiv recvEdge
      simp only [renameEdge] at hTrace
      -- Rewrite goal
      rw [he]
      simp only [renameEdge]
      rw [hD₁', hD₂', lookupD_update_eq, lookupD_update_eq]
      -- rest₁ and rest₂ are the tails after consuming the label
      -- From hBuf₁: lookupD D₁ recvEdge = label :: rest₁
      -- From hTrace: lookupD D₂ (rename recvEdge) = (lookupD D₁ recvEdge).map rename
      --            = (label :: rest₁).map rename = label' :: rest₁.map rename
      -- From hBuf₂: lookupD D₂ (rename recvEdge) = label' :: rest₂
      -- So rest₂ = rest₁.map rename
      rw [hBuf₁, List.map_cons] at hTrace
      rw [hBuf₂] at hTrace
      simp only [List.cons.injEq] at hTrace
      rw [hTrace.2]
    · -- Case: e' ≠ recvEdge (frame)
      have hne₂ : renameEdge ρ e' ≠ renameEdge ρ recvEdge := by
        intro heq; exact he (renameEdge_inj ρ e' recvEdge heq)
      simp only [renameEdge] at hne₂
      rw [hSpec₁.frame_D e' he, hSpec₂.frame_D (renameEdge ρ e') hne₂]
      exact hD_equiv e'

/-- Open is equivariant under session renaming. -/
theorem OpenSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {roles : List Role}
    (hSpec : OpenSpec G G' D D' s roles) :
    OpenSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
             (ρ.f s) roles where
  fresh := by
    intro ep hSome hEq
    -- If ep.sid = ρ.f s, need to derive contradiction from freshness
    -- lookupG (renameGEnv ρ G) ep = some _ means there's a preimage
    rw [Option.isSome_iff_exists] at hSome
    obtain ⟨L, hL⟩ := hSome
    obtain ⟨ep', L', hEp, hL'_eq, hLookup⟩ := lookupG_rename_inv ρ G ep L hL
    have hPreimage : ep'.sid = s := by
      have hSidEq : ep.sid = ρ.f ep'.sid := by
        rw [hEp]
        simp only [renameEndpoint]
      rw [hEq] at hSidEq
      exact ρ.inj _ _ hSidEq.symm
    have hSome' : (lookupG G ep').isSome := by
      rw [Option.isSome_iff_exists]
      exact ⟨L', hLookup⟩
    exact hSpec.fresh ep' hSome' hPreimage
  endpoints_added := by
    intro r hr
    have hAdded := hSpec.endpoints_added r hr
    rw [Option.isSome_iff_exists] at hAdded ⊢
    obtain ⟨L, hL⟩ := hAdded
    use renameLocalType ρ L
    have hEp : { sid := ρ.f s, role := r : Endpoint } = renameEndpoint ρ { sid := s, role := r } := by
      simp only [renameEndpoint]
    rw [hEp, lookupG_rename, hL]
    simp only [Option.map_some]
  frame_G := by
    intro ep hSidNe
    have hSidNe' : ep.sid ≠ ρ.f s := hSidNe
    -- If ep.sid ≠ ρ.f s, check if ep is in the renamed image
    by_cases hPre : ∃ ep', renameEndpoint ρ ep' = ep
    case pos =>
      obtain ⟨ep', hEp⟩ := hPre
      have hSidNe'' : ep'.sid ≠ s := by
        intro hEq
        have hSid : ep.sid = ρ.f ep'.sid := by
          rw [← hEp]
          simp only [renameEndpoint]
        rw [hEq] at hSid
        exact hSidNe' hSid
      have hFrame := hSpec.frame_G ep' hSidNe''
      rw [← hEp, lookupG_rename, lookupG_rename, hFrame]
    case neg =>
      -- ep not in renamed image, so lookupG is none on both sides
      have hNone : lookupG (renameGEnv ρ G) ep = none := by
        by_contra hSome
        rw [← ne_eq, Option.ne_none_iff_exists'] at hSome
        obtain ⟨L, hL⟩ := hSome
        obtain ⟨ep', _, hEp, _, _⟩ := lookupG_rename_inv ρ G ep L hL
        exact hPre ⟨ep', hEp.symm⟩
      have hNone' : lookupG (renameGEnv ρ G') ep = none := by
        by_contra hSome
        rw [← ne_eq, Option.ne_none_iff_exists'] at hSome
        obtain ⟨L, hL⟩ := hSome
        obtain ⟨ep', _, hEp, _, _⟩ := lookupG_rename_inv ρ G' ep L hL
        exact hPre ⟨ep', hEp.symm⟩
      rw [hNone, hNone']
  traces_empty := by
    intro e hSidEq
    -- e.sid = ρ.f s, need to find preimage edge
    -- The trace should be empty because original trace was empty
    by_cases hPre : ∃ e', renameEdge ρ e' = e
    case pos =>
      obtain ⟨e', hE⟩ := hPre
      have hSidEq' : e'.sid = s := by
        have hSid : e.sid = ρ.f e'.sid := by
          rw [← hE]
          simp only [renameEdge]
        rw [hSidEq] at hSid
        exact ρ.inj _ _ hSid.symm
      have hEmpty := hSpec.traces_empty e' hSidEq'
      rw [← hE, lookupD_rename, hEmpty]
      simp only [List.map_nil]
    case neg =>
      -- Not in preimage, so lookup returns empty by default
      by_contra hNe
      obtain ⟨e', hE, _⟩ := lookupD_rename_inv ρ D' e hNe
      exact hPre ⟨e', hE.symm⟩
  frame_D := by
    intro e hSidNe
    by_cases hPre : ∃ e', renameEdge ρ e' = e
    case pos =>
      obtain ⟨e', hE⟩ := hPre
      have hSidNe' : e'.sid ≠ s := by
        intro hEq
        have hSid : e.sid = ρ.f e'.sid := by
          rw [← hE]
          simp only [renameEdge]
        rw [hEq] at hSid
        exact hSidNe hSid
      have hFrame := hSpec.frame_D e' hSidNe'
      rw [← hE, lookupD_rename, lookupD_rename, hFrame]
    case neg =>
      -- Not in preimage, lookup returns empty on both
      have hEmpty : lookupD (renameDEnv ρ D) e = [] := by
        by_contra hNe
        obtain ⟨e', hE, _⟩ := lookupD_rename_inv ρ D e hNe
        exact hPre ⟨e', hE.symm⟩
      have hEmpty' : lookupD (renameDEnv ρ D') e = [] := by
        by_contra hNe
        obtain ⟨e', hE, _⟩ := lookupD_rename_inv ρ D' e hNe
        exact hPre ⟨e', hE.symm⟩
      rw [hEmpty, hEmpty']

/-- Open respects ConfigEquiv.

    Note: This proof requires additional specification constraints on OpenSpec.
    Specifically, OpenSpec needs to constrain:
    1. What types are assigned to new endpoints (must be projections of global type)
    2. What happens to non-role endpoints in the new session (should remain None)

    These constraints would ensure that two Opens with related session IDs
    produce ConfigEquiv outputs. For now, the core structure is in place
    with sorries for the parts needing specification enhancement. -/
theorem OpenSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {s : SessionId} {roles : List Role}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : OpenSpec G₁ G₁' D₁ D₁' s roles)
    (hSpec₂ : OpenSpec G₂ G₂' D₂ D₂' (hEquiv.choose.fwd s) roles)
    (hNewRoles :
      ∀ r, r ∈ roles →
        ∃ L, lookupG G₁' { sid := s, role := r } = some L ∧
          lookupG G₂' { sid := hEquiv.choose.fwd s, role := r } =
            some (renameLocalType (hEquiv.choose.toRenaming) L))
    (hNoExtra₁ : ∀ r, r ∉ roles → lookupG G₁' { sid := s, role := r } = none)
    (hNoExtra₂ : ∀ r, r ∉ roles →
      lookupG G₂' { sid := hEquiv.choose.fwd s, role := r } = none) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG, hD⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩
  · intro e
    cases e with
    | mk sid role =>
      by_cases hSid : sid = s
      · subst hSid
        by_cases hIn : role ∈ roles
        · rcases hNewRoles role hIn with ⟨L, hL₁, hL₂⟩
          simpa [σ, ρ, renameEndpoint, hL₁, hL₂]
        · have hNone₁ : lookupG G₁' { sid := sid, role := role } = none := hNoExtra₁ role hIn
          have hNone₂ : lookupG G₂' { sid := σ.fwd sid, role := role } = none := hNoExtra₂ role hIn
          simpa [σ, ρ, renameEndpoint, hNone₁, hNone₂]
      · have hSidNe₂ : (renameEndpoint ρ { sid := sid, role := role }).sid ≠ σ.fwd s := by
          change ρ.f sid ≠ ρ.f s
          intro hEq
          exact hSid (ρ.inj _ _ hEq)
        have hFrame₁ : lookupG G₁' { sid := sid, role := role } = lookupG G₁ { sid := sid, role := role } :=
          hSpec₁.frame_G { sid := sid, role := role } hSid
        have hFrame₂ :
            lookupG G₂' (renameEndpoint ρ { sid := sid, role := role }) =
              lookupG G₂ (renameEndpoint ρ { sid := sid, role := role }) :=
          hSpec₂.frame_G (renameEndpoint ρ { sid := sid, role := role }) hSidNe₂
        calc
          lookupG G₂' (renameEndpoint ρ { sid := sid, role := role })
              = lookupG G₂ (renameEndpoint ρ { sid := sid, role := role }) := hFrame₂
          _ = (lookupG G₁ { sid := sid, role := role }).map (renameLocalType ρ) :=
                hG { sid := sid, role := role }
          _ = (lookupG G₁' { sid := sid, role := role }).map (renameLocalType ρ) := by
                rw [hFrame₁]
  · intro e
    cases e with
    | mk sid sender receiver =>
      by_cases hSid : sid = s
      · subst hSid
        have hEmpty₁ : lookupD D₁' { sid := sid, sender := sender, receiver := receiver } = [] :=
          hSpec₁.traces_empty { sid := sid, sender := sender, receiver := receiver } rfl
        have hEmpty₂ :
            lookupD D₂' (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) = [] := by
          have hSidRen :
              (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }).sid = σ.fwd sid := by
            change ρ.f sid = σ.fwd sid
            rfl
          exact hSpec₂.traces_empty (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) hSidRen
        rw [hEmpty₁, hEmpty₂]
        simp
      · have hSidNe₂ : (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }).sid ≠ σ.fwd s := by
          change ρ.f sid ≠ ρ.f s
          intro hEq
          exact hSid (ρ.inj _ _ hEq)
        have hFrame₁ :
            lookupD D₁' { sid := sid, sender := sender, receiver := receiver } =
              lookupD D₁ { sid := sid, sender := sender, receiver := receiver } :=
          hSpec₁.frame_D { sid := sid, sender := sender, receiver := receiver } hSid
        have hFrame₂ :
            lookupD D₂' (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) =
              lookupD D₂ (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) :=
          hSpec₂.frame_D (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) hSidNe₂
        calc
          lookupD D₂' (renameEdge ρ { sid := sid, sender := sender, receiver := receiver })
              = lookupD D₂ (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) := hFrame₂
          _ = (lookupD D₁ { sid := sid, sender := sender, receiver := receiver }).map (renameValType ρ) :=
                hD { sid := sid, sender := sender, receiver := receiver }
          _ = (lookupD D₁' { sid := sid, sender := sender, receiver := receiver }).map (renameValType ρ) := by
                rw [hFrame₁]

/-- Close is equivariant under session renaming. -/
theorem CloseSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D : DEnv} {ep : Endpoint}
    (hSpec : CloseSpec G G' D ep) :
    CloseSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D)
              (renameEndpoint ρ ep) where
  endpoint_at_end := by
    rw [lookupG_rename, hSpec.endpoint_at_end]
    simp only [Option.map_some, renameLocalType]
  outgoing_empty := by
    intro other
    have hEmpty := hSpec.outgoing_empty other
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := ep.role, receiver := other })
    simp only [renameEdge] at hLookup
    rw [hLookup, hEmpty]
    simp only [List.map_nil]
  incoming_empty := by
    intro other
    have hEmpty := hSpec.incoming_empty other
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := other, receiver := ep.role })
    simp only [renameEdge] at hLookup
    rw [hLookup, hEmpty]
    simp only [List.map_nil]
  endpoint_removed := by
    rw [lookupG_rename, hSpec.endpoint_removed]
    simp only [Option.map_none]
  frame_G := by
    intro ep' hne
    by_cases hPre : ∃ ep'', renameEndpoint ρ ep'' = ep'
    case pos =>
      obtain ⟨ep'', hEp⟩ := hPre
      have hne'' : ep'' ≠ ep := by
        intro hEq
        subst hEq
        exact hne hEp.symm
      have hFrame := hSpec.frame_G ep'' hne''
      rw [← hEp, lookupG_rename, lookupG_rename, hFrame]
    case neg =>
      -- ep' not in renamed image
      have hNone : lookupG (renameGEnv ρ G) ep' = none := by
        by_contra hSome
        rw [← ne_eq, Option.ne_none_iff_exists'] at hSome
        obtain ⟨L, hL⟩ := hSome
        obtain ⟨ep'', _, hEp, _, _⟩ := lookupG_rename_inv ρ G ep' L hL
        exact hPre ⟨ep'', hEp.symm⟩
      have hNone' : lookupG (renameGEnv ρ G') ep' = none := by
        by_contra hSome
        rw [← ne_eq, Option.ne_none_iff_exists'] at hSome
        obtain ⟨L, hL⟩ := hSome
        obtain ⟨ep'', _, hEp, _, _⟩ := lookupG_rename_inv ρ G' ep' L hL
        exact hPre ⟨ep'', hEp.symm⟩
      rw [hNone, hNone']

/-- Close respects ConfigEquiv.
    Note: Close doesn't modify D, so D₁ = D₁' and D₂ = D₂'. -/
theorem CloseSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₂ : DEnv}
    {ep : Endpoint}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : CloseSpec G₁ G₁' D₁ ep)
    (hSpec₂ : CloseSpec G₂ G₂' D₂ (renameEndpoint (hEquiv.choose.toRenaming) ep)) :
    ConfigEquiv ⟨G₁', D₁⟩ ⟨G₂', D₂⟩ := by
  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩
  -- G condition
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the removed endpoint)
      calc lookupG G₂' (renameEndpoint ρ e')
          = lookupG G₂' (renameEndpoint ρ ep) := by rw [he]
        _ = none := hSpec₂.endpoint_removed
        _ = Option.map (renameLocalType ρ) none := by simp only [Option.map_none]
        _ = (lookupG G₁' ep).map (renameLocalType ρ) := by rw [hSpec₁.endpoint_removed]
        _ = (lookupG G₁' e').map (renameLocalType ρ) := by rw [← he]
    · -- Case: e' ≠ ep (frame)
      have hne₂ : renameEndpoint ρ e' ≠ renameEndpoint ρ ep := by
        intro heq; exact he (renameEndpoint_inj ρ e' ep heq)
      rw [hSpec₁.frame_G e' he, hSpec₂.frame_G (renameEndpoint ρ e') hne₂]
      exact hG_equiv e'
  -- D condition: unchanged
  · exact hD_equiv

/-- Transfer is equivariant under session renaming. -/
theorem TransferSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv}
    {ep : Endpoint} {r : Role} {delegatedSession : SessionId} {delegatedRole : Role}
    (hSpec : TransferSpec G G' D D' ep r delegatedSession delegatedRole) :
    TransferSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
                 (renameEndpoint ρ ep) r (ρ.f delegatedSession) delegatedRole where
  sender_type := by
    obtain ⟨L', hSender⟩ := hSpec.sender_type
    use renameLocalType ρ L'
    rw [lookupG_rename]
    simp only [hSender, Option.map_some, renameLocalType, renameValType]
  type_updated := by
    intro L'_renamed hSender_renamed
    rw [lookupG_rename] at hSender_renamed
    obtain ⟨L', hSender⟩ := hSpec.sender_type
    rw [hSender] at hSender_renamed
    simp only [Option.map_some, renameLocalType, renameValType] at hSender_renamed
    have hL'_eq : L'_renamed = renameLocalType ρ L' := by
      cases hSender_renamed
      rfl
    have hG' := hSpec.type_updated L' hSender
    rw [hG', renameGEnv_updateG, hL'_eq]
  trace_extended := by
    have hD' := hSpec.trace_extended
    simp only at hD'
    simp only [renameEndpoint]
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    congr 1
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := ep.role, receiver := r })
    simp only [renameEdge] at hLookup
    rw [List.map_append, List.map, hLookup, renameValType]
    simp
  frame_G := by
    intro ep' hne
    obtain ⟨L', hSender⟩ := hSpec.sender_type
    have hG' := hSpec.type_updated L' hSender
    rw [hG', renameGEnv_updateG]
    exact lookupG_update_neq (renameGEnv ρ G) (renameEndpoint ρ ep) ep'
      (renameLocalType ρ L') hne.symm
  frame_D := by
    intro e hne
    have hD' := hSpec.trace_extended
    simp only at hD'
    simp only [renameEndpoint] at hne ⊢
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    exact lookupD_update_neq (renameDEnv ρ D)
      { sid := ρ.f ep.sid, sender := ep.role, receiver := r } e
      ((lookupD D { sid := ep.sid, sender := ep.role, receiver := r } ++ [ValType.chan delegatedSession delegatedRole]).map (renameValType ρ))
      hne.symm

/-- Transfer respects ConfigEquiv. -/
theorem TransferSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {delegatedSession : SessionId} {delegatedRole : Role}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : TransferSpec G₁ G₁' D₁ D₁' ep r delegatedSession delegatedRole)
    (hSpec₂ : TransferSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r
              (hEquiv.choose.fwd delegatedSession) delegatedRole) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by
  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩
  -- G condition
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the updated endpoint)
      obtain ⟨L'₁, hSender₁⟩ := hSpec₁.sender_type
      have hG₁' := hSpec₁.type_updated L'₁ hSender₁
      obtain ⟨L'₂, hSender₂⟩ := hSpec₂.sender_type
      have hG₂' := hSpec₂.type_updated L'₂ hSender₂
      -- Determine L'₂ from input equivalence
      have hSender₂_raw := hG_equiv ep
      rw [hSender₁] at hSender₂_raw
      simp only [Option.map_some, renameLocalType, renameValType] at hSender₂_raw
      rw [hSender₂_raw] at hSender₂
      simp only [Option.some.injEq, LocalType.send.injEq] at hSender₂
      -- send has 3 fields: role, valtype, continuation
      obtain ⟨_, _, hL'₂_eq⟩ := hSender₂
      -- Compute both sides
      calc lookupG G₂' (renameEndpoint ρ e')
          = lookupG G₂' (renameEndpoint ρ ep) := by rw [he]
        _ = lookupG (updateG G₂ (renameEndpoint ρ ep) L'₂) (renameEndpoint ρ ep) := by rw [hG₂']
        _ = some L'₂ := lookupG_update_eq _ _ _
        _ = some (renameLocalType ρ L'₁) := by rw [hL'₂_eq]
        _ = (some L'₁).map (renameLocalType ρ) := by simp only [Option.map_some]
        _ = (lookupG (updateG G₁ ep L'₁) ep).map (renameLocalType ρ) := by rw [lookupG_update_eq]
        _ = (lookupG G₁' ep).map (renameLocalType ρ) := by rw [← hG₁']
        _ = (lookupG G₁' e').map (renameLocalType ρ) := by rw [← he]
    · -- Case: e' ≠ ep (frame)
      have hne₂ : renameEndpoint ρ e' ≠ renameEndpoint ρ ep := by
        intro heq; exact he (renameEndpoint_inj ρ e' ep heq)
      rw [hSpec₁.frame_G e' he, hSpec₂.frame_G (renameEndpoint ρ e') hne₂]
      exact hG_equiv e'
  -- D condition
  · intro e'
    let sendEdge : Edge := { sid := ep.sid, sender := ep.role, receiver := r }
    by_cases he : e' = sendEdge
    · -- Case: e' = sendEdge (the updated edge)
      have hD₁' := hSpec₁.trace_extended
      have hD₂' := hSpec₂.trace_extended
      simp only [renameEndpoint] at hD₂'
      have hTrace := hD_equiv sendEdge
      simp only [renameEdge] at hTrace
      -- Rewrite goal: lookupD D₂' (renameEdge ρ e') = (lookupD D₁' e').map (renameValType ρ)
      rw [he]
      simp only [renameEdge]
      rw [hD₁', hD₂', lookupD_update_eq, lookupD_update_eq]
      -- Goal: lookupD D₂ (...) ++ [chan...] = (lookupD D₁ sendEdge ++ [chan...]).map (renameValType ρ)
      rw [List.map_append, List.map_singleton, renameValType, hTrace]
      -- The remaining goal equates σ.fwd with σ.toRenaming.f which are definitionally equal
      rfl
    · -- Case: e' ≠ sendEdge (frame)
      have hne₂ : renameEdge ρ e' ≠ renameEdge ρ sendEdge := by
        intro heq; exact he (renameEdge_inj ρ e' sendEdge heq)
      simp only [renameEdge] at hne₂
      rw [hSpec₁.frame_D e' he, hSpec₂.frame_D (renameEdge ρ e') hne₂]
      exact hD_equiv e'

/-- Acquire is equivariant under session renaming.

    Note: This is a `def` rather than `theorem` because `AcquireSpec` contains
    data (via `DelegationStep.A_type : LocalType`) and is thus not a Prop. -/
def AcquireSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv}
    {ep : Endpoint} {r : Role} {delegatedSession : SessionId} {delegatedRole : Role}
    (hSpec : AcquireSpec G G' D D' ep r delegatedSession delegatedRole) :
    AcquireSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
                (renameEndpoint ρ ep) r (ρ.f delegatedSession) delegatedRole where
  receiver_type := by
    obtain ⟨L', hLookup⟩ := hSpec.receiver_type
    refine ⟨renameLocalType ρ L', ?_⟩
    rw [lookupG_rename]
    simp only [hLookup, Option.map_some, renameLocalType, renameValType]
  buffer_has_capability := by
    obtain ⟨rest, hLookup⟩ := hSpec.buffer_has_capability
    refine ⟨rest.map (renameValType ρ), ?_⟩
    -- The edge in the renamed spec is { sid := (renameEndpoint ρ ep).sid, sender := r, receiver := (renameEndpoint ρ ep).role }
    -- which equals renameEdge ρ { sid := ep.sid, sender := r, receiver := ep.role }
    have hEdge : { sid := (renameEndpoint ρ ep).sid, sender := r, receiver := (renameEndpoint ρ ep).role } =
                 renameEdge ρ { sid := ep.sid, sender := r, receiver := ep.role } := by
      simp only [renameEndpoint, renameEdge]
    rw [hEdge, lookupD_rename, hLookup]
    simp only [List.map_cons, renameValType]
  type_updated := by
    intro L' hLookup'
    -- L' is the continuation in the renamed space
    -- We need to find the original continuation and apply type_updated
    rw [lookupG_rename] at hLookup'
    cases hOrig : lookupG G ep with
    | none => simp [hOrig] at hLookup'
    | some Lorig =>
      simp only [hOrig, Option.map_some] at hLookup'
      have hEq := Option.some.inj hLookup'
      -- Lorig should be .recv r (.chan delegatedSession delegatedRole) L'_orig
      -- where L' = renameLocalType ρ L'_orig
      cases Lorig with
      | recv r' T' L'_orig =>
        simp only [renameLocalType] at hEq
        have ⟨hr, hT, hL⟩ := LocalType.recv.inj hEq
        -- T' must be a chan for hT to be valid
        cases T' with
        | chan sid role =>
          simp only [renameValType] at hT
          have hT' := ValType.chan.inj hT
          have hSid := ρ.inj _ _ hT'.1.symm
          -- Apply type_updated with the original L'_orig
          have hLookupOrig : lookupG G ep = some (.recv r (.chan delegatedSession delegatedRole) L'_orig) := by
            simp only [hOrig, ← hr, ← hSid, ← hT'.2]
          have hUpd := hSpec.type_updated L'_orig hLookupOrig
          rw [hUpd, renameGEnv_updateG]
          simp only [← hL]
        | unit => simp only [renameValType] at hT; nomatch hT
        | bool => simp only [renameValType] at hT; nomatch hT
        | nat => simp only [renameValType] at hT; nomatch hT
        | string => simp only [renameValType] at hT; nomatch hT
        | prod _ _ => simp only [renameValType] at hT; nomatch hT
      | send _ _ _ => simp only [renameLocalType] at hEq; nomatch hEq
      | select _ _ => simp only [renameLocalType] at hEq; nomatch hEq
      | branch _ _ => simp only [renameLocalType] at hEq; nomatch hEq
      | end_ => simp only [renameLocalType] at hEq; nomatch hEq
      | var _ => simp only [renameLocalType] at hEq; nomatch hEq
      | mu _ => simp only [renameLocalType] at hEq; nomatch hEq
  delegation_applied :=
    DelegationStep_respects_renaming ρ hSpec.delegation_applied

/-- Acquire respects `ConfigEquiv` constructively. -/
theorem AcquireSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {delegatedSession : SessionId} {delegatedRole : Role}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : AcquireSpec G₁ G₁' D₁ D₁' ep r delegatedSession delegatedRole)
    (hSpec₂ : AcquireSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r
              (hEquiv.choose.fwd delegatedSession) delegatedRole) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG, hD⟩ := hEquiv.choose_spec
  let hDeleg₁ := hSpec₁.delegation_applied
  let hDeleg₂ := hSpec₂.delegation_applied
  have hATypeEq : hDeleg₂.A_type = renameLocalType ρ hDeleg₁.A_type := by
    have hAlookup₂ : lookupG G₂ { sid := ρ.f delegatedSession, role := r } = some hDeleg₂.A_type := by
      simpa [ρ] using hDeleg₂.A_lookup
    have hLookupEq :
        lookupG G₂ { sid := ρ.f delegatedSession, role := r } =
          (lookupG G₁ { sid := delegatedSession, role := r }).map (renameLocalType ρ) := by
      simpa [ρ] using hG { sid := delegatedSession, role := r }
    have hLookupEq' : some hDeleg₂.A_type = (some hDeleg₁.A_type).map (renameLocalType ρ) := by
      rw [← hAlookup₂, hLookupEq, hDeleg₁.A_lookup]
    simpa using Option.some.inj hLookupEq'
  refine ⟨σ, ?_, ?_⟩
  · intro e
    by_cases hSid : e.sid = delegatedSession
    · by_cases hA : e.role = r
      · have hA' : e = { sid := delegatedSession, role := r } := by
          cases e
          simp only [Endpoint.mk.injEq]
          exact ⟨hSid, hA⟩
        rw [hA']
        simp only [renameEndpoint]
        have hAremoved₂ : lookupG G₂' { sid := ρ.f delegatedSession, role := r } = none := by
          simpa [ρ] using hDeleg₂.A_removed
        rw [hDeleg₁.A_removed, hAremoved₂]
        simp
      · by_cases hB : e.role = ep.role
        · have hB' : e = { sid := delegatedSession, role := ep.role } := by
            cases e
            simp only [Endpoint.mk.injEq]
            exact ⟨hSid, hB⟩
          rw [hB']
          simp only [renameEndpoint]
          have hBadded₂ :
              lookupG G₂' { sid := ρ.f delegatedSession, role := ep.role } =
                some (renameLocalTypeRole (ρ.f delegatedSession) r ep.role hDeleg₂.A_type) := by
            simpa [ρ] using hDeleg₂.B_added
          rw [hDeleg₁.B_added, hBadded₂]
          simp only [Option.map_some]
          rw [hATypeEq]
          congr 1
          exact (renameLocalType_renameLocalTypeRole_comm ρ delegatedSession r ep.role hDeleg₁.A_type).symm
        · have hOther₁ := hDeleg₁.other_roles_G e hSid hA hB
          have hSidRen : (renameEndpoint ρ e).sid = ρ.f delegatedSession := by
            simp only [renameEndpoint, hSid]
          have hOther₂ := hDeleg₂.other_roles_G (renameEndpoint ρ e) hSidRen hA hB
          rw [hOther₁, hOther₂, hG]
          simp only [Option.map_map]
          congr 1
          funext L
          exact (renameLocalType_renameLocalTypeRole_comm ρ delegatedSession r ep.role L).symm
    · have hSidRen : (renameEndpoint ρ e).sid ≠ ρ.f delegatedSession := by
        simp only [renameEndpoint]
        intro hEq
        exact hSid (ρ.inj _ _ hEq)
      rw [hDeleg₁.other_sessions_G e hSid, hDeleg₂.other_sessions_G (renameEndpoint ρ e) hSidRen]
      exact hG e
  · intro e
    by_cases hSid : e.sid = delegatedSession
    · by_cases hInc : e.sender = r ∨ e.receiver = r
      · have hEmpty₁ : lookupD D₁' e = [] := hDeleg₁.A_incident_empty e hSid hInc
        have hSidRen : (renameEdge ρ e).sid = ρ.f delegatedSession := by
          simp only [renameEdge, hSid]
        have hIncRen : (renameEdge ρ e).sender = r ∨ (renameEdge ρ e).receiver = r := by
          simpa [renameEdge] using hInc
        have hEmpty₂ : lookupD D₂' (renameEdge ρ e) = [] :=
          hDeleg₂.A_incident_empty (renameEdge ρ e) hSidRen hIncRen
        rw [hEmpty₁, hEmpty₂]
        simp
      · have hSenderNe : e.sender ≠ r := by
          intro hEq
          exact hInc (Or.inl hEq)
        have hReceiverNe : e.receiver ≠ r := by
          intro hEq
          exact hInc (Or.inr hEq)
        have hRedir₁ : IsRedirectedEdge e e delegatedSession r ep.role := by
          rw [IsRedirectedEdge]
          exact (redirectEdge_no_A e delegatedSession r ep.role hSid hSenderNe hReceiverNe).symm
        have hD₁' :
            lookupD D₁' e =
              (lookupD D₁ e).map (renameValTypeRole delegatedSession r ep.role) :=
          hDeleg₁.trace_preserved e e hRedir₁
        have hSidRen : (renameEdge ρ e).sid = ρ.f delegatedSession := by
          simp only [renameEdge, hSid]
        have hSenderNeRen : (renameEdge ρ e).sender ≠ r := by
          simpa [renameEdge] using hSenderNe
        have hReceiverNeRen : (renameEdge ρ e).receiver ≠ r := by
          simpa [renameEdge] using hReceiverNe
        have hRedir₂ :
            IsRedirectedEdge (renameEdge ρ e) (renameEdge ρ e) (ρ.f delegatedSession) r ep.role := by
          rw [IsRedirectedEdge]
          exact (redirectEdge_no_A (renameEdge ρ e) (ρ.f delegatedSession) r ep.role
            hSidRen hSenderNeRen hReceiverNeRen).symm
        have hD₂' :
            lookupD D₂' (renameEdge ρ e) =
              (lookupD D₂ (renameEdge ρ e)).map (renameValTypeRole (ρ.f delegatedSession) r ep.role) :=
          hDeleg₂.trace_preserved (renameEdge ρ e) (renameEdge ρ e) hRedir₂
        rw [hD₂', hD e, hD₁']
        simp only [List.map_map]
        congr 1
        funext T
        exact (renameValType_renameValTypeRole_comm ρ delegatedSession r ep.role T).symm
    · have hSidRen : (renameEdge ρ e).sid ≠ ρ.f delegatedSession := by
        simp only [renameEdge]
        intro hEq
        exact hSid (ρ.inj _ _ hEq)
      rw [hDeleg₂.other_sessions_D (renameEdge ρ e) hSidRen, hDeleg₁.other_sessions_D e hSid]
      exact hD e


end
