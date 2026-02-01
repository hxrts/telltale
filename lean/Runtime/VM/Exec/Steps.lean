import Protocol.Environments.Part1
import Runtime.Resources.ResourceModel
import Runtime.VM.Exec.Helpers

/-
The Problem. Define instruction-level semantics that update coroutine state,
VM buffers, and session store state.

Solution Structure. Implement a small step function per instruction and
compose them in a single dispatcher.
-/

set_option autoImplicit false

universe u

/-! ## Instruction semantics -/

private def primaryEndpoint {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (coro : CoroutineState γ ε) : Endpoint :=
  -- Choose a representative endpoint for observability.
  match coro.ownedEndpoints with
  | e :: _ => e
  | [] => { sid := 0, role := "" }

private def stepSend {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan val : Reg) : StepPack ι γ π ε ν :=
  -- Send a value on a owned endpoint and append to buffers.
  match readReg coro.regs chan, readReg coro.regs val with
  | some (.chan ep), some v =>
      if owns coro ep then
        match SessionStore.lookupType st.sessions ep with
        | some (.send r T L') =>
            if decide (valTypeOf v = T) then
              let edge := edgeTo ep r
              if edgePartitioned st edge then
                -- Partitioned edges block sends in V1.
                blockPack st coro (.sendWait edge)
              else if edgeCrashed st edge then
                -- Crashed endpoints fail fast.
                faultPack st coro (.specFault "edge crashed") "edge crashed"
              else
                match SessionStore.lookupHandler st.sessions edge with
                | none =>
                    faultPack st coro (.specFault "no handler bound") "no handler bound"
                | some h =>
                    if st.config.handlerSpecOk h = false then
                      faultPack st coro (.specFault "handler spec failed") "handler spec failed"
                    else
                    -- Sign the payload with the role's signing key.
                    let signed := signValue (st.config.roleSigningKey ep.role) v
                    let cfg := st.config.bufferConfig edge
                    let (res, bufs') := bufEnqueue cfg st.buffers edge signed
                    match res with
                    | .ok =>
                        let sessions1 := updateSessBuffers st.sessions ep.sid bufs'
                        let trace := SessionStore.lookupTrace sessions1 edge
                        let sessions2 := SessionStore.updateTrace sessions1 edge (trace ++ [T])
                        let sessions3 := SessionStore.updateType sessions2 ep L'
                        let st' := { st with buffers := bufs', sessions := sessions3 }
                        continuePack st' coro (some (.obs (.sent edge v 0)))
                    | .blocked =>
                        blockPack st coro (.sendWait edge)
                    | .dropped =>
                        faultPack st coro (.flowViolation "buffer drop") "buffer drop"
                    | .error =>
                        faultPack st coro (.flowViolation "buffer overflow") "buffer overflow"
            else
              faultPack st coro (.typeViolation T (valTypeOf v)) "bad send payload"
        | _ =>
            faultPack st coro (.specFault "send not permitted") "send not permitted"
      else
        faultPack st coro (.channelClosed ep) "endpoint not owned"
  | some (.chan _), none =>
      faultPack st coro .outOfRegisters "missing send value"
  | some v, _ =>
      faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad send channel"
  | none, _ =>
      faultPack st coro .outOfRegisters "missing send channel"

private def stepRecv {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan dst : Reg) : StepPack ι γ π ε ν :=
  -- Receive a value or block if none is available.
  match readReg coro.regs chan with
  | some (.chan ep) =>
      if owns coro ep then
        match SessionStore.lookupType st.sessions ep with
        | some (.recv r T L') =>
            let edge := edgeFrom r ep
            let token := { sid := edge.sid, endpoint := { sid := edge.sid, role := edge.receiver } }
            if edgePartitioned st edge then
              -- Partitioned edges block receives in V1.
              blockPack st coro (.recvWait edge token)
            else if edgeCrashed st edge then
              -- Crashed endpoints fail fast.
              faultPack st coro (.specFault "edge crashed") "edge crashed"
            else
              match SessionStore.lookupHandler st.sessions edge with
              | none =>
                  faultPack st coro (.specFault "no handler bound") "no handler bound"
              | some h =>
                  if st.config.handlerSpecOk h = false then
                    faultPack st coro (.specFault "handler spec failed") "handler spec failed"
                  else
                  match consumeProgressToken coro.progressTokens token with
                  | none =>
                      faultPack st coro (.noProgressToken edge) "missing progress token"
                  | some tokens' =>
                      match bufDequeue st.buffers edge with
                      | none =>
                          let coro' := { coro with progressTokens := tokens' }
                          blockPack st coro' (.recvWait edge token)
                      | some (sv, bufs') =>
                          -- Verify the signature against the sender role.
                          let vk := VerificationModel.verifyKeyOf (st.config.roleSigningKey edge.sender)
                          if verifySignedValue vk sv then
                            if decide (valTypeOf sv.payload = T) then
                              match setReg coro.regs dst sv.payload with
                              | none => faultPack st coro .outOfRegisters "bad dst reg"
                              | some regs' =>
                                  let sessions1 := updateSessBuffers st.sessions ep.sid bufs'
                                  let trace := SessionStore.lookupTrace sessions1 edge
                                  let trace' := match trace with | [] => [] | _ :: ts => ts
                                  let sessions2 := SessionStore.updateTrace sessions1 edge trace'
                                  let sessions3 := SessionStore.updateType sessions2 ep L'
                                  let st' := { st with buffers := bufs', sessions := sessions3 }
                                  let coro' := { coro with regs := regs', progressTokens := tokens' }
                                  continuePack st' coro' (some (.obs (.received edge sv.payload 0)))
                            else
                              faultPack st coro (.typeViolation T (valTypeOf sv.payload)) "bad recv payload"
                          else
                            faultPack st coro (.invalidSignature edge) "invalid signature"
        | _ =>
            faultPack st coro (.specFault "recv not permitted") "recv not permitted"
      else
        faultPack st coro (.channelClosed ep) "endpoint not owned"
  | some v =>
      faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad recv channel"
  | none =>
      faultPack st coro .outOfRegisters "missing recv channel"

private def stepOffer {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan : Reg) (lbl : Label) : StepPack ι γ π ε ν :=
  -- Offer a label by enqueuing it on the buffer.
  match readReg coro.regs chan with
  | some (.chan ep) =>
      if owns coro ep then
        match SessionStore.lookupType st.sessions ep with
        | some (.select r choices) =>
            match choices.find? (fun p => p.fst == lbl) with
            | none =>
                faultPack st coro (.unknownLabel lbl) "unknown label"
            | some (_, L') =>
                let edge := edgeTo ep r
                if edgePartitioned st edge then
                  -- Partitioned edges block offers in V1.
                  blockPack st coro (.sendWait edge)
                else if edgeCrashed st edge then
                  -- Crashed endpoints fail fast.
                  faultPack st coro (.specFault "edge crashed") "edge crashed"
                else
                  let v := Value.string lbl
                  -- Sign the label payload before enqueue.
                  let signed := signValue (st.config.roleSigningKey ep.role) v
                  match SessionStore.lookupHandler st.sessions edge with
                  | none =>
                      faultPack st coro (.specFault "no handler bound") "no handler bound"
                  | some h =>
                      if st.config.handlerSpecOk h = false then
                        faultPack st coro (.specFault "handler spec failed") "handler spec failed"
                      else
                      let cfg := st.config.bufferConfig edge
                      let (res, bufs') := bufEnqueue cfg st.buffers edge signed
                      match res with
                      | .ok =>
                          let sessions1 := updateSessBuffers st.sessions ep.sid bufs'
                          let trace := SessionStore.lookupTrace sessions1 edge
                          let sessions2 := SessionStore.updateTrace sessions1 edge (trace ++ [.string])
                          let sessions3 := SessionStore.updateType sessions2 ep L'
                          let st' := { st with buffers := bufs', sessions := sessions3 }
                          continuePack st' coro (some (.obs (.offered edge lbl)))
                      | .blocked =>
                          blockPack st coro (.sendWait edge)
                      | .dropped =>
                          faultPack st coro (.flowViolation "buffer drop") "buffer drop"
                      | .error =>
                          faultPack st coro (.flowViolation "buffer overflow") "buffer overflow"
        | _ =>
            faultPack st coro (.specFault "offer not permitted") "offer not permitted"
      else
        faultPack st coro (.channelClosed ep) "endpoint not owned"
  | some v =>
      faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad offer channel"
  | none =>
      faultPack st coro .outOfRegisters "missing offer channel"

private def stepChoose {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan : Reg) (table : List (Label × PC)) : StepPack ι γ π ε ν :=
  -- Consume a label and jump to the selected branch.
  match readReg coro.regs chan with
  | some (.chan ep) =>
      if owns coro ep then
        match SessionStore.lookupType st.sessions ep with
        | some (.branch r choices) =>
            let edge := edgeFrom r ep
            let token := { sid := edge.sid, endpoint := { sid := edge.sid, role := edge.receiver } }
            if edgePartitioned st edge then
              -- Partitioned edges block chooses in V1.
              blockPack st coro (.recvWait edge token)
            else if edgeCrashed st edge then
              -- Crashed endpoints fail fast.
              faultPack st coro (.specFault "edge crashed") "edge crashed"
            else
              match SessionStore.lookupHandler st.sessions edge with
              | none =>
                  faultPack st coro (.specFault "no handler bound") "no handler bound"
              | some h =>
                  if st.config.handlerSpecOk h = false then
                    faultPack st coro (.specFault "handler spec failed") "handler spec failed"
                  else
                  match bufDequeue st.buffers edge with
                  | some (sv, bufs') =>
                      -- Verify the signature before consuming the label.
                      let vk := VerificationModel.verifyKeyOf (st.config.roleSigningKey edge.sender)
                      if verifySignedValue vk sv then
                        match sv.payload with
                        | .string lbl =>
                            match table.find? (fun b => b.fst == lbl) with
                            | some (_, target) =>
                                match choices.find? (fun b => b.fst == lbl) with
                                | none =>
                                    let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                                    faultPack st' coro (.unknownLabel lbl) "unknown label"
                                | some (_, L') =>
                                    let coro' := { coro with pc := target, status := .ready }
                                    let sessions1 := updateSessBuffers st.sessions ep.sid bufs'
                                    let trace := SessionStore.lookupTrace sessions1 edge
                                    let trace' := match trace with | [] => [] | _ :: ts => ts
                                    let sessions2 := SessionStore.updateTrace sessions1 edge trace'
                                    let sessions3 := SessionStore.updateType sessions2 ep L'
                                    let st' := { st with buffers := bufs', sessions := sessions3 }
                                    pack coro' st' (mkRes .continue (some (.obs (.chose edge lbl))))
                            | none =>
                                let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                                faultPack st' coro (.unknownLabel lbl) "unknown label"
                        | _ =>
                            let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                            faultPack st' coro (.typeViolation .string (valTypeOf sv.payload)) "bad label payload"
                      else
                        faultPack st coro (.invalidSignature edge) "invalid signature"
                  | none =>
                      blockPack st coro (.recvWait edge token)
        | _ =>
            faultPack st coro (.specFault "choose not permitted") "choose not permitted"
      else
        faultPack st coro (.channelClosed ep) "endpoint not owned"
  | some v =>
      faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad choose channel"
  | none =>
      faultPack st coro .outOfRegisters "missing choose channel"

private def zipOpenArgs (localTypes : List (Role × LocalType))
    (dsts : List (Role × Reg)) : Option (List (Role × LocalType × Reg)) :=
  -- Align local types with destination registers by role.
  match localTypes, dsts with
  | [], [] => some []
  | (r, lt) :: ls, (r', d) :: ds =>
      if r == r' then
        (zipOpenArgs ls ds).map (fun rest => (r, lt, d) :: rest)
      else
        none
  | _, _ => none

private def writeEndpoints (regs : RegFile) (sid : SessionId)
    (pairs : List (Role × Reg)) : Option RegFile :=
  -- Write fresh endpoints into destination registers.
  let mkEp (r : Role) : Endpoint := { sid := sid, role := r }
  let rec go (rs : List (Role × Reg)) (acc : RegFile) : Option RegFile :=
    match rs with
    | [] => some acc
    | (r, d) :: rest =>
        match setReg acc d (.chan (mkEp r)) with
        | none => none
        | some acc' => go rest acc'
  go pairs regs

private def handlerBound (handlers : List (Edge × HandlerId)) (edge : Edge) : Bool :=
  -- Check whether a handler binding exists for the edge.
  handlers.any (fun h => decide (h.fst = edge))

private def handlersCoverRoles (sid : SessionId) (roles : List Role)
    (handlers : List (Edge × HandlerId)) : Bool :=
  -- Ensure every role's self-edge is bound to some handler.
  roles.all (fun r => handlerBound handlers { sid := sid, sender := r, receiver := r })

private def allEdges (sid : SessionId) (roles : List Role) : List Edge :=
  -- Enumerate all directed edges between roles for a session.
  roles.foldl
    (fun acc r1 => acc ++ roles.map (fun r2 => { sid := sid, sender := r1, receiver := r2 }))
    []

private def handlersCoverEdges (sid : SessionId) (roles : List Role)
    (handlers : List (Edge × HandlerId)) : Bool :=
  -- Ensure every session edge is bound to some handler.
  (allEdges sid roles).all (fun e => handlerBound handlers e)

private def stepOpen {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (localTypes : List (Role × LocalType))
    (handlers : List (Edge × HandlerId))
    (dsts : List (Role × Reg)) : StepPack ι γ π ε ν :=
  -- Create a new session and install endpoints in registers.
  match zipOpenArgs localTypes dsts with
  | none => faultPack st coro (.closeFault "open arity mismatch") "open arity mismatch"
  | some triples =>
      let sid := st.nextSessionId
      let roles := triples.map (fun p => p.1)
      let dstRegs := triples.map (fun p => p.2.2)
      let pairs := List.zip roles dstRegs
      if !handlersCoverEdges sid roles handlers then
        faultPack st coro (.specFault "handler bindings incomplete") "handler bindings incomplete"
      else
        match writeEndpoints coro.regs sid pairs with
        | none => faultPack st coro .outOfRegisters "bad dst reg"
        | some regs' =>
            let scope := { id := sid }
            let payload := Value.prod (.nat sid) (.string (String.intercalate "," roles))
            let endpoints := roles.map (fun r => { sid := sid, role := r })
            let localTypes' := triples.map (fun p => ({ sid := sid, role := p.1 }, p.2.1))
            let edges := allEdges sid roles
            let bufs' := signedBuffersEnsure st.buffers edges
            let sess : SessionState ν :=
              -- V1 binds session scope to the session id.
              { scope := scope
              , sid := sid
              , roles := roles
              , endpoints := endpoints
              , localTypes := localTypes'
              , traces := initDEnv sid roles
              , buffers := buffersFor bufs' sid
              , handlers := handlers
              , epoch := 0
              , phase := .active }
            let coro' := advancePc ({ coro with regs := regs', status := .ready, ownedEndpoints := endpoints ++ coro.ownedEndpoints })
            let res : Resource ν :=
              { logic := VerificationModel.hashTagged .resourceKind payload
              , label := VerificationModel.hashTagged .contentId payload
              , quantity := 1
              , value := payload
              , nonce := VerificationModel.defaultNonce
              , ckey := VerificationModel.defaultCommitmentKey
              , nullifierKey := VerificationModel.defaultNullifierKey
              , isEphemeral := false }
            let tx : Transaction ν :=
              { created := [res]
              , consumed := []
              , deltaProof := ()
              , logicProofs := []
              , complianceProofs := [st.config.complianceProof res]
              , authorizedImbalance := true }
            match applyTransactionAtScope st.resourceStates scope tx with
            | none =>
                faultPack st coro (.specFault "resource transaction failed") "resource transaction failed"
            | some resources' =>
                let persist' := PersistenceModel.apply st.persistent (PersistenceModel.openDelta sid)
                let st' :=
                  { st with nextSessionId := st.nextSessionId + 1
                          , sessions := (sid, sess) :: st.sessions
                          , resourceStates := resources'
                          , buffers := bufs'
                          , persistent := persist' }
                pack coro' st' (mkRes .continue (some (.obs (.opened sid roles))))

private def stepClose {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (session : Reg) : StepPack ι γ π ε ν :=
  -- Close a session endpoint and clear its buffers.
  match readReg coro.regs session with
  | some (.chan ep) =>
      if owns coro ep then
        let rec findEpoch (ss : SessionStore ν) : Nat :=
          match ss with
          | [] => 0
          | (sid, s) :: rest => if sid = ep.sid then s.epoch else findEpoch rest
        let epoch' := findEpoch st.sessions + 1
        let updatePhase (s : SessionState ν) : SessionState ν :=
          -- Closing clears buffers and traces while marking the phase.
          { s with phase := .closed, buffers := [], traces := (∅ : DEnv), epoch := epoch' }
        let rec findRoles (ss : SessionStore ν) : RoleSet :=
          match ss with
          | [] => []
          | (sid, s) :: rest => if sid = ep.sid then s.roles else findRoles rest
        let roles := findRoles st.sessions
        let payload := Value.prod (.nat ep.sid) (.string (String.intercalate "," roles))
        let rec closeSess (ss : SessionStore ν) : SessionStore ν :=
          match ss with
          | [] => []
          | (sid, s) :: rest =>
              if _h : sid = ep.sid then
                (sid, updatePhase s) :: rest
              else
                (sid, s) :: closeSess rest
        let res : Resource ν :=
          { logic := VerificationModel.hashTagged .resourceKind payload
          , label := VerificationModel.hashTagged .contentId payload
          , quantity := 1
          , value := payload
          , nonce := VerificationModel.defaultNonce
          , ckey := VerificationModel.defaultCommitmentKey
          , nullifierKey := VerificationModel.defaultNullifierKey
          , isEphemeral := false }
        let tx : Transaction ν :=
          { created := []
          , consumed := [res]
          , deltaProof := ()
          , logicProofs := []
          , complianceProofs := [st.config.complianceProof res]
          , authorizedImbalance := true }
        match applyTransactionAtScope st.resourceStates { id := ep.sid } tx with
        | none =>
            faultPack st coro (.closeFault "resource transaction failed") "resource transaction failed"
        | some resources' =>
            let persist' := PersistenceModel.apply st.persistent (PersistenceModel.closeDelta ep.sid)
            let st' := { st with sessions := closeSess st.sessions
                                , resourceStates := resources'
                                , persistent := persist' }
            let st'' := appendEvent st' (some (StepEvent.obs (.epochAdvanced ep.sid epoch')))
            let owned' := coro.ownedEndpoints.filter (fun e => decide (e ≠ ep))
            let coro' := advancePc { coro with status := .ready, ownedEndpoints := owned' }
            pack coro' st'' (mkRes .continue (some (.obs (.closed ep.sid))))
      else
        faultPack st coro (.closeFault "endpoint not owned") "endpoint not owned"
  | some v =>
      faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad close operand"
  | none =>
      faultPack st coro .outOfRegisters "missing close operand"

private def stepAcquire {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (layer : γ) (dst : Reg) : StepPack ι γ π ε ν :=
  -- Acquire a guard-layer resource and return evidence.
  if st.config.guardChain.active layer = false then
    faultPack st coro (.acquireFault "guard-layer" "inactive layer") "inactive layer"
  else
    match guardResourceLookup st.guardResources layer with
    | none => faultPack st coro (.acquireFault "guard-layer" "unknown layer") "unknown layer"
    | some r =>
        match GuardLayer.open_ r with
        | none => blockPack st coro (.acquireDenied layer)
        | some ev =>
            let encoded := GuardLayer.encodeEvidence ev
            match setReg coro.regs dst encoded with
            | none => faultPack st coro .outOfRegisters "bad dst reg"
            | some regs' =>
                let ev := StepEvent.obs (.acquired (GuardLayer.layerNs layer) (primaryEndpoint coro))
                continuePack st { coro with regs := regs' } (some ev)

private def stepRelease {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (_layer : γ) (_evidence : Reg) : StepPack ι γ π ε ν :=
  -- Release a guard-layer resource and record the layer.
  if st.config.guardChain.active _layer = false then
    faultPack st coro (.acquireFault "guard-layer" "inactive layer") "inactive layer"
  else
    match readReg coro.regs _evidence with
    | none => faultPack st coro .outOfRegisters "missing evidence"
    | some v =>
        match GuardLayer.decodeEvidence v with
        | none => faultPack st coro (.acquireFault "guard-layer" "bad evidence") "bad evidence"
        | some evd =>
            match guardResourceLookup st.guardResources _layer with
            | none => faultPack st coro (.acquireFault "guard-layer" "unknown layer") "unknown layer"
            | some _ =>
                let rs' := guardResourceUpdate st.guardResources _layer (fun r => GuardLayer.close r evd)
                let st' := { st with guardResources := rs' }
                let ev := StepEvent.obs (.released (GuardLayer.layerNs _layer) (primaryEndpoint coro))
                continuePack st' coro (some ev)

private def stepInvoke {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (action : EffectModel.EffectAction ε) : StepPack ι γ π ε ν :=
  -- Execute an effect action via the bound handler (placeholder response model).
  match SessionStore.defaultHandler st.sessions with
  | none =>
      faultPack st coro (.invokeFault "no handler bound") "no handler bound"
  | some handlerId =>
      let ctx' := EffectModel.exec action coro.effectCtx
      let delta := PersistenceEffectBridge.bridge (π:=π) (ε:=ε) action
      let persist' := PersistenceModel.apply st.persistent delta
      let st' := { st with persistent := persist' }
      let ev := StepEvent.obs (.invoked (primaryEndpoint coro) action)
      continuePack st' { coro with effectCtx := ctx' } (some ev)

private def stepFork {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (sidReg : Reg) : StepPack ι γ π ε ν :=
  -- Enter speculation mode for a ghost session id.
  match readReg coro.regs sidReg with
  | some (.nat gsid) =>
      let coro' := advancePc { coro with specState := some { ghostSid := gsid, depth := 0 } }
      pack coro' st (mkRes (.forked gsid) (some (.obs (.forked gsid gsid))))
  | some v =>
      faultPack st coro (.typeViolation .nat (valTypeOf v)) "bad fork operand"
  | none =>
      faultPack st coro .outOfRegisters "missing fork operand"

private def stepJoin {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : StepPack ι γ π ε ν :=
  -- Join speculation: clear ghost state.
  let sid :=
    match coro.specState with
    | some s => s.ghostSid
    | none => 0
  let coro' := advancePc { coro with specState := none }
  pack coro' st (mkRes .joined (some (.obs (.joined sid))))

private def stepAbort {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : StepPack ι γ π ε ν :=
  -- Abort speculation: clear ghost state.
  let sid :=
    match coro.specState with
    | some s => s.ghostSid
    | none => 0
  let coro' := advancePc { coro with specState := none }
  pack coro' st (mkRes .aborted (some (.obs (.aborted sid))))

private def stepTransfer {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (endpoint targetCoro _bundle : Reg) : StepPack ι γ π ε ν :=
  -- Transfer an owned endpoint to another coroutine.
  match readReg coro.regs endpoint, readReg coro.regs targetCoro with
  | some (.chan ep), some (.nat tid) =>
      if owns coro ep then
        let owned' := coro.ownedEndpoints.filter (fun e => decide (e ≠ ep))
        let movedTokens := coro.progressTokens.filter (fun t => decide (t.endpoint = ep))
        let keptTokens := coro.progressTokens.filter (fun t => decide (t.endpoint ≠ ep))
        let movedFacts := coro.knowledgeSet.filter (fun k => decide (k.endpoint = ep))
        let keptFacts := coro.knowledgeSet.filter (fun k => decide (k.endpoint ≠ ep))
        let coros' :=
          if h : tid < st.coroutines.size then
            let cT := st.coroutines[tid]'h
            let cT' :=
              { cT with ownedEndpoints := ep :: cT.ownedEndpoints
                       , progressTokens := movedTokens ++ cT.progressTokens
                       , knowledgeSet := movedFacts ++ cT.knowledgeSet }
            st.coroutines.set (i := tid) (v := cT') (h := h)
          else
            st.coroutines
        let st' := { st with coroutines := coros' }
        let coro' := advancePc { coro with ownedEndpoints := owned'
                                          , progressTokens := keptTokens
                                          , knowledgeSet := keptFacts }
        pack coro' st' (mkRes (.transferred ep tid) (some (.obs (.transferred ep coro.id tid))))
      else
        faultPack st coro (.transferFault "endpoint not owned") "endpoint not owned"
  | some (.chan _), none =>
      faultPack st coro .outOfRegisters "missing transfer target"
  | some (.chan _), some v =>
      faultPack st coro (.typeViolation .nat (valTypeOf v)) "bad transfer target"
  | some v, _ =>
      faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad transfer endpoint"
  | none, _ =>
      faultPack st coro .outOfRegisters "missing transfer endpoint"

private def stepTag {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (fact dst : Reg) : StepPack ι γ π ε ν :=
  -- Record a knowledge fact and return success.
  match readReg coro.regs fact with
  | some (.prod (.chan ep) (.string s)) =>
      match setReg coro.regs dst (.bool true) with
      | none => faultPack st coro .outOfRegisters "bad dst reg"
      | some regs' =>
          let fact' := { endpoint := ep, fact := s }
          let know' := fact' :: coro.knowledgeSet
          let ev := StepEvent.obs (.tagged fact')
          continuePack st { coro with regs := regs', knowledgeSet := know' } (some ev)
  | some v =>
      faultPack st coro (.typeViolation (.prod (.chan 0 "") .string) (valTypeOf v)) "bad fact"
  | none =>
      faultPack st coro .outOfRegisters "missing fact"

private def stepCheck {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (knowledge target dst : Reg) : StepPack ι γ π ε ν :=
  -- Check whether a fact is in the knowledge set.
  match readReg coro.regs knowledge with
  | some (.prod (.chan ep) (.string s)) =>
      let fact := { endpoint := ep, fact := s }
      let permitted := st.config.flowPolicy.allowed fact
      let tgtRole : Role :=
        match readReg coro.regs target with
        | some (.string r) => r
        | _ => ""
      let ok := permitted tgtRole && coro.knowledgeSet.any (fun k => k == fact)
      match setReg coro.regs dst (.bool ok) with
      | none => faultPack st coro .outOfRegisters "bad dst reg"
      | some regs' =>
          let ev := StepEvent.obs (.checked tgtRole ok)
          continuePack st { coro with regs := regs' } (some ev)
  | some v =>
      faultPack st coro (.typeViolation (.prod (.chan 0 "") .string) (valTypeOf v)) "bad knowledge"
  | none =>
      faultPack st coro .outOfRegisters "missing knowledge"

private def stepSpawn {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (target : PC) (args : List Reg) : StepPack ι γ π ε ν :=
  -- Spawn a new coroutine with copied arguments.
  let newId := st.nextCoroId
  let initRegs : RegFile := Array.mk (List.replicate coro.regs.size Value.unit)
  let rec copyArgs (idx : Nat) (regs : RegFile) (xs : List Reg) : RegFile :=
    match xs with
    | [] => regs
    | r :: rs =>
        match readReg coro.regs r with
        | none => copyArgs (idx + 1) regs rs
        | some v =>
            if h : idx < regs.size then
              copyArgs (idx + 1) (regs.set (i := idx) (v := v) (h := h)) rs
            else
              regs
  let newRegs := copyArgs 0 initRegs args
  let budget := st.config.costModel.defaultBudget
  let newCoro : CoroutineState γ ε :=
    { id := newId, pc := target, regs := newRegs, status := .ready
      effectCtx := coro.effectCtx, ownedEndpoints := [], progressTokens := []
      knowledgeSet := [], costBudget := budget, specState := none }
  let coros' := st.coroutines.push newCoro
  let st' := { st with coroutines := coros', nextCoroId := newId + 1 }
  let coro' := advancePc { coro with status := .ready }
  pack coro' st' (mkRes (.spawned newId) none)

private def stepLoadImm {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (dst : Reg) (v : Value) : StepPack ι γ π ε ν :=
  -- Load an immediate value into a register.
  match setReg coro.regs dst v with
  | some regs' => continuePack st { coro with regs := regs' } none
  | none => faultPack st coro .outOfRegisters "out of registers"

private def stepMov {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (dst src : Reg) : StepPack ι γ π ε ν :=
  -- Move a value between registers.
  match readReg coro.regs src with
  | none => faultPack st coro .outOfRegisters "bad src reg"
  | some v =>
      match setReg coro.regs dst v with
      | none => faultPack st coro .outOfRegisters "bad dst reg"
      | some regs' => continuePack st { coro with regs := regs' } none

private def stepJmp {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (target : PC) : StepPack ι γ π ε ν :=
  -- Jump to a new program counter.
  let coro' := { coro with pc := target, status := .ready }
  pack coro' st (mkRes .continue none)

private def stepYield {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : StepPack ι γ π ε ν :=
  -- Yield to scheduler by blocking the coroutine.
  let coro' := advancePc { coro with status := .blocked .spawnWait }
  pack coro' st (mkRes .yielded none)

/-- Dispatch to per-instruction semantics. -/
def stepInstr {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (i : Instr γ ε) : StepPack ι γ π ε ν :=
  -- Call the appropriate per-instruction helper.
  match i with
  | .send chan val => stepSend st coro chan val
  | .recv chan dst => stepRecv st coro chan dst
  | .offer chan lbl => stepOffer st coro chan lbl
  | .choose chan table => stepChoose st coro chan table
  | .acquire layer dst => stepAcquire st coro layer dst
  | .release layer evidence => stepRelease st coro layer evidence
  | .invoke action => stepInvoke st coro action
  | .open _roles localTypes handlers dsts => stepOpen st coro localTypes handlers dsts
  | .close session => stepClose st coro session
  | .fork sid => stepFork st coro sid
  | .join => stepJoin st coro
  | .abort => stepAbort st coro
  | .transfer ep target bundle => stepTransfer st coro ep target bundle
  | .tag fact dst => stepTag st coro fact dst
  | .check knowledge target dst => stepCheck st coro knowledge target dst
  | .loadImm dst v => stepLoadImm st coro dst v
  | .mov dst src => stepMov st coro dst src
  | .jmp target => stepJmp st coro target
  | .spawn target args => stepSpawn st coro target args
  | .yield => stepYield st coro
  | .halt => haltPack st coro
