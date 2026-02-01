import Protocol.Environments.Part1
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
        let edge := edgeOf ep
        -- Sign the payload with the role's signing key.
        let signed := signValue (st.config.roleSigningKey ep.role) v
        let bufs' := bufEnqueue st.buffers edge signed
        let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
        continuePack st' coro (some (.send edge "" v))
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
        let edge := edgeOf ep
        let token := { sid := edge.sid, endpoint := { sid := edge.sid, role := edge.receiver } }
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
                  match setReg coro.regs dst sv.payload with
                  | none => faultPack st coro .outOfRegisters "bad dst reg"
                  | some regs' =>
                      let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                      let coro' := { coro with regs := regs', progressTokens := tokens' }
                      continuePack st' coro' (some (.recv edge "" sv.payload))
                else
                  faultPack st coro (.invalidSignature edge) "invalid signature"
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
        let edge := edgeOf ep
        let v := Value.string lbl
        -- Sign the label payload before enqueue.
        let signed := signValue (st.config.roleSigningKey ep.role) v
        let bufs' := bufEnqueue st.buffers edge signed
        let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
        continuePack st' coro (some (.offer edge lbl))
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
        let edge := edgeOf ep
        match bufDequeue st.buffers edge with
        | some (sv, bufs') =>
            -- Verify the signature before consuming the label.
            let vk := VerificationModel.verifyKeyOf (st.config.roleSigningKey edge.sender)
            if verifySignedValue vk sv then
              match sv.payload with
              | .string lbl =>
                  match table.find? (fun b => b.fst == lbl) with
                  | some (_, target) =>
                      let coro' := { coro with pc := target, status := .ready }
                      let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                      pack coro' st' (mkRes .continue (some (.choose edge lbl)))
                  | none =>
                      let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                      faultPack st' coro (.unknownLabel lbl) "unknown label"
              | _ =>
                  let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                  faultPack st' coro (.typeViolation .string (valTypeOf sv.payload)) "bad label payload"
            else
              faultPack st coro (.invalidSignature edge) "invalid signature"
        | none =>
            let token := { sid := edge.sid, endpoint := { sid := edge.sid, role := edge.receiver } }
            blockPack st coro (.recvWait edge token)
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
      if !handlersCoverRoles sid roles handlers then
        faultPack st coro (.specFault "handler bindings incomplete") "handler bindings incomplete"
      else
        match writeEndpoints coro.regs sid pairs with
        | none => faultPack st coro .outOfRegisters "bad dst reg"
        | some regs' =>
            let endpoints := roles.map (fun r => { sid := sid, role := r })
            let localTypes' := triples.map (fun p => ({ sid := sid, role := p.1 }, p.2.1))
            let sess : SessionState ν :=
              -- V1 binds session scope to the session id.
              { scope := { id := sid }
              , sid := sid
              , roles := roles
              , endpoints := endpoints
              , localTypes := localTypes'
              , traces := initDEnv sid roles
              , buffers := []
              , handlers := handlers
              , epoch := 0
              , phase := .active }
            let coro' := advancePc ({ coro with regs := regs', status := .ready, ownedEndpoints := endpoints ++ coro.ownedEndpoints })
            let st' :=
              { st with nextSessionId := st.nextSessionId + 1, sessions := (sid, sess) :: st.sessions }
            pack coro' st' (mkRes .continue (some (.open sid)))

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
        let updatePhase (s : SessionState ν) : SessionState ν :=
          -- Closing clears buffers and traces while marking the phase.
          { s with phase := .closed, buffers := [], traces := (∅ : DEnv) }
        let rec closeSess (ss : SessionStore ν) : SessionStore ν :=
          match ss with
          | [] => []
          | (sid, s) :: rest =>
              if _h : sid = ep.sid then
                (sid, updatePhase s) :: rest
              else
                (sid, s) :: closeSess rest
        let st' := { st with sessions := closeSess st.sessions }
        let owned' := coro.ownedEndpoints.filter (fun e => decide (e ≠ ep))
        let coro' := advancePc { coro with status := .ready, ownedEndpoints := owned' }
        pack coro' st' (mkRes .continue (some (.close ep.sid)))
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
  let res? : Option (GuardLayer.Resource γ) :=
    match st.guardResources with
    | [] => none
    | (_, r) :: _ => some r
  match res? with
  | none => faultPack st coro (.acquireFault "guard-layer" "unknown layer") "unknown layer"
  | some r =>
      match GuardLayer.open_ r with
      | none => blockPack st coro (.acquireDenied layer)
      | some _ev =>
          match setReg coro.regs dst .unit with
          | none => faultPack st coro .outOfRegisters "bad dst reg"
          | some regs' =>
              let ev := StepEvent.acquire (GuardLayer.layerNs layer)
              continuePack st { coro with regs := regs' } (some ev)

private def stepRelease {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (_layer : γ) (_evidence : Reg) : StepPack ι γ π ε ν :=
  -- Release a guard-layer resource and record the layer.
  let ev := StepEvent.release (GuardLayer.layerNs _layer)
  continuePack st coro (some ev)

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
      let ev := StepEvent.invoke handlerId
      continuePack st { coro with effectCtx := ctx' } (some ev)

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
      pack coro' st (mkRes (.forked gsid) none)
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
  let coro' := advancePc { coro with specState := none }
  pack coro' st (mkRes .joined none)

private def stepAbort {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : StepPack ι γ π ε ν :=
  -- Abort speculation: clear ghost state.
  let coro' := advancePc { coro with specState := none }
  pack coro' st (mkRes .aborted none)

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
        let coros' :=
          if h : tid < st.coroutines.size then
            let cT := st.coroutines[tid]'h
            let cT' := { cT with ownedEndpoints := ep :: cT.ownedEndpoints }
            st.coroutines.set (i := tid) (v := cT') (h := h)
          else
            st.coroutines
        let st' := { st with coroutines := coros' }
        let coro' := advancePc { coro with ownedEndpoints := owned' }
        pack coro' st' (mkRes (.transferred ep tid) (some (.transfer ep coro.id tid)))
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
  | some (.string s) =>
      match setReg coro.regs dst (.bool true) with
      | none => faultPack st coro .outOfRegisters "bad dst reg"
      | some regs' =>
          let know' := s :: coro.knowledgeSet
          let ev := StepEvent.tag s
          continuePack st { coro with regs := regs', knowledgeSet := know' } (some ev)
  | some v =>
      faultPack st coro (.typeViolation .string (valTypeOf v)) "bad fact"
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
  | some (.string s) =>
      let ok := coro.knowledgeSet.any (fun k => k == s)
      let tgtRole : Role :=
        match readReg coro.regs target with
        | some (.string r) => r
        | _ => ""
      match setReg coro.regs dst (.bool ok) with
      | none => faultPack st coro .outOfRegisters "bad dst reg"
      | some regs' =>
          let ev := StepEvent.check tgtRole ok
          continuePack st { coro with regs := regs' } (some ev)
  | some v =>
      faultPack st coro (.typeViolation .string (valTypeOf v)) "bad knowledge"
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
