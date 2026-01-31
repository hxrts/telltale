import Std
import Runtime.VM.TypeClasses
import Runtime.Resources.Arena

/-!
# Task 11: Bytecode VM Definition

Bytecode instruction set, registers, coroutine structure, and single-step
execution from iris_runtime_2.md §3.

## Definitions

- `Reg`, `Addr`, `Imm` — register file types
- `Instr` — full instruction set
- `CodeImage` — instruction array
- `RegFile` — register contents
- `CoroutineState` — pc, registers, stack, status
- `VMState` — coroutines, arena, session store, scheduler state, buffers
- `ExecResult` — step outcomes
- `execInstr` — single instruction execution

Dependencies: Task 10.
-/

set_option autoImplicit false

universe u

/-! ## Core VM scalars -/

abbrev Reg := Nat
abbrev Addr := Nat
abbrev PC := Nat
abbrev CoroutineId := Nat
abbrev Imm := Value

structure Expr where
  cid : CoroutineId
  halted : Bool
  deriving Repr, DecidableEq

/-! ## Bytecode instructions -/

inductive Instr (ε : Type u) [EffectModel ε] where
  -- Communication
  | send (chan val : Reg)
  | recv (chan dst : Reg)
  | offer (chan : Reg) (branches : List (Label × Addr))
  | choose (chan : Reg) (label : Label)

  -- Session lifecycle
  | open (roles : List Role) (types : List LocalType)
      (handlers : List (EffectModel.EffectAction ε)) (dsts : List Reg)
  | close (session : Reg)

  -- Guard/effect layers
  | acquire (layer : Nat) (dst : Reg)
  | release (layer : Nat) (evidence : Reg)
  | invoke (action : EffectModel.EffectAction ε)

  -- Speculation
  | fork (sid : SessionId)
  | join
  | abort

  -- Transfer and knowledge
  | transfer (endpoint : Reg) (targetCoro : Reg) (bundle : Reg)
  | tag (fact : Reg) (dst : Reg)
  | check (knowledge : Reg) (target : Reg) (dst : Reg)

  -- Control
  | loadImm (dst : Reg) (v : Imm)
  | mov (dst src : Reg)
  | jmp (target : PC)
  | spawn (target : PC) (args : List Reg)
  | yield
  | halt

abbrev CodeImage (ε : Type u) [EffectModel ε] := Array (Instr ε)
abbrev RegFile := Array Value

/-! ## Coroutine state -/

structure ProgressToken where
  endpoint : Endpoint
  deriving Repr

abbrev KnowledgeFact := String
abbrev KnowledgeSet := List KnowledgeFact

structure SpeculationState where
  sid : SessionId
  deriving Repr

inductive BlockReason where
  | recvWait (edge : Edge)
  | sendWait (edge : Edge)
  | acquireDenied (layer : Nat)
  | invokeWait (handler : Nat)
  | consensusWait (tag : Nat)
  | spawnWait
  | closeWait (sid : SessionId)
  deriving Repr

inductive Fault where
  | typeViolation (expected actual : ValType)
  | unknownLabel (label : Label)
  | channelClosed (endpoint : Endpoint)
  | acquireFault (layer : Nat) (msg : String)
  | invokeFault (msg : String)
  | transferFault (msg : String)
  | closeFault (msg : String)
  | specFault (msg : String)
  | flowViolation (msg : String)
  | noProgressToken (edge : Edge)
  | outOfRegisters
  deriving Repr

inductive CoroStatus where
  | ready
  | blocked (reason : BlockReason)
  | done
  | faulted (err : Fault)
  | speculating
  deriving Repr

structure CoroutineState (ε : Type u) [EffectModel ε] where
  id : CoroutineId
  pc : PC
  regs : RegFile
  status : CoroStatus
  effectCtx : EffectModel.EffectCtx ε
  ownedEndpoints : List Endpoint
  progressTokens : List ProgressToken
  knowledgeSet : KnowledgeSet
  specState : Option SpeculationState

/-! ## Execution results and events -/

inductive StepEvent where
  | send (edge : Edge) (label : Label) (val : Value)
  | recv (edge : Edge) (label : Label) (val : Value)
  | open (sid : SessionId)
  | close (sid : SessionId)
  | fault (msg : String)
  deriving Repr

inductive ExecStatus where
  | ok
  | yielded
  | blocked
  | halted
  | faulted
  deriving Repr

structure ExecResult where
  status : ExecStatus
  event : Option StepEvent
  deriving Repr

/-! ## VM state -/

structure VMState (ι π ε : Type u) [IdentityModel ι]
    [PersistenceModel π] [EffectModel ε] where
  code : CodeImage ε
  coroutines : Array (CoroutineState ε)
  buffers : List (Edge × List Value)
  persistent : PersistenceModel.PState π
  nextCoroId : CoroutineId
  nextSessionId : SessionId
  arena : Arena
  sessions : SessionStore
  sched : Unit
  obsTrace : List StepEvent

def WFVMState {ι π ε : Type u} [IdentityModel ι]
    [PersistenceModel π] [EffectModel ε] (st : VMState ι π ε) : Prop :=
  (∀ i (h : i < st.coroutines.size),
    (st.coroutines[i]'h).pc < st.code.size) ∧
  (∀ s ∈ st.sessions, s.fst < st.nextSessionId)

/-! ## Single-instruction execution (placeholder) -/

def execInstr {ι π ε : Type u} [IdentityModel ι]
    [PersistenceModel π] [EffectModel ε]
    (st : VMState ι π ε) (coroId : CoroutineId) : VMState ι π ε × ExecResult :=
  let edgeOf (ep : Endpoint) : Edge :=
    { sid := ep.sid, sender := ep.role, receiver := ep.role }
  let rec enqueue (bufs : List (Edge × List Value)) (edge : Edge) (v : Value) :=
    match bufs with
    | [] => [(edge, [v])]
    | (e, vs) :: rest =>
        if _h : e = edge then
          (e, vs ++ [v]) :: rest
        else
          (e, vs) :: enqueue rest edge v
  let rec dequeue (bufs : List (Edge × List Value)) (edge : Edge) :
      Option (Value × List (Edge × List Value)) :=
    match bufs with
    | [] => none
    | (e, vs) :: rest =>
        if _h : e = edge then
          match vs with
          | [] => none
          | v :: vs' => some (v, (e, vs') :: rest)
        else
          match dequeue rest edge with
          | none => none
          | some (v, rest') => some (v, (e, vs) :: rest')
  let appendEvent (st' : VMState ι π ε) (ev : Option StepEvent) : VMState ι π ε :=
    match ev with
    | none => st'
    | some e => { st' with obsTrace := st'.obsTrace ++ [e] }
  let owns (c : CoroutineState ε) (ep : Endpoint) : Bool :=
    c.ownedEndpoints.any (fun e => e == ep)
  let buffersFor (bufs : List (Edge × List Value)) (sid : SessionId) : List (Edge × List Value) :=
    bufs.filter (fun p => decide (p.fst.sid = sid))
  let rec updateSessBuffers (store : SessionStore) (sid : SessionId)
      (bufs : List (Edge × List Value)) : SessionStore :=
    match store with
    | [] => []
    | (sid', s) :: rest =>
        if _h : sid' = sid then
          (sid', { s with buffers := buffersFor bufs sid }) :: rest
        else
          (sid', s) :: updateSessBuffers rest sid bufs
  let getCoro := st.coroutines[coroId]?
  match getCoro with
  | none =>
      (st, { status := .faulted, event := some (.fault "unknown coroutine") })
  | some coro =>
      match coro.status with
      | .done =>
          (st, { status := .halted, event := none })
      | .faulted _err =>
          (st, { status := .faulted, event := some (.fault "faulted coroutine") })
      | _ =>
          match st.code[coro.pc]? with
          | none =>
              let coro' := { coro with status := .faulted (.closeFault "pc out of range") }
              let coros' :=
                if h : coroId < st.coroutines.size then
                  st.coroutines.set (i := coroId) (v := coro') (h := h)
                else
                  st.coroutines
              ( { st with coroutines := coros' }
              , { status := .faulted, event := some (.fault "pc out of range") } )
          | some instr =>
              let advancePc (c : CoroutineState ε) : CoroutineState ε :=
                { c with pc := c.pc + 1 }
              let setReg (regs : RegFile) (r : Reg) (v : Value) : Option RegFile :=
                if h : r < regs.size then
                  some (regs.set (i := r) (v := v) (h := h))
                else
                  none
              let readReg (regs : RegFile) (r : Reg) : Option Value :=
                regs[r]?
              let (coro', res, stBase, ev) :
                  CoroutineState ε × ExecResult × VMState ι π ε × Option StepEvent :=
                match instr with
                | .send chan val =>
                    match readReg coro.regs chan, readReg coro.regs val with
                    | some (.chan ep), some v =>
                        if owns coro ep then
                        let edge := edgeOf ep
                        let bufs' := enqueue st.buffers edge v
                        let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                        (advancePc { coro with status := .ready }, { status := .ok, event := some (.send edge "" v) }, st', some (.send edge "" v))
                        else
                          ( { coro with status := .faulted (.channelClosed ep) }
                          , { status := .faulted, event := some (.fault "endpoint not owned") }
                          , st
                          , some (.fault "endpoint not owned"))
                    | _, _ =>
                        ( { coro with status := .faulted (.channelClosed { sid := 0, role := "" }) }
                        , { status := .faulted, event := some (.fault "bad send operands") }
                        , st
                        , some (.fault "bad send operands"))
                | .recv chan dst =>
                    match readReg coro.regs chan with
                    | some (.chan ep) =>
                        if owns coro ep then
                        let edge := edgeOf ep
                        match dequeue st.buffers edge with
                        | none =>
                            ( { coro with status := .blocked (.recvWait edge) }
                            , { status := .blocked, event := none }
                            , st
                            , none )
                        | some (v, bufs') =>
                            match setReg coro.regs dst v with
                            | none =>
                                ( { coro with status := .faulted .outOfRegisters }
                                , { status := .faulted, event := some (.fault "bad dst reg") }
                                , { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                                , some (.fault "bad dst reg"))
                            | some regs' =>
                                (advancePc { coro with regs := regs', status := .ready }
                                , { status := .ok, event := some (.recv edge "" v) }
                                , { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                                , some (.recv edge "" v))
                        else
                          ( { coro with status := .faulted (.channelClosed ep) }
                          , { status := .faulted, event := some (.fault "endpoint not owned") }
                          , st
                          , some (.fault "endpoint not owned"))
                    | _ =>
                        ( { coro with status := .faulted (.channelClosed { sid := 0, role := "" }) }
                        , { status := .faulted, event := some (.fault "bad recv channel") }
                        , st
                        , some (.fault "bad recv channel"))
                | .offer chan branches =>
                    match readReg coro.regs chan with
                    | some (.chan ep) =>
                        if owns coro ep then
                        let edge := edgeOf ep
                        match dequeue st.buffers edge with
                        | some (.string lbl, bufs') =>
                            match branches.find? (fun b => b.fst == lbl) with
                            | some (_, target) =>
                                ( { coro with pc := target, status := .ready }
                                , { status := .ok, event := some (.recv edge lbl (.string lbl)) }
                                , { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                                , some (.recv edge lbl (.string lbl)))
                            | none =>
                                ( { coro with status := .faulted (.unknownLabel lbl) }
                                , { status := .faulted, event := some (.fault "unknown label") }
                                , { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                                , some (.fault "unknown label"))
                        | _ =>
                            ( { coro with status := .blocked (.recvWait edge) }
                            , { status := .blocked, event := none }
                            , st
                            , none )
                        else
                          ( { coro with status := .faulted (.channelClosed ep) }
                          , { status := .faulted, event := some (.fault "endpoint not owned") }
                          , st
                          , some (.fault "endpoint not owned"))
                    | _ =>
                        ( { coro with status := .faulted (.channelClosed { sid := 0, role := "" }) }
                        , { status := .faulted, event := some (.fault "bad offer channel") }
                        , st
                        , some (.fault "bad offer channel"))
                | .choose chan lbl =>
                    match readReg coro.regs chan with
                    | some (.chan ep) =>
                        if owns coro ep then
                        let edge := edgeOf ep
                        let bufs' := enqueue st.buffers edge (.string lbl)
                        let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
                        (advancePc { coro with status := .ready }
                        , { status := .ok, event := some (.send edge lbl (.string lbl)) }
                        , st'
                        , some (.send edge lbl (.string lbl)))
                        else
                          ( { coro with status := .faulted (.channelClosed ep) }
                          , { status := .faulted, event := some (.fault "endpoint not owned") }
                          , st
                          , some (.fault "endpoint not owned"))
                    | _ =>
                        ( { coro with status := .faulted (.channelClosed { sid := 0, role := "" }) }
                        , { status := .faulted, event := some (.fault "bad choose channel") }
                        , st
                        , some (.fault "bad choose channel"))
                | .open roles types _handlers dsts =>
                    if _hLen : roles.length = types.length ∧ roles.length = dsts.length then
                      let sid := st.nextSessionId
                      let mkEp (r : Role) : Endpoint := { sid := sid, role := r }
                      let rec writeAll (regs : RegFile) (rs : List Role) (ds : List Reg) : Option RegFile :=
                        match rs, ds with
                        | [], [] => some regs
                        | r :: rs', d :: ds' =>
                            match setReg regs d (.chan (mkEp r)) with
                            | none => none
                            | some regs' => writeAll regs' rs' ds'
                        | _, _ => none
                      match writeAll coro.regs roles dsts with
                      | none =>
                          ( { coro with status := .faulted .outOfRegisters }
                          , { status := .faulted, event := some (.fault "bad dst reg") }
                          , st
                          , some (.fault "bad dst reg"))
                      | some regs' =>
                          let endpoints := roles.map mkEp
                          let localTypes := List.zip endpoints types
                          let sess : SessionState :=
                            { endpoints := endpoints
                            , localTypes := localTypes
                            , buffers := []
                            , phase := .active
                            }
                          let coro' :=
                            advancePc
                              { coro with
                                  regs := regs'
                                  status := .ready
                                  ownedEndpoints := endpoints ++ coro.ownedEndpoints
                              }
                          let st' :=
                            { st with
                              nextSessionId := st.nextSessionId + 1
                              sessions := (sid, sess) :: st.sessions
                            }
                          (coro', { status := .ok, event := some (.open sid) }, st', some (.open sid))
                    else
                      ( { coro with status := .faulted (.closeFault "open arity mismatch") }
                      , { status := .faulted, event := some (.fault "open arity mismatch") }
                      , st
                      , some (.fault "open arity mismatch"))
                | .close session =>
                    match readReg coro.regs session with
                    | some (.chan ep) =>
                        if owns coro ep then
                        let updatePhase (s : SessionState) : SessionState :=
                          { s with phase := .closed, buffers := [] }
                        let rec closeSess (ss : SessionStore) : SessionStore :=
                          match ss with
                          | [] => []
                          | (sid, s) :: rest =>
                              if _h : sid = ep.sid then
                                (sid, updatePhase s) :: rest
                              else
                                (sid, s) :: closeSess rest
                        let st' := { st with sessions := closeSess st.sessions }
                        let owned' := coro.ownedEndpoints.filter (fun e => decide (e ≠ ep))
                        (advancePc { coro with status := .ready, ownedEndpoints := owned' }
                        , { status := .ok, event := some (.close ep.sid) }
                        , st'
                        , some (.close ep.sid))
                        else
                          ( { coro with status := .faulted (.closeFault "endpoint not owned") }
                          , { status := .faulted, event := some (.fault "endpoint not owned") }
                          , st
                          , some (.fault "endpoint not owned"))
                    | _ =>
                        ( { coro with status := .faulted (.closeFault "bad close operand") }
                        , { status := .faulted, event := some (.fault "bad close operand") }
                        , st
                        , some (.fault "bad close operand"))
                | .acquire _ dst =>
                    match setReg coro.regs dst (.unit) with
                    | none =>
                        ( { coro with status := .faulted .outOfRegisters }
                        , { status := .faulted, event := some (.fault "bad dst reg") }
                        , st
                        , some (.fault "bad dst reg"))
                    | some regs' =>
                        (advancePc { coro with regs := regs', status := .ready }
                        , { status := .ok, event := none }
                        , st
                        , none)
                | .release _ _ =>
                    (advancePc { coro with status := .ready }
                    , { status := .ok, event := none }
                    , st
                    , none)
                | .invoke action =>
                    let ctx' := EffectModel.exec action coro.effectCtx
                    (advancePc { coro with effectCtx := ctx', status := .ready }
                    , { status := .ok, event := none }
                    , st
                    , none)
                | .fork sid =>
                    (advancePc { coro with specState := some { sid := sid }, status := .ready }
                    , { status := .ok, event := none }
                    , st
                    , none)
                | .join =>
                    (advancePc { coro with specState := none, status := .ready }
                    , { status := .ok, event := none }
                    , st
                    , none)
                | .abort =>
                    (advancePc { coro with specState := none, status := .ready }
                    , { status := .ok, event := none }
                    , st
                    , none)
                | .transfer endpoint targetCoro _ =>
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
                        (advancePc { coro with status := .ready, ownedEndpoints := owned' }
                        , { status := .ok, event := none }
                        , st'
                        , none)
                        else
                          ( { coro with status := .faulted (.transferFault "endpoint not owned") }
                          , { status := .faulted, event := some (.fault "endpoint not owned") }
                          , st
                          , some (.fault "endpoint not owned"))
                    | _, _ =>
                        ( { coro with status := .faulted (.transferFault "bad transfer operands") }
                        , { status := .faulted, event := some (.fault "bad transfer operands") }
                        , st
                        , some (.fault "bad transfer operands"))
                | .tag fact dst =>
                    match readReg coro.regs fact with
                    | some (.string s) =>
                        match setReg coro.regs dst (.bool true) with
                        | none =>
                            ( { coro with status := .faulted .outOfRegisters }
                            , { status := .faulted, event := some (.fault "bad dst reg") }
                            , st
                            , some (.fault "bad dst reg"))
                        | some regs' =>
                            let know' := s :: coro.knowledgeSet
                            (advancePc { coro with regs := regs', status := .ready, knowledgeSet := know' }
                            , { status := .ok, event := none }
                            , st
                            , none)
                    | _ =>
                        ( { coro with status := .faulted (.flowViolation "bad fact") }
                        , { status := .faulted, event := some (.fault "bad fact") }
                        , st
                        , some (.fault "bad fact"))
                | .check knowledge _ dst =>
                    match readReg coro.regs knowledge with
                    | some (.string s) =>
                        let ok := coro.knowledgeSet.any (fun k => k == s)
                        match setReg coro.regs dst (.bool ok) with
                        | none =>
                            ( { coro with status := .faulted .outOfRegisters }
                            , { status := .faulted, event := some (.fault "bad dst reg") }
                            , st
                            , some (.fault "bad dst reg"))
                        | some regs' =>
                            (advancePc { coro with regs := regs', status := .ready }
                            , { status := .ok, event := none }
                            , st
                            , none)
                    | _ =>
                        ( { coro with status := .faulted (.flowViolation "bad knowledge") }
                        , { status := .faulted, event := some (.fault "bad knowledge") }
                        , st
                        , some (.fault "bad knowledge"))
                | .spawn target args =>
                    let newId := st.nextCoroId
                    let initRegs : RegFile := Array.mk (List.replicate coro.regs.size Value.unit)
                    let rec copyArgs (idx : Nat) (regs : RegFile) (args : List Reg) : RegFile :=
                      match args with
                      | [] => regs
                      | r :: rs =>
                          match readReg coro.regs r with
                          | none => regs
                          | some v =>
                              if h : idx < regs.size then
                                copyArgs (idx + 1) (regs.set (i := idx) (v := v) (h := h)) rs
                              else
                                regs
                    let newRegs := copyArgs 0 initRegs args
                    let newCoro : CoroutineState ε :=
                      { id := newId
                      , pc := target
                      , regs := newRegs
                      , status := .ready
                      , effectCtx := coro.effectCtx
                      , ownedEndpoints := []
                      , progressTokens := []
                      , knowledgeSet := []
                      , specState := none
                      }
                    let coros' := st.coroutines.push newCoro
                    let st' := { st with coroutines := coros', nextCoroId := newId + 1 }
                    (advancePc { coro with status := .ready }
                    , { status := .ok, event := none }
                    , st'
                    , none)
                | .loadImm dst v =>
                    match setReg coro.regs dst v with
                    | some regs' =>
                        (advancePc { coro with regs := regs', status := .ready }
                        , { status := .ok, event := none }
                        , st
                        , none)
                    | none =>
                        ( { coro with status := .faulted .outOfRegisters }
                        , { status := .faulted, event := some (.fault "out of registers") }
                        , st
                        , some (.fault "out of registers"))
                | .mov dst src =>
                    match readReg coro.regs src with
                    | none =>
                        ( { coro with status := .faulted .outOfRegisters }
                        , { status := .faulted, event := some (.fault "bad src reg") }
                        , st
                        , some (.fault "bad src reg"))
                    | some v =>
                        match setReg coro.regs dst v with
                        | none =>
                            ( { coro with status := .faulted .outOfRegisters }
                            , { status := .faulted, event := some (.fault "bad dst reg") }
                            , st
                            , some (.fault "bad dst reg"))
                        | some regs' =>
                            (advancePc { coro with regs := regs', status := .ready }
                            , { status := .ok, event := none }
                            , st
                            , none)
                | .jmp target =>
                    ( { coro with pc := target, status := .ready }
                    , { status := .ok, event := none }
                    , st
                    , none)
                | .yield =>
                    (advancePc { coro with status := .blocked .spawnWait }
                    , { status := .yielded, event := none }
                    , st
                    , none)
                | .halt =>
                    (advancePc { coro with status := .done }
                    , { status := .halted, event := none }
                    , st
                    , none)
              let coros' :=
                if h : coroId < stBase.coroutines.size then
                  stBase.coroutines.set (i := coroId) (v := coro') (h := h)
                else
                  stBase.coroutines
              let st' := { stBase with coroutines := coros' }
              ( appendEvent st' ev, res )
