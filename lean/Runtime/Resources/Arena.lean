import Protocol.Environments.Core
import Batteries.Data.RBMap
import Batteries.Data.RBMap.Lemmas
import Runtime.VM.TypeClasses
import Runtime.VM.Core
import Runtime.Resources.BufferRA

/-!
# Task 15: Arena and Session Store

Physical backing model for session state from iris_runtime_2.md §5.3–5.5.

## Definitions

- `Arena` — contiguous memory region with typed slots
- `ArenaSlot` — tagged union of value types
- `SessionState` — per-session metadata
- `SessionStore` — map from SessionId to SessionState
- `SessionPhase` — opening, active, closing, closed
- `sessionStore_refines_envs`
- `arena_lookup_typed`

Dependencies: Task 10, Shim.ResourceAlgebra.
-/

set_option autoImplicit false

universe u

inductive SessionPhase where
  | opening
  | active
  | closing
  | closed
  deriving Repr

inductive Slot where
  -- Tagged arena slots for runtime backing.
  | value (v : Value)
  | localType (t : LocalType)
  | buffer (buf : BoundedBuffer)
  | free
  deriving Repr

structure Arena where
  -- Arena storage with a simple bump allocator.
  slots : Array Slot -- Concrete slot storage.
  nextFree : Addr -- Bump allocator cursor.
  capacity : Nat -- Maximum number of slots.
  inv : nextFree ≤ capacity -- Capacity invariant.
  deriving Repr

def Arena.alloc (a : Arena) (s : Slot) : Option (Arena × Addr) :=
  -- Allocate the next free slot when within capacity.
  if hcap : a.nextFree < a.capacity then
    let idx := a.nextFree
    let slots' :=
      if hidx : idx < a.slots.size then
        a.slots.set (i := idx) (v := s) (h := hidx)
      else
        a.slots.push s
    -- Preserve the capacity invariant after bumping the cursor.
    let hInv : idx + 1 ≤ a.capacity := Nat.succ_le_of_lt hcap
    let a' := { a with slots := slots', nextFree := idx + 1, inv := hInv }
    some (a', idx)
  else
    none

def Arena.read (a : Arena) (addr : Addr) : Option Slot :=
  -- Read a slot when the address is in bounds.
  a.slots[addr]?

def Arena.write (a : Arena) (addr : Addr) (s : Slot) : Option Arena :=
  -- Overwrite a slot when the address is in bounds.
  if h : addr < a.slots.size then
    some { a with slots := a.slots.set (i := addr) (v := s) (h := h) }
  else
    none

def Arena.free (a : Arena) (addr : Addr) : Arena :=
  -- Mark a slot as free when the address is in bounds.
  if h : addr < a.slots.size then
    { a with slots := a.slots.set (i := addr) (v := .free) (h := h) }
  else
    a

structure SessionState (ν : Type u) [VerificationModel ν] where
  -- Scope for resource commitments and nullifiers.
  scope : ScopeId -- Local resource scope.
  sid : SessionId -- Session identifier.
  roles : RoleSet -- Participating roles.
  endpoints : List Endpoint -- Allocated endpoints.
  localTypes : List (Endpoint × LocalType) -- Endpoint types (GEnv slice).
  traces : DEnv -- In-flight type traces (DEnv slice).
  buffers : SignedBuffers ν -- In-memory signed buffers.
  handlers : List (Edge × HandlerId) -- Handler bindings per edge.
  epoch : Nat -- Epoch tag for rotation.
  phase : SessionPhase -- Lifecycle status.

abbrev SessionStore (ν : Type u) [VerificationModel ν] :=
  List (SessionId × SessionState ν)

/-! ## Session environment projections -/

def SessionState.lookupType {ν : Type u} [VerificationModel ν]
    (st : SessionState ν) (e : Endpoint) : Option LocalType :=
  -- Lookup a local type in this session's endpoint map.
  st.localTypes.lookup e

def SessionState.lookupTrace {ν : Type u} [VerificationModel ν]
    (st : SessionState ν) (edge : Edge) : List ValType :=
  -- Lookup a type trace in this session's DEnv slice.
  lookupD st.traces edge

def SessionState.updateType {ν : Type u} [VerificationModel ν]
    (st : SessionState ν) (e : Endpoint) (L : LocalType) : SessionState ν :=
  -- Update the local type map for an endpoint.
  { st with localTypes := updateG st.localTypes e L }

def SessionState.updateTrace {ν : Type u} [VerificationModel ν]
    (st : SessionState ν) (edge : Edge) (ts : List ValType) : SessionState ν :=
  -- Update the type trace for an edge.
  { st with traces := updateD st.traces edge ts }

def SignedBuffer.payloads {ν : Type u} [VerificationModel ν]
    (buf : SignedBuffer ν) : Buffer :=
  -- Strip signatures to recover payload buffers.
  buf.map (fun sv => sv.payload)

def SignedBuffers.payloads {ν : Type u} [VerificationModel ν]
    (bufs : SignedBuffers ν) : Buffers :=
  -- Strip signatures across all edge buffers.
  bufs.map (fun p => (p.fst, SignedBuffer.payloads p.snd))

def SessionState.lookupBuffer {ν : Type u} [VerificationModel ν]
    (st : SessionState ν) (edge : Edge) : Buffer :=
  -- Lookup a buffer and project to payloads.
  lookupBuf (SignedBuffers.payloads st.buffers) edge

def SessionState.lookupHandler {ν : Type u} [VerificationModel ν]
    (st : SessionState ν) (edge : Edge) : Option HandlerId :=
  -- Lookup the handler bound to a given edge.
  st.handlers.lookup edge

@[simp] theorem SessionState.lookupBuffer_updateType {ν : Type u} [VerificationModel ν]
    (st : SessionState ν) (e : Endpoint) (L : LocalType) (edge : Edge) :
    (st.updateType e L).lookupBuffer edge = st.lookupBuffer edge := by
  simp [SessionState.updateType, SessionState.lookupBuffer]

@[simp] theorem SessionState.lookupBuffer_updateTrace {ν : Type u} [VerificationModel ν]
    (st : SessionState ν) (edge : Edge) (ts : List ValType) (edge' : Edge) :
    (st.updateTrace edge ts).lookupBuffer edge' = st.lookupBuffer edge' := by
  simp [SessionState.updateTrace, SessionState.lookupBuffer]

def SessionStore.lookupType {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) (e : Endpoint) : Option LocalType :=
  -- Find the matching session and then its local type.
  match store with
  | [] => none
  | (sid, st) :: rest =>
      if _h : sid = e.sid then
        st.lookupType e
      else
        SessionStore.lookupType rest e

def SessionStore.lookupTrace {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) (edge : Edge) : List ValType :=
  -- Find the matching session and then its trace.
  match store with
  | [] => []
  | (sid, st) :: rest =>
      if _h : sid = edge.sid then
        st.lookupTrace edge
      else
        SessionStore.lookupTrace rest edge

def SessionStore.lookupBuffer {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) (edge : Edge) : Buffer :=
  -- Find the matching session and then its buffer.
  match store with
  | [] => []
  | (sid, st) :: rest =>
      if _h : sid = edge.sid then
        st.lookupBuffer edge
      else
        SessionStore.lookupBuffer rest edge

def SessionStore.lookupHandler {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) (edge : Edge) : Option HandlerId :=
  -- Find the matching session and then its handler binding.
  match store with
  | [] => none
  | (sid, st) :: rest =>
      if _h : sid = edge.sid then
        st.lookupHandler edge
      else
        SessionStore.lookupHandler rest edge

def SessionStore.updateType {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) (e : Endpoint) (L : LocalType) : SessionStore ν :=
  -- Update the local type for the endpoint in its session.
  match store with
  | [] => []
  | (sid, st) :: rest =>
      if sid = e.sid then
        (sid, st.updateType e L) :: rest
      else
        (sid, st) :: SessionStore.updateType rest e L

def SessionStore.updateTrace {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) (edge : Edge) (ts : List ValType) : SessionStore ν :=
  -- Update the trace for the edge in its session.
  match store with
  | [] => []
  | (sid, st) :: rest =>
      if sid = edge.sid then
        (sid, st.updateTrace edge ts) :: rest
      else
        (sid, st) :: SessionStore.updateTrace rest edge ts

def SessionStore.defaultHandler {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) : Option HandlerId :=
  -- Pick any handler id from the active session store.
  match store with
  | [] => none
  | (_, st) :: rest =>
      match st.handlers with
      | [] => SessionStore.defaultHandler rest
      | (_, h) :: _ => some h

def SessionStore.toGEnv {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) : GEnv :=
  -- Flatten per-session local types into a single GEnv.
  store.foldl (fun acc p => acc ++ p.snd.localTypes) []

def SessionStore.toDEnv {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) : DEnv :=
  -- Union per-session DEnv slices (left-biased on conflicts).
  store.foldl (fun acc p => acc ++ p.snd.traces) (∅ : DEnv)

def SessionStore.toBuffers {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) : Buffers :=
  -- Flatten and project signed buffers into payload buffers.
  store.foldl (fun acc p => acc ++ SignedBuffers.payloads p.snd.buffers) []

def sessionStore_refines_envs {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) : Prop :=
  -- Store lookups agree with the corresponding environment projections.
  let G := store.toGEnv
  let D := store.toDEnv
  let bufs := store.toBuffers
  (∀ sid st, (sid, st) ∈ store →
    st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid)) ∧
  (∀ e, lookupG G e = SessionStore.lookupType store e) ∧
  (∀ edge, lookupD D edge = SessionStore.lookupTrace store edge) ∧
  (∀ edge, lookupBuf bufs edge = SessionStore.lookupBuffer store edge)

def arena_lookup_typed (arena : Arena) (idx : Addr) (slot : Slot) : Prop :=
  -- Typed lookup means the slot exists and is not free.
  arena.read idx = some slot ∧ slot ≠ .free

def arena_lookup_value (arena : Arena) (idx : Addr) (v : Value) : Prop :=
  -- Value slot lookup.
  arena_lookup_typed arena idx (.value v)

def arena_lookup_buffer (arena : Arena) (idx : Addr) (buf : BoundedBuffer) : Prop :=
  -- Buffer slot lookup.
  arena_lookup_typed arena idx (.buffer buf)

def arena_lookup_localType (arena : Arena) (idx : Addr) (t : LocalType) : Prop :=
  -- Local type slot lookup.
  arena_lookup_typed arena idx (.localType t)

/-! ## SessionStore Update/Lookup Lemmas -/

variable {ν : Type u} [VerificationModel ν]

/-! ### SessionState-level lemmas -/

@[simp] theorem SessionState.lookupType_updateType_eq {st : SessionState ν} {e : Endpoint} {L : LocalType} :
    (st.updateType e L).lookupType e = some L := by
  simpa [SessionState.updateType, SessionState.lookupType, lookupG] using
    (lookupG_updateG_eq (env := st.localTypes) (e := e) (L := L))

theorem SessionState.lookupType_updateType_ne {st : SessionState ν} {e e' : Endpoint} {L : LocalType}
    (hne : e' ≠ e) :
    (st.updateType e L).lookupType e' = st.lookupType e' := by
  simpa [SessionState.updateType, SessionState.lookupType, lookupG] using
    (lookupG_updateG_ne (env := st.localTypes) (e := e) (e' := e') (L := L) hne)

@[simp] theorem SessionState.lookupTrace_updateTrace_eq {st : SessionState ν} {edge : Edge} {ts : List ValType} :
    (st.updateTrace edge ts).lookupTrace edge = ts := by
  simp only [SessionState.updateTrace, SessionState.lookupTrace, lookupD_update_eq]

theorem SessionState.lookupTrace_updateTrace_ne {st : SessionState ν} {edge edge' : Edge} {ts : List ValType}
    (hne : edge' ≠ edge) :
    (st.updateTrace edge ts).lookupTrace edge' = st.lookupTrace edge' := by
  simpa [SessionState.updateTrace, SessionState.lookupTrace] using
    (lookupD_update_neq (env := st.traces) (e := edge) (e' := edge') (ts := ts) (Ne.symm hne))

-- Type update doesn't affect traces
@[simp] theorem SessionState.lookupTrace_updateType {st : SessionState ν} {e : Endpoint} {L : LocalType} {edge : Edge} :
    (st.updateType e L).lookupTrace edge = st.lookupTrace edge := by
  simp only [SessionState.updateType, SessionState.lookupTrace]

-- Trace update doesn't affect types
@[simp] theorem SessionState.lookupType_updateTrace {st : SessionState ν} {edge : Edge} {ts : List ValType} {e : Endpoint} :
    (st.updateTrace edge ts).lookupType e = st.lookupType e := by
  simp only [SessionState.updateTrace, SessionState.lookupType]

/-! ### SessionStore-level lemmas -/

/-- Helper: find the session containing an endpoint. -/
def SessionStore.findSession (store : SessionStore ν) (sid : SessionId) : Option (SessionState ν) :=
  match store with
  | [] => none
  | (sid', st) :: rest =>
      if sid' = sid then some st
      else SessionStore.findSession rest sid

/-- Updating type at endpoint e, then looking up e, gives the new type. -/
@[simp] theorem SessionStore.lookupType_updateType_eq {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (hMem : ∃ st, (e.sid, st) ∈ store) :
    SessionStore.lookupType (store.updateType e L) e = some L := by
  induction store with
  | nil => simp at hMem
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = e.sid
    · simp [SessionStore.updateType, SessionStore.lookupType, hsid,
        SessionState.lookupType_updateType_eq]
    · have hMem' : ∃ st, (e.sid, st) ∈ tl := by
        obtain ⟨st', hst'⟩ := hMem
        cases hst' with
        | head =>
            cases hsid rfl
        | tail _ htl =>
            exact ⟨st', htl⟩
      simp [SessionStore.updateType, SessionStore.lookupType, hsid]
      exact ih hMem'

/-- Updating type at endpoint e doesn't affect lookups at other endpoints. -/
theorem SessionStore.lookupType_updateType_ne {store : SessionStore ν} {e e' : Endpoint} {L : LocalType}
    (hne : e' ≠ e) :
    SessionStore.lookupType (store.updateType e L) e' = SessionStore.lookupType store e' := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = e.sid
    · by_cases hsid' : sid = e'.sid
      · simp [SessionStore.updateType, SessionStore.lookupType, hsid,
          SessionState.lookupType_updateType_ne hne]
      · have hsid_ne : e.sid ≠ e'.sid := by
          simpa [hsid] using hsid'
        simp [SessionStore.updateType, SessionStore.lookupType, hsid, hsid_ne]
    · by_cases hsid' : sid = e'.sid
      · have hsid_ne : e'.sid ≠ e.sid := by
          simpa [hsid'] using hsid
        simp [SessionStore.updateType, SessionStore.lookupType, hsid', hsid_ne]
      · simp [SessionStore.updateType, SessionStore.lookupType, hsid, hsid', ih]

/-- Updating type at endpoint doesn't affect trace lookups. -/
@[simp] theorem SessionStore.lookupTrace_updateType {store : SessionStore ν} {e : Endpoint} {L : LocalType} {edge : Edge} :
    SessionStore.lookupTrace (store.updateType e L) edge = SessionStore.lookupTrace store edge := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = e.sid
    · by_cases hsid_edge : sid = edge.sid
      · have heq : edge.sid = e.sid := by
          calc
            edge.sid = sid := hsid_edge.symm
            _ = e.sid := hsid
        simp [SessionStore.updateType, SessionStore.lookupTrace, hsid, heq,
          SessionState.lookupTrace_updateType]
      · have hsid_ne : edge.sid ≠ e.sid := by
          intro h
          apply hsid_edge
          calc
            sid = e.sid := hsid
            _ = edge.sid := h.symm
        simp [SessionStore.updateType, SessionStore.lookupTrace, hsid]
    · by_cases hsid_edge : sid = edge.sid
      · have hsid_ne : edge.sid ≠ e.sid := by
          intro h
          apply hsid
          calc
            sid = edge.sid := hsid_edge
            _ = e.sid := h
        simp [SessionStore.updateType, SessionStore.lookupTrace, hsid_edge, hsid_ne]
      · simp [SessionStore.updateType, SessionStore.lookupTrace, hsid, hsid_edge, ih]

/-- Updating trace at edge, then looking up that edge, gives the new trace. -/
@[simp] theorem SessionStore.lookupTrace_updateTrace_eq {store : SessionStore ν} {edge : Edge} {ts : List ValType}
    (hMem : ∃ st, (edge.sid, st) ∈ store) :
    SessionStore.lookupTrace (store.updateTrace edge ts) edge = ts := by
  induction store with
  | nil => simp at hMem
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = edge.sid
    · simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid,
        SessionState.lookupTrace_updateTrace_eq]
    · have hMem' : ∃ st, (edge.sid, st) ∈ tl := by
        obtain ⟨st', hst'⟩ := hMem
        cases hst' with
        | head =>
            cases hsid rfl
        | tail _ htl =>
            exact ⟨st', htl⟩
      simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid]
      exact ih hMem'

/-- Updating trace at edge doesn't affect lookups at other edges. -/
theorem SessionStore.lookupTrace_updateTrace_ne {store : SessionStore ν} {edge edge' : Edge} {ts : List ValType}
    (hne : edge' ≠ edge) :
    SessionStore.lookupTrace (store.updateTrace edge ts) edge' = SessionStore.lookupTrace store edge' := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = edge.sid
    · by_cases hsid' : sid = edge'.sid
      · simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid,
          SessionState.lookupTrace_updateTrace_ne hne]
      · have hsid_ne : edge.sid ≠ edge'.sid := by
          simpa [hsid] using hsid'
        simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid, hsid_ne]
    · by_cases hsid' : sid = edge'.sid
      · have hsid_ne : edge'.sid ≠ edge.sid := by
          simpa [hsid'] using hsid
        simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid', hsid_ne]
      · simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid, hsid', ih]

/-- Updating trace doesn't affect type lookups. -/
@[simp] theorem SessionStore.lookupType_updateTrace {store : SessionStore ν} {edge : Edge} {ts : List ValType} {e : Endpoint} :
    SessionStore.lookupType (store.updateTrace edge ts) e = SessionStore.lookupType store e := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid_edge : sid = edge.sid
    · by_cases hsid_e : sid = e.sid
      · simp [SessionStore.updateTrace, SessionStore.lookupType, hsid_edge,
          SessionState.lookupType_updateTrace]
      · have hsid_ne : e.sid ≠ edge.sid := by
          intro h
          apply hsid_e
          calc
            sid = edge.sid := hsid_edge
            _ = e.sid := h.symm
        simp [SessionStore.updateTrace, SessionStore.lookupType, hsid_edge]
    · by_cases hsid_e : sid = e.sid
      · have hsid_ne : e.sid ≠ edge.sid := by
          intro h
          apply hsid_edge
          calc
            sid = e.sid := hsid_e
            _ = edge.sid := h
        simp [SessionStore.updateTrace, SessionStore.lookupType, hsid_e, hsid_ne]
      · simp [SessionStore.updateTrace, SessionStore.lookupType, hsid_edge, hsid_e, ih]

/-- Updating type doesn't affect buffer lookups. -/
@[simp] theorem SessionStore.lookupBuffer_updateType {store : SessionStore ν} {e : Endpoint} {L : LocalType} {edge : Edge} :
    SessionStore.lookupBuffer (store.updateType e L) edge = SessionStore.lookupBuffer store edge := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = e.sid
    · by_cases hsid_edge : sid = edge.sid
      · have heq : e.sid = edge.sid := by
          calc
            e.sid = sid := hsid.symm
            _ = edge.sid := hsid_edge
        simp [SessionStore.updateType, SessionStore.lookupBuffer, hsid, heq,
          SessionState.updateType, SessionState.lookupBuffer]
      · have hsid_ne : e.sid ≠ edge.sid := by
          intro h
          apply hsid_edge
          calc
            sid = e.sid := hsid
            _ = edge.sid := h
        simp [SessionStore.updateType, SessionStore.lookupBuffer, hsid, hsid_ne]
    · by_cases hsid_edge : sid = edge.sid
      · have hsid_ne : edge.sid ≠ e.sid := by
          intro h
          apply hsid
          calc
            sid = edge.sid := hsid_edge
            _ = e.sid := h
        simp [SessionStore.updateType, SessionStore.lookupBuffer, hsid_edge, hsid_ne]
      · simp [SessionStore.updateType, SessionStore.lookupBuffer, hsid, hsid_edge, ih]

/-- Updating trace doesn't affect buffer lookups. -/
@[simp] theorem SessionStore.lookupBuffer_updateTrace {store : SessionStore ν} {edge : Edge} {ts : List ValType} {edge' : Edge} :
    SessionStore.lookupBuffer (store.updateTrace edge ts) edge' = SessionStore.lookupBuffer store edge' := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = edge.sid
    · by_cases hsid_edge : sid = edge'.sid
      · have heq : edge.sid = edge'.sid := by
          calc
            edge.sid = sid := hsid.symm
            _ = edge'.sid := hsid_edge
        simp [SessionStore.updateTrace, SessionStore.lookupBuffer, hsid, heq,
          SessionState.updateTrace, SessionState.lookupBuffer]
      · have hsid_ne : edge.sid ≠ edge'.sid := by
          intro h
          apply hsid_edge
          calc
            sid = edge.sid := hsid
            _ = edge'.sid := h
        simp [SessionStore.updateTrace, SessionStore.lookupBuffer, hsid, hsid_ne]
    · by_cases hsid_edge : sid = edge'.sid
      · have hsid_ne : edge'.sid ≠ edge.sid := by
          intro h
          apply hsid
          calc
            sid = edge'.sid := hsid_edge
            _ = edge.sid := h
        simp [SessionStore.updateTrace, SessionStore.lookupBuffer, hsid_edge, hsid_ne]
      · simp [SessionStore.updateTrace, SessionStore.lookupBuffer, hsid, hsid_edge, ih]

/-! ### Session consistency predicates -/

/-- A session state is consistent if all endpoints in localTypes have the session's sid,
    and all edges in traces have the session's sid. -/
def SessionState.consistent {ν : Type u} [VerificationModel ν] (st : SessionState ν) : Prop :=
  (∀ e L, (e, L) ∈ st.localTypes → e.sid = st.sid) ∧
  (∀ edge, st.traces.find? edge ≠ none → edge.sid = st.sid)

/-- A session store is consistent if all sessions are consistent and keyed correctly. -/
def SessionStore.consistent {ν : Type u} [VerificationModel ν] (store : SessionStore ν) : Prop :=
  ∀ sid st, (sid, st) ∈ store → st.sid = sid ∧ st.consistent

/-- If a session state is consistent and an endpoint has different sid, it's not in localTypes. -/
theorem SessionState.lookupG_none_of_sid_ne {st : SessionState ν} {e : Endpoint}
    (hCons : st.consistent) (hne : e.sid ≠ st.sid) :
    lookupG st.localTypes e = none := by
  by_contra h
  push_neg at h
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp (Option.ne_none_iff_isSome.mp h)
  have hMem := lookupG_mem st.localTypes e L hL
  have hEq := hCons.1 e L hMem
  exact hne hEq

/-- If a session state is consistent and an edge has different sid, it's not in traces. -/
theorem SessionState.traces_find?_none_of_sid_ne {st : SessionState ν} {edge : Edge}
    (hCons : st.consistent) (hne : edge.sid ≠ st.sid) :
    st.traces.find? edge = none := by
  by_contra h
  have hEq := hCons.2 edge h
  exact hne hEq

/-! Helper lemmas for DEnv updates. -/

private theorem DEnv_find?_updateD_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    (updateD env e ts).find? e' = env.find? e' := by
  have hne' : compare e' e ≠ .eq := by
    intro hEq
    exact hne ((Edge.compare_eq_iff_eq e' e).1 hEq).symm
  have hfind :=
    Batteries.RBMap.find?_insert_of_ne (t := env.map) (k := e) (v := ts) (k' := e') hne'
  calc
    (updateD env e ts).find? e'
        = (DEnv.ofMap (env.map.insert e ts)).find? e' := by
            rfl
    _ = (env.map.insert e ts).find? e' := by
            simp
    _ = env.map.find? e' := hfind
    _ = env.find? e' := by
            rfl

/-- updateType preserves session consistency. -/
theorem SessionState.updateType_preserves_consistent {st : SessionState ν} {e : Endpoint} {L : LocalType}
    (hCons : st.consistent) (hSid : e.sid = st.sid) :
    (st.updateType e L).consistent := by
  constructor
  · intro e' L' hMem
    simp only [SessionState.updateType] at hMem
    cases updateG_mem_of st.localTypes e L e' L' hMem with
    | inl heq => exact heq.1 ▸ hSid
    | inr hmem => exact hCons.1 e' L' hmem
  · intro edge h
    simp only [SessionState.updateType] at h
    exact hCons.2 edge h

/-- updateTrace preserves session consistency. -/
theorem SessionState.updateTrace_preserves_consistent {st : SessionState ν} {edge : Edge} {ts : List ValType}
    (hCons : st.consistent) (hSid : edge.sid = st.sid) :
    (st.updateTrace edge ts).consistent := by
  constructor
  · intro e L hMem
    simp only [SessionState.updateTrace] at hMem
    exact hCons.1 e L hMem
  · intro edge' h
    simp only [SessionState.updateTrace] at h
    by_cases he : edge' = edge
    · exact he ▸ hSid
    · -- edge' ≠ edge, so find? is unchanged
      have hNe : edge ≠ edge' := Ne.symm he
      have hEq := DEnv_find?_updateD_neq (env := st.traces) (e := edge) (e' := edge') (ts := ts) hNe
      have hOrig : st.traces.find? edge' ≠ none := by
        intro hnone
        apply h
        simp [hEq, hnone]
      exact hCons.2 edge' hOrig

/-- SessionState.updateType preserves sid field. -/
@[simp] theorem SessionState.updateType_sid {st : SessionState ν} {e : Endpoint} {L : LocalType} :
    (st.updateType e L).sid = st.sid := rfl

/-- SessionState.updateTrace preserves sid field. -/
@[simp] theorem SessionState.updateTrace_sid {st : SessionState ν} {edge : Edge} {ts : List ValType} :
    (st.updateTrace edge ts).sid = st.sid := rfl

/-- SessionStore.updateType preserves store consistency. -/
theorem SessionStore.updateType_preserves_consistent {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (hCons : store.consistent)
    (hMem : ∃ st, (e.sid, st) ∈ store) :
    (store.updateType e L).consistent := by
  intro sid st hMemUpdated
  induction store with
  | nil => simp [SessionStore.updateType] at hMemUpdated
  | cons hd tl ih =>
    obtain ⟨sid', st'⟩ := hd
    simp only [SessionStore.updateType] at hMemUpdated
    by_cases hsid : sid' = e.sid
    · -- Found the session to update
      simp only [hsid, ↓reduceIte] at hMemUpdated
      -- After simp: hMemUpdated : (sid, st) ∈ (e.sid, st'.updateType e L) :: updateType tl e L
      simp only [List.mem_cons] at hMemUpdated
      cases hMemUpdated with
      | inl heq =>
        -- head case: (sid, st) = (e.sid, st'.updateType e L)
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hsid_eq, hst_eq⟩ := heq
        have hOrigCons := hCons sid' st' (List.Mem.head _)
        constructor
        · -- st.sid = sid
          rw [hst_eq, hsid_eq]
          simp [hOrigCons.1, hsid]
        · -- st.consistent
          rw [hst_eq]
          have hSidEq : e.sid = st'.sid := by
            rw [← hsid]
            exact hOrigCons.1.symm
          exact SessionState.updateType_preserves_consistent hOrigCons.2 hSidEq
      | inr hmem =>
        -- tail case: (sid, st) ∈ tl
        have hTlCons : SessionStore.consistent tl := fun sid'' st'' h =>
          hCons sid'' st'' (List.Mem.tail _ h)
        exact hTlCons sid st hmem
    · -- Not the session to update
      simp only [hsid, ↓reduceIte] at hMemUpdated
      -- After simp: hMemUpdated : (sid, st) ∈ (sid', st') :: updateType tl e L
      simp only [List.mem_cons] at hMemUpdated
      cases hMemUpdated with
      | inl heq =>
        -- head case: (sid, st) = (sid', st')
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hsid_eq, hst_eq⟩ := heq
        have hOrigCons := hCons sid' st' (List.Mem.head _)
        constructor
        · rw [hst_eq, hsid_eq]; exact hOrigCons.1
        · rw [hst_eq]; exact hOrigCons.2
      | inr hmem =>
        -- tail case: recurse
        have hTlCons : SessionStore.consistent tl := fun sid'' st'' h =>
          hCons sid'' st'' (List.Mem.tail _ h)
        have hTlMem : ∃ st, (e.sid, st) ∈ tl := by
          obtain ⟨st'', hst''⟩ := hMem
          simp only [List.mem_cons] at hst''
          cases hst'' with
          | inl heq =>
            simp only [Prod.mk.injEq] at heq
            exact absurd heq.1 hsid
          | inr hmem' => exact ⟨st'', hmem'⟩
        exact ih hTlCons hTlMem hmem

/-- SessionStore.updateTrace preserves store consistency. -/
theorem SessionStore.updateTrace_preserves_consistent {store : SessionStore ν} {edge : Edge} {ts : List ValType}
    (hCons : store.consistent)
    (hMem : ∃ st, (edge.sid, st) ∈ store) :
    (store.updateTrace edge ts).consistent := by
  intro sid st hMemUpdated
  induction store with
  | nil => simp [SessionStore.updateTrace] at hMemUpdated
  | cons hd tl ih =>
    obtain ⟨sid', st'⟩ := hd
    simp only [SessionStore.updateTrace] at hMemUpdated
    by_cases hsid : sid' = edge.sid
    · -- Found the session to update
      simp only [hsid, ↓reduceIte] at hMemUpdated
      simp only [List.mem_cons] at hMemUpdated
      cases hMemUpdated with
      | inl heq =>
        -- head case
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hsid_eq, hst_eq⟩ := heq
        have hOrigCons := hCons sid' st' (List.Mem.head _)
        constructor
        · rw [hst_eq, hsid_eq]
          simp [hOrigCons.1, hsid]
        · rw [hst_eq]
          have hSidEq : edge.sid = st'.sid := by
            rw [← hsid]
            exact hOrigCons.1.symm
          exact SessionState.updateTrace_preserves_consistent hOrigCons.2 hSidEq
      | inr hmem =>
        -- tail case
        have hTlCons : SessionStore.consistent tl := fun sid'' st'' h =>
          hCons sid'' st'' (List.Mem.tail _ h)
        exact hTlCons sid st hmem
    · -- Not the session to update
      simp only [hsid, ↓reduceIte] at hMemUpdated
      simp only [List.mem_cons] at hMemUpdated
      cases hMemUpdated with
      | inl heq =>
        -- head case
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hsid_eq, hst_eq⟩ := heq
        have hOrigCons := hCons sid' st' (List.Mem.head _)
        constructor
        · rw [hst_eq, hsid_eq]; exact hOrigCons.1
        · rw [hst_eq]; exact hOrigCons.2
      | inr hmem =>
        -- tail case
        have hTlCons : SessionStore.consistent tl := fun sid'' st'' h =>
          hCons sid'' st'' (List.Mem.tail _ h)
        have hTlMem : ∃ st, (edge.sid, st) ∈ tl := by
          obtain ⟨st'', hst''⟩ := hMem
          simp only [List.mem_cons] at hst''
          cases hst'' with
          | inl heq =>
            simp only [Prod.mk.injEq] at heq
            exact absurd heq.1 hsid
          | inr hmem' => exact ⟨st'', hmem'⟩
        exact ih hTlCons hTlMem hmem

/-! ### toGEnv/toDEnv under updates -/

/-- Helper: DEnv append distributes over foldl. -/
private theorem DEnv_foldl_append_comm {ν : Type u} [VerificationModel ν]
    (D : DEnv) (store : SessionStore ν) :
    List.foldl (fun acc p => acc ++ p.snd.traces) D store =
    D ++ List.foldl (fun acc p => acc ++ p.snd.traces) (∅ : DEnv) store := by
  induction store generalizing D with
  | nil =>
    simp only [List.foldl]
    -- D ++ ∅ = D
    have h : D ++ (∅ : DEnv) = D := DEnvUnion_empty_right D
    exact h.symm
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [ih (D ++ hd.snd.traces)]
    -- rewrite the RHS foldl using IH at (∅ ++ hd.snd.traces)
    rw [ih (∅ ++ hd.snd.traces)]
    -- reassociate and eliminate ∅ on the right
    -- (D ++ hd.traces) ++ X = D ++ ((∅ ++ hd.traces) ++ X)
    -- -> D ++ (hd.traces ++ X) = D ++ (∅ ++ (hd.traces ++ X))
    -- -> D ++ (hd.traces ++ X) = D ++ (hd.traces ++ X)
    rw [DEnvUnion_assoc D hd.snd.traces (List.foldl (fun acc p => acc ++ p.snd.traces) ∅ tl)]
    rw [DEnvUnion_assoc (∅ : DEnv) hd.snd.traces
      (List.foldl (fun acc p => acc ++ p.snd.traces) ∅ tl)]
    change
      D ++ (hd.snd.traces ++ List.foldl (fun acc p => acc ++ p.snd.traces) ∅ tl) =
        D ++ (DEnvUnion (∅ : DEnv)
          (hd.snd.traces ++ List.foldl (fun acc p => acc ++ p.snd.traces) ∅ tl))
    rw [DEnvUnion_empty_left]

/-- lookupG in appended GEnv: searches left first. -/
private theorem lookupG_append_left {G1 G2 : GEnv} {e : Endpoint} {L : LocalType}
    (h : lookupG G1 e = some L) :
    lookupG (G1 ++ G2) e = some L := by
  induction G1 with
  | nil =>
      simp [lookupG] at h
  | cons hd tl ih =>
      cases hEq : (e == hd.1) with
      | true =>
          have hL : hd.2 = L := by
            simpa [lookupG, List.lookup, hEq] using h
          simp [lookupG, List.lookup, hEq, hL]
      | false =>
          have h' : lookupG tl e = some L := by
            simpa [lookupG, List.lookup, hEq] using h
          have ih' := ih h'
          simpa [lookupG, List.lookup, hEq] using ih'

/-- lookupG in appended GEnv: if not in left, search right. -/
private theorem lookupG_append_right {G1 G2 : GEnv} {e : Endpoint}
    (h : lookupG G1 e = none) :
    lookupG (G1 ++ G2) e = lookupG G2 e := by
  induction G1 with
  | nil =>
      simp [lookupG] at h ⊢
  | cons hd tl ih =>
      cases hEq : (e == hd.1) with
      | true =>
          have : False := by
            simp [lookupG, List.lookup, hEq] at h
          exact this.elim
      | false =>
          have h' : lookupG tl e = none := by
            simpa [lookupG, List.lookup, hEq] using h
          have ih' := ih h'
          simpa [lookupG, List.lookup, hEq] using ih'

/-- updateG distributes over append (left). -/
private theorem updateG_append_left {G1 G2 : GEnv} {e : Endpoint} {L : LocalType}
    (hMem : ∃ L', lookupG G1 e = some L') :
    updateG (G1 ++ G2) e L = updateG G1 e L ++ G2 := by
  induction G1 with
  | nil =>
      cases hMem with
      | intro L' hLookup =>
          have : False := by
            simp [lookupG] at hLookup
          exact this.elim
  | cons hd tl ih =>
    obtain ⟨e', L'⟩ := hd
    by_cases he : e = e'
    · simp [updateG, he]
    · obtain ⟨L'', hLookup⟩ := hMem
      have hbeq : (e == e') = false := by
        exact beq_eq_false_iff_ne.mpr he
      have hMem' : ∃ L', lookupG tl e = some L' := by
        refine ⟨L'', ?_⟩
        simpa [lookupG, List.lookup, hbeq] using hLookup
      have ih' := ih hMem'
      simp [updateG, he, ih', List.cons_append]

/-- updateG distributes over append (right) when not in left. -/
private theorem updateG_append_right {G1 G2 : GEnv} {e : Endpoint} {L : LocalType}
    (hNotMem : lookupG G1 e = none) :
    updateG (G1 ++ G2) e L = G1 ++ updateG G2 e L := by
  induction G1 with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨e', L'⟩ := hd
    by_cases he : e = e'
    · have : False := by
        have hbeq : (e == e') = true := by
          simp [he]
        simp [lookupG, List.lookup, hbeq] at hNotMem
      exact this.elim
    · have hNotMem' : lookupG tl e = none := by
        have hbeq : (e == e') = false := by
          exact beq_eq_false_iff_ne.mpr he
        simpa [lookupG, List.lookup, hbeq] using hNotMem
      have ih' := ih hNotMem'
      simp [updateG, he, ih', List.cons_append]

/-! ### toGEnv/toDEnv commute with updates -/

/-- Helper: GEnv foldl append comm. -/
private theorem GEnv_foldl_append_comm {ν : Type u} [VerificationModel ν]
    (G : GEnv) (store : SessionStore ν) :
    List.foldl (fun acc p => acc ++ p.snd.localTypes) G store =
    G ++ List.foldl (fun acc p => acc ++ p.snd.localTypes) [] store := by
  induction store generalizing G with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [ih (G ++ hd.snd.localTypes)]
    simp only [List.nil_append]
    rw [ih hd.snd.localTypes]
    simp only [List.append_assoc]

/-- Helper: Buffers foldl append comm. -/
private theorem Buffers_foldl_append_comm {ν : Type u} [VerificationModel ν]
    (B : Buffers) (store : SessionStore ν) :
    List.foldl (fun acc p => acc ++ SignedBuffers.payloads p.snd.buffers) B store =
    B ++ List.foldl (fun acc p => acc ++ SignedBuffers.payloads p.snd.buffers) [] store := by
  induction store generalizing B with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [ih (B ++ SignedBuffers.payloads hd.snd.buffers)]
    simp only [List.nil_append]
    rw [ih (SignedBuffers.payloads hd.snd.buffers)]
    simp only [List.append_assoc]

/-- Key lemma: toGEnv commutes with updateType.
    This is the bridge between SessionStore operations and Protocol-level GEnv operations.
    Requires store consistency to know endpoints have correct sids. -/
theorem SessionStore.toGEnv_updateType {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (hMem : ∃ st, (e.sid, st) ∈ store)
    (hCons : store.consistent) :
    (store.updateType e L).toGEnv = updateG (store.toGEnv) e L := by
  sorry

/-- Key lemma: toDEnv commutes with updateTrace.
    Requires store consistency to know edges have correct sids. -/
theorem SessionStore.toDEnv_updateTrace {store : SessionStore ν} {edge : Edge} {ts : List ValType}
    (hMem : ∃ st, (edge.sid, st) ∈ store)
    (hCons : store.consistent) :
    (store.updateTrace edge ts).toDEnv = updateD (store.toDEnv) edge ts := by
  -- updateTrace updates the trace for a specific edge; toDEnv projects the whole DEnv
  sorry

/-- toDEnv is unchanged by updateType (type update doesn't affect traces). -/
theorem SessionStore.toDEnv_updateType {store : SessionStore ν} {e : Endpoint} {L : LocalType} :
    (store.updateType e L).toDEnv = store.toDEnv := by
  -- Type updates only modify localTypes, not traces
  sorry

/-- toGEnv is unchanged by updateTrace (trace update doesn't affect types). -/
theorem SessionStore.toGEnv_updateTrace {store : SessionStore ν} {edge : Edge} {ts : List ValType} :
    (store.updateTrace edge ts).toGEnv = store.toGEnv := by
  -- Trace updates only modify traces, not localTypes
  sorry

/-- toBuffers is unchanged by updateType (type update doesn't affect buffers). -/
theorem SessionStore.toBuffers_updateType {store : SessionStore ν} {e : Endpoint} {L : LocalType} :
    (store.updateType e L).toBuffers = store.toBuffers := by
  -- Type updates only modify localTypes, not buffers
  sorry

/-- toBuffers is unchanged by updateTrace (trace update doesn't affect buffers). -/
theorem SessionStore.toBuffers_updateTrace {store : SessionStore ν} {edge : Edge} {ts : List ValType} :
    (store.updateTrace edge ts).toBuffers = store.toBuffers := by
  -- Trace updates only modify traces, not buffers
  sorry

/-! ### WFSessionStore Preservation -/

/-- Empty store is well-formed. -/
theorem WFSessionStore_nil : sessionStore_refines_envs ([] : SessionStore ν) := by
  simp only [sessionStore_refines_envs, SessionStore.toGEnv, SessionStore.toDEnv, SessionStore.toBuffers]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ h; cases h
  · intro e; simp [lookupG, SessionStore.lookupType]
  · intro edge; simp [lookupD_empty, SessionStore.lookupTrace]
  · intro edge; simp [lookupBuf, SessionStore.lookupBuffer]

/-- Helper: session consistency is preserved by updateType. -/
private theorem updateType_preserves_session_consistency {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (hSid : ∀ sid st, (sid, st) ∈ store → st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid)) :
    ∀ sid st, (sid, st) ∈ store.updateType e L → st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid) := by
  -- updateType only modifies localTypes, not sid or endpoints
  sorry

/-- Helper: session consistency is preserved by updateTrace. -/
private theorem updateTrace_preserves_session_consistency {store : SessionStore ν} {edge : Edge} {ts : List ValType}
    (hSid : ∀ sid st, (sid, st) ∈ store → st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid)) :
    ∀ sid st, (sid, st) ∈ store.updateTrace edge ts → st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid) := by
  -- updateTrace only modifies traces, not sid or endpoints
  sorry

/-- Type update preserves WFSessionStore. -/
theorem SessionStore.updateType_preserves_WFSessionStore {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (hWF : sessionStore_refines_envs store)
    (hMem : ∃ st, (e.sid, st) ∈ store)
    (hCons : store.consistent) :
    sessionStore_refines_envs (store.updateType e L) := by
  obtain ⟨hSid, hG, hD, hBuf⟩ := hWF
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Session consistency preserved
    exact updateType_preserves_session_consistency hSid
  · -- Type lookups agree: lookupG (toGEnv store') e' = lookupType store' e'
    intro e'
    -- We have: lookupG (toGEnv store) e' = lookupType store e' (from hG)
    -- Need: lookupG (toGEnv store') e' = lookupType store' e'
    -- where store' = store.updateType e L
    -- Case split on whether e' = e
    by_cases he : e' = e
    · -- e' = e: both sides give some L
      subst he
      rw [SessionStore.lookupType_updateType_eq hMem]
      -- Need: lookupG (toGEnv store') e = some L
      -- This requires toGEnv_updateType
      rw [SessionStore.toGEnv_updateType hMem hCons]
      simp [lookupG_updateG_eq]
    · -- e' ≠ e: both sides unchanged
      rw [SessionStore.lookupType_updateType_ne he]
      rw [← hG e']
      -- Need: lookupG (toGEnv store') e' = lookupG (toGEnv store) e'
      rw [SessionStore.toGEnv_updateType hMem hCons]
      exact lookupG_updateG_ne he
  · -- Trace lookups agree (toGEnv update doesn't affect toDEnv)
    intro edge
    rw [SessionStore.lookupTrace_updateType]
    rw [← hD edge]
    congr 1
    exact SessionStore.toDEnv_updateType
  · -- Buffer lookups agree (unchanged by type update)
    intro edge
    rw [SessionStore.toBuffers_updateType]
    rw [SessionStore.lookupBuffer_updateType]
    exact hBuf edge

/-- Trace update preserves WFSessionStore. -/
theorem SessionStore.updateTrace_preserves_WFSessionStore {store : SessionStore ν} {edge : Edge} {ts : List ValType}
    (hWF : sessionStore_refines_envs store)
    (hMem : ∃ st, (edge.sid, st) ∈ store)
    (hCons : store.consistent) :
    sessionStore_refines_envs (store.updateTrace edge ts) := by
  obtain ⟨hSid, hG, hD, hBuf⟩ := hWF
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Session consistency preserved
    exact updateTrace_preserves_session_consistency hSid
  · -- Type lookups agree (unchanged by trace update)
    intro e
    rw [SessionStore.lookupType_updateTrace]
    rw [← hG e]
    congr 1
    exact SessionStore.toGEnv_updateTrace
  · -- Trace lookups agree
    intro edge'
    by_cases he : edge' = edge
    · -- edge' = edge: both sides give ts
      subst he
      rw [SessionStore.lookupTrace_updateTrace_eq hMem]
      rw [SessionStore.toDEnv_updateTrace hMem hCons]
      simp [lookupD_update_eq]
    · -- edge' ≠ edge: both sides unchanged
      rw [SessionStore.lookupTrace_updateTrace_ne he]
      rw [← hD edge']
      rw [SessionStore.toDEnv_updateTrace hMem hCons]
      exact lookupD_update_neq _ _ _ _ (Ne.symm he)
  · -- Buffer lookups agree (unchanged by trace update)
    intro edge'
    rw [SessionStore.toBuffers_updateTrace]
    rw [SessionStore.lookupBuffer_updateTrace]
    exact hBuf edge'
