import Protocol.Environments.Part1
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
