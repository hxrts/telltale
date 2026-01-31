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

structure SessionState where
  -- Scope for resource commitments and nullifiers.
  scope : ScopeId -- Local resource scope.
  sid : SessionId -- Session identifier.
  roles : RoleSet -- Participating roles.
  endpoints : List Endpoint -- Allocated endpoints.
  localTypes : List (Endpoint × LocalType) -- Endpoint types (GEnv slice).
  traces : DEnv -- In-flight type traces (DEnv slice).
  buffers : Buffers -- In-memory buffers (protocol Buffers).
  handlers : List (Edge × HandlerId) -- Handler bindings per edge.
  epoch : Nat -- Epoch tag for rotation.
  phase : SessionPhase -- Lifecycle status.

abbrev SessionStore := List (SessionId × SessionState)

/-! ## Session environment projections -/

def SessionState.lookupType (st : SessionState) (e : Endpoint) : Option LocalType :=
  -- Lookup a local type in this session's endpoint map.
  st.localTypes.lookup e

def SessionState.lookupTrace (st : SessionState) (edge : Edge) : List ValType :=
  -- Lookup a type trace in this session's DEnv slice.
  lookupD st.traces edge

def SessionState.lookupBuffer (st : SessionState) (edge : Edge) : Buffer :=
  -- Lookup a buffer in this session's buffer slice.
  lookupBuf st.buffers edge

def SessionState.lookupHandler (st : SessionState) (edge : Edge) : Option HandlerId :=
  -- Lookup the handler bound to a given edge.
  st.handlers.lookup edge

def SessionStore.lookupType (store : SessionStore) (e : Endpoint) : Option LocalType :=
  -- Find the matching session and then its local type.
  match store with
  | [] => none
  | (sid, st) :: rest =>
      if _h : sid = e.sid then
        st.lookupType e
      else
        SessionStore.lookupType rest e

def SessionStore.lookupTrace (store : SessionStore) (edge : Edge) : List ValType :=
  -- Find the matching session and then its trace.
  match store with
  | [] => []
  | (sid, st) :: rest =>
      if _h : sid = edge.sid then
        st.lookupTrace edge
      else
        SessionStore.lookupTrace rest edge

def SessionStore.lookupBuffer (store : SessionStore) (edge : Edge) : Buffer :=
  -- Find the matching session and then its buffer.
  match store with
  | [] => []
  | (sid, st) :: rest =>
      if _h : sid = edge.sid then
        st.lookupBuffer edge
      else
        SessionStore.lookupBuffer rest edge

def SessionStore.lookupHandler (store : SessionStore) (edge : Edge) : Option HandlerId :=
  -- Find the matching session and then its handler binding.
  match store with
  | [] => none
  | (sid, st) :: rest =>
      if _h : sid = edge.sid then
        st.lookupHandler edge
      else
        SessionStore.lookupHandler rest edge

def SessionStore.defaultHandler (store : SessionStore) : Option HandlerId :=
  -- Pick any handler id from the active session store.
  match store with
  | [] => none
  | (_, st) :: rest =>
      match st.handlers with
      | [] => SessionStore.defaultHandler rest
      | (_, h) :: _ => some h

def SessionStore.toGEnv (store : SessionStore) : GEnv :=
  -- Flatten per-session local types into a single GEnv.
  store.foldl (fun acc p => acc ++ p.snd.localTypes) []

def SessionStore.toDEnv (store : SessionStore) : DEnv :=
  -- Union per-session DEnv slices (left-biased on conflicts).
  store.foldl (fun acc p => acc ++ p.snd.traces) (∅ : DEnv)

def SessionStore.toBuffers (store : SessionStore) : Buffers :=
  -- Flatten per-session buffers into a single Buffers list.
  store.foldl (fun acc p => acc ++ p.snd.buffers) []

def sessionStore_refines_envs (store : SessionStore) : Prop :=
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
