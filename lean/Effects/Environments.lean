import Effects.LocalType
import Effects.Values

/-!
# MPST Environments

This module defines the runtime environments for multiparty session types:

- `Store`: Variable store mapping variables to runtime values
- `SEnv`: Type environment mapping variables to value types
- `GEnv`: Session environment mapping endpoints to local types
- `DEnv`: Delayed type environment for in-flight message traces per directed edge
- `Buffers`: Per-edge FIFO message buffers keyed by (sid, from, to)

The key difference from binary session types is that buffers and type traces
are keyed by **directed edges** `(sid, from, to)` rather than endpoints.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Variables -/

/-- Variables are strings. -/
abbrev Var := String

/-! ## Store: Variable → Value -/

/-- Store maps variables to runtime values. -/
abbrev Store := List (Var × Value)

/-- Lookup a value in the store. -/
def lookupStr (store : Store) (x : Var) : Option Value :=
  store.lookup x

/-- Update or insert a variable in the store. -/
def updateStr (store : Store) (x : Var) (v : Value) : Store :=
  match store with
  | [] => [(x, v)]
  | (y, w) :: rest =>
    if x = y then (x, v) :: rest
    else (y, w) :: updateStr rest x v

/-! ## SEnv: Variable → ValType -/

/-- SEnv maps variables to their value types. -/
abbrev SEnv := List (Var × ValType)

/-- Lookup a type in SEnv. -/
def lookupSEnv (env : SEnv) (x : Var) : Option ValType :=
  env.lookup x

/-- Update or insert in SEnv. -/
def updateSEnv (env : SEnv) (x : Var) (T : ValType) : SEnv :=
  match env with
  | [] => [(x, T)]
  | (y, U) :: rest =>
    if x = y then (x, T) :: rest
    else (y, U) :: updateSEnv rest x T

/-! ## GEnv: Endpoint → LocalType -/

/-- GEnv maps session endpoints to their current local session types. -/
abbrev GEnv := List (Endpoint × LocalType)

/-- Lookup a local type in GEnv. -/
def lookupG (env : GEnv) (e : Endpoint) : Option LocalType :=
  env.lookup e

/-- Update or insert in GEnv. -/
def updateG (env : GEnv) (e : Endpoint) (L : LocalType) : GEnv :=
  match env with
  | [] => [(e, L)]
  | (e', L') :: rest =>
    if e = e' then (e, L) :: rest
    else (e', L') :: updateG rest e L

/-! ## Directed Edge Buffers -/

/-- A buffer is a FIFO queue of values. -/
abbrev Buffer := List Value

/-- Buffers maps directed edges to their message queues.
    Each buffer holds messages from `e.sender` to `e.receiver`. -/
abbrev Buffers := List (Edge × Buffer)

/-- Lookup a buffer for a directed edge. -/
def lookupBuf (bufs : Buffers) (e : Edge) : Buffer :=
  bufs.lookup e |>.getD []

/-- Update a buffer for a directed edge. -/
def updateBuf (bufs : Buffers) (e : Edge) (buf : Buffer) : Buffers :=
  match bufs with
  | [] => [(e, buf)]
  | (e', buf') :: rest =>
    if e = e' then (e, buf) :: rest
    else (e', buf') :: updateBuf rest e buf

/-- Enqueue a value at a directed edge buffer. -/
def enqueueBuf (bufs : Buffers) (e : Edge) (v : Value) : Buffers :=
  updateBuf bufs e (lookupBuf bufs e ++ [v])

/-- Dequeue from a directed edge buffer (returns updated buffers and value). -/
def dequeueBuf (bufs : Buffers) (e : Edge) : Option (Buffers × Value) :=
  match lookupBuf bufs e with
  | [] => none
  | v :: vs => some (updateBuf bufs e vs, v)

/-! ## DEnv: Directed Edge → Type Trace -/

/-- DEnv maps directed edges to their in-flight type traces.
    This tracks the types of messages that have been sent but not yet received
    on each directed edge. -/
abbrev DEnv := List (Edge × List ValType)

/-- Lookup a type trace for a directed edge. -/
def lookupD (env : DEnv) (e : Edge) : List ValType :=
  env.lookup e |>.getD []

/-- Update a type trace for a directed edge. -/
def updateD (env : DEnv) (e : Edge) (ts : List ValType) : DEnv :=
  match env with
  | [] => [(e, ts)]
  | (e', ts') :: rest =>
    if e = e' then (e, ts) :: rest
    else (e', ts') :: updateD rest e ts

/-- Append a type to the in-flight trace. -/
def appendD (env : DEnv) (e : Edge) (T : ValType) : DEnv :=
  updateD env e (lookupD env e ++ [T])

/-- Pop a type from the in-flight trace. -/
def popD (env : DEnv) (e : Edge) : Option (DEnv × ValType) :=
  match lookupD env e with
  | [] => none
  | T :: ts => some (updateD env e ts, T)

/-! ## Session Management -/

/-- Initialize empty buffers for all directed edges between roles. -/
def initBuffers (sid : SessionId) (roles : RoleSet) : Buffers :=
  (RoleSet.allEdges sid roles).map fun e => (e, [])

/-- Initialize empty type traces for all directed edges. -/
def initDEnv (sid : SessionId) (roles : RoleSet) : DEnv :=
  (RoleSet.allEdges sid roles).map fun e => (e, [])

/-! ## Environment Lemmas

### Proof Technique for lookup/update Lemmas

The proofs follow a standard pattern for association list operations:

**For `lookup_update_eq`**: Show that looking up key k after updating (k, v) returns v.
- Unfold `update` definition: prepends (k, v) after erasing k
- Unfold `lookup` definition: returns first match
- Since (k, v) is at the head, lookup immediately returns v
- Key lemma: `List.lookup_cons` + decidable equality

**For `lookup_update_neq`**: Show that looking up k' ≠ k after updating (k, v) is unchanged.
- Unfold both definitions
- The new (k, v) at head doesn't match k' (by hne)
- Continue through erased list
- By induction: if (k', v') was in original, it's in erased list (k' ≠ k)
- Key lemma: membership in erase when key differs

**Alternative: Use generic Assoc module**
The binary session types use a generic `Assoc` module with these lemmas proven once.
MPST could import it via: `import Effects.Assoc` and define:
  `def lookupG (env : GEnv) (e : Endpoint) := Assoc.lookup env e`
This would give the lemmas for free via `Assoc.lookup_update_eq`.
-/

theorem lookupStr_update_eq (store : Store) (x : Var) (v : Value) :
    lookupStr (updateStr store x v) x = some v := by
  sorry  -- Proof: unfold updateStr, see (x, v) at head, lookup returns v

theorem lookupStr_update_neq (store : Store) (x y : Var) (v : Value) (hne : x ≠ y) :
    lookupStr (updateStr store x v) y = lookupStr store y := by
  sorry  -- Proof: (x, v) at head doesn't match y, induction on rest

theorem lookupG_update_eq (env : GEnv) (e : Endpoint) (L : LocalType) :
    lookupG (updateG env e L) e = some L := by
  sorry  -- Proof: same pattern as lookupStr_update_eq

theorem lookupG_update_neq (env : GEnv) (e e' : Endpoint) (L : LocalType) (hne : e ≠ e') :
    lookupG (updateG env e L) e' = lookupG env e' := by
  sorry  -- Proof: same pattern as lookupStr_update_neq

theorem lookupBuf_update_eq (bufs : Buffers) (e : Edge) (buf : Buffer) :
    lookupBuf (updateBuf bufs e buf) e = buf := by
  sorry  -- Proof: same pattern, but lookupBuf uses getD [] for default

theorem lookupBuf_update_neq (bufs : Buffers) (e e' : Edge) (buf : Buffer) (hne : e ≠ e') :
    lookupBuf (updateBuf bufs e buf) e' = lookupBuf bufs e' := by
  sorry  -- Proof: same pattern

theorem lookupD_update_eq (env : DEnv) (e : Edge) (ts : List ValType) :
    lookupD (updateD env e ts) e = ts := by
  sorry  -- Proof: same pattern, lookupD uses getD [] for default

theorem lookupD_update_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    lookupD (updateD env e ts) e' = lookupD env e' := by
  sorry  -- Proof: same pattern

end
