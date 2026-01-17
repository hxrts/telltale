import Mathlib

/-!
# MPST Basic Definitions

This module defines the foundational types for multiparty session types:
- `SessionId`: unique identifier for a session instance
- `Role`: participant identifier within a session
- `Endpoint`: a (SessionId × Role) pair representing a participant's view
- `Label`: branch/select labels for choice
- `Edge`: directed communication edge (sender, receiver) within a session
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-- Session identifiers are natural numbers. -/
abbrev SessionId := Nat

/-- Role identifiers for participants in a session. -/
abbrev Role := String

/-- Labels for branching and selection in protocols. -/
abbrev Label := String

/-- An endpoint is a (SessionId × Role) pair, representing a participant's
    view of a particular session. -/
structure Endpoint where
  sid : SessionId
  role : Role
  deriving Repr, DecidableEq, Hashable

namespace Endpoint

/-- Create an endpoint from session ID and role. -/
def mk' (s : SessionId) (r : Role) : Endpoint := { sid := s, role := r }

instance : Inhabited Endpoint := ⟨{ sid := 0, role := "" }⟩

end Endpoint

/-- A directed edge represents a communication channel from one role to another
    within a session. Messages flow from `sender` to `receiver`. -/
structure Edge where
  sid : SessionId
  sender : Role
  receiver : Role
  deriving Repr, DecidableEq, Hashable

namespace Edge

/-- Create an edge from session ID and role pair. -/
def mk' (s : SessionId) (p q : Role) : Edge := { sid := s, sender := p, receiver := q }

/-- The reverse edge (swap sender and receiver). -/
def reverse (e : Edge) : Edge := { sid := e.sid, sender := e.receiver, receiver := e.sender }

/-- Two edges are reverse of each other. -/
def areReverse (e₁ e₂ : Edge) : Prop :=
  e₁.sid = e₂.sid ∧ e₁.sender = e₂.receiver ∧ e₁.receiver = e₂.sender

theorem reverse_reverse (e : Edge) : e.reverse.reverse = e := by
  simp [reverse]

theorem reverse_ne_self (e : Edge) (h : e.sender ≠ e.receiver) : e.reverse ≠ e := by
  intro heq
  simp only [reverse] at heq
  have h1 : e.receiver = e.sender := by
    have := congrArg Edge.sender heq
    simp at this
    exact this
  exact h h1.symm

instance : Inhabited Edge := ⟨{ sid := 0, sender := "", receiver := "" }⟩

instance : Ord Edge where
  compare a b :=
    match compare a.sid b.sid with
    | .lt => .lt
    | .gt => .gt
    | .eq =>
      match compare a.sender b.sender with
      | .lt => .lt
      | .gt => .gt
      | .eq => compare a.receiver b.receiver

end Edge

/-- A role set is the collection of participants in a session. -/
abbrev RoleSet := List Role

namespace RoleSet

/-- Check if a role is in the role set. -/
def contains (rs : RoleSet) (r : Role) : Bool :=
  rs.elem r

/-- Get all directed edges between roles in a session. -/
def allEdges (sid : SessionId) (rs : RoleSet) : List Edge :=
  rs.flatMap fun p => rs.filterMap fun q =>
    if p ≠ q then some { sid := sid, sender := p, receiver := q } else none

/-- All edges in allEdges have the specified session ID. -/
theorem allEdges_sid (sid : SessionId) (rs : RoleSet) :
    ∀ e ∈ allEdges sid rs, e.sid = sid := by
  intro e he
  simp only [allEdges, List.mem_flatMap, List.mem_filterMap] at he
  obtain ⟨p, _, q, _, hite⟩ := he
  split at hite
  · simp only [Option.some.injEq] at hite
    rw [← hite]
  · exact Option.noConfusion hite

/-- Get all endpoints for a session. -/
def allEndpoints (sid : SessionId) (rs : RoleSet) : List Endpoint :=
  rs.map fun r => { sid := sid, role := r }

end RoleSet

end
