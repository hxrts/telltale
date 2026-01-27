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

/-- Unfolding lemma for Edge.compare. -/
theorem compare_def (a b : Edge) :
    compare a b =
      match compare a.sid b.sid with
      | .lt => .lt
      | .gt => .gt
      | .eq =>
        match compare a.sender b.sender with
        | .lt => .lt
        | .gt => .gt
        | .eq => compare a.receiver b.receiver := by
  -- compare is defined lexicographically on fields.
  rfl

/-- Edge comparison is exact: `.eq` iff the edges are equal. -/
theorem compare_eq_iff_eq (e₁ e₂ : Edge) :
    compare e₁ e₂ = .eq ↔ e₁ = e₂ := by
  -- Unfold the lexicographic compare and reduce to component equalities.
  cases e₁ with
  | mk sid₁ s₁ r₁ =>
    cases e₂ with
    | mk sid₂ s₂ r₂ =>
      constructor
      · intro h
        cases hSid : compare sid₁ sid₂ <;> simp [compare_def, hSid] at h
        cases hSend : compare s₁ s₂ <;> simp [hSend] at h
        have hSidEq : sid₁ = sid₂ := (_root_.compare_eq_iff_eq (a:=sid₁) (b:=sid₂)).1 hSid
        have hSendEq : s₁ = s₂ := (_root_.compare_eq_iff_eq (a:=s₁) (b:=s₂)).1 hSend
        have hRecvEq : r₁ = r₂ := by
          simpa using h
        cases hSidEq; cases hSendEq; cases hRecvEq; rfl
      · intro h
        -- Equal edges compare equal by reflexivity on each component.
        cases h
        have hSid : compare sid₁ sid₁ = .eq :=
          (_root_.compare_eq_iff_eq (a:=sid₁) (b:=sid₁)).2 rfl
        have hSend : compare s₁ s₁ = .eq :=
          (_root_.compare_eq_iff_eq (a:=s₁) (b:=s₁)).2 rfl
        have hRecv : compare r₁ r₁ = .eq :=
          (_root_.compare_eq_iff_eq (a:=r₁) (b:=r₁)).2 rfl
        simp [compare_def]

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

/-- Edges in allEdges have senders in the role set. -/
theorem allEdges_sender_mem (sid : SessionId) (rs : RoleSet) :
    ∀ e ∈ allEdges sid rs, e.sender ∈ rs := by
  -- Unpack the flatMap/filterMap witness and rewrite the sender.
  intro e he
  simp only [allEdges, List.mem_flatMap, List.mem_filterMap] at he
  obtain ⟨p, hp, q, hq, hite⟩ := he
  by_cases hneq : p ≠ q
  · have hEq : e = { sid := sid, sender := p, receiver := q } := by
      have hEq' : { sid := sid, sender := p, receiver := q } = e := by
        simpa [hneq] using hite
      exact hEq'.symm
    simpa [hEq] using hp
  · have : False := by
      simp [hneq] at hite
    exact this.elim

/-- Get all endpoints for a session. -/
def allEndpoints (sid : SessionId) (rs : RoleSet) : List Endpoint :=
  rs.map fun r => { sid := sid, role := r }

end RoleSet

end
