import Effects.Typing

/-!
# MPST Operational Semantics

This module defines the operational semantics for MPST processes.

## Step Relations

- `StepBase`: Head reductions (send, recv, select, branch, newSession, assign)
- `Step`: Contextual closure (in seq left, par left, par right)

## Async Semantics

The semantics is asynchronous:
- **Send** enqueues the value at the directed edge buffer (from sender to receiver)
- **Recv** dequeues from the directed edge buffer (from sender to receiver)
- **Select** enqueues a label
- **Branch** dequeues a label and selects the branch

Messages travel on directed edges: a send from role p to role q
places the message in buffer (sid, p, q), and a receive at q from p
dequeues from the same buffer.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Base Step Relation -/

/-- Base step relation: head reductions.

Each rule consumes the current process and produces a configuration
with `skip` as the process (indicating the action completed). -/
inductive StepBase : Config → Config → Prop where
  /-- Send: enqueue value at directed edge.
      Preconditions:
      - k maps to channel endpoint e
      - x maps to value v
      Effect: enqueue v at edge (e.sid, e.role, target_role) -/
  | send {C k x e v target} :
      C.proc = .send k x →
      lookupStr C.store k = some (.chan e) →
      lookupStr C.store x = some v →
      -- target role comes from the local type (implicit in well-typed)
      StepBase C (sendStep C { sid := e.sid, sender := e.role, receiver := target } v)

  /-- Recv: dequeue value from directed edge.
      Preconditions:
      - k maps to channel endpoint e
      - buffer at (sid, source, e.role) is non-empty
      Effect: dequeue value into variable x -/
  | recv {C k x e v source} :
      C.proc = .recv k x →
      lookupStr C.store k = some (.chan e) →
      lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = v :: _ →
      StepBase C (recvStep C { sid := e.sid, sender := source, receiver := e.role } x v)

  /-- Select: enqueue label at directed edge.
      Similar to send but for labels (represented as string values). -/
  | select {C k e ℓ target} :
      C.proc = .select k ℓ →
      lookupStr C.store k = some (.chan e) →
      StepBase C (sendStep C { sid := e.sid, sender := e.role, receiver := target } (.string ℓ))

  /-- Branch: dequeue label and select branch.
      Preconditions:
      - k maps to channel endpoint e
      - buffer has a label value
      - label matches one of the branches
      Effect: continue with selected branch process -/
  | branch {C k e ℓ source bs P bufs'} :
      C.proc = .branch k bs →
      lookupStr C.store k = some (.chan e) →
      lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = .string ℓ :: _ →
      bs.find? (fun b => b.1 == ℓ) = some (ℓ, P) →
      dequeueBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = some (bufs', _) →
      StepBase C { C with proc := P, bufs := bufs' }

  /-- NewSession: create a new session with fresh ID.
      Effect:
      - allocate endpoints for all roles
      - initialize empty buffers for all directed edges -/
  | newSession {C roles f P} :
      C.proc = .newSession roles f P →
      StepBase C
        { (newSessionStep C roles f) with proc := P }

  /-- Assign: store a value in a variable. -/
  | assign {C x v} :
      C.proc = .assign x v →
      StepBase C
        { C with
          proc := .skip
          store := updateStr C.store x v }

  /-- Seq with skip: seq skip Q → Q -/
  | seq2 {C Q} :
      C.proc = .seq .skip Q →
      StepBase C { C with proc := Q }

  /-- Par with skip left: par skip Q → Q -/
  | par_skip_left {C Q} :
      C.proc = .par .skip Q →
      StepBase C { C with proc := Q }

  /-- Par with skip right: par P skip → P -/
  | par_skip_right {C P} :
      C.proc = .par P .skip →
      StepBase C { C with proc := P }

/-! ## Contextual Step Relation -/

/-- Step relation: contextual closure of base steps. -/
inductive Step : Config → Config → Prop where
  /-- Base step. -/
  | base {C C'} : StepBase C C' → Step C C'

  /-- Step in left of seq. -/
  | seq_left {C P P' Q} :
      C.proc = .seq P Q →
      Step { C with proc := P } { C with proc := P' } →
      Step C { C with proc := .seq P' Q }

  /-- Step in left of par. -/
  | par_left {C P P' Q} :
      C.proc = .par P Q →
      Step { C with proc := P } { C with proc := P' } →
      Step C { C with proc := .par P' Q }

  /-- Step in right of par. -/
  | par_right {C P Q Q'} :
      C.proc = .par P Q →
      Step { C with proc := Q } { C with proc := Q' } →
      Step C { C with proc := .par P Q' }

/-! ## Step Properties -/

/-- Step is deterministic for base steps (modulo which par branch).

    **Proof outline**: Case analysis on h₁ and h₂.
    - Same constructors: Extract equalities from preconditions
    - Different constructors: Show C.proc can't match both patterns
    - Par exception: The `hSame` disjunct handles non-deterministic choice

    This is a standard determinism proof requiring extensive case work. -/
theorem stepBase_deterministic {C C₁ C₂} (h₁ : StepBase C C₁) (h₂ : StepBase C C₂)
    (hSame : C₁.proc = C₂.proc ∨ (∃ P Q, C.proc = .par P Q)) :
    C₁ = C₂ ∨ (∃ P Q, C.proc = .par P Q) := by
  sorry  -- Full proof requires case analysis on h₁, h₂

/-- A configuration terminates if its process is skip. -/
def Step.Terminates (C : Config) : Prop :=
  C.proc = .skip

/-- A configuration is stuck if it cannot step and is not terminated. -/
def Step.Stuck (C : Config) : Prop :=
  ¬Step.Terminates C ∧ ¬∃ C', Step C C'

/-- Multi-step relation (reflexive transitive closure). -/
def Steps : Config → Config → Prop :=
  Relation.ReflTransGen Step

/-! ## Progress Lemmas -/

/-- A recv can step if its buffer is non-empty. -/
theorem recv_can_step {C k x e source} (hProc : C.proc = .recv k x)
    (hk : lookupStr C.store k = some (.chan e))
    (hBuf : (lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role }).length > 0) :
    ∃ C', Step C C' := by
  obtain ⟨v, vs, hEq⟩ : ∃ v vs, lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = v :: vs := by
    cases h : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } with
    | nil => simp_all
    | cons v vs => exact ⟨v, vs, rfl⟩
  exact ⟨_, Step.base (StepBase.recv hProc hk hEq)⟩

/-- A send can always step (async semantics). -/
theorem send_can_step {C : Config} {k x : Var} {e : Endpoint} {v : Value} {target : Role}
    (hProc : C.proc = .send k x)
    (hk : lookupStr C.store k = some (.chan e))
    (hx : lookupStr C.store x = some v) :
    ∃ C', Step C C' :=
  ⟨_, Step.base (StepBase.send (target := target) hProc hk hx)⟩

end
