import Protocol.Typing

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
with `skip` as the process (indicating the action completed).

**Key design**: Target/source roles are determined by the type environment G,
ensuring determinism. -/
inductive StepBase : Config → Config → Prop where
  /-- Send: enqueue value at directed edge.
      Preconditions:
      - k maps to channel endpoint e
      - x maps to value v
      - G[e] = send(target, T, L) determines the target role
      Effect: enqueue v at edge, advance type to L -/
  | send {C k x e v target T L} :
      C.proc = .send k x →
      lookupStr C.store k = some (.chan e) →
      lookupStr C.store x = some v →
      lookupG C.G e = some (.send target T L) →
      StepBase C (sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L)

  /-- Recv: dequeue value from directed edge.
      Preconditions:
      - k maps to channel endpoint e
      - G[e] = recv(source, T, L) determines the source role
      - buffer at (sid, source, e.role) is non-empty
      Effect: dequeue value into variable x, advance type to L -/
  | recv {C k x e v source T L} :
      C.proc = .recv k x →
      lookupStr C.store k = some (.chan e) →
      lookupG C.G e = some (.recv source T L) →
      lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = v :: _ →
      StepBase C (recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L)

  /-- Select: enqueue label at directed edge.
      G[e] = select(target, branches) determines the target role. -/
  | select {C k e ℓ target branches L} :
      C.proc = .select k ℓ →
      lookupStr C.store k = some (.chan e) →
      lookupG C.G e = some (.select target branches) →
      branches.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
      StepBase C (sendStep C e { sid := e.sid, sender := e.role, receiver := target } (.string ℓ) .string L)

  /-- Branch: dequeue label and select branch.
      Preconditions:
      - k maps to channel endpoint e
      - G[e] = branch(source, typeBranches) determines source role
      - buffer has a label value ℓ
      - both process and type branches have entry for ℓ
      Effect: continue with selected branch process, advance type -/
  | branch {C k e ℓ source procBranches typeBranches P L bufs'} :
      C.proc = .branch k procBranches →
      lookupStr C.store k = some (.chan e) →
      lookupG C.G e = some (.branch source typeBranches) →
      lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = .string ℓ :: _ →
      procBranches.find? (fun b => b.1 == ℓ) = some (ℓ, P) →
      typeBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
      dequeueBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = some (bufs', _) →
      StepBase C { C with proc := P, bufs := bufs', G := updateG C.G e L, D := updateD C.D { sid := e.sid, sender := source, receiver := e.role } (lookupD C.D { sid := e.sid, sender := source, receiver := e.role }).tail }

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
  | par_skip_left {C Q nS nG} :
      C.proc = .par nS nG .skip Q →
      StepBase C { C with proc := Q }

  /-- Par with skip right: par P skip → P -/
  | par_skip_right {C P nS nG} :
      C.proc = .par nS nG P .skip →
      StepBase C { C with proc := P }

/-! ## Contextual Step Relation -/

/-- Step relation: contextual closure of base steps. -/
inductive Step : Config → Config → Prop where
  /-- Base step. -/
  | base {C C'} : StepBase C C' → Step C C'

  /-- Step in left of seq. -/
  | seq_left {C C' P Q} :
      C.proc = .seq P Q →
      Step { C with proc := P } C' →
      Step C { C' with proc := .seq C'.proc Q }

  /-- Step in left of par. -/
  | par_left {C C' P Q nS nG nS' nG'} :
      C.proc = .par nS nG P Q →
      Step { C with proc := P } C' →
      Step C { C' with proc := .par nS' nG' C'.proc Q }

  /-- Step in right of par. -/
  | par_right {C C' P Q nS nG nS' nG'} :
      C.proc = .par nS nG P Q →
      Step { C with proc := Q } C' →
      Step C { C' with proc := .par nS' nG' P C'.proc }

/-! ## Step Properties -/

/-- Step is deterministic for base steps (modulo par).

    Since target/source roles are now determined by G, the only source of
    non-determinism is `par skip skip` which can reduce via either
    `par_skip_left` or `par_skip_right`. -/
theorem stepBase_deterministic {C C₁ C₂} (h₁ : StepBase C C₁) (h₂ : StepBase C C₂) :
    C₁ = C₂ ∨ (∃ nS nG P Q, C.proc = .par nS nG P Q) := by
  cases h₁ with
  | send hProc₁ hk₁ hx₁ hG₁ =>
    cases h₂ with
    | send hProc₂ hk₂ hx₂ hG₂ =>
      left
      have heq := hProc₁.symm.trans hProc₂
      simp only [Process.send.injEq] at heq
      obtain ⟨hk_eq, hx_eq⟩ := heq
      subst hk_eq hx_eq
      rw [hk₁] at hk₂
      rw [hx₁] at hx₂
      simp only [Option.some.injEq, Value.chan.injEq] at hk₂ hx₂
      subst hk₂ hx₂
      -- Now G lookups must match since same endpoint
      rw [hG₁] at hG₂
      simp only [Option.some.injEq, LocalType.send.injEq] at hG₂
      obtain ⟨htgt, hT, hL⟩ := hG₂
      subst htgt hT hL
      rfl
    | _ => simp_all
  | recv hProc₁ hk₁ hG₁ hBuf₁ =>
    cases h₂ with
    | recv hProc₂ hk₂ hG₂ hBuf₂ =>
      left
      have heq := hProc₁.symm.trans hProc₂
      simp only [Process.recv.injEq] at heq
      obtain ⟨hk_eq, hx_eq⟩ := heq
      subst hk_eq hx_eq
      rw [hk₁] at hk₂
      simp only [Option.some.injEq, Value.chan.injEq] at hk₂
      subst hk₂
      -- G lookups must match
      rw [hG₁] at hG₂
      simp only [Option.some.injEq, LocalType.recv.injEq] at hG₂
      obtain ⟨hsrc, hT, hL⟩ := hG₂
      subst hsrc hT hL
      -- Buffer lookups at same edge must match
      rw [hBuf₁] at hBuf₂
      simp only [List.cons.injEq] at hBuf₂
      obtain ⟨hv, _⟩ := hBuf₂
      subst hv
      rfl
    | _ => simp_all
  | select hProc₁ hk₁ hG₁ hFind₁ =>
    cases h₂ with
    | select hProc₂ hk₂ hG₂ hFind₂ =>
      left
      have heq := hProc₁.symm.trans hProc₂
      simp only [Process.select.injEq] at heq
      obtain ⟨hk_eq, hℓ_eq⟩ := heq
      subst hk_eq hℓ_eq
      rw [hk₁] at hk₂
      simp only [Option.some.injEq, Value.chan.injEq] at hk₂
      subst hk₂
      rw [hG₁] at hG₂
      simp only [Option.some.injEq, LocalType.select.injEq] at hG₂
      obtain ⟨htgt, hbs⟩ := hG₂
      subst htgt hbs
      rw [hFind₁] at hFind₂
      simp only [Option.some.injEq, Prod.mk.injEq] at hFind₂
      obtain ⟨_, hL⟩ := hFind₂
      subst hL
      rfl
    | _ => simp_all
  | branch hProc₁ hk₁ hG₁ hBuf₁ hFindP₁ hFindT₁ hDq₁ =>
    cases h₂ with
    | branch hProc₂ hk₂ hG₂ hBuf₂ hFindP₂ hFindT₂ hDq₂ =>
      left
      have heq := hProc₁.symm.trans hProc₂
      simp only [Process.branch.injEq] at heq
      obtain ⟨hk_eq, hbs_eq⟩ := heq
      subst hk_eq hbs_eq
      rw [hk₁] at hk₂
      simp only [Option.some.injEq, Value.chan.injEq] at hk₂
      subst hk₂
      -- Extract type branch equality via injection
      rw [hG₁] at hG₂
      simp only [Option.some.injEq] at hG₂
      cases hG₂
      -- Same buffer lookup
      rw [hBuf₁] at hBuf₂
      simp only [List.cons.injEq, Value.string.injEq] at hBuf₂
      obtain ⟨hℓ_eq, _⟩ := hBuf₂
      subst hℓ_eq
      -- Same process branch lookup (same procBranches, same ℓ)
      rw [hFindP₁] at hFindP₂
      simp only [Option.some.injEq, Prod.mk.injEq] at hFindP₂
      obtain ⟨_, hP_eq⟩ := hFindP₂
      subst hP_eq
      -- Same type branch lookup (same typeBranches, same ℓ)
      rw [hFindT₁] at hFindT₂
      simp only [Option.some.injEq, Prod.mk.injEq] at hFindT₂
      obtain ⟨_, hL_eq⟩ := hFindT₂
      subst hL_eq
      -- Same dequeue result
      rw [hDq₁] at hDq₂
      simp only [Option.some.injEq, Prod.mk.injEq] at hDq₂
      obtain ⟨hbufs_eq, _⟩ := hDq₂
      subst hbufs_eq
      rfl
    | _ => simp_all
  | newSession hProc₁ =>
    cases h₂ with
    | newSession hProc₂ =>
      left
      have heq := hProc₁.symm.trans hProc₂
      simp only [Process.newSession.injEq] at heq
      obtain ⟨hr_eq, hf_eq, hP_eq⟩ := heq
      simp only [hr_eq, hf_eq, hP_eq]
    | _ => simp_all
  | assign hProc₁ =>
    cases h₂ with
    | assign hProc₂ =>
      left
      have heq := hProc₁.symm.trans hProc₂
      simp only [Process.assign.injEq] at heq
      obtain ⟨hx_eq, hv_eq⟩ := heq
      simp only [hx_eq, hv_eq]
    | _ => simp_all
  | seq2 hProc₁ =>
    cases h₂ with
    | seq2 hProc₂ =>
      left
      have heq := hProc₁.symm.trans hProc₂
      simp only [Process.seq.injEq] at heq
      rcases heq with ⟨_, ⟨_, ⟨_, hQ_eq⟩⟩⟩
      simp only [hQ_eq]
    | _ => simp_all
  | par_skip_left hProc₁ =>
    cases h₂ with
    | par_skip_left hProc₂ =>
      left
      have heq := hProc₁.symm.trans hProc₂
      simp only [Process.par.injEq] at heq
      obtain ⟨_, hQ_eq⟩ := heq
      simp only [hQ_eq]
    | par_skip_right hProc₂ =>
      right
      exact ⟨_, _, _, _, hProc₁⟩
    | _ => simp_all
  | par_skip_right hProc₁ =>
    cases h₂ with
    | par_skip_right hProc₂ =>
      left
      have heq := hProc₁.symm.trans hProc₂
      simp only [Process.par.injEq] at heq
      rcases heq with ⟨_, ⟨_, ⟨hP_eq, _⟩⟩⟩
      simp only [hP_eq]
    | par_skip_left hProc₂ =>
      right
      exact ⟨_, _, _, _, hProc₁⟩
    | _ => simp_all

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

/-- A recv can step if:
    - The process is recv k x
    - k maps to endpoint e
    - G[e] says recv from source with type T and continuation L
    - The buffer at (sid, source, e.role) is non-empty -/
theorem recv_can_step {C k x e source T L} (hProc : C.proc = .recv k x)
    (hk : lookupStr C.store k = some (.chan e))
    (hG : lookupG C.G e = some (.recv source T L))
    (hBuf : (lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role }).length > 0) :
    ∃ C', Step C C' := by
  obtain ⟨v, vs, hEq⟩ : ∃ v vs, lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = v :: vs := by
    cases h : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } with
    | nil => simp_all
    | cons v vs => exact ⟨v, vs, rfl⟩
  exact ⟨_, Step.base (StepBase.recv hProc hk hG hEq)⟩

/-- A send can step if:
    - The process is send k x
    - k maps to endpoint e
    - x maps to value v
    - G[e] says send to target with type T and continuation L -/
theorem send_can_step {C : Config} {k x : Var} {e : Endpoint} {v : Value} {target : Role} {T : ValType} {L : LocalType}
    (hProc : C.proc = .send k x)
    (hk : lookupStr C.store k = some (.chan e))
    (hx : lookupStr C.store x = some v)
    (hG : lookupG C.G e = some (.send target T L)) :
    ∃ C', Step C C' :=
  ⟨_, Step.base (StepBase.send hProc hk hx hG)⟩

end
