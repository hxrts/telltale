import Protocol.Preservation.PreservationProgressWrappers

/-! # Progress Lemmas

Progress theorems for individual process forms (send, recv, select,
branch), showing well-typed processes can always step unless blocked
on an empty buffer. -/

/-
The Problem. Type safety requires progress: well-typed configurations
either step or are in a recognized blocked state. We need per-constructor
progress lemmas for send, recv, select, and branch.

Solution Structure. Define `BlockedRecv` predicate for the blocked-recv
case. Prove `progress_send`, `progress_recv`, `progress_select`,
`progress_branch` showing typed processes step or are blocked.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## Progress Lemmas for Individual Process Forms

These lemmas are currently axiomatized to keep the development building while
TypedStep-based proofs are refactored.
-/

/-- Blocked recv predicate: recv/branch is waiting on an empty buffer. -/
def BlockedRecv (C : Config) : Prop :=
  (∃ k x source T L, ∃ e : Endpoint,
    C.proc = .recv k x ∧
    lookupStr C.store k = some (.chan e) ∧
    lookupG C.G e = some (.recv source T L) ∧
    lookupBuf C.bufs ⟨e.sid, source, e.role⟩ = []) ∨
  (∃ k procs source bs, ∃ e : Endpoint,
    C.proc = .branch k procs ∧
    lookupStr C.store k = some (.chan e) ∧
    lookupG C.G e = some (.branch source bs) ∧
    lookupBuf C.bufs ⟨e.sid, source, e.role⟩ = [])


end
