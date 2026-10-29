
import Runtime.Proofs.ProgressCore
import Runtime.Proofs.FairTermination

/-! # Runtime.Proofs.ProgressTheorems

Protocol-machine progress, fairness-based termination, and HeadCoherent frame preservation.
-/

/-
The Problem. Derive executable progress and termination consequences from protocol-machine invariants.

Solution Structure. Progress: well-formedness discharges the readiness side
conditions, so any pending output (send, or select with a branch) or matching
frontier yields an enabled instruction. The step from "not all sessions
complete" to "some output is pending" needs global deadlock freedom and is not
proved here. Termination: `FairTermination.fair_termination` derives the
`k * measure` bound from one-step ranking obligations on the step function.
-/

/- ## Structured Block 1 -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

section

universe u
variable {ν : Type u} [VerificationModel ν]
-- Progress Theorem

/-- Terminal state: all sessions are complete (all endpoints at `end`). -/
def AllSessionsComplete (store : SessionStore ν) : Prop :=
  ∀ e L, SessionStore.lookupType store e = some L → L = .end_

/-- Frontier condition: at least one communication action is enabled at the type/buffer frontier. -/
def FrontierEnabled (store : SessionStore ν) : Prop :=
  (∃ ep target T L', SessionStore.lookupType store ep = some (.send target T L')) ∨
  (∃ ep source T L' rest,
    SessionStore.lookupType store ep = some (.recv source T L') ∧
    SessionStore.lookupTrace store { sid := ep.sid, sender := source, receiver := ep.role } = T :: rest) ∨
  (∃ ep target ℓ bs L',
    SessionStore.lookupType store ep = some (.select target bs) ∧
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L')) ∨
  (∃ ep source bs ℓ L' rest,
    SessionStore.lookupType store ep = some (.branch source bs) ∧
    SessionStore.lookupBuffer store { sid := ep.sid, sender := source, receiver := ep.role } = .string ℓ :: rest ∧
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L'))

/-- Protocol-machine progress conclusion: some concrete instruction form is enabled. -/
def EnabledInstruction (store : SessionStore ν) : Prop :=
  (∃ ep target T, SendEnabled store ep target T) ∨
  (∃ ep source T, RecvEnabled store ep source T) ∨
  (∃ ep target ℓ, SelectEnabled store ep target ℓ) ∨
  (∃ ep source, BranchEnabled store ep source)

/-- Some endpoint has a pending output: a send, or a select with at least one branch. -/
def HasPendingOutput (store : SessionStore ν) : Prop :=
  (∃ ep target T L', SessionStore.lookupType store ep = some (.send target T L')) ∨
  (∃ ep target ℓ L' bs,
    SessionStore.lookupType store ep = some (.select target ((ℓ, L') :: bs)))

/-- Frontier-to-instruction: a well-formed state's enabled frontier is an
enabled instruction (send/select readiness is discharged from `ProgressVMState`). -/
theorem enabled_instruction_of_frontier {store : SessionStore ν}
    (hWF : WellFormedVMState store) (hFrontier : FrontierEnabled store) :
    EnabledInstruction store := by
  have hSendReady : SendReady (SessionStore.toGEnv store) (SessionStore.toDEnv store) :=
    send_ready_of_progress_vm_state hWF.progress
  have hSelectReady : SelectReady (SessionStore.toGEnv store) (SessionStore.toDEnv store) :=
    select_ready_of_progress_vm_state hWF.progress
  rcases hFrontier with hSend | hRecv | hSelect | hBranch
  · rcases hSend with ⟨ep, target, T, L', hTy⟩
    exact Or.inl ⟨ep, target, T, ⟨L', hTy, hSendReady⟩⟩
  · rcases hRecv with ⟨ep, source, T, L', rest, hTy, hTrace⟩
    exact Or.inr (Or.inl ⟨ep, source, T, ⟨L', hTy, rest, hTrace⟩⟩)
  · rcases hSelect with ⟨ep, target, ℓ, bs, L', hTy, hFind⟩
    exact Or.inr (Or.inr (Or.inl ⟨ep, target, ℓ, ⟨bs, L', hTy, hFind, hSelectReady⟩⟩))
  · rcases hBranch with ⟨ep, source, bs, ℓ, L', rest, hTy, hBuf, hFind⟩
    exact Or.inr (Or.inr (Or.inr ⟨ep, source, ⟨bs, hTy, ℓ, L', rest, hBuf, hFind⟩⟩))

/-- A pending output is an enabled frontier (the first select branch is enabled). -/
theorem frontier_of_pending_output {store : SessionStore ν}
    (h : HasPendingOutput store) : FrontierEnabled store := by
  rcases h with ⟨ep, target, T, L', hTy⟩ | ⟨ep, target, ℓ, L', bs, hTy⟩
  · exact Or.inl ⟨ep, target, T, L', hTy⟩
  · exact Or.inr (Or.inr (Or.inl ⟨ep, target, ℓ, (ℓ, L') :: bs, L', hTy, by simp⟩))

/-- Progress: a well-formed state with a pending output has an enabled instruction.

    Input-only states (every live endpoint waits on recv/branch) need global
    deadlock freedom to rule out cyclic waiting; that fact is not derived here. -/
theorem protocol_machine_progress {store : SessionStore ν}
    (hWF : WellFormedVMState store) (hOut : HasPendingOutput store) :
    EnabledInstruction store :=
  enabled_instruction_of_frontier hWF (frontier_of_pending_output hOut)

-- Termination Under Fairness

/-- Sum of per-endpoint communication work in a session store. -/
def protocolMachineTypeMeasure (store : SessionStore ν) : Nat :=
  ((SessionStore.toGEnv store).map (fun p => p.2.progressMeasure)).foldl (· + ·) 0

/-- Sum of pending trace payload sizes in a session store. -/
/- ## Structured Block 2 -/
def protocolMachineTraceMeasure (store : SessionStore ν) : Nat :=
  ((SessionStore.toDEnv store).list.map (fun p => p.2.length)).foldl (· + ·) 0

/-- Lyapunov measure: endpoint communication work + pending trace load. -/
def protocolMachineMeasure (store : SessionStore ν) : Nat :=
  protocolMachineTypeMeasure store + protocolMachineTraceMeasure store

/-- Execute `n` scheduler-indexed steps from an initial session store. -/
abbrev executeSchedule
    (step : SessionStore ν → Nat → SessionStore ν)
    (store₀ : SessionStore ν) (sched : Nat → Nat) : Nat → SessionStore ν :=
  Runtime.Proofs.FairTermination.run step store₀ sched

/-- k-fairness over role indices: every role is scheduled in every k-window. -/
abbrev FairScheduler (numRoles k : Nat) (sched : Nat → Nat) : Prop :=
  Runtime.Proofs.FairTermination.KFair numRoles k sched

/-- One-step ranking obligations for a protocol-machine step function, with the
Lyapunov measure `protocolMachineMeasure`. Every field is a single-step fact;
the termination bound is derived, not assumed. -/
structure ProtocolMachineTerminationModel where
  /-- Finite role universe used by the scheduler. -/
  numRoles : Nat
  /-- At least one role exists. -/
  numRoles_pos : numRoles > 0
  /-- One-step semantics indexed by scheduled role. -/
  step : SessionStore ν → Nat → SessionStore ν
  /-- Role `r` has an enabled (productive) instruction. -/
  Enabled : SessionStore ν → Nat → Prop
  /-- No step increases the measure. -/
  nonincreasing : ∀ s r, protocolMachineMeasure (step s r) ≤ protocolMachineMeasure s
  /-- Running an enabled role strictly decreases the measure. -/
  enabled_decreases : ∀ s r, Enabled s r →
    protocolMachineMeasure (step s r) < protocolMachineMeasure s
  /-- Unproductive steps do not disable other roles. -/
  enabled_stable : ∀ s r r', Enabled s r →
    protocolMachineMeasure (step s r') = protocolMachineMeasure s → Enabled (step s r') r
  /-- A state that is not complete has an enabled role. -/
  progress : ∀ s, ¬ AllSessionsComplete s → ∃ r, r < numRoles ∧ Enabled s r

/-- The generic ranking induced by a termination model. -/
def ProtocolMachineTerminationModel.toRanking (model : ProtocolMachineTerminationModel (ν := ν)) :
    Runtime.Proofs.FairTermination.FairRanking (SessionStore ν) where
  numRoles := model.numRoles
  step := model.step
  measure := protocolMachineMeasure
  Done := AllSessionsComplete
  Enabled := model.Enabled
  nonincreasing := model.nonincreasing
  enabled_decreases := model.enabled_decreases
  enabled_stable := model.enabled_stable
  progress := model.progress

/-- Under k-fair scheduling, completion is reached within `k * measure` steps. -/
theorem protocol_machine_termination_under_fairness {store₀ : SessionStore ν}
    (model : ProtocolMachineTerminationModel (ν := ν))
    {sched : Nat → Nat} {k : Nat}
    (hFair : FairScheduler model.numRoles k sched) :
    ∃ (n : Nat) (store_final : SessionStore ν),
      store_final = executeSchedule model.step store₀ sched n ∧
      AllSessionsComplete store_final ∧
      n ≤ k * protocolMachineMeasure store₀ := by
  obtain ⟨n, hn, hDone⟩ :=
    Runtime.Proofs.FairTermination.FairRanking.fair_termination model.toRanking store₀ sched hFair
  exact ⟨n, _, rfl, hDone, hn⟩

-- HeadCoherent Maintenance

/-- HeadCoherent is preserved for edges not affected by an instruction.

    This is the frame property for HeadCoherent: if an instruction only
    affects session s, HeadCoherent is preserved for all other sessions. -/
theorem instr_preserves_head_coherent_other {store store' : SessionStore ν}
    {s : SessionId}
    (hWF : sessionStore_refines_envs store)
    (hWF' : sessionStore_refines_envs store')
    (hHead : HeadCoherent (SessionStore.toGEnv store) (SessionStore.toDEnv store))
    (hFrame : ∀ e, e.sid ≠ s → SessionStore.lookupType store e = SessionStore.lookupType store' e)
    (hFrameD : ∀ edge, edge.sid ≠ s →
      SessionStore.lookupTrace store edge = SessionStore.lookupTrace store' edge) :
    ∀ e, e.sid ≠ s → ActiveEdge (SessionStore.toGEnv store') e →
      match lookupG (SessionStore.toGEnv store') { sid := e.sid, role := e.receiver } with
      | some (.recv _ T _) =>
          match lookupD (SessionStore.toDEnv store') e with
/- ## Structured Block 3 -/
          | [] => True
          | T' :: _ => T = T'
      | some (.branch _ _) =>
          match lookupD (SessionStore.toDEnv store') e with
          | [] => True
          | T' :: _ => T' = .string
      | _ => True := by
  intro e hSidNe hActive'
  let senderEp : Endpoint := { sid := e.sid, role := e.sender }
  let receiverEp : Endpoint := { sid := e.sid, role := e.receiver }

  -- # Global Lookup Frame Equalities

  have hSenderEq : lookupG (SessionStore.toGEnv store') senderEp =
      lookupG (SessionStore.toGEnv store) senderEp := by
    calc
      lookupG (SessionStore.toGEnv store') senderEp
          = SessionStore.lookupType store' senderEp := store_lookup_type_eq_lookup_g (hWF := hWF')
      _ = SessionStore.lookupType store senderEp := by
            symm
            exact hFrame senderEp (by simpa [senderEp] using hSidNe)
      _ = lookupG (SessionStore.toGEnv store) senderEp :=
            (store_lookup_type_eq_lookup_g (hWF := hWF)).symm
  have hReceiverEq : lookupG (SessionStore.toGEnv store') receiverEp =
      lookupG (SessionStore.toGEnv store) receiverEp := by
    calc
      lookupG (SessionStore.toGEnv store') receiverEp
          = SessionStore.lookupType store' receiverEp := store_lookup_type_eq_lookup_g (hWF := hWF')
      _ = SessionStore.lookupType store receiverEp := by
            symm
            exact hFrame receiverEp (by simpa [receiverEp] using hSidNe)
      _ = lookupG (SessionStore.toGEnv store) receiverEp :=
            (store_lookup_type_eq_lookup_g (hWF := hWF)).symm

  -- # Trace Lookup Equality

  have hTraceEq : lookupD (SessionStore.toDEnv store') e =
      lookupD (SessionStore.toDEnv store) e := by
    calc
      lookupD (SessionStore.toDEnv store') e
          = SessionStore.lookupTrace store' e := store_lookup_trace_eq_lookup_d (hWF := hWF')
      _ = SessionStore.lookupTrace store e := by
            symm
            exact hFrameD e hSidNe
      _ = lookupD (SessionStore.toDEnv store) e :=
            (store_lookup_trace_eq_lookup_d (hWF := hWF)).symm

  -- # ActiveEdge and HeadCoherent Transfer

  have hActive : ActiveEdge (SessionStore.toGEnv store) e := by
    unfold ActiveEdge at hActive' ⊢
    constructor
    · have hS := hActive'.1
      simpa [senderEp, hSenderEq] using hS
    · have hR := hActive'.2
      simpa [receiverEp, hReceiverEq] using hR
  have hOld := hHead e hActive
  rw [hReceiverEq, hTraceEq]
  exact hOld


end
