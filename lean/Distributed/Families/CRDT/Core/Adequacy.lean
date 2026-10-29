import Distributed.Families.CRDT.Core.CoreModel
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Tauto

set_option autoImplicit false

/-! # Distributed.Families.CRDT.Core.Adequacy

Observational adequacy and convergence of an `n`-replica anti-entropy (gossip)
state-based CRDT cluster against the reference exactly-once delivery
semantics.

Cluster (`Cluster`, `GStep`):
- `update i o`: replica `i` applies a local update, `st i := M.apply o (st i)`,
- `send i`: replica `i` puts a snapshot of its current state on the network
  (messages are never removed, so they may be delivered late, reordered, or
  any number of times),
- `recv j m`: replica `j` merges a peer state `m` from the network,
  `st j := join (st j) m`.

The ghost field `known` (and the ghost op log carried by each message) records
which updates a state has absorbed; it never influences the real state.

Theorems (all from the join-semilattice laws, via `Model.sec`):
- `reachable_inv`: every replica state is the reference delivery of its
  absorbed updates,
- `replica_adequacy`: each replica equals exactly-once delivery of the
  duplicate-free list of updates it absorbed,
- `replicas_converge`: two replicas that absorbed the same set of updates are
  equal (strong eventual consistency for the gossip system),
- `gossip_execution_adequacy`: along any execution, each replica's run is
  observationally adequate for its reference run.
-/

/-
The Problem. A previous gossip replica only re-merged states it already
dominated, never a peer's state, so the simulation was trivial.
Solution Structure. Model `n` replicas and a network of sent states, prove an
invariant linking each state to the reference delivery of its ghost op log,
and conclude with `Model.sec`.
-/

namespace Distributed
namespace CRDT

universe u v w x y

variable {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}

/-! ## Gossip Cluster -/

/-- Cluster configuration: replica states, ghost op logs, and the network. -/
structure Cluster (State : Type u) (Op : Type v) (n : Nat) where
  st : Fin n → State
  known : Fin n → List Op
  net : List (State × List Op)

/-- Gossip steps: local update, send a snapshot, merge a received peer state. -/
inductive GStep (M : Model State Op Context Obs Program) {n : Nat} :
    Cluster State Op n → Cluster State Op n → Prop
  | update (c : Cluster State Op n) (i : Fin n) (o : Op) :
      GStep M c ⟨Function.update c.st i (M.apply o (c.st i)),
        Function.update c.known i (c.known i ++ [o]), c.net⟩
  | send (c : Cluster State Op n) (i : Fin n) :
      GStep M c ⟨c.st, c.known, (c.st i, c.known i) :: c.net⟩
  | recv (c : Cluster State Op n) (j : Fin n) (m : State × List Op) (hm : m ∈ c.net) :
      GStep M c ⟨Function.update c.st j (M.lattice.join (c.st j) m.1),
        Function.update c.known j (c.known j ++ m.2), c.net⟩

/-- Initial cluster: every replica at `base`, nothing absorbed, empty network. -/
def initCluster {n : Nat} (base : State) : Cluster State Op n :=
  ⟨fun _ => base, fun _ => [], []⟩

/-- Reachable cluster configurations. -/
inductive GReach (M : Model State Op Context Obs Program) {n : Nat} (base : State) :
    Cluster State Op n → Prop
  | init : GReach M base (initCluster base)
  | step {c c'} : GReach M base c → GStep M c c' → GReach M base c'

/-- Invariant: replica states and network messages are reference deliveries of
their ghost op logs. -/
def ClusterInv (M : Model State Op Context Obs Program) {n : Nat} (base : State)
    (c : Cluster State Op n) : Prop :=
  (∀ i, c.st i = M.deliver base (c.known i)) ∧ ∀ m ∈ c.net, m.1 = M.deliver base m.2

/-! ## Delivery Algebra -/

/-- Delivering one more update is applying it. -/
theorem Model.deliver_snoc (M : Model State Op Context Obs Program) (base : State)
    (l : List Op) (o : Op) : M.deliver base (l ++ [o]) = M.apply o (M.deliver base l) := by
  simp [Model.deliver, List.foldl_append]

/-- Merging two deliveries from a common base delivers the concatenated logs. -/
theorem Model.join_deliver (M : Model State Op Context Obs Program) (base : State)
    (l₁ l₂ : List Op) :
    M.lattice.join (M.deliver base l₁) (M.deliver base l₂) = M.deliver base (l₁ ++ l₂) := by
  rw [M.deliver_eq_mergeAll, M.deliver_eq_mergeAll, M.deliver_eq_mergeAll]
  apply M.lattice.eq_of_le_iff
  intro c
  rw [M.lattice.join_le_iff, mergeAll_le_iff, mergeAll_le_iff, mergeAll_le_iff]
  simp only [List.map_append, List.mem_append, or_imp, forall_and]
  tauto

/-! ## Invariant -/

/-- Each step preserves the invariant. -/
theorem gstep_inv {M : Model State Op Context Obs Program} {n : Nat} {base : State}
    {c c' : Cluster State Op n} (h : GStep M c c') (hI : ClusterInv M base c) :
    ClusterInv M base c' := by
  obtain ⟨hSt, hNet⟩ := hI
  cases h with
  | update i o =>
    refine ⟨fun k => ?_, hNet⟩
    by_cases hk : k = i
    · subst hk; simp [M.deliver_snoc, hSt]
    · simp [Function.update_of_ne hk, hSt]
  | send i =>
    refine ⟨hSt, fun m hm => ?_⟩
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hSt i
    · exact hNet m hm
  | recv j m hm =>
    refine ⟨fun k => ?_, hNet⟩
    by_cases hk : k = j
    · subst hk; simp [hSt, hNet m hm, M.join_deliver]
    · simp [Function.update_of_ne hk, hSt]

/-- Reachable clusters satisfy the invariant. -/
theorem reachable_inv {M : Model State Op Context Obs Program} {n : Nat} {base : State}
    {c : Cluster State Op n} (h : GReach M base c) : ClusterInv M base c := by
  induction h with
  | init => exact ⟨fun _ => rfl, fun _ hm => by simp [initCluster] at hm⟩
  | step _ hs ih => exact gstep_inv hs ih

/-! ## Adequacy and Convergence -/

/-- Replica adequacy: a reachable replica equals exactly-once reference delivery
of the duplicate-free list of updates it absorbed. -/
theorem replica_adequacy {M : Model State Op Context Obs Program} {n : Nat} {base : State}
    {c : Cluster State Op n} [DecidableEq Op] (h : GReach M base c) (i : Fin n) :
    c.st i = M.deliver base (c.known i).dedup := by
  rw [(reachable_inv h).1 i]
  exact M.sec base _ _ fun o => List.mem_dedup.symm

/-- Strong eventual consistency of the gossip cluster: replicas that absorbed
the same set of updates hold equal states. -/
theorem replicas_converge {M : Model State Op Context Obs Program} {n : Nat} {base : State}
    {c : Cluster State Op n} (h : GReach M base c) (i j : Fin n)
    (hSame : ∀ o, o ∈ c.known i ↔ o ∈ c.known j) : c.st i = c.st j := by
  rw [(reachable_inv h).1 i, (reachable_inv h).1 j]
  exact M.sec base _ _ hSame

/-- An execution of the gossip cluster from `initCluster base`. -/
def IsGossipExecution (M : Model State Op Context Obs Program) {n : Nat} (base : State)
    (exec : Nat → Cluster State Op n) : Prop :=
  exec 0 = initCluster base ∧ ∀ k, GStep M (exec k) (exec (k + 1))

/-- Prefixes of an execution are reachable. -/
theorem execution_reachable {M : Model State Op Context Obs Program} {n : Nat}
    {base : State} {exec : Nat → Cluster State Op n} (hE : IsGossipExecution M base exec) :
    ∀ k, GReach M base (exec k)
  | 0 => hE.1 ▸ GReach.init
  | k + 1 => GReach.step (execution_reachable hE k) (hE.2 k)

/-- Execution-level adequacy: along any gossip execution, replica `i`'s run is
observationally adequate for exactly-once delivery of its absorbed updates. -/
theorem gossip_execution_adequacy [DecidableEq Op] (M : Model State Op Context Obs Program)
    {n : Nat} (base : State) (exec : Nat → Cluster State Op n)
    (hE : IsGossipExecution M base exec) (i : Fin n) :
    ObservationalAdequacyModuloEnvelope M
      (· = fun k => M.deliver base ((exec k).known i).dedup)
      (· = fun k => (exec k).st i) := by
  rintro _ _ rfl rfl k
  exact congrArg M.observe (replica_adequacy (execution_reachable hE k) i).symm

end CRDT
end Distributed
