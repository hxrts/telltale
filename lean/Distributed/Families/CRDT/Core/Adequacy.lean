import Distributed.Families.CRDT.Core.CoreModel
import Distributed.Model.Simulation

set_option autoImplicit false

/-! # Distributed.Families.CRDT.Core.Adequacy

Observational adequacy of an anti-entropy (gossip) CRDT replica against the
reference exactly-once delivery semantics, proved by lockstep simulation.

Reference step on update `o`: `s' = M.apply o s`.
Implementation step on update `o`: first re-merge any state `d` the replica
already dominates (a duplicated/stale gossip message), then apply `o`.
Idempotence of join makes the duplicate invisible, so the two runs are equal at
every index and in particular stay inside the envelope.
-/

/-
The Problem. CRDT adequacy was a restated refinement premise.
Solution Structure. Define both step relations from `Model`, use equality as
the simulation relation, discharge the step obligation with `join_of_le`.
-/

namespace Distributed
namespace CRDT

open Simulation

universe u v w x y

variable {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}

/-- Reference semantics: exactly-once delivery from initial state `base`. -/
def refDeliverySystem (M : Model State Op Context Obs Program) (base : State) :
    LabeledSystem State Op where
  init s := s = base
  step o s s' := s' = M.apply o s

/-- Implementation: gossip replica that may re-merge an already-dominated state
before applying the next update. -/
def gossipReplicaSystem (M : Model State Op Context Obs Program) (base : State) :
    LabeledSystem State Op where
  init s := s = base
  step o t t' := ∃ d, M.lattice.le d t ∧ t' = M.apply o (M.lattice.join t d)

/-- Equality is a lockstep simulation between reference and gossip replica. -/
def gossipSimulation (M : Model State Op Context Obs Program) (base : State) :
    LockstepSimulation (refDeliverySystem M base) (gossipReplicaSystem M base)
      M.observe M.observe where
  rel s t := s = t
  init hs ht := hs.trans ht.symm
  step := by
    intro o s s' t t' hRel hs ht
    obtain ⟨d, hd, rfl⟩ := ht
    simp only [refDeliverySystem] at hs
    rw [hs, hRel, M.lattice.join_of_le hd]
  obs h := congrArg _ h

/-- Proved adequacy: gossip-replica runs are observationally adequate for the
reference delivery semantics on every update stream. -/
theorem gossip_replica_adequacy (M : Model State Op Context Obs Program)
    (base : State) (labels : Nat → Op) :
    ObservationalAdequacyModuloEnvelope M
      (RunOf (refDeliverySystem M base) labels)
      (RunOf (gossipReplicaSystem M base) labels) := by
  intro ref impl hRef hImpl n
  exact obs_agree_of_simulation (gossipSimulation M base) hRef hImpl n

end CRDT
end Distributed
