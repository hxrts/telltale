set_option autoImplicit false

/-! # Distributed.Model.Simulation

Labeled transition systems and lockstep forward simulation, used to *prove*
observational adequacy of an implementation against a reference model instead
of assuming it as a refinement hypothesis.
-/

/-
The Problem. Envelope/adequacy statements previously took the per-step
observational agreement of reference and implementation runs as a premise.
Solution Structure. Give both sides labeled step relations, define runs driven
by a shared label stream, and prove agreement at every index by induction from
a simulation relation that implies observational equality.
-/

namespace Distributed
namespace Simulation

universe u v w x

/-! ## Labeled Systems and Runs -/

/-- A labeled transition system with an initial-state predicate. -/
structure LabeledSystem (State : Type u) (Label : Type v) where
  init : State → Prop
  step : Label → State → State → Prop

/-- `r` is a run of `S` driven by the label stream `labels`. -/
def RunOf {State : Type u} {Label : Type v} (S : LabeledSystem State Label)
    (labels : Nat → Label) (r : Nat → State) : Prop :=
  S.init (r 0) ∧ ∀ n, S.step (labels n) (r n) (r (n + 1))

/-! ## Lockstep Simulation -/

/-- Lockstep forward simulation between a reference and an implementation
system: related initial states, preservation under same-label steps, and
observational agreement of related states. -/
structure LockstepSimulation
    {RState : Type u} {IState : Type v} {Label : Type w} {Obs : Type x}
    (Ref : LabeledSystem RState Label) (Impl : LabeledSystem IState Label)
    (obsRef : RState → Obs) (obsImpl : IState → Obs) where
  rel : RState → IState → Prop
  init : ∀ {s t}, Ref.init s → Impl.init t → rel s t
  step : ∀ {l s s' t t'}, rel s t → Ref.step l s s' → Impl.step l t t' → rel s' t'
  obs : ∀ {s t}, rel s t → obsRef s = obsImpl t

/-- Runs driven by the same labels stay related at every index. -/
theorem rel_of_runs
    {RState : Type u} {IState : Type v} {Label : Type w} {Obs : Type x}
    {Ref : LabeledSystem RState Label} {Impl : LabeledSystem IState Label}
    {obsRef : RState → Obs} {obsImpl : IState → Obs}
    (sim : LockstepSimulation Ref Impl obsRef obsImpl)
    {labels : Nat → Label} {ref : Nat → RState} {impl : Nat → IState}
    (hRef : RunOf Ref labels ref) (hImpl : RunOf Impl labels impl) :
    ∀ n, sim.rel (ref n) (impl n) := by
  intro n
  induction n with
  | zero => exact sim.init hRef.1 hImpl.1
  | succ n ih => exact sim.step ih (hRef.2 n) (hImpl.2 n)

/-- Adequacy by simulation: same-label runs agree observationally at every index. -/
theorem obs_agree_of_simulation
    {RState : Type u} {IState : Type v} {Label : Type w} {Obs : Type x}
    {Ref : LabeledSystem RState Label} {Impl : LabeledSystem IState Label}
    {obsRef : RState → Obs} {obsImpl : IState → Obs}
    (sim : LockstepSimulation Ref Impl obsRef obsImpl)
    {labels : Nat → Label} {ref : Nat → RState} {impl : Nat → IState}
    (hRef : RunOf Ref labels ref) (hImpl : RunOf Impl labels impl) :
    ∀ n, obsRef (ref n) = obsImpl (impl n) :=
  fun n => sim.obs (rel_of_runs sim hRef hImpl n)

end Simulation
end Distributed
