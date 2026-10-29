import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic

set_option autoImplicit false

/-! # Distributed.Families.CAP.Register

A concrete two-node asynchronous read/write register model for the CAP
theorem (Gilbert–Lynch, "Brewer's Conjecture and the Feasibility of
Consistent, Available, Partition-Tolerant Web Services", SIGACT News 2002,
Theorem 1).

* Two nodes `a`, `b` run a deterministic algorithm. On each event a node
  receives an input (a client invocation, a delivered message, or a local
  `tick`), updates its state, sends a list of messages to the other node, and
  may emit a client response.
* Executions are infinite event sequences. Messages sit in the recipient's
  in-flight list until a `deliver` event; a *partitioned* execution never
  delivers, i.e. every message between the two sides is lost.
* `Available`: in every partitioned fair execution (both nodes keep taking
  steps), every invocation at a node is followed by a response at that node.
* `Atomic`: the two consequences of linearizability (atomic consistency) for
  a register with initial value `v₀` used by Gilbert–Lynch, stated on every
  execution: (1) a read with no write invoked before its response returns
  `v₀`; (2) a read invoked after the response to the only write `write v`
  returns `v`.
-/

/-
The Problem. The CAP family previously took the inconsistent partitioned run as
a premise. Solution Structure. Give a concrete register model in which the
Gilbert–Lynch execution can be constructed; the proof is in `CAP.Theorem`.
-/

namespace Distributed
namespace CAP
namespace Register

/-! ## Nodes, Operations, Algorithms -/

/-- The two nodes, one on each side of the partition. -/
inductive Node where
  | a
  | b
  deriving DecidableEq, Repr

/-- The node across the partition. -/
def Node.other : Node → Node
  | .a => .b
  | .b => .a

/-- Register operations invoked by clients. -/
inductive Op (Val : Type) where
  | write (v : Val)
  | read

/-- Client responses. -/
inductive Out (Val : Type) where
  | ack
  | ret (v : Val)
  deriving DecidableEq

/-- Inputs to a node's local step. -/
inductive Input (Val Msg : Type) where
  | invoke (op : Op Val)
  | recv (m : Msg)
  | tick

/-- A deterministic two-node register algorithm. A step returns the new local
state, messages sent to the other node, and an optional client response. -/
structure Algorithm (Val Msg St : Type) where
  init : Node → St
  step : Node → St → Input Val Msg → St × List Msg × Option (Out Val)

/-! ## Executions -/

/-- Scheduler events: invocations, local ticks, and deliveries of the `i`-th
in-flight message to a node. -/
inductive Event (Val : Type) where
  | invoke (n : Node) (op : Op Val)
  | tick (n : Node)
  | deliver (n : Node) (i : ℕ)

/-- The node taking the step. -/
def Event.node {Val : Type} : Event Val → Node
  | .invoke n _ => n
  | .tick n => n
  | .deliver n _ => n

/-- Whether the event is a client invocation. -/
def Event.isInvoke {Val : Type} : Event Val → Bool
  | .invoke _ _ => true
  | _ => false

/-- Global configuration: local states and in-flight messages per recipient. -/
structure Config (Msg St : Type) where
  st : Node → St
  inbox : Node → List Msg

variable {Val Msg St : Type} (A : Algorithm Val Msg St)

/-- The local input of an event (a delivery of a missing message is a no-op). -/
def Event.input (C : Config Msg St) : Event Val → Option (Input Val Msg)
  | .invoke _ op => some (.invoke op)
  | .tick _ => some .tick
  | .deliver n i => (C.inbox n)[i]?.map Input.recv

/-- In-flight messages after consuming the delivered one. -/
def consumed (C : Config Msg St) : Event Val → (Node → List Msg)
  | .deliver n i => Function.update C.inbox n ((C.inbox n).eraseIdx i)
  | _ => C.inbox

/-- One global step: the new configuration and the emitted response. -/
def stepC (C : Config Msg St) (e : Event Val) : Config Msg St × Option (Out Val) :=
  match e.input C with
  | none => (C, none)
  | some inp =>
    let r := A.step e.node (C.st e.node) inp
    let ib := consumed C e
    ({ st := Function.update C.st e.node r.1
       inbox := Function.update ib e.node.other (ib e.node.other ++ r.2.1) }, r.2.2)

/-- Configurations of the execution driven by the event sequence `e`. -/
def cfgs (e : ℕ → Event Val) : ℕ → Config Msg St
  | 0 => ⟨A.init, fun _ => []⟩
  | k + 1 => (stepC A (cfgs e k) (e k)).1

/-- The response emitted at step `k` (at node `(e k).node`). -/
def outAt (e : ℕ → Event Val) (k : ℕ) : Option (Out Val) :=
  (stepC A (cfgs A e k) (e k)).2

/-! ## Partitions, Fairness, Responses -/

/-- A partitioned execution: no message is ever delivered. -/
def Partitioned (e : ℕ → Event Val) : Prop :=
  ∀ k n i, e k ≠ .deliver n i

/-- A fair execution: both nodes take infinitely many local steps. -/
def Fair (e : ℕ → Event Val) : Prop :=
  ∀ n N, ∃ k, N ≤ k ∧ e k = .tick n

/-- Step `j` is the first response at node `n` after the invocation at `k`,
with no further invocation at `n` in between. -/
def Responds (e : ℕ → Event Val) (n : Node) (k j : ℕ) : Prop :=
  k < j ∧ (e j).node = n ∧ (outAt A e j).isSome ∧
    ∀ i, k < i → i < j → (e i).node = n → outAt A e i = none ∧ (e i).isInvoke = false

/-- Gilbert–Lynch availability under partition: in every partitioned fair
execution, every invocation at a node receives a later response at that node. -/
def Available : Prop :=
  ∀ e : ℕ → Event Val, Partitioned e → Fair e → ∀ k n op, e k = .invoke n op →
    ∃ j, k < j ∧ (e j).node = n ∧ (outAt A e j).isSome

/-- Atomic (linearizable) register consistency with initial value `v₀`, in the
two instances used by the CAP proof; both hold in every execution of a
linearizable register. -/
def Atomic (v₀ : Val) : Prop :=
  (∀ (e : ℕ → Event Val) k j m,
      (∀ i, i < j → ∀ n v, e i ≠ .invoke n (.write v)) →
      e k = .invoke m .read → Responds A e m k j → outAt A e j = some (.ret v₀)) ∧
  (∀ (e : ℕ → Event Val) k₁ j₁ k₂ j₂ n m (v : Val), e k₁ = .invoke n (.write v) →
      (∀ i, i < j₂ → i ≠ k₁ → ∀ n' v', e i ≠ .invoke n' (.write v')) →
      Responds A e n k₁ j₁ → j₁ < k₂ → e k₂ = .invoke m .read →
      Responds A e m k₂ j₂ → outAt A e j₂ = some (.ret v))

/-! ## Indistinguishability Lemmas -/

/-- Executions agreeing on the first `N` events agree on configurations up to `N`. -/
theorem cfgs_prefix {e e' : ℕ → Event Val} {N : ℕ} (h : ∀ i, i < N → e i = e' i) :
    ∀ k, k ≤ N → cfgs (Msg := Msg) A e k = cfgs A e' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    simp only [cfgs, ih (by omega), h k (by omega)]

/-- Executions agreeing on the first `N` events emit the same responses there. -/
theorem outAt_prefix {e e' : ℕ → Event Val} {N : ℕ} (h : ∀ i, i < N → e i = e' i)
    {k : ℕ} (hk : k < N) : outAt A e k = outAt A e' k := by
  unfold outAt
  rw [cfgs_prefix A h k (Nat.le_of_lt hk), h k hk]

/-- A non-delivery step leaves the state of every other node unchanged. -/
theorem stepC_st_other (C : Config Msg St) (x : Event Val) (hx : ∀ n i, x ≠ .deliver n i)
    {n : Node} (hn : x.node ≠ n) : (stepC A C x).1.st n = C.st n := by
  cases x with
  | invoke m op =>
    simp only [Event.node] at hn
    simp [stepC, Event.input, Event.node, Function.update_of_ne (Ne.symm hn)]
  | tick m =>
    simp only [Event.node] at hn
    simp [stepC, Event.input, Event.node, Function.update_of_ne (Ne.symm hn)]
  | deliver m i => exact absurd rfl (hx m i)

/-- A non-delivery step at a node depends only on that node's state. -/
theorem stepC_self {C D : Config Msg St} (x : Event Val) (hx : ∀ n i, x ≠ .deliver n i)
    (h : C.st x.node = D.st x.node) :
    (stepC A C x).1.st x.node = (stepC A D x).1.st x.node ∧ (stepC A C x).2 = (stepC A D x).2 := by
  cases x with
  | invoke m op => simp_all [stepC, Event.input, Event.node]
  | tick m => simp_all [stepC, Event.input, Event.node]
  | deliver m i => exact absurd rfl (hx m i)

/-- Under partition, a node's state depends only on the events at that node. -/
theorem cfgs_local {e e' : ℕ → Event Val} (n : Node) (hp : Partitioned e) (hp' : Partitioned e')
    (h : ∀ i, (e i).node = n ∨ (e' i).node = n → e i = e' i) :
    ∀ k, (cfgs (Msg := Msg) A e k).st n = (cfgs A e' k).st n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (stepC A (cfgs A e k) (e k)).1.st n = (stepC A (cfgs A e' k) (e' k)).1.st n
    by_cases hn : (e k).node = n
    · have hee := h k (Or.inl hn)
      rw [← hee]
      have := (stepC_self A (C := cfgs A e k) (D := cfgs A e' k) (e k) (hp k)
        (by rw [hn]; exact ih)).1
      rwa [hn] at this
    · have hn' : (e' k).node ≠ n := fun h' => hn (by rw [h k (Or.inr h')] <;> exact h')
      rw [stepC_st_other A _ _ (hp k) hn, stepC_st_other A _ _ (hp' k) hn', ih]

/-- Under partition, responses at a node depend only on the events at that node. -/
theorem outAt_local {e e' : ℕ → Event Val} (n : Node) (hp : Partitioned e)
    (hp' : Partitioned e') (h : ∀ i, (e i).node = n ∨ (e' i).node = n → e i = e' i)
    {k : ℕ} (hk : (e k).node = n) : outAt (Msg := Msg) A e k = outAt A e' k := by
  have hee := h k (Or.inl hk)
  unfold outAt
  rw [← hee]
  exact (stepC_self A (e k) (hp k)
    (by rw [hk]; exact cfgs_local A n hp hp' h k)).2

/-- Transfer a first-response fact between executions that agree, on the
relevant window, at the events and responses of node `n`. -/
theorem responds_transfer {e e' : ℕ → Event Val} {n : Node} {k j : ℕ}
    (h : ∀ i, k < i → i ≤ j → ((e i).node = n ∨ (e' i).node = n) →
      e i = e' i ∧ outAt (Msg := Msg) A e i = outAt A e' i)
    (hr : Responds (Msg := Msg) A e n k j) : Responds A e' n k j := by
  obtain ⟨hkj, hnode, hsome, hmid⟩ := hr
  obtain ⟨hej, hoj⟩ := h j hkj (Nat.le_refl j) (Or.inl hnode)
  refine ⟨hkj, by rw [← hej]; exact hnode, by rw [← hoj]; exact hsome,
    fun i hki hij hni => ?_⟩
  obtain ⟨hei, hoi⟩ := h i hki (Nat.le_of_lt hij) (Or.inr hni)
  rw [← hei] at hni ⊢
  rw [← hoi]
  exact hmid i hki hij hni

end Register
end CAP
end Distributed
