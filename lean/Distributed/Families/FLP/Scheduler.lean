import Distributed.Families.FLP.Runs
import Mathlib.Basic.Countable.Basic
import Mathlib.Data.Nat.Pairing

set_option autoImplicit false

/-! # Distributed.Families.FLP.Scheduler

A generic fair-scheduler construction for the FLP model.

FLP (1985, Theorem 1) builds admissible runs in stages: a queue of targets
(a process together with a message for it, or the null message) is served in
turn, and each stage executes a nonempty finite schedule that contains the
target event whenever that event is applicable. We abstract this as `Sched`:
a stage function, an enumeration of targets hitting every target infinitely
often, a stage invariant, and the set of `Alive` processes whose targets must
be served. The resulting infinite run is a `Run` in which every alive process
takes infinitely many steps and every message to an alive process is
eventually received. A finite prefix schedule may be executed first.
-/

namespace Distributed
namespace FLP
namespace Async

variable {Proc Msg St : Type} [DecidableEq Proc] [DecidableEq Msg]
variable {P : Protocol Proc Msg St}

/-! ## Target Enumeration -/

/-- A countable nonempty type admits an enumeration hitting every element
infinitely often. -/
theorem exists_tgt (α : Type) [Nonempty α] [Countable α] :
    ∃ f : ℕ → α, ∀ t N, ∃ i, N ≤ i ∧ f i = t := by
  obtain ⟨g, hg⟩ := exists_surjective_nat α
  refine ⟨fun i => g (Nat.unpair i).1, fun t N => ?_⟩
  obtain ⟨a, rfl⟩ := hg t
  exact ⟨Nat.pair a N, Nat.right_le_pair a N, by simp [Nat.unpair_pair]⟩

/-- An event that is never taken from index `k` on stays applicable. -/
theorem Run.applicable_persist (r : Run P) {k : ℕ} {t : Event Proc Msg}
    (hne : ∀ j, k ≤ j → r.ev j ≠ t) (ht : Applicable (r.cfg k) t) :
    ∀ n, Applicable (r.cfg (k + n)) t := by
  intro n
  induction n with
  | zero => exact ht
  | succ n ih =>
    rw [← Nat.add_assoc, (r.valid _).2]
    exact applicable_apply_of_ne P ih (hne _ (by omega))

/-! ## Stage Schedulers -/

/-- A stage scheduler: stages are nonempty applicable schedules preserving the
invariant and containing every applicable target of an alive process. -/
structure Sched (P : Protocol Proc Msg St) where
  stage : Config Proc Msg St → Event Proc Msg → Schedule Proc Msg
  tgt : ℕ → Event Proc Msg
  Inv : Config Proc Msg St → Prop
  Alive : Proc → Prop
  nonempty : ∀ C t, Inv C → stage C t ≠ []
  appl : ∀ C t, Inv C → Appl P C (stage C t)
  inv : ∀ C t, Inv C → Inv (exec P C (stage C t))
  serves : ∀ C t, Inv C → Alive t.1 → Applicable C t → t ∈ stage C t
  tgt_inf : ∀ t N, ∃ i, N ≤ i ∧ tgt i = t

/-- Machine state: next stage index, pending events, current configuration. -/
structure MState (Proc Msg St : Type) where
  idx : ℕ
  pend : Schedule Proc Msg
  cfg : Config Proc Msg St

namespace Sched

variable (S : Sched P)

/-- Start a new stage when nothing is pending. -/
def refill (s : MState Proc Msg St) : MState Proc Msg St :=
  match s.pend with
  | [] => ⟨s.idx + 1, S.stage s.cfg (S.tgt s.idx), s.cfg⟩
  | _ :: _ => s

/-- Execute the next pending event (the scheduler argument is only for dot notation). -/
def pop (_S : Sched P) (s : MState Proc Msg St) : MState Proc Msg St :=
  match s.pend with
  | [] => s
  | e :: rest => ⟨s.idx, rest, apply P s.cfg e⟩

/-- Machine states, starting with the prefix `pre` at configuration `C₀`. -/
def states (pre : Schedule Proc Msg) (C₀ : Config Proc Msg St) : ℕ → MState Proc Msg St
  | 0 => ⟨0, pre, C₀⟩
  | k + 1 => S.pop (S.refill (states pre C₀ k))

/-- Machine invariant: pending events are applicable and lead to `Inv`. -/
def Good (s : MState Proc Msg St) : Prop :=
  Appl P s.cfg s.pend ∧ S.Inv (exec P s.cfg s.pend)

/-- Refilling preserves `Good`, yields pending work, and keeps the configuration. -/
theorem refill_good {s : MState Proc Msg St} (h : S.Good s) :
    S.Good (S.refill s) ∧ (S.refill s).pend ≠ [] ∧ (S.refill s).cfg = s.cfg := by
  rcases s with ⟨i, _ | ⟨e, rest⟩, C⟩
  · have hI : S.Inv C := h.2
    exact ⟨⟨S.appl C _ hI, S.inv C _ hI⟩, S.nonempty C _ hI, rfl⟩
  · exact ⟨h, List.cons_ne_nil _ _, rfl⟩

/-- Popping preserves `Good`. -/
theorem pop_good {s : MState Proc Msg St} (h : S.Good s) : S.Good (S.pop s) := by
  rcases s with ⟨i, _ | ⟨e, rest⟩, C⟩
  · exact h
  · exact ⟨h.1.2, h.2⟩

variable (pre : Schedule Proc Msg) (C₀ : Config Proc Msg St)

/-- Every machine state is `Good` when the start is. -/
theorem states_good (h0 : Appl P C₀ pre ∧ S.Inv (exec P C₀ pre)) :
    ∀ k, S.Good (S.states pre C₀ k) := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih => exact S.pop_good (S.refill_good ih).1

/-- Popping keeps the stage index. -/
theorem pop_idx (s : MState Proc Msg St) : (S.pop s).idx = s.idx := by
  rcases s with ⟨i, _ | ⟨e, rest⟩, C⟩ <;> rfl

/-- Refilling increments the stage index by at most one. -/
theorem refill_idx (s : MState Proc Msg St) : (S.refill s).idx ≤ s.idx + 1 := by
  rcases s with ⟨i, _ | ⟨e, rest⟩, C⟩ <;> simp [refill]

/-- The stage index grows by at most one per tick. -/
theorem idx_le (k : ℕ) : (S.states pre C₀ k).idx ≤ k := by
  induction k with
  | zero => exact le_refl 0
  | succ k ih =>
    show (S.pop (S.refill (S.states pre C₀ k))).idx ≤ k + 1
    rw [S.pop_idx]
    exact (S.refill_idx _).trans (by omega)

/-- The event executed at tick `k` (`d` is an unreachable default). -/
def ev (d : Event Proc Msg) (k : ℕ) : Event Proc Msg :=
  (S.refill (S.states pre C₀ k)).pend.headD d

/-- With a pending event, a tick executes exactly that event. -/
theorem tick_of_cons {k : ℕ} {e : Event Proc Msg} {rest : Schedule Proc Msg}
    (d : Event Proc Msg) (hk : (S.states pre C₀ k).pend = e :: rest) :
    S.ev pre C₀ d k = e ∧
      S.states pre C₀ (k + 1) = ⟨(S.states pre C₀ k).idx, rest, apply P (S.states pre C₀ k).cfg e⟩ := by
  show (S.refill (S.states pre C₀ k)).pend.headD d = e ∧ S.pop (S.refill (S.states pre C₀ k)) = _
  generalize S.states pre C₀ k = s at hk ⊢
  rcases s with ⟨i, l, C⟩
  dsimp only at hk
  subst hk
  exact ⟨rfl, rfl⟩

/-- At a stage boundary, a tick starts the stage for target `tgt idx`. -/
theorem tick_of_nil {k : ℕ} (d : Event Proc Msg) (hk : (S.states pre C₀ k).pend = [])
    (hI : S.Inv (S.states pre C₀ k).cfg) :
    ∃ e rest, S.stage (S.states pre C₀ k).cfg (S.tgt (S.states pre C₀ k).idx) = e :: rest ∧
      S.ev pre C₀ d k = e ∧
      S.states pre C₀ (k + 1) = ⟨(S.states pre C₀ k).idx + 1, rest, apply P (S.states pre C₀ k).cfg e⟩ := by
  show ∃ e rest, _ ∧ (S.refill (S.states pre C₀ k)).pend.headD d = e ∧
    S.pop (S.refill (S.states pre C₀ k)) = _
  generalize S.states pre C₀ k = s at hk hI ⊢
  rcases s with ⟨i, l, C⟩
  dsimp only at hk hI
  subst hk
  have hne := S.nonempty C (S.tgt i) hI
  generalize hst : S.stage C (S.tgt i) = l at hne
  rcases l with _ | ⟨e, rest⟩
  · exact absurd rfl hne
  · refine ⟨e, rest, rfl, ?_, ?_⟩ <;> simp [refill, pop, hst]

/-- Executing a pending list `l` reaches a boundary after `l.length` ticks. -/
theorem pend_run (l : Schedule Proc Msg) : ∀ k, (S.states pre C₀ k).pend = l →
    (S.states pre C₀ (k + l.length)).pend = [] ∧
    (S.states pre C₀ (k + l.length)).cfg = exec P (S.states pre C₀ k).cfg l ∧
    (S.states pre C₀ (k + l.length)).idx = (S.states pre C₀ k).idx := by
  induction l with
  | nil => intro k hk; exact ⟨hk, rfl, rfl⟩
  | cons e rest ih =>
    intro k hk
    obtain ⟨-, hs⟩ := S.tick_of_cons pre C₀ e hk
    obtain ⟨h1, h2, h3⟩ := ih (k + 1) (by rw [hs])
    rw [show k + (e :: rest).length = k + 1 + rest.length by simp; omega]
    rw [hs] at h2 h3
    exact ⟨h1, h2, h3⟩

/-- Every pending event is eventually executed. -/
theorem pend_events (d : Event Proc Msg) (l : Schedule Proc Msg) : ∀ k,
    (S.states pre C₀ k).pend = l → ∀ e ∈ l, ∃ j, k ≤ j ∧ S.ev pre C₀ d j = e := by
  induction l with
  | nil => intro k _ e he; cases he
  | cons a rest ih =>
    intro k hk e he
    obtain ⟨h1, hs⟩ := S.tick_of_cons pre C₀ d hk
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨k, le_refl k, h1⟩
    · obtain ⟨j, hj, hev⟩ := ih (k + 1) (by rw [hs]) e he
      exact ⟨j, by omega, hev⟩

end Sched

end Async
end FLP
end Distributed
